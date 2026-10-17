"""Isolated durable issued views over already closed offline source snapshots."""

from __future__ import annotations

from contextlib import contextmanager, nullcontext
from datetime import datetime, timezone
import fcntl
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import shutil
import sqlite3
import stat
import tempfile
import threading
import time
from typing import Any, Iterator
import uuid

from .policy import (
    AccessContext,
    HostPolicy,
    PolicyRedactionError,
    assert_visible_output,
    authorize_envelope,
    context_binding,
    merge_envelopes,
    redact_output,
    redact_values,
)
from .references import (
    ProjectionError,
    ViewRef,
    canonical_json,
    sha256_digest,
    valid_digest,
    validate_ref,
)

FORMAT_VERSION = 1
CHUNK_BYTES = 256 * 1024
MAX_OBJECT_BYTES = 128 * 1024 * 1024
TRANSFORMS = ("json-v1", "text-v1")
RECOVERY_TABLES = frozenset({
    "projection_meta", "views", "associations", "association_heads",
    "association_commands", "association_command_conflicts", "view_objects",
})

SCHEMA_SQL = """
                    CREATE TABLE IF NOT EXISTS projection_meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
                    CREATE TABLE IF NOT EXISTS views(
                        view_id TEXT PRIMARY KEY, manifest_digest TEXT UNIQUE NOT NULL,
                        format_version INTEGER NOT NULL, source_pair_refs TEXT NOT NULL,
                        policy_binding TEXT NOT NULL, extraction_version TEXT NOT NULL,
                        coverage TEXT NOT NULL, installed_at TEXT NOT NULL);
                    CREATE TABLE IF NOT EXISTS associations(
                        relation_id TEXT NOT NULL, revision INTEGER NOT NULL,
                        predecessor_revision INTEGER, body_digest TEXT NOT NULL,
                        body_object_ref TEXT NOT NULL, command_id TEXT NOT NULL,
                        PRIMARY KEY(relation_id,revision));
                    CREATE TABLE IF NOT EXISTS association_heads(relation_id TEXT PRIMARY KEY, revision INTEGER NOT NULL);
                    CREATE TABLE IF NOT EXISTS association_commands(command_id TEXT PRIMARY KEY,
                        canonical_body_digest TEXT NOT NULL, outcome TEXT NOT NULL, envelope TEXT NOT NULL);
                    CREATE TABLE IF NOT EXISTS association_command_conflicts(command_id TEXT NOT NULL,
                        canonical_body_digest TEXT NOT NULL, PRIMARY KEY(command_id,canonical_body_digest));
                    CREATE TABLE IF NOT EXISTS view_objects(
                        object_digest TEXT PRIMARY KEY, byte_length INTEGER NOT NULL,
                        codec TEXT NOT NULL, sidecar_blob_locator TEXT NOT NULL);
                """


@lru_cache(maxsize=1)
def _owned_schema() -> tuple[tuple[Any, ...], ...]:
    connection = sqlite3.connect(":memory:")
    try:
        connection.executescript(SCHEMA_SQL)
        return tuple(connection.execute(
            "SELECT type,name,tbl_name,sql FROM sqlite_master ORDER BY type,name"
        ))
    finally:
        connection.close()


def _overlaps(a: Path, b: Path) -> bool:
    return a == b or a in b.parents or b in a.parents


def _without_symlinks(path: Path) -> None:
    for current in (path, *path.parents):
        if current.is_symlink():
            raise ProjectionError(
                "observation_unavailable", "symlink aliases are not sidecar locations"
            )


def _private_directory(path: Path) -> None:
    info = path.lstat()
    if (
        not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.getuid()
        or info.st_mode & 0o077
    ):
        raise ProjectionError(
            "observation_unavailable",
            "sidecar directories must be private to their owner",
        )


class ViewStore:
    """The selected directory must be disjoint from all source and scan roots.

    The host supplies the complete source/scanner inventory. Source adapters close
    their inputs before calling materialize_view. No canonical owner is imported.
    """

    def __init__(
        self,
        directory: str | Path,
        *,
        source_roots: list[str | Path] | tuple[str | Path, ...],
        scanner_roots: list[str | Path] | tuple[str | Path, ...] = (),
        max_storage_bytes: int = 512 * 1024 * 1024,
        create: bool = True,
    ):
        if type(max_storage_bytes) is not int or max_storage_bytes <= 0:
            raise ProjectionError("observation_unavailable", "invalid storage ceiling")
        self.directory = Path(os.path.abspath(directory))
        self.source_roots = tuple(Path(os.path.abspath(p)) for p in source_roots)
        self.scanner_roots = tuple(Path(os.path.abspath(p)) for p in scanner_roots)
        self._write_mutex = threading.RLock()
        self._write_state = threading.local()
        if not self.source_roots:
            raise ProjectionError(
                "observation_unavailable", "source roots must be explicitly declared"
            )
        _without_symlinks(self.directory)
        for parent in self.directory.parents:
            if parent.exists():
                mode = parent.stat().st_mode
                if mode & 0o022 and not mode & stat.S_ISVTX:
                    raise ProjectionError(
                        "observation_unavailable",
                        "sidecar ancestors permit unrelated directory replacement",
                    )
        for root in (*self.source_roots, *self.scanner_roots):
            if _overlaps(self.directory.resolve(), root.resolve()):
                raise ProjectionError(
                    "observation_unavailable",
                    "sidecar overlaps a source or scanner root",
                )
        self.max_storage_bytes = max_storage_bytes
        if not self.directory.exists():
            if not create:
                raise ProjectionError("observation_unavailable")
            self.directory.mkdir(mode=0o700, parents=True)
        _private_directory(self.directory)
        self._directory_identity = (
            self.directory.stat().st_dev,
            self.directory.stat().st_ino,
        )
        self.blobs = self.directory / "blobs"
        self.objects = self.directory / "objects"
        self.database = self.directory / "projection.sqlite3"
        for path in (self.blobs, self.objects):
            if not path.exists() and create and not self.database.exists():
                path.mkdir(mode=0o700, exist_ok=True)
            _private_directory(path)
        self._check_paths()
        if not self.database.exists() and not create:
            raise ProjectionError("observation_unavailable")
        if self.database.exists():
            self.namespace = self._existing_namespace()
        elif create:
            with self.write_lock():
                # Another opener may have initialized the sidecar while this
                # one waited. Existing formats are never bootstrapped or repaired.
                if self.database.exists():
                    self.namespace = self._existing_namespace()
                else:
                    self._initialize_database()
                    self.namespace = self._existing_namespace()
        if create:
            # A durable file inside a newly created directory does not itself
            # persist that directory's name in its parent after a power loss.
            for path in (
                self.blobs,
                self.objects,
                self.directory,
                *self.directory.parents,
            ):
                descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
                try:
                    os.fsync(descriptor)
                finally:
                    os.close(descriptor)

    def _initialize_database(self) -> None:
        with self._connection() as connection:
            connection.executescript(SCHEMA_SQL)
            connection.execute(
                "INSERT OR IGNORE INTO projection_meta VALUES ('format_version', ?)",
                (str(FORMAT_VERSION),),
            )
            connection.execute(
                "INSERT OR IGNORE INTO projection_meta VALUES ('namespace', ?)",
                ("projection:" + uuid.uuid4().hex,),
            )

    def _existing_namespace(self) -> str:
        """Validate retained metadata before any schema or bootstrap write."""
        try:
            with self._connect(readonly=True) as connection:
                return self._namespace_from_connection(connection)
        except sqlite3.Error as error:
            if (
                getattr(error, "sqlite_errorcode", None)
                == sqlite3.SQLITE_READONLY_ROLLBACK
            ):
                return self._recover_existing_namespace()
            raise ProjectionError(
                "observation_unavailable", "unsupported sidecar format"
            ) from error

    @staticmethod
    def _namespace_from_connection(connection: sqlite3.Connection) -> str:
        """Inspect only supported real metadata tables, with bounded values."""
        previous_limit = connection.setlimit(sqlite3.SQLITE_LIMIT_LENGTH, 64 * 1024)
        try:
            tables = {
                row[0]
                for row in connection.execute(
                    "SELECT name FROM sqlite_master WHERE type='table' LIMIT 64"
                )
            }
            required = {
                "projection_meta",
                "views",
                "associations",
                "association_heads",
                "association_commands",
                "association_command_conflicts",
                "view_objects",
            }
            if not required <= tables:
                raise ProjectionError(
                    "observation_unavailable", "unsupported sidecar format"
                )
            metadata = dict(
                connection.execute("SELECT key,value FROM projection_meta LIMIT 3")
            )
            namespace = metadata.get("namespace")
            if (
                metadata.get("format_version") != str(FORMAT_VERSION)
                or not isinstance(namespace, str)
                or not namespace.startswith("projection:")
                or len(metadata) != 2
            ):
                raise ProjectionError(
                    "observation_unavailable", "unsupported sidecar format"
                )
            return namespace
        finally:
            connection.setlimit(sqlite3.SQLITE_LIMIT_LENGTH, previous_limit)

    def _recover_existing_namespace(self) -> str:
        """Recover an interrupted isolated write after validating a private copy.

        SQLite must write to replay a hot rollback journal. Recovering a bounded
        copy first keeps unsupported retained formats unchanged. The original
        journal is never removed by application code or treated as disposable.
        """
        if not (self.directory / ".write.lock").is_file():
            raise ProjectionError(
                "observation_unavailable", "unsupported sidecar format"
            )
        with self.write_lock():
            journal = Path(str(self.database) + "-journal")
            if not journal.exists():
                # A preceding opener may already have completed recovery.
                with self._connection(readonly=True) as connection:
                    return self._namespace_from_connection(connection)
            deadline = time.monotonic() + 10.0
            self._check_capacity()
            try:
                with self._recovery_staging_directory() as temporary:
                    clone = temporary / self.database.name
                    signatures = {}
                    remaining = self.max_storage_bytes
                    for original in (self.database, journal):
                        destination = temporary / original.name
                        signature = self._copy_recovery_file(
                            original, destination, remaining, deadline
                        )
                        signatures[original] = signature
                        remaining -= signature[2]
                    self._validate_recovery_files(clone, Path(str(clone) + "-journal"), deadline)
                    receipt_bytes = self._read_file(self.directory / "recovery-state.json", maximum=4096)
                    try:
                        receipt = json.loads(receipt_bytes)
                    except (ValueError, RecursionError) as error:
                        raise ProjectionError("observation_unavailable", "invalid recovery state") from error
                    if (
                        not isinstance(receipt, dict)
                        or set(receipt) != {"version", "namespace", "state_digest"}
                        or type(receipt["version"]) is not int
                        or receipt["version"] != 1
                        or not valid_digest(receipt["state_digest"])
                    ):
                        raise ProjectionError("observation_unavailable", "invalid recovery state")
                    connection = sqlite3.connect(
                        clone.as_uri() + "?mode=rw", uri=True, timeout=1.0
                    )
                    try:
                        connection.set_progress_handler(
                            lambda: int(time.monotonic() >= deadline), 1000
                        )
                        self._configure_durability(connection)
                        expected = self._namespace_from_connection(connection)
                        state = self._recovery_state(connection, deadline)
                        connection.set_progress_handler(
                            lambda: int(time.monotonic() >= deadline), 1000
                        )
                        if (
                            expected != receipt["namespace"]
                            or state != receipt["state_digest"]
                            or connection.execute("PRAGMA integrity_check").fetchall() != [("ok",)]
                        ):
                            raise ProjectionError("observation_unavailable", "recovered state differs from committed state")
                    finally:
                        connection.close()
                    if time.monotonic() >= deadline:
                        raise ProjectionError(
                            "observation_unavailable", "recovery timed out"
                        )
                    self._check_paths()
                    if self._read_file(self.directory / "recovery-state.json", maximum=4096) != receipt_bytes:
                        raise ProjectionError("observation_unavailable", "recovery state changed")
                    for original, expected_signature in signatures.items():
                        info = original.stat()
                        if self._file_signature(info) != expected_signature:
                            raise ProjectionError(
                                "observation_unavailable", "recovery inputs changed"
                            )
                # Only SQLite rolls back the now-validated original. Its normal
                # locks and the sidecar writer lock serialize this with writers.
                with self._connection() as connection:
                    connection.set_progress_handler(
                        lambda: int(time.monotonic() >= deadline), 1000
                    )
                    namespace = self._namespace_from_connection(connection)
                    if namespace != expected:
                        raise ProjectionError(
                            "observation_unavailable", "recovery metadata changed"
                        )
                    return namespace
            except (OSError, sqlite3.Error) as error:
                raise ProjectionError(
                    "observation_unavailable", "sidecar recovery unavailable"
                ) from error

    @contextmanager
    def _recovery_staging_directory(self) -> Iterator[Path]:
        """Create a private external copy location after checking its exact path.

        The default tempfile selection can probe TMPDIR before returning a path.
        Avoid it, including its cached directory, because even those probe writes
        must stay outside protected trees. A sibling normally shares the sidecar's
        safe ancestors; explicit alternatives support an unwritable parent.
        """
        failure: OSError | ProjectionError | None = None
        parents = dict.fromkeys((self.directory.parent, Path("/tmp"), Path("/var/tmp")))
        for parent in parents:
            self._check_paths()
            temporary = parent / ("projection-recovery-" + uuid.uuid4().hex)
            try:
                _without_symlinks(temporary)
                for ancestor in temporary.parents:
                    mode = ancestor.stat().st_mode
                    if mode & 0o022 and not mode & stat.S_ISVTX:
                        raise ProjectionError(
                            "observation_unavailable", "unsafe recovery staging ancestor"
                        )
                for root in (*self.source_roots, *self.scanner_roots):
                    if _overlaps(temporary.resolve(), root.resolve()):
                        raise ProjectionError(
                            "observation_unavailable", "recovery staging overlaps a protected root"
                        )
                temporary.mkdir(mode=0o700)
            except (OSError, ProjectionError) as error:
                failure = error
                continue
            try:
                _private_directory(temporary)
                yield temporary
            finally:
                shutil.rmtree(temporary)
            return
        raise ProjectionError(
            "observation_unavailable", "isolated recovery staging unavailable"
        ) from failure

    @staticmethod
    def _file_signature(info: os.stat_result) -> tuple[int, int, int, int, int]:
        return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns

    def _copy_recovery_file(
        self, original: Path, destination: Path, maximum: int, deadline: float
    ) -> tuple[int, int, int, int, int]:
        descriptor = os.open(original, os.O_RDONLY | os.O_NOFOLLOW)
        try:
            before = os.fstat(descriptor)
            if before.st_size > maximum:
                raise ProjectionError(
                    "observation_unavailable", "recovery exceeds storage ceiling"
                )
            with (
                os.fdopen(descriptor, "rb", closefd=False) as source,
                destination.open("xb") as target,
            ):
                total = 0
                while chunk := source.read(CHUNK_BYTES):
                    total += len(chunk)
                    if total > before.st_size or time.monotonic() >= deadline:
                        raise ProjectionError(
                            "observation_unavailable", "recovery copy changed or timed out"
                        )
                    target.write(chunk)
            signature = self._file_signature(before)
            if total != before.st_size or signature != self._file_signature(os.fstat(descriptor)):
                raise ProjectionError(
                    "observation_unavailable", "recovery inputs changed"
                )
            return signature
        finally:
            os.close(descriptor)

    def _validate_recovery_files(self, database: Path, journal: Path, deadline: float) -> None:
        """Admit only bounded single-database DELETE-mode recovery inputs."""
        with database.open("rb") as stream:
            header = stream.read(100)
        if header[:16] != b"SQLite format 3\x00" or header[18:20] != b"\x01\x01":
            raise ProjectionError("observation_unavailable", "unsupported sidecar format")
        database_page_size = int.from_bytes(header[16:18], "big")
        if database_page_size == 1:
            database_page_size = 65536
        with journal.open("rb") as stream:
            header = stream.read(28)
            stream.seek(-min(journal.stat().st_size, 8), os.SEEK_END)
            trailer = stream.read(8)
        magic = bytes.fromhex("d9d505f920a163d7")
        # SQLite may leave an empty journal or zero magic before synchronization.
        # Such an interrupted write has no committed rollback records here.
        # The staged database must still match the durable committed state;
        # this admission alone never permits recovery or journal removal.
        if (not header or header[:8] == bytes(8)) and trailer != magic:
            return
        page_size = int.from_bytes(header[24:28], "big")
        original_pages = int.from_bytes(header[16:20], "big")
        sector_size = int.from_bytes(header[20:24], "big")
        if (
            len(header) != 28
            or header[:8] != magic
            or not 512 <= page_size <= 65536
            or page_size & (page_size - 1)
            or page_size != database_page_size
            or not 512 <= sector_size <= 65536
            or sector_size & (sector_size - 1)
            or not original_pages
            or original_pages * page_size > self.max_storage_bytes
            # Ordinary sidecar transactions never shrink the database file.
            # Recovery therefore must not expand the bounded copied image.
            or original_pages * page_size > database.stat().st_size
            # A super-journal can name databases outside the isolated sidecar.
            # This store never uses ATTACH, so such journals are unsupported.
            or trailer == magic
        ):
            raise ProjectionError("observation_unavailable", "unsupported sidecar recovery journal")
        size = journal.stat().st_size
        seen: set[int] = set()
        offset = 0
        with journal.open("rb") as stream:
            while offset < size:
                stream.seek(offset)
                segment = stream.read(sector_size)
                # A cache spill can leave synced segments followed by an
                # unfinished zero-magic segment. SQLite replays only the synced
                # prefix, which must restore the independently retained state.
                if segment[:8] == bytes(8):
                    return
                if (
                    len(segment) != sector_size
                    or segment[:8] != magic
                    or int.from_bytes(segment[16:20], "big") != original_pages
                    or int.from_bytes(segment[20:24], "big") != sector_size
                    or int.from_bytes(segment[24:28], "big") != page_size
                    or any(segment[28:])
                ):
                    raise ProjectionError("observation_unavailable", "invalid recovery journal segment")
                count = int.from_bytes(segment[8:12], "big")
                nonce = int.from_bytes(segment[12:16], "big")
                offset += sector_size
                if not count:
                    return
                if count == 0xFFFFFFFF:
                    count, remainder = divmod(size - offset, page_size + 8)
                    if remainder:
                        raise ProjectionError("observation_unavailable", "incomplete recovery journal")
                if not count or count > (size - offset) // (page_size + 8):
                    raise ProjectionError("observation_unavailable", "incomplete recovery journal")
                for _ in range(count):
                    if time.monotonic() >= deadline:
                        raise ProjectionError("observation_unavailable", "recovery timed out")
                    record = stream.read(page_size + 8)
                    number = int.from_bytes(record[:4], "big")
                    page = record[4:-4]
                    checksum = (nonce + sum(page[page_size - 200::-200])) & 0xFFFFFFFF
                    if (
                        not 1 <= number <= original_pages
                        or number in seen
                        or int.from_bytes(record[-4:], "big") != checksum
                    ):
                        raise ProjectionError("observation_unavailable", "invalid recovery journal page")
                    seen.add(number)
                    offset += page_size + 8
                if offset == size:
                    break
                aligned = ((offset + sector_size - 1) // sector_size) * sector_size
                if aligned > size or any(stream.read(aligned - offset)):
                    raise ProjectionError("observation_unavailable", "invalid recovery journal padding")
                offset = aligned

    def _recovery_state(
        self, connection: sqlite3.Connection, deadline: float,
        *, maximum_bytes: int | None = None,
    ) -> str:
        """Hash every owned schema entry and row, excluding unused page bytes.

        SQLite does not journal freelist leaf contents. Logical state equality
        therefore admits normal free-page reuse while covering every retained
        view, association, command outcome, index definition and metadata value.
        """
        maximum = self.max_storage_bytes if maximum_bytes is None else maximum_bytes
        previous_limit = connection.setlimit(sqlite3.SQLITE_LIMIT_LENGTH, min(MAX_OBJECT_BYTES, maximum))
        connection.set_progress_handler(lambda: int(time.monotonic() >= deadline), 1000)
        try:
            schema = [tuple(row) for row in connection.execute(
                "SELECT type,name,tbl_name,rootpage,sql FROM sqlite_master ORDER BY type,name LIMIT 64"
            )]
            if tuple((row[0], row[1], row[2], row[4]) for row in schema) != _owned_schema():
                raise ProjectionError("observation_unavailable", "unsupported sidecar format")
            digest = hashlib.sha256(canonical_json(schema))
            for pragma in (
                "application_id", "user_version", "schema_version", "encoding",
                "page_size", "auto_vacuum", "page_count", "freelist_count",
            ):
                digest.update(canonical_json((pragma, tuple(connection.execute(f"PRAGMA {pragma}").fetchone()))))
            remaining = maximum * 6
            for table in sorted(RECOVERY_TABLES):
                digest.update(canonical_json(table))
                for row in connection.execute(f'SELECT rowid,* FROM "{table}" ORDER BY rowid'):
                    if time.monotonic() >= deadline:
                        raise ProjectionError("observation_unavailable", "recovery state timed out")
                    if any(value is not None and type(value) not in {int, str} for value in row):
                        raise ProjectionError("observation_unavailable", "unsupported sidecar value")
                    value = canonical_json(tuple(row))
                    remaining -= len(value)
                    if remaining < 0:
                        raise ProjectionError("observation_unavailable", "recovery state exceeds storage ceiling")
                    digest.update(len(value).to_bytes(8, "big"))
                    digest.update(value)
            return digest.hexdigest()
        finally:
            connection.setlimit(sqlite3.SQLITE_LIMIT_LENGTH, previous_limit)
            connection.set_progress_handler(None, 0)

    def _save_recovery_state(self, connection: sqlite3.Connection) -> None:
        # Empty bootstrap has no acknowledged records. Its first ordinary write
        # installs the same receipt as an existing clean store adopting recovery.
        if not connection.execute("SELECT 1 FROM sqlite_master LIMIT 1").fetchone():
            return
        self._install_recovery_state(self._recovery_state_record(connection))

    def _recovery_state_record(
        self, connection: sqlite3.Connection, *, maximum_bytes: int | None = None,
    ) -> bytes:
        return canonical_json({
            "version": 1,
            "namespace": self._namespace_from_connection(connection),
            "state_digest": self._recovery_state(
                connection, time.monotonic() + 10.0, maximum_bytes=maximum_bytes,
            ),
        })

    def _acknowledge_replay(self) -> None:
        """Durably bind an existing command before returning its saved outcome.

        A failed postcommit state installation leaves the SQLite commit intact.
        A later exact replay must finish that installation before acknowledging
        success. Matching state needs no allocation or SQLite write transaction.
        """
        with self.write_lock(), self._connect(readonly=True) as connection:
            # A smaller write quota must not disable an allocation-free replay
            # of existing data. Reads remain bounded by its retained file size.
            content = self._recovery_state_record(
                connection,
                maximum_bytes=max(self.max_storage_bytes, self.database.stat().st_size),
            )
            path = self.directory / "recovery-state.json"
            if path.exists() and self._read_file(path, maximum=4096) == content:
                descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
                try:
                    os.fsync(descriptor)
                finally:
                    os.close(descriptor)
                directory_fd = os.open(self.directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
                try:
                    os.fsync(directory_fd)
                finally:
                    os.close(directory_fd)
            else:
                self._install_recovery_state(content)

    def _install_recovery_state(self, content: bytes) -> None:
        self._check_capacity(self._allocation_budget(len(content)))
        descriptor, name = tempfile.mkstemp(prefix=".recovery-", dir=self.directory)
        temporary = Path(name)
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(content)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, self.directory / "recovery-state.json")
            directory_fd = os.open(self.directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        finally:
            temporary.unlink(missing_ok=True)

    @staticmethod
    def _configure_durability(connection: sqlite3.Connection) -> None:
        # EXTRA includes the containing-directory sync after DELETE journal
        # unlink, so a returned commit does not depend on an unsynced unlink.
        connection.execute("PRAGMA synchronous=EXTRA")
        mode = connection.execute("PRAGMA journal_mode").fetchone()[0]
        if mode != "delete":
            raise ProjectionError("observation_unavailable", "unsupported sidecar journal mode")
        if (
            connection.execute("PRAGMA journal_mode=DELETE").fetchone()[0] != "delete"
            or connection.execute("PRAGMA synchronous").fetchone()[0] != 3
        ):
            raise ProjectionError("storage_unavailable", "durable sidecar journal unavailable")

    @contextmanager
    def write_lock(self) -> Iterator[None]:
        """Serialize complete mutations across threads and processes, with a deadline."""
        if not self._write_mutex.acquire(timeout=1.0):
            raise ProjectionError("storage_unavailable", "sidecar writer busy")
        descriptor = None
        try:
            if getattr(self._write_state, "active", False):
                yield
                return
            self._check_paths()
            descriptor = os.open(
                self.directory / ".write.lock",
                os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW,
                0o600,
            )
            info = os.fstat(descriptor)
            if (
                not stat.S_ISREG(info.st_mode)
                or info.st_nlink != 1
                or info.st_uid != os.getuid()
            ):
                raise ProjectionError("storage_unavailable", "unsafe writer lock")
            deadline = time.monotonic() + 1.0
            while True:
                try:
                    fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise ProjectionError(
                            "storage_unavailable", "sidecar writer busy"
                        ) from None
                    time.sleep(0.01)
            self._write_state.active = True
            self._check_paths()
            yield
        finally:
            if descriptor is not None:
                self._write_state.active = False
                os.close(descriptor)
            self._write_mutex.release()

    def _check_paths(self) -> None:
        _without_symlinks(self.directory)
        _private_directory(self.directory)
        info = self.directory.stat()
        if (info.st_dev, info.st_ino) != self._directory_identity:
            raise ProjectionError(
                "observation_unavailable", "sidecar directory identity changed"
            )
        for root in (*self.source_roots, *self.scanner_roots):
            if _overlaps(self.directory.resolve(), root.resolve()):
                raise ProjectionError(
                    "observation_unavailable", "source/scanner overlap changed"
                )
        for path in (self.blobs, self.objects):
            _private_directory(path)
        # Every installed file has a single link. This rejects aliases into any
        # canonical namespace, including hardlinks not covered by a scanner.
        for path in self.directory.rglob("*"):
            info = path.lstat()
            if stat.S_ISDIR(info.st_mode):
                _private_directory(path)
            elif (
                not stat.S_ISREG(info.st_mode)
                or info.st_nlink != 1
                or info.st_uid != os.getuid()
            ):
                raise ProjectionError(
                    "observation_unavailable", "unsafe sidecar file identity"
                )

    def _check_capacity(self, extra: int = 0) -> None:
        self._check_paths()
        used = self._storage_usage()
        if used + extra > self.max_storage_bytes:
            raise ProjectionError(
                "storage_unavailable", "sidecar storage ceiling reached"
            )

    @staticmethod
    def _allocated_size(path: Path) -> int:
        info = path.stat()
        return max(info.st_size, info.st_blocks * 512)

    def _storage_usage(self) -> int:
        """Count file allocation and directories, retaining sparse-file lengths."""
        return self._allocated_size(self.directory) + sum(
            self._allocated_size(path) for path in self.directory.rglob("*")
        )

    def _allocation_budget(self, size: int) -> int:
        unit = os.statvfs(self.directory).f_frsize
        return ((size + unit - 1) // unit) * unit

    @contextmanager
    def _connect(self, readonly: bool = False) -> Iterator[sqlite3.Connection]:
        with nullcontext() if readonly else self.write_lock():
            journal = Path(str(self.database) + "-journal")
            if journal.exists():
                self._recover_existing_namespace()
            with self._connection(readonly=readonly) as connection:
                if not readonly:
                    self._save_recovery_state(connection)
                    connection.execute("BEGIN IMMEDIATE")
                    # The context owns this transaction. An inner commit or
                    # executescript must not create a second transaction using
                    # the first transaction's recovery state.
                    connection.set_authorizer(
                        lambda action, first, second, database, trigger:
                        sqlite3.SQLITE_DENY if action in {sqlite3.SQLITE_TRANSACTION, sqlite3.SQLITE_SAVEPOINT}
                        else sqlite3.SQLITE_OK
                    )
                try:
                    yield connection
                finally:
                    if not readonly:
                        connection.set_authorizer(None)

    @contextmanager
    def _connection(self, readonly: bool = False) -> Iterator[sqlite3.Connection]:
        self._check_paths()
        if self.database.exists():
            info = self.database.lstat()
            if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                raise ProjectionError("observation_unavailable", "unsafe database file")
            if info.st_size:
                descriptor = os.open(self.database, os.O_RDONLY | os.O_NOFOLLOW)
                with os.fdopen(descriptor, "rb") as stream:
                    header = stream.read(20)
                if header[18:20] != b"\x01\x01" or any(
                    Path(str(self.database) + suffix).exists()
                    for suffix in ("-wal", "-shm")
                ):
                    raise ProjectionError("observation_unavailable", "unsupported sidecar journal mode")
        elif not readonly:
            descriptor = os.open(
                self.database,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                0o600,
            )
            os.close(descriptor)
        connection = sqlite3.connect(
            self.database.as_uri() + ("?mode=ro" if readonly else "?mode=rw"),
            uri=True,
            timeout=1.0,
        )
        connection.row_factory = sqlite3.Row
        try:
            if readonly:
                connection.execute("PRAGMA query_only=ON")
            else:
                self._configure_durability(connection)
                # Reserve a complete rollback journal and its header before
                # SQLite can dirty pages. Bound database growth independently
                # of immutable blobs, under the enclosing writer lock.
                page_size = connection.execute("PRAGMA page_size").fetchone()[0]
                used = self._storage_usage()
                database_size = self.database.stat().st_size
                database_allocation = self._allocated_size(self.database)
                journal_records = database_size + (database_size // page_size) * 8
                reserve = self._allocation_budget(max(journal_records + 8192, 65536))
                maximum_pages = (
                    self.max_storage_bytes - used + database_allocation - reserve
                ) // page_size
                existing_pages = connection.execute("PRAGMA page_count").fetchone()[0]
                if maximum_pages < max(existing_pages, 1):
                    raise ProjectionError(
                        "storage_unavailable", "sidecar storage ceiling reached"
                    )
                connection.execute(f"PRAGMA max_page_count={maximum_pages}")
            yield connection
            self._check_paths()
            if not readonly:
                # New SQLite pages can still be in its cache. Include their
                # eventual file growth before acknowledging a durable commit.
                projected_size = (
                    connection.execute("PRAGMA page_count").fetchone()[0] * page_size
                )
                self._check_capacity(
                    max(
                        0,
                        self._allocation_budget(projected_size)
                        - self._allocated_size(self.database),
                    )
                )
                connection.commit()
                # A retained journal from a completed transaction must not be
                # reusable to erase an acknowledged commit. Publish its new
                # committed state before reporting success to the caller.
                self._save_recovery_state(connection)
                self._check_capacity()
        except BaseException:
            connection.rollback()
            raise
        finally:
            connection.close()

    def _read_file(self, path: Path, maximum: int = MAX_OBJECT_BYTES) -> bytes:
        self._check_paths()
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
        try:
            info = os.fstat(descriptor)
            if (
                not stat.S_ISREG(info.st_mode)
                or info.st_nlink != 1
                or info.st_size > maximum
            ):
                raise ProjectionError("view_unavailable")
            with os.fdopen(descriptor, "rb", closefd=False) as stream:
                content = stream.read(maximum + 1)
            if len(content) > maximum:
                raise ProjectionError("view_unavailable")
            after = os.fstat(descriptor)
            if (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns) != (
                after.st_dev,
                after.st_ino,
                after.st_size,
                after.st_mtime_ns,
            ):
                raise ProjectionError("view_unavailable")
            return content
        finally:
            os.close(descriptor)

    def _install_file(self, path: Path, content: bytes) -> None:
        self._check_paths()
        if path.exists():
            if self._read_file(path) != content:
                raise ProjectionError(
                    "storage_unavailable", "immutable object collision or corruption"
                )
            # A previous attempt may have renamed this exact orphan and then
            # failed to sync its directory. Existence is no durability receipt.
            descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
            directory_fd = os.open(
                path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
            )
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
            return
        self._check_capacity(self._allocation_budget(len(content)) + 65536)
        descriptor, name = tempfile.mkstemp(prefix=".pending-", dir=path.parent)
        temporary = Path(name)
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(content)
                stream.flush()
                os.fsync(stream.fileno())
            # Concurrent installers of this content address have identical bytes.
            # Replacing the private temporary name atomically avoids transient
            # hardlink aliases visible to concurrent isolation checks.
            if path.exists():
                if self._read_file(path) != content:
                    raise ProjectionError("storage_unavailable")
                temporary.unlink()
            else:
                os.replace(temporary, path)
            directory_fd = os.open(
                path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
            )
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        finally:
            temporary.unlink(missing_ok=True)

    def _install_object(self, content: bytes) -> str:
        if not isinstance(content, bytes) or len(content) > MAX_OBJECT_BYTES:
            raise ProjectionError(
                "storage_unavailable", "object exceeds the bounded installation limit"
            )
        digest = sha256_digest(content)
        chunks = []
        for offset in range(0, len(content), CHUNK_BYTES):
            chunk = content[offset : offset + CHUNK_BYTES]
            chunk_digest = sha256_digest(chunk)
            self._install_file(self.blobs / (chunk_digest + ".blob"), chunk)
            chunks.append({"digest": chunk_digest, "byte_length": len(chunk)})
        descriptor = canonical_json(
            {
                "format_version": FORMAT_VERSION,
                "object_digest": digest,
                "byte_length": len(content),
                "chunks": chunks,
            }
        )
        self._install_file(self.objects / (digest + ".json"), descriptor)
        return digest

    def _read_object(self, digest: str) -> bytes:
        if not valid_digest(digest):
            raise ProjectionError("view_unavailable")
        try:
            descriptor = json.loads(
                self._read_file(self.objects / (digest + ".json"), maximum=256 * 1024)
            )
        except (RecursionError, ValueError) as error:
            raise ProjectionError("view_unavailable") from error
        if not isinstance(descriptor, dict):
            raise ProjectionError("view_unavailable")
        if (
            descriptor.get("format_version") != FORMAT_VERSION
            or descriptor.get("object_digest") != digest
        ):
            raise ProjectionError("view_unavailable")
        size = descriptor.get("byte_length")
        chunks = descriptor.get("chunks")
        if (
            type(size) is not int
            or not 0 <= size <= MAX_OBJECT_BYTES
            or not isinstance(chunks, list)
            or len(chunks) > MAX_OBJECT_BYTES // CHUNK_BYTES + 1
        ):
            raise ProjectionError("view_unavailable")
        result = bytearray()
        for chunk in chunks:
            chunk_digest = chunk.get("digest")
            if not valid_digest(chunk_digest):
                raise ProjectionError("view_unavailable")
            data = self._read_file(
                self.blobs / (chunk_digest + ".blob"), maximum=CHUNK_BYTES
            )
            if (
                len(data) != chunk.get("byte_length")
                or sha256_digest(data) != chunk_digest
            ):
                raise ProjectionError("view_unavailable")
            result.extend(data)
            if len(result) > size:
                raise ProjectionError("view_unavailable")
        if len(result) != size or sha256_digest(result) != digest:
            raise ProjectionError("view_unavailable")
        return bytes(result)

    def materialize_view(
        self, snapshot: dict[str, Any], *, policy: HostPolicy, context: AccessContext
    ) -> dict[str, Any]:
        try:
            with self.write_lock():
                return self._materialize_view(snapshot, policy=policy, context=context)
        except (OSError, ProjectionError):
            return {"status": "observation_unavailable"}

    def _materialize_view(
        self, snapshot: dict[str, Any], *, policy: HostPolicy, context: AccessContext
    ) -> dict[str, Any]:
        try:
            if snapshot.get("sources_closed") is not True:
                return {"status": "source_unavailable"}
            # Round-trip severs caller-owned mutable structures before installing.
            snapshot = json.loads(canonical_json(snapshot))
            raw_envelope = snapshot.get("envelope")
            if not isinstance(raw_envelope, dict):
                return {"status": "not_authorized"}
            envelope = merge_envelopes(raw_envelope, {
                "dependencies": [], "context_bindings": [context_binding(context)],
            })
            if not self._authorize_envelope(envelope, policy, context):
                return {"status": "not_authorized"}
            snapshot["envelope"] = envelope
            for required in (
                "values",
                "source_pair_refs",
                "coverage",
                "extraction_version",
            ):
                if required not in snapshot:
                    return {"status": "source_unavailable"}
            visible = self._visible_snapshot(snapshot, policy, context)
            witness = self._install_policy_witness(
                {key: value for key, value in visible.items() if key != "envelope"},
                policy=policy,
                context=context,
            )
            envelope = merge_envelopes(
                envelope, {"dependencies": [], "redaction_witnesses": [witness]}
            )
            snapshot["envelope"] = envelope
            visible["envelope"] = envelope
            snapshot_bytes = canonical_json(snapshot)
            snapshot_object = self._install_object(snapshot_bytes)
            timestamp = datetime.now(timezone.utc).isoformat()
            manifest: dict[str, Any] = {
                "format_version": FORMAT_VERSION,
                "namespace": self.namespace,
                "issuance": uuid.uuid4().hex,
                "installed_at": timestamp,
                "snapshot_object": snapshot_object,
                "transforms": list(TRANSFORMS),
                "policy_binding": context_binding(context),
                "visible_digest": sha256_digest(canonical_json(visible)),
            }
            digest = self._install_object(canonical_json(manifest))
            self._check_capacity(65536)
            with self._connect() as connection:
                connection.execute(
                    "INSERT OR IGNORE INTO view_objects VALUES (?,?,?,?)",
                    (
                        snapshot_object,
                        len(snapshot_bytes),
                        "json-utf8",
                        snapshot_object,
                    ),
                )
                connection.execute(
                    "INSERT INTO views VALUES (?,?,?,?,?,?,?,?)",
                    (
                        self.namespace + ":view:" + manifest["issuance"],
                        digest,
                        FORMAT_VERSION,
                        canonical_json(snapshot["source_pair_refs"]).decode(),
                        manifest["policy_binding"],
                        str(snapshot["extraction_version"]),
                        canonical_json(snapshot["coverage"]).decode(),
                        timestamp,
                    ),
                )
            return {
                "status": "saved",
                "view_ref": ViewRef(self.namespace, digest).to_dict(),
            }
        except PolicyRedactionError:
            return {"status": "not_authorized"}
        except (
            OSError,
            sqlite3.Error,
            ValueError,
            TypeError,
            KeyError,
            ProjectionError,
        ):
            return {"status": "observation_unavailable"}

    @staticmethod
    def _visible_snapshot(
        snapshot: dict[str, Any], policy: HostPolicy, context: AccessContext
    ) -> dict[str, Any]:
        # Internal dependency locators are authorization inputs, not inspector
        # content. Keep them intact while filtering every emitted source value.
        content = {key: value for key, value in snapshot.items() if key != "envelope"}
        assert_visible_output(content, context)
        visible = redact_output(content, policy, context)
        assert_visible_output(visible, context)
        if (
            not isinstance(visible, dict)
            or visible.keys() != content.keys()
            or visible.get("sources_closed") is not True
            or visible.get("extraction_version") != content["extraction_version"]
        ):
            raise PolicyRedactionError("redaction changes the projection protocol")
        visible["envelope"] = snapshot["envelope"]
        return visible

    @staticmethod
    def _public_envelope(envelope: dict[str, Any]) -> dict[str, str]:
        """Expose a stable opaque binding without source-item locators."""
        return {"policy_binding": sha256_digest(canonical_json(envelope))}

    def _install_policy_witness(
        self,
        value: Any,
        *,
        policy: HostPolicy | None = None,
        context: AccessContext | None = None,
    ) -> dict[str, str]:
        """Pin already-authorized visible values for transitive policy checks."""
        if policy is not None and context is not None:
            text = canonical_json(value).decode("utf-8")
            record = {
                "value": value,
                "text_digest": sha256_digest(
                    policy.redact(text, context).encode("utf-8")
                ),
                "values_digest": sha256_digest(
                    canonical_json(redact_values(value, policy, context))
                ),
            }
            return {
                "object_digest": self._install_object(canonical_json(record)),
                "encoding": "visible-json-v1",
            }
        return {
            "object_digest": self._install_object(canonical_json(value)),
            "encoding": "json-v1",
        }

    def _authorize_envelope(
        self, envelope: dict[str, Any], policy: HostPolicy, context: AccessContext
    ) -> bool:
        return authorize_envelope(
            envelope,
            policy,
            context,
            witness_validator=lambda witness: self._policy_witness_valid(
                witness, policy, context
            ),
        )

    def _policy_witness_valid(
        self, witness: dict[str, Any], policy: HostPolicy, context: AccessContext
    ) -> bool:
        try:
            text = self._read_object(witness["object_digest"]).decode("utf-8")
            if witness["encoding"] == "association-output-v1":
                from .associations import AssociationStore

                return AssociationStore(self)._output_witness_valid(
                    json.loads(text), witness["object_digest"], witness["endpoint_applicability"],
                    policy=policy, context=context,
                )
            if witness["encoding"] == "visible-json-v1":
                record = json.loads(text)
                value = record["value"]
                current_text = policy.redact(
                    canonical_json(value).decode("utf-8"), context
                )
                current_values = canonical_json(redact_values(value, policy, context))
                return (
                    sha256_digest(current_text.encode("utf-8")) == record["text_digest"]
                    and sha256_digest(current_values) == record["values_digest"]
                )
            if policy.redact(text, context) != text:
                return False
            if witness["encoding"] == "json-v1":
                value = json.loads(text)
                # Older association witnesses captured a prepared body before
                # its final identity existed. They cannot establish transitive
                # contextual visibility, even if the old copy is still stored.
                if (isinstance(value, dict)
                        and {"kind", "source", "target", "scope", "evidence_refs", "prose",
                             "status", "author", "predecessor_revision"} <= value.keys()
                        and not {"relation_id", "revision"} <= value.keys()):
                    return False
                if redact_values(value, policy, context) != value:
                    return False
            elif witness["encoding"] != "text-v1":
                return False
            return True
        except (OSError, ValueError, TypeError, KeyError, ProjectionError):
            return False

    def read_view(
        self, ref: dict[str, Any], *, policy: HostPolicy, context: AccessContext
    ) -> dict[str, Any]:
        result = self._read_view_authorized(ref, policy=policy, context=context)
        if result.get("status") == "ok":
            result["snapshot"]["envelope"] = self._public_envelope(
                result["snapshot"]["envelope"]
            )
        return result

    def _read_view_authorized(
        self, ref: dict[str, Any], *, policy: HostPolicy, context: AccessContext,
        include_original_values: bool = False,
    ) -> dict[str, Any]:
        """Trusted consumers retain the exact transitive authorization envelope.

        Rendering and search request original values to filter each selected
        transform once while preserving the globally authorized visible value.
        Public reads never include these unfiltered implementation inputs.
        """
        try:
            ref = validate_ref(ref)
            if ref["kind"] != "view" or ref["namespace"] != self.namespace:
                return {"status": "view_unavailable"}
            with self._connect(readonly=True) as connection:
                row = connection.execute(
                    "SELECT * FROM views WHERE manifest_digest=?",
                    (ref["manifest_digest"],),
                ).fetchone()
            if row is None:
                return {"status": "view_unavailable"}
            manifest = json.loads(self._read_object(ref["manifest_digest"]))
            if (
                manifest["namespace"] != self.namespace
                or manifest["format_version"] != FORMAT_VERSION
                or row["format_version"] != FORMAT_VERSION
            ):
                return {"status": "view_unavailable"}
            if manifest["policy_binding"] != context_binding(context):
                return {"status": "not_authorized"}
            snapshot = json.loads(self._read_object(manifest["snapshot_object"]))
            source_envelope = {**snapshot["envelope"], "redaction_witnesses": []}
            if not authorize_envelope(source_envelope, policy, context):
                return {"status": "not_authorized"}
            visible = self._visible_snapshot(snapshot, policy, context)
            if sha256_digest(canonical_json(visible)) != manifest["visible_digest"]:
                return {"status": "stale_policy"}
            if not self._authorize_envelope(snapshot["envelope"], policy, context):
                return {"status": "not_authorized"}
            result = {
                "status": "ok",
                "view_ref": ref,
                "snapshot": visible,
                "transforms": manifest["transforms"],
                "policy_binding": manifest["policy_binding"],
            }
            if include_original_values:
                result["_original_values"] = snapshot["values"]
            return result
        except PolicyRedactionError:
            return {"status": "stale_policy"}
        except (
            OSError,
            sqlite3.Error,
            ValueError,
            TypeError,
            KeyError,
            AttributeError,
            ProjectionError,
        ):
            return {"status": "view_unavailable"}

    def delete_view(
        self, ref: dict[str, Any], *, policy: HostPolicy, context: AccessContext
    ) -> dict[str, Any]:
        result = self.read_view(ref, policy=policy, context=context)
        if result["status"] != "ok":
            return {"status": result["status"]}
        try:
            with self.write_lock(), self._connect() as connection:
                connection.execute(
                    "DELETE FROM views WHERE manifest_digest=?",
                    (ref["manifest_digest"],),
                )
            return {"status": "deleted"}
        except (OSError, sqlite3.Error, ProjectionError):
            return {"status": "observation_unavailable"}


def materialize_view(
    store: ViewStore,
    snapshot: dict[str, Any],
    *,
    policy: HostPolicy,
    context: AccessContext,
) -> dict[str, Any]:
    return store.materialize_view(snapshot, policy=policy, context=context)
