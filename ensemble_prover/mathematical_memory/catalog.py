"""Bounded local advisory ledger with immutable events and current safety masks.

Raw filesystem rollback cannot be detected without an external nonrollback
journal. Explicit restore/clone changes epoch and blocks history until a trusted
current reconciliation authority supplies complete invalidation coverage.
"""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import sqlite3
import tempfile
import time
import uuid
from dataclasses import dataclass
from collections.abc import Iterator
from typing import Any, Callable, Mapping

from .model import (
    SCHEMA_VERSION,
    CatalogView,
    EligibilityPolicy,
    EvidenceReference,
    GenerationPin,
    MemoryEvent,
    MemoryProvenance,
    StoreResult,
    canonical_json,
    content_digest,
    integer,
    strings,
    text,
)


class MemoryUnavailable(RuntimeError):
    """An advisory store operation has no usable result."""


@dataclass(frozen=True)
class AuthoritySnapshot:
    """Response from a configured trusted current invalidation authority.

    A serialized copy is never an authority. The caller must supply a live
    callback backed by independently retained complete invalidation history.
    """

    authority_id: str
    policy_version: int
    watermark: str
    complete: bool
    denied_event_ids: tuple[str, ...] = ()
    denied_source_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        text(self.authority_id, "authority identity")
        text(self.watermark, "authority watermark")
        integer(self.policy_version, "authority policy", 1)
        if type(self.complete) is not bool:
            raise ValueError("authority completeness requires a boolean")
        for seq in (self.denied_event_ids, self.denied_source_ids):
            for value in seq:
                text(value, "denied identity")


class MemoryCatalog:
    """Advisory storage with live, bounded controller snapshot callbacks.

    Both authority callbacks must read cached in-memory state without I/O or
    blocking locks. They grant visibility, never mathematical verification.
    """

    _root_fd: int | None
    outbox_event_cap: int
    outbox_byte_cap: int
    artifact_byte_cap: int
    query_scan_cap: int
    artifact_store_byte_cap: int
    artifact_count_cap: int
    event_count_cap: int
    event_byte_cap: int
    query_byte_cap: int

    def __init__(
        self,
        root: str | Path,
        *,
        outbox_event_cap: int = 256,
        outbox_byte_cap: int = 16 * 1024 * 1024,
        artifact_byte_cap: int = 16 * 1024 * 1024,
        query_scan_cap: int = 4096,
        artifact_store_byte_cap: int = 512 * 1024 * 1024,
        artifact_count_cap: int = 65536,
        read_only: bool = False,
        event_authority: Callable[[MemoryEvent], bool] | None = None,
        event_count_cap: int = 65536,
        event_byte_cap: int = 128 * 1024 * 1024,
        query_byte_cap: int = 8 * 1024 * 1024,
        current_authority: Callable[[MemoryProvenance, str], bool] | None = None,
        reconciliation_authority: Callable[[str], AuthoritySnapshot] | None = None,
    ) -> None:
        self.root = Path(root).absolute()
        self.read_only = read_only
        self.current_authority = current_authority
        self.event_authority = event_authority
        self.reconciliation_authority = reconciliation_authority
        for name, value in (
            ("outbox_event_cap", outbox_event_cap),
            ("outbox_byte_cap", outbox_byte_cap),
            ("artifact_byte_cap", artifact_byte_cap),
            ("query_scan_cap", query_scan_cap),
            ("artifact_store_byte_cap", artifact_store_byte_cap),
            ("artifact_count_cap", artifact_count_cap),
            ("event_count_cap", event_count_cap),
            ("event_byte_cap", event_byte_cap),
            ("query_byte_cap", query_byte_cap),
        ):
            integer(value, name, 1)
            hard_limits = {
                "query_scan_cap": 4096,
                "outbox_event_cap": 4096,
                "artifact_byte_cap": 16 * 1024 * 1024,
                "outbox_byte_cap": 64 * 1024 * 1024,
                "artifact_store_byte_cap": 512 * 1024 * 1024,
                "artifact_count_cap": 65536,
                "event_count_cap": 65536,
                "event_byte_cap": 128 * 1024 * 1024,
                "query_byte_cap": 8 * 1024 * 1024,
            }
            if name in hard_limits and value > hard_limits[name]:
                raise ValueError(f"{name} exceeds the storage hard limit")
            setattr(self, name, value)
        self.db_path = self.root / "catalog.sqlite3"
        self.artifact_root = self.root / "artifacts"
        self.outbox_root = self.root / "outbox"
        from .evidence import contained_directory

        with contained_directory(self.root, create_parents=not read_only) as root_fd:
            self._root_fd = os.dup(root_fd)
            if not read_only:
                for name in ("artifacts", "outbox"):
                    try:
                        os.mkdir(name, mode=0o700, dir_fd=root_fd)
                    except FileExistsError:
                        pass
                    child = os.open(
                        name,
                        os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                        dir_fd=root_fd,
                    )
                    os.close(child)
        if not read_only:
            self._initialize()
        elif not self.db_path.is_file():
            raise MemoryUnavailable("memory catalog is unavailable")
        with self._connect() as conn:
            meta = dict(conn.execute("SELECT key,value FROM metadata"))
            if meta.get("schema") != str(SCHEMA_VERSION):
                raise MemoryUnavailable("unsupported memory catalog schema")
            self._location_matches = meta.get("location") == str(self.root.resolve())

    def close(self) -> None:
        descriptor = getattr(self, "_root_fd", None)
        if descriptor is not None:
            with contextlib.suppress(OSError):
                os.close(descriptor)
            self._root_fd = None

    def __del__(self) -> None:
        self.close()

    @staticmethod
    def _safe_components(path: Path) -> None:
        for candidate in (path, *path.parents):
            if candidate.is_symlink():
                raise MemoryUnavailable("memory paths cannot contain symbolic links")

    @contextlib.contextmanager
    def _connect(
        self, deadline_monotonic: float | None = None
    ) -> Iterator[sqlite3.Connection]:
        if self._root_fd is None:
            raise MemoryUnavailable("memory catalog is closed")
        # SQLite and its sidecars stay under the opened directory, even when
        # a checked ancestor is renamed or replaced during connection setup.
        descriptor = os.open(
            "catalog.sqlite3",
            os.O_RDONLY
            | os.O_NOFOLLOW
            | os.O_NONBLOCK
            | (0 if self.read_only else os.O_CREAT),
            0o600,
            dir_fd=self._root_fd,
        )
        import stat

        pinned_file = os.fstat(descriptor)
        if not stat.S_ISREG(pinned_file.st_mode) or pinned_file.st_nlink != 1:
            os.close(descriptor)
            raise MemoryUnavailable("catalog is not a regular private file")
        anchored_db = Path(f"/proc/self/fd/{descriptor}")
        if deadline_monotonic is not None and time.monotonic() >= deadline_monotonic:
            os.close(descriptor)
            raise MemoryUnavailable("memory deadline exhausted")
        wait_s = 0.05
        if deadline_monotonic is not None:
            wait_s = min(wait_s, max(0.0, deadline_monotonic - time.monotonic()))
        try:
            conn = sqlite3.connect(
                anchored_db.as_uri() + ("?mode=ro" if self.read_only else "?mode=rw"),
                uri=True,
                timeout=wait_s,
            )
        except BaseException:
            os.close(descriptor)
            raise
        try:
            current_file = os.stat(
                "catalog.sqlite3", dir_fd=self._root_fd, follow_symlinks=False
            )
            if not stat.S_ISREG(current_file.st_mode) or (
                current_file.st_dev,
                current_file.st_ino,
            ) != (pinned_file.st_dev, pinned_file.st_ino):
                raise MemoryUnavailable("catalog file changed during open")
            if deadline_monotonic is not None:
                conn.set_progress_handler(
                    lambda: int(time.monotonic() >= deadline_monotonic), 1000
                )
            if not self.read_only:
                conn.execute("PRAGMA synchronous=FULL")
            conn.row_factory = sqlite3.Row
            yield conn
            conn.commit()
        except sqlite3.OperationalError as exc:
            conn.set_progress_handler(None, 0)
            conn.rollback()
            if (
                deadline_monotonic is not None
                and time.monotonic() >= deadline_monotonic
            ):
                raise MemoryUnavailable("memory deadline exhausted") from exc
            raise
        except BaseException:
            conn.set_progress_handler(None, 0)
            conn.rollback()
            raise
        finally:
            conn.close()
            os.close(descriptor)

    def _initialize(self) -> None:
        lock_path = self.root / ".initialize.lock"
        self._safe_components(lock_path)
        fd = os.open(
            ".initialize.lock",
            os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW,
            0o600,
            dir_fd=self._root_fd,
        )
        try:
            deadline = time.monotonic() + 0.05
            while True:
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError as exc:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise MemoryUnavailable("memory initialization busy") from exc
                    time.sleep(min(0.002, remaining))
            self._initialize_locked()
        finally:
            os.close(fd)

    def _initialize_locked(self) -> None:
        with self._connect() as conn:
            has_meta = conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='metadata'"
            ).fetchone()
            if has_meta:
                meta = dict(conn.execute("SELECT key,value FROM metadata"))
                if meta.get("schema") != str(SCHEMA_VERSION):
                    raise MemoryUnavailable(
                        "unsupported memory catalog schema; use explicit migration"
                    )
                self._ensure_scope_index(conn)
                self._ensure_storage_accounting(conn)
                if meta.get("location") != str(self.root.resolve()):
                    conn.execute("BEGIN IMMEDIATE")
                    conn.execute(
                        "UPDATE metadata SET value=? WHERE key='epoch'",
                        (content_digest(uuid.uuid4().bytes),),
                    )
                    conn.execute("UPDATE metadata SET value='0' WHERE key='reconciled'")
                    conn.execute(
                        "UPDATE metadata SET value='1' WHERE key='requires_authority'"
                    )
                    conn.execute(
                        "UPDATE metadata SET value=? WHERE key='location'",
                        (str(self.root.resolve()),),
                    )
                    conn.commit()
                return
            conn.execute("PRAGMA journal_mode=WAL")
            conn.executescript("""
            CREATE TABLE metadata(key TEXT PRIMARY KEY, value TEXT NOT NULL);
            CREATE TABLE events(event_id TEXT PRIMARY KEY, sequence INTEGER NOT NULL,
                kind TEXT NOT NULL, payload TEXT NOT NULL, digest TEXT NOT NULL);
            CREATE INDEX event_sequence ON events(sequence);
            CREATE INDEX event_kind_sequence ON events(kind,sequence);
            CREATE TABLE invalidations(identity TEXT NOT NULL, kind TEXT NOT NULL,
                sequence INTEGER NOT NULL, reason TEXT NOT NULL,
                PRIMARY KEY(identity,kind));
            CREATE TABLE conflicts(event_id TEXT NOT NULL, digest TEXT NOT NULL,
                payload TEXT NOT NULL, sequence INTEGER NOT NULL,
                PRIMARY KEY(event_id,digest));
            """)
            for key, value in {
                "schema": str(SCHEMA_VERSION),
                "lineage": content_digest(uuid.uuid4().bytes),
                "epoch": content_digest(uuid.uuid4().bytes),
                "sequence": "0",
                "location": str(self.root.resolve()),
                "reconciled": "1",
                "requires_authority": "0",
            }.items():
                conn.execute("INSERT INTO metadata VALUES(?,?)", (key, value))
            self._ensure_scope_index(conn)
            self._ensure_storage_accounting(conn)

    @staticmethod
    def _ensure_storage_accounting(conn: sqlite3.Connection) -> None:
        if (
            conn.execute("SELECT 1 FROM metadata WHERE key='event_bytes'").fetchone()
            is None
        ):
            count, size = conn.execute(
                "SELECT COUNT(*),COALESCE(SUM(length(CAST(payload AS BLOB))),0) FROM events"
            ).fetchone()
            extra_count, extra_size = conn.execute(
                "SELECT COUNT(*),COALESCE(SUM(length(CAST(payload AS BLOB))),0) FROM conflicts"
            ).fetchone()
            masks, mask_bytes = conn.execute(
                "SELECT COUNT(*),COALESCE(SUM(length(CAST(identity||kind||reason AS BLOB))),0) FROM invalidations"
            ).fetchone()
            conn.execute(
                "INSERT INTO metadata VALUES('event_rows',?)",
                (str(count + extra_count + masks),),
            )
            conn.execute(
                "INSERT INTO metadata VALUES('event_bytes',?)",
                (str(size + extra_size + mask_bytes),),
            )

    def _charge_event_storage(self, conn: sqlite3.Connection, raw: str) -> bool:
        count = int(
            conn.execute(
                "SELECT value FROM metadata WHERE key='event_rows'"
            ).fetchone()[0]
        )
        size = int(
            conn.execute(
                "SELECT value FROM metadata WHERE key='event_bytes'"
            ).fetchone()[0]
        )
        cost = len(raw.encode("utf-8"))
        if count >= self.event_count_cap or size + cost > self.event_byte_cap:
            return False
        conn.execute(
            "UPDATE metadata SET value=? WHERE key='event_rows'", (str(count + 1),)
        )
        conn.execute(
            "UPDATE metadata SET value=? WHERE key='event_bytes'", (str(size + cost),)
        )
        return True

    def _insert_invalidation(
        self,
        conn: sqlite3.Connection,
        identity: str,
        kind: str,
        sequence: int,
        reason: str,
    ) -> None:
        if conn.execute(
            "SELECT 1 FROM invalidations WHERE identity=? AND kind=?", (identity, kind)
        ).fetchone():
            return
        if not self._charge_event_storage(conn, identity + kind + reason):
            # Losing a deny record must never expose stale history. A bounded
            # overflow flag closes every read until a new explicit store exists.
            conn.execute(
                "INSERT OR REPLACE INTO metadata VALUES('invalidation_overflow','1')"
            )
            return
        conn.execute(
            "INSERT INTO invalidations VALUES(?,?,?,?)",
            (identity, kind, sequence, reason),
        )

    @staticmethod
    def _ensure_scope_index(conn: sqlite3.Connection) -> None:
        # A derived index over existing immutable payloads is not a history or
        # epoch migration. Invalid JSON causes an unavailable store, never a
        # destructive repair or invented eligibility projection.
        conn.execute("""CREATE INDEX IF NOT EXISTS event_scope_sequence ON events(
            json_extract(payload, '$.provenance.scope'),
            json_extract(payload, '$.provenance.scope_id'), sequence)""")

    @staticmethod
    def _advance(conn: sqlite3.Connection) -> int:
        value = (
            int(
                conn.execute(
                    "SELECT value FROM metadata WHERE key='sequence'"
                ).fetchone()[0]
            )
            + 1
        )
        conn.execute("UPDATE metadata SET value=? WHERE key='sequence'", (str(value),))
        return value

    @staticmethod
    def _pin(conn: sqlite3.Connection) -> GenerationPin:
        meta = dict(conn.execute("SELECT key,value FROM metadata"))
        return GenerationPin(meta["lineage"], meta["epoch"], int(meta["sequence"]))

    def generation(self, *, deadline_monotonic: float | None = None) -> GenerationPin:
        with self._connect(deadline_monotonic) as conn:
            return self._pin(conn)

    @staticmethod
    def _fsync_directory(path: Path) -> None:
        fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)

    @classmethod
    def _atomic_bytes(cls, path: Path, data: bytes) -> None:
        from .evidence import contained_directory, write_contained

        with contained_directory(path.parent) as fd:
            write_contained(fd, path.name, data)

    @classmethod
    def _file_digest(cls, path: Path) -> str:
        from .evidence import contained_directory

        digest = hashlib.sha256()
        with contained_directory(path.parent) as parent:
            fd = os.open(
                path.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent
            )
            with os.fdopen(fd, "rb") as stream:
                import stat

                if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                    raise MemoryUnavailable("snapshot is not a regular file")
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
        return digest.hexdigest()

    def put_artifact(
        self,
        data: bytes,
        *,
        kind: str = "json",
        deadline_monotonic: float | None = None,
    ) -> EvidenceReference:
        from .evidence import (
            EvidenceUnavailable,
            contained_directory,
            read_contained,
            write_contained,
        )

        if self.read_only:
            raise MemoryUnavailable("read-only memory catalog")
        if not isinstance(data, bytes) or len(data) > self.artifact_byte_cap:
            raise MemoryUnavailable("evidence artifact exceeds byte limit")
        if deadline_monotonic is not None and time.monotonic() >= deadline_monotonic:
            raise MemoryUnavailable("memory deadline exhausted")
        ref = EvidenceReference(hashlib.sha256(data).hexdigest(), len(data), kind)
        try:
            with contained_directory(self.root, "artifacts") as fd:
                try:
                    existing = read_contained(
                        fd, ref.digest, ref.size, deadline_monotonic
                    )
                    if existing != data:
                        raise MemoryUnavailable(
                            "evidence digest collision or corruption"
                        )
                except FileNotFoundError:
                    lock = os.open(
                        ".publication.lock",
                        os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW,
                        0o600,
                        dir_fd=fd,
                    )
                    try:
                        try:
                            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        except BlockingIOError as exc:
                            raise MemoryUnavailable(
                                "evidence publication busy"
                            ) from exc
                        names = os.listdir(fd)
                        used, count = 0, 0
                        for name in names:
                            if (
                                deadline_monotonic is not None
                                and time.monotonic() >= deadline_monotonic
                            ):
                                raise MemoryUnavailable("memory deadline exhausted")
                            if name == ".publication.lock":
                                continue
                            import stat

                            info = os.stat(name, dir_fd=fd, follow_symlinks=False)
                            if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                                raise MemoryUnavailable(
                                    "evidence store contains unsupported entries"
                                )
                            # Interrupted temporary publications consume real
                            # space too. Do not exempt orphans from store caps.
                            count += 1
                            used += info.st_size
                            if (
                                count > self.artifact_count_cap
                                or used > self.artifact_store_byte_cap
                            ):
                                raise MemoryUnavailable(
                                    "evidence store capacity exhausted"
                                )
                        if ref.digest not in names:
                            if (
                                count >= self.artifact_count_cap
                                or used + len(data) > self.artifact_store_byte_cap
                            ):
                                raise MemoryUnavailable(
                                    "evidence store capacity exhausted"
                                )
                            write_contained(fd, ref.digest, data, deadline_monotonic)
                        elif (
                            read_contained(fd, ref.digest, ref.size, deadline_monotonic)
                            != data
                        ):
                            raise MemoryUnavailable(
                                "concurrent evidence publication integrity mismatch"
                            )
                    finally:
                        os.close(lock)
        except (OSError, EvidenceUnavailable) as exc:
            raise MemoryUnavailable("evidence publication unavailable") from exc
        return ref

    def read_artifact(
        self, ref: EvidenceReference, *, deadline_monotonic: float | None = None
    ) -> bytes:
        from .evidence import EvidenceUnavailable, contained_directory, read_contained

        if not isinstance(ref, EvidenceReference) or ref.size > self.artifact_byte_cap:
            raise MemoryUnavailable("invalid or oversized evidence reference")
        try:
            with contained_directory(self.root, "artifacts") as fd:
                data = read_contained(fd, ref.digest, ref.size, deadline_monotonic)
        except (OSError, EvidenceUnavailable) as exc:
            raise MemoryUnavailable("evidence bytes unavailable") from exc
        if len(data) != ref.size or hashlib.sha256(data).hexdigest() != ref.digest:
            raise MemoryUnavailable("evidence digest or length mismatch")
        return data

    def append(
        self,
        event: MemoryEvent,
        *,
        deadline_monotonic: float | None = None,
        cancelled: Callable[[], bool] | None = None,
        queue_on_failure: bool = True,
    ) -> StoreResult:
        if not isinstance(event, MemoryEvent):
            raise ValueError("append requires a typed immutable event")
        if self.read_only:
            return StoreResult(
                "unavailable", event.event_id, "read-only memory catalog", True
            )
        if (cancelled and cancelled()) or (
            deadline_monotonic is not None and time.monotonic() >= deadline_monotonic
        ):
            return StoreResult(
                "unavailable", event.event_id, "cancelled or deadline exhausted", True
            )
        raw = canonical_json(event.to_record())
        if len(raw.encode("utf-8")) > 2 * 1024 * 1024:
            return StoreResult(
                "unavailable", event.event_id, "memory event exceeds byte limit", True
            )
        try:
            for ref in event.evidence:
                self.read_artifact(ref, deadline_monotonic=deadline_monotonic)
            with self._connect(deadline_monotonic) as conn:
                conn.execute("BEGIN IMMEDIATE")
                if (cancelled and cancelled()) or (
                    deadline_monotonic is not None
                    and time.monotonic() >= deadline_monotonic
                ):
                    raise MemoryUnavailable("cancelled or deadline exhausted")
                existing = conn.execute(
                    "SELECT digest FROM events WHERE event_id=?",
                    (event.event_id,),
                ).fetchone()
                invalid = conn.execute(
                    "SELECT 1 FROM invalidations WHERE identity=? AND kind='event'",
                    (event.event_id,),
                ).fetchone()
                if existing and existing["digest"] == event.payload_digest:
                    return StoreResult(
                        "conflict" if invalid else "duplicate",
                        event.event_id,
                        "event invalidated" if invalid else "",
                    )
                if existing:
                    prior_conflict = conn.execute(
                        "SELECT 1 FROM conflicts WHERE event_id=? AND digest=?",
                        (event.event_id, event.payload_digest),
                    ).fetchone()
                    if not prior_conflict:
                        seq = self._advance(conn)
                        if self._charge_event_storage(conn, raw):
                            conn.execute(
                                "INSERT INTO conflicts VALUES(?,?,?,?)",
                                (event.event_id, event.payload_digest, raw, seq),
                            )
                        self._insert_invalidation(
                            conn,
                            event.event_id,
                            "event",
                            seq,
                            "conflicting immutable event payloads",
                        )
                    return StoreResult(
                        "conflict",
                        event.event_id,
                        "conflicting immutable event payloads",
                    )
                if not self._charge_event_storage(conn, raw):
                    return StoreResult(
                        "unavailable",
                        event.event_id,
                        "memory event capacity exhausted",
                        True,
                    )
                seq = self._advance(conn)
                conn.execute(
                    "INSERT INTO events VALUES(?,?,?,?,?)",
                    (event.event_id, seq, event.kind, raw, event.payload_digest),
                )
            return StoreResult("stored", event.event_id)
        except (OSError, sqlite3.Error, MemoryUnavailable) as exc:
            if (
                queue_on_failure
                and not (cancelled and cancelled())
                and (
                    deadline_monotonic is None or time.monotonic() < deadline_monotonic
                )
            ):
                return self._enqueue(event, str(exc), deadline_monotonic)
            return StoreResult("unavailable", event.event_id, str(exc), True)

    def _enqueue(
        self, event: MemoryEvent, diagnostic: str, deadline: float | None
    ) -> StoreResult:
        try:
            lock_path = self.outbox_root / ".lock"
            self._safe_components(lock_path)
            fd = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                raw = canonical_json(event.to_record()).encode("utf-8")
                path = self.outbox_root / (content_digest(event.event_id) + ".json")
                if path.exists():
                    old = self._read_json_file(path, 2 * 1024 * 1024)
                    if canonical_json(old) != raw.decode("utf-8"):
                        marker = self.outbox_root / (path.stem + ".conflict")
                        if not marker.exists():
                            self._atomic_bytes(
                                marker,
                                canonical_json({"event_id": event.event_id}).encode(),
                            )
                        return StoreResult(
                            "conflict", event.event_id, "conflicting pending event"
                        )
                    return StoreResult("pending", event.event_id, diagnostic)
                files = []
                with os.scandir(self.outbox_root) as entries:
                    for entry in entries:
                        if entry.name.endswith(".json"):
                            files.append(Path(entry.path))
                            if len(files) >= self.outbox_event_cap:
                                return StoreResult(
                                    "unavailable",
                                    event.event_id,
                                    "memory outbox capacity exhausted",
                                    True,
                                )
                byte_count = 0
                for oldpath in files:
                    if deadline is not None and time.monotonic() >= deadline:
                        raise MemoryUnavailable("memory deadline exhausted")
                    self._safe_components(oldpath)
                    old = self._read_json_file(oldpath, 2 * 1024 * 1024)
                    # Reserve space for a durable conflict marker per delivery.
                    byte_count += (
                        oldpath.stat().st_size
                        + sum(ref["size"] for ref in old.get("evidence", ()))
                        + 4096
                    )
                    if byte_count > self.outbox_byte_cap:
                        return StoreResult(
                            "unavailable",
                            event.event_id,
                            "memory outbox capacity exhausted",
                            True,
                        )
                cost = len(raw) + sum(ref.size for ref in event.evidence) + 4096
                if (
                    len(files) >= self.outbox_event_cap
                    or byte_count + cost > self.outbox_byte_cap
                ):
                    return StoreResult(
                        "unavailable",
                        event.event_id,
                        "memory outbox capacity exhausted",
                        True,
                    )
                if deadline is not None and time.monotonic() >= deadline:
                    return StoreResult(
                        "unavailable", event.event_id, "memory deadline exhausted", True
                    )
                self._atomic_bytes(path, raw)
                return StoreResult("pending", event.event_id, diagnostic)
            finally:
                os.close(fd)
        except (OSError, ValueError, MemoryUnavailable) as exc:
            return StoreResult(
                "unavailable", event.event_id, f"outbox unavailable: {exc}", True
            )

    @staticmethod
    def _read_json_file(path: Path, limit: int) -> Mapping[str, Any]:
        from .evidence import contained_directory, read_contained

        with contained_directory(path.parent) as directory:
            data = read_contained(directory, path.name, limit)
        payload = json.loads(data)
        if not isinstance(payload, dict):
            raise MemoryUnavailable("metadata is not an object")
        return payload

    def drain_outbox(
        self,
        *,
        limit: int = 64,
        deadline_monotonic: float | None = None,
        cancelled: Callable[[], bool] | None = None,
    ) -> tuple[StoreResult, ...]:
        integer(limit, "drain limit", 1)
        from .evidence import contained_directory

        with contained_directory(self.root, "outbox") as directory:
            lock = os.open(
                ".lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600, dir_fd=directory
            )
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                os.close(lock)
                return ()
            try:
                return self._drain_outbox_locked(limit, deadline_monotonic, cancelled)
            finally:
                os.close(lock)

    def _drain_outbox_locked(
        self,
        limit: int,
        deadline_monotonic: float | None,
        cancelled: Callable[[], bool] | None,
    ) -> tuple[StoreResult, ...]:
        results = []
        paths = []
        with os.scandir(self.outbox_root) as entries:
            for entry in entries:
                if entry.name.endswith(".json"):
                    paths.append(Path(entry.path))
                    if len(paths) >= min(limit, self.outbox_event_cap):
                        break
        for path in paths:
            if (cancelled and cancelled()) or (
                deadline_monotonic is not None
                and time.monotonic() >= deadline_monotonic
            ):
                break
            try:
                event = MemoryEvent.from_record(
                    self._read_json_file(path, 2 * 1024 * 1024)
                )
                marker = self.outbox_root / (path.stem + ".conflict")
                if marker.exists():
                    self._read_json_file(marker, 4096)
                    self.invalidate(event.event_id, reason="conflicting pending event")
                result = self.append(
                    event,
                    deadline_monotonic=deadline_monotonic,
                    cancelled=cancelled,
                    queue_on_failure=False,
                )
                if result.status in {"stored", "duplicate", "conflict"}:
                    path.unlink()
                    with contextlib.suppress(FileNotFoundError):
                        marker.unlink()
                    self._fsync_directory(self.outbox_root)
            except (
                ValueError,
                KeyError,
                TypeError,
                OSError,
                sqlite3.Error,
                MemoryUnavailable,
            ) as exc:
                result = StoreResult(
                    "unavailable", path.stem, f"invalid outbox record: {exc}"
                )
            results.append(result)
        return tuple(results)

    def invalidate(
        self,
        identity: str,
        *,
        kind: str = "event",
        reason: str = "currently ineligible",
    ) -> GenerationPin:
        text(identity, "invalidation identity")
        text(reason, "invalidation reason")
        if self.read_only or kind not in {"event", "source"}:
            raise MemoryUnavailable("unsupported invalidation")
        with self._connect() as conn:
            conn.execute("BEGIN IMMEDIATE")
            if not conn.execute(
                "SELECT 1 FROM invalidations WHERE identity=? AND kind=?",
                (identity, kind),
            ).fetchone():
                seq = self._advance(conn)
                self._insert_invalidation(conn, identity, kind, seq, reason)
            return self._pin(conn)

    def revoke_source(
        self, source_id: str, *, reason: str = "source visibility revoked"
    ) -> GenerationPin:
        return self.invalidate(source_id, kind="source", reason=reason)

    def reconcile(self, authority: Callable[[str], AuthoritySnapshot]) -> bool:
        if self.read_only or not callable(authority):
            raise MemoryUnavailable(
                "reconciliation requires a configured live trusted authority"
            )
        self.reconciliation_authority = authority
        snapshot = self._authority_snapshot()
        if snapshot is None or not snapshot.complete:
            return False
        with self._connect() as conn:
            conn.execute("BEGIN IMMEDIATE")
            conn.execute("UPDATE metadata SET value='1' WHERE key='reconciled'")
            for key, value in (
                ("authority_id", snapshot.authority_id),
                ("authority_watermark", snapshot.watermark),
                ("authority_policy_version", str(snapshot.policy_version)),
            ):
                conn.execute(
                    "INSERT OR REPLACE INTO metadata VALUES(?,?)", (key, value)
                )
        return True

    def _authority_snapshot(
        self, deadline_monotonic: float | None = None
    ) -> AuthoritySnapshot | None:
        """Read a bounded, nonblocking snapshot supplied by the live controller.

        Authority adapters must use precomputed in-memory state: no I/O,
        waiting on locks or invoking a prover/provider. Synchronous callbacks
        cannot be preempted; overdue responses fail closed after returning.
        """
        if self.reconciliation_authority is None:
            return None
        try:
            snapshot = self.reconciliation_authority(
                self.generation(deadline_monotonic=deadline_monotonic).lineage
            )
            if (
                deadline_monotonic is not None
                and time.monotonic() >= deadline_monotonic
            ):
                return None
            return (
                snapshot
                if isinstance(snapshot, AuthoritySnapshot) and snapshot.complete
                else None
            )
        except Exception:
            return None

    def _read_context(
        self,
        conn: sqlite3.Connection,
        policy: EligibilityPolicy,
        deadline_monotonic: float | None = None,
    ) -> tuple[set[str], set[str], bool]:
        meta = dict(conn.execute("SELECT key,value FROM metadata"))
        events: set[str] = set()
        sources: set[str] = set()
        usable = (
            meta.get("reconciled") == "1"
            and self._location_matches
            and meta.get("invalidation_overflow") != "1"
        )
        snapshot = self._authority_snapshot(deadline_monotonic)
        if self.reconciliation_authority is not None and snapshot is None:
            usable = False
        if meta.get("requires_authority") == "1":
            usable = (
                usable
                and snapshot is not None
                and snapshot.policy_version == policy.policy_version
            )
        if snapshot:
            usable = usable and snapshot.policy_version == policy.policy_version
            # The query window bounds returned events, not the complete set of
            # current revocations. Every supplied mask remains authoritative.
            for destination, identities in (
                (events, snapshot.denied_event_ids),
                (sources, snapshot.denied_source_ids),
            ):
                for identity in identities:
                    if (
                        deadline_monotonic is not None
                        and time.monotonic() >= deadline_monotonic
                    ):
                        raise MemoryUnavailable("memory deadline exhausted")
                    destination.add(identity)
        return events, sources, usable

    def _eligible(
        self,
        event: MemoryEvent,
        policy: EligibilityPolicy,
        events: set[str],
        sources: set[str],
        deadline_monotonic: float | None = None,
    ) -> bool:
        if deadline_monotonic is not None and time.monotonic() >= deadline_monotonic:
            raise MemoryUnavailable("memory deadline exhausted")
        if event.event_id in events or sources.intersection(
            event.provenance.source_record_ids + event.provenance.ancestry_source_ids
        ):
            return False
        identities = tuple(
            dict.fromkeys(
                event.provenance.source_record_ids
                + event.provenance.ancestry_source_ids
            )
        )
        with self._connect(deadline_monotonic) as conn:
            denied = conn.execute(
                "SELECT 1 FROM invalidations WHERE identity=? AND kind='event'",
                (event.event_id,),
            ).fetchone()
            if denied is not None:
                return False
            if self._source_mask_denied(conn, identities, deadline_monotonic):
                return False
        marker = self.outbox_root / (content_digest(event.event_id) + ".conflict")
        if marker.exists():
            return False
        if not policy.permits(event.provenance):
            return False
        if self.event_authority is not None:
            try:
                if self.event_authority(event) is not True:
                    return False
            except Exception:
                return False
        if event.provenance.complete and self.current_authority is None:
            return False
        if self.current_authority is not None:
            try:
                if self.current_authority(event.provenance, event.event_id) is not True:
                    return False
                if (
                    deadline_monotonic is not None
                    and time.monotonic() >= deadline_monotonic
                ):
                    raise MemoryUnavailable("memory deadline exhausted")
            except Exception:
                return False
        for ref in event.evidence:
            self.read_artifact(ref, deadline_monotonic=deadline_monotonic)
        return True

    @staticmethod
    def _validate_pin(
        current: GenerationPin, pin: GenerationPin | None
    ) -> GenerationPin:
        if pin is None:
            return current
        if (
            not isinstance(pin, GenerationPin)
            or pin.lineage != current.lineage
            or pin.epoch != current.epoch
            or pin.sequence > current.sequence
        ):
            raise MemoryUnavailable("unknown, stale-epoch or future memory generation")
        return pin

    def query(
        self,
        policy: EligibilityPolicy,
        pinned_generation: GenerationPin | None = None,
        *,
        kind: str | None = None,
        limit: int = 64,
        deadline_monotonic: float | None = None,
    ) -> CatalogView:
        if not isinstance(policy, EligibilityPolicy):
            raise ValueError("memory reads require an explicit eligibility policy")
        integer(limit, "query limit", 1)
        limit = min(limit, self.query_scan_cap)
        with self._connect(deadline_monotonic) as conn:
            conn.execute("BEGIN")
            pin = self._validate_pin(self._pin(conn), pinned_generation)
            denied_events, denied_sources, usable = self._read_context(
                conn, policy, deadline_monotonic
            )
            if not usable:
                return CatalogView((), pin, False, None, ("eligibility_unreconciled",))
            if len(policy.visible_scopes) > 128:
                raise ValueError(
                    "memory visibility scope count exceeds bounded query coverage"
                )
            conditions = "sequence<=?"
            args: list[Any] = [pin.sequence]
            if policy.visible_scopes:
                conditions += (
                    " AND ("
                    + " OR ".join(
                        "(json_extract(payload, '$.provenance.scope')=? AND "
                        "json_extract(payload, '$.provenance.scope_id')=?)"
                        for _ in policy.visible_scopes
                    )
                    + ")"
                )
                args.extend(value for scope in policy.visible_scopes for value in scope)
            else:
                conditions += " AND 0"
            if kind is not None:
                text(kind, "query kind")
                conditions += " AND kind=?"
                args.append(kind)
            headers = conn.execute(
                f"SELECT event_id,length(CAST(payload AS BLOB)) AS size FROM events WHERE {conditions} ORDER BY sequence DESC LIMIT ?",
                (*args, self.query_scan_cap + 1),
            ).fetchall()
            rows = []
            read_bytes = 0
            byte_truncated = False
            for header in headers:
                if read_bytes + header["size"] > self.query_byte_cap:
                    byte_truncated = True
                    break
                rows.append(
                    conn.execute(
                        "SELECT payload,digest FROM events WHERE event_id=?",
                        (header["event_id"],),
                    ).fetchone()
                )
                read_bytes += header["size"]
        found = []
        diagnostics = ["memory query byte coverage exhausted"] if byte_truncated else []
        invalidated = 0
        complete = not byte_truncated and len(headers) <= self.query_scan_cap
        for row in rows[: self.query_scan_cap]:
            if (
                deadline_monotonic is not None
                and time.monotonic() >= deadline_monotonic
            ):
                complete = False
                diagnostics.append("memory deadline exhausted")
                break
            try:
                event = MemoryEvent.from_record(json.loads(row["payload"]))
                if event.payload_digest != row["digest"]:
                    raise MemoryUnavailable("memory event digest mismatch")
                if self._eligible(
                    event, policy, denied_events, denied_sources, deadline_monotonic
                ):
                    found.append(event)
                else:
                    invalidated += 1
            except (ValueError, KeyError, TypeError, MemoryUnavailable) as exc:
                invalidated += 1
                complete = False
                diagnostics.append(type(exc).__name__ + ": evidence unavailable")
        # Repeat current masks after artifact I/O without retaining the read lock.
        with self._connect(deadline_monotonic) as conn:
            now_events, now_sources, usable = self._read_context(
                conn, policy, deadline_monotonic
            )
        if not usable:
            return CatalogView((), pin, False, None, ("eligibility_unreconciled",))
        kept = []
        for event in found:
            try:
                if self._eligible(
                    event, policy, now_events, now_sources, deadline_monotonic
                ):
                    kept.append(event)
            except MemoryUnavailable:
                complete = False
        invalidated += len(found) - len(kept)
        return CatalogView(
            tuple(kept[:limit]),
            pin,
            complete,
            max(0, len(kept) - limit) if complete else None,
            tuple(dict.fromkeys(diagnostics)),
            invalidated,
        )

    def get_event(
        self,
        event_id: str,
        policy: EligibilityPolicy,
        pinned_generation: GenerationPin | None = None,
        *,
        deadline_monotonic: float | None = None,
    ) -> MemoryEvent | None:
        text(event_id, "event identity")
        with self._connect(deadline_monotonic) as conn:
            pin = self._validate_pin(self._pin(conn), pinned_generation)
            denied_events, denied_sources, usable = self._read_context(
                conn, policy, deadline_monotonic
            )
            row = conn.execute(
                "SELECT payload,digest FROM events WHERE event_id=? AND sequence<=? AND length(CAST(payload AS BLOB))<=2097152",
                (event_id, pin.sequence),
            ).fetchone()
        if not usable or row is None:
            return None
        try:
            event = MemoryEvent.from_record(json.loads(row["payload"]))
            if event.payload_digest != row["digest"] or not self._eligible(
                event, policy, denied_events, denied_sources, deadline_monotonic
            ):
                return None
            with self._connect(deadline_monotonic) as conn:
                now_events, now_sources, usable = self._read_context(
                    conn, policy, deadline_monotonic
                )
            return (
                event
                if usable
                and self._eligible(
                    event, policy, now_events, now_sources, deadline_monotonic
                )
                else None
            )
        except (ValueError, KeyError, TypeError, MemoryUnavailable):
            return None

    @staticmethod
    def _source_mask_denied(
        conn: sqlite3.Connection,
        identities: tuple[str, ...],
        deadline_monotonic: float | None,
    ) -> bool:
        """Check complete ancestry in bounded SQL statements on one connection."""
        batch_size = min(512, conn.getlimit(sqlite3.SQLITE_LIMIT_VARIABLE_NUMBER))
        if batch_size < 1:
            raise MemoryUnavailable("memory source mask lookup unavailable")
        for offset in range(0, len(identities), batch_size):
            if deadline_monotonic is not None and time.monotonic() >= deadline_monotonic:
                raise MemoryUnavailable("memory deadline exhausted")
            batch = identities[offset:offset + batch_size]
            denied = conn.execute(
                "SELECT 1 FROM invalidations WHERE kind='source' AND identity IN ("
                + ",".join("?" for _ in batch) + ") LIMIT 1",
                batch,
            ).fetchone()
            if denied is not None:
                return True
        if deadline_monotonic is not None and time.monotonic() >= deadline_monotonic:
            raise MemoryUnavailable("memory deadline exhausted")
        return False

    def sources_eligible(
        self,
        source_record_ids: tuple[str, ...],
        policy: EligibilityPolicy,
        *,
        deadline_monotonic: float | None = None,
    ) -> bool:
        """Consult current masks for every source with one catalog connection.

        This checks local masks only; callers separately validate live source
        integrity, complete ancestry and policy before exposing a candidate.
        """
        identities = strings(source_record_ids, "source identities")
        with self._connect(deadline_monotonic) as conn:
            _, denied_sources, usable = self._read_context(
                conn, policy, deadline_monotonic
            )
            if not usable or denied_sources.intersection(identities):
                return False
            return not self._source_mask_denied(conn, identities, deadline_monotonic)

    def source_eligible(
        self,
        source_record_id: str,
        policy: EligibilityPolicy,
        *,
        deadline_monotonic: float | None = None,
    ) -> bool:
        """Consult current catalog reconciliation for one source identity."""
        text(source_record_id, "source identity")
        return self.sources_eligible(
            (source_record_id,), policy, deadline_monotonic=deadline_monotonic,
        )

    def inspect(self) -> dict[str, Any]:
        with self._connect() as conn:
            meta = dict(conn.execute("SELECT key,value FROM metadata"))
            counts = {
                table: conn.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0]
                for table in ("events", "invalidations", "conflicts")
            }
        return {
            "schema_version": SCHEMA_VERSION,
            "generation": self.generation().to_record(),
            **counts,
            "outbox_pending": len(list(self.outbox_root.glob("*.json"))),
            "eligibility_reconciled": meta.get("reconciled") == "1"
            and (
                meta.get("requires_authority") != "1"
                or self._authority_snapshot() is not None
            ),
            "requires_current_authority": meta.get("requires_authority") == "1",
            "rollback_protection": False,
            "limitations": "Raw rollback detection needs an independently retained nonrollback journal; local backup metadata is insufficient.",
        }

    def backup(self, destination: str | Path) -> Path:
        """Keep the database and pending deny metadata in one spool snapshot."""
        from .evidence import contained_directory

        with contained_directory(self.outbox_root) as directory:
            lock = os.open(
                ".lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600, dir_fd=directory
            )
            try:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError as exc:
                    raise MemoryUnavailable("outbox is busy during backup") from exc
                return self._backup_locked(destination)
            finally:
                os.close(lock)

    def _backup_locked(self, destination: str | Path) -> Path:
        dest = Path(destination).absolute()
        from .evidence import contained_directory

        with contained_directory(dest.parent, create_parents=True) as parent:
            try:
                os.mkdir(dest.name, mode=0o700, dir_fd=parent)
            except FileExistsError as exc:
                raise MemoryUnavailable("backup destination must not exist") from exc
            backup_fd = os.open(
                dest.name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent
            )
        artifacts = dest / "artifacts"
        try:
            os.mkdir("artifacts", mode=0o700, dir_fd=backup_fd)
            target_fd = os.open(
                "catalog.sqlite3",
                os.O_CREAT | os.O_EXCL | os.O_RDWR | os.O_NOFOLLOW,
                0o600,
                dir_fd=backup_fd,
            )
        except BaseException:
            os.close(backup_fd)
            raise
        target_identity = os.fstat(target_fd)
        anchored_db = f"file:/proc/self/fd/{target_fd}?mode=rw"
        try:
            with (
                self._connect() as source,
                sqlite3.connect(anchored_db, uri=True) as target,
            ):
                info = os.stat(
                    "catalog.sqlite3", dir_fd=backup_fd, follow_symlinks=False
                )
                if (info.st_dev, info.st_ino) != (
                    target_identity.st_dev,
                    target_identity.st_ino,
                ):
                    raise MemoryUnavailable("backup file changed during open")
                source.backup(target)
            with sqlite3.connect(anchored_db, uri=True) as snapshot:
                meta = dict(snapshot.execute("SELECT key,value FROM metadata"))
                refs = {}
                for (raw,) in snapshot.execute("SELECT payload FROM events"):
                    for ref in MemoryEvent.from_record(json.loads(raw)).evidence:
                        refs[ref.digest] = ref
            # Pending events are separately retained, with unchanged identities.
            pending = dest / "outbox"
            os.mkdir("outbox", mode=0o700, dir_fd=backup_fd)
            for path in list(self.outbox_root.glob("*.json"))[: self.outbox_event_cap]:
                event = MemoryEvent.from_record(
                    self._read_json_file(path, 2 * 1024 * 1024)
                )
                self._atomic_bytes(
                    pending / path.name, canonical_json(event.to_record()).encode()
                )
                marker = path.with_suffix(".conflict")
                if marker.exists():
                    marker_data = self._read_json_file(marker, 4096)
                    self._atomic_bytes(
                        pending / marker.name, canonical_json(marker_data).encode()
                    )
                for ref in event.evidence:
                    refs[ref.digest] = ref
            unavailable = []
            for ref in refs.values():
                try:
                    self._atomic_bytes(artifacts / ref.digest, self.read_artifact(ref))
                except MemoryUnavailable:
                    unavailable.append(ref.digest)
            manifest = {
                "schema_version": SCHEMA_VERSION,
                "generation": GenerationPin(
                    meta["lineage"], meta["epoch"], int(meta["sequence"])
                ).to_record(),
                "database_digest": self._file_digest(dest / "catalog.sqlite3"),
                "artifacts": [ref.to_record() for ref in refs.values()],
                "unavailable_artifacts": unavailable,
            }
            self._atomic_bytes(
                dest / "manifest.json", canonical_json(manifest).encode()
            )
            self._fsync_directory(dest)
            return dest
        except Exception:
            # A partial backup never has a valid manifest; retain it for diagnosis.
            raise
        finally:
            os.close(target_fd)
            os.close(backup_fd)

    @classmethod
    def restore(
        cls,
        backup: str | Path,
        destination: str | Path,
        *,
        retain_epoch: bool = False,
        **kwargs: Any,
    ) -> MemoryCatalog:
        if retain_epoch:
            raise MemoryUnavailable(
                "retaining an epoch requires externally certified complete nonforking continuation and predecessor fencing"
            )
        src, dest = Path(backup).absolute(), Path(destination).absolute()
        cls._safe_components(src)
        cls._safe_components(dest)
        manifest = cls._read_json_file(src / "manifest.json", 16 * 1024 * 1024)
        if manifest.get("schema_version") != SCHEMA_VERSION:
            raise MemoryUnavailable("unsupported backup manifest")
        cls._safe_components(src / "catalog.sqlite3")
        digest = cls._file_digest(src / "catalog.sqlite3")
        if digest != manifest.get("database_digest"):
            raise MemoryUnavailable("backup database digest mismatch")
        if dest.exists():
            raise MemoryUnavailable("restore destination must not exist")
        dest.mkdir(parents=True, mode=0o700)
        for directory in ("artifacts", "outbox"):
            (dest / directory).mkdir(mode=0o700)
        shutil.copyfile(
            src / "catalog.sqlite3", dest / "catalog.sqlite3", follow_symlinks=False
        )
        if cls._file_digest(dest / "catalog.sqlite3") != manifest["database_digest"]:
            raise MemoryUnavailable("snapshot changed during restore")
        fd = os.open(dest / "catalog.sqlite3", os.O_RDONLY | os.O_NOFOLLOW)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
        restored_bytes = 0
        restored_count = 0
        for payload in manifest.get("artifacts", ()):
            ref = EvidenceReference.from_record(payload)
            path = src / "artifacts" / ref.digest
            if ref.digest in manifest.get("unavailable_artifacts", ()):
                continue
            cls._safe_components(path)
            if not path.is_file():
                continue
            restored_count += 1
            restored_bytes += ref.size
            if (
                restored_count > kwargs.get("artifact_count_cap", 65536)
                or restored_bytes
                > kwargs.get("artifact_store_byte_cap", 512 * 1024 * 1024)
                or ref.size > kwargs.get("artifact_byte_cap", 16 * 1024 * 1024)
            ):
                raise MemoryUnavailable("restored evidence store capacity exhausted")
            fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            with os.fdopen(fd, "rb") as stream:
                data = stream.read(
                    min(
                        ref.size + 1,
                        kwargs.get("artifact_byte_cap", 16 * 1024 * 1024) + 1,
                    )
                )
            if len(data) != ref.size or hashlib.sha256(data).hexdigest() != ref.digest:
                raise MemoryUnavailable("backup artifact digest mismatch")
            cls._atomic_bytes(dest / "artifacts" / ref.digest, data)
        pending_count = 0
        pending_bytes = 0
        for path in (src / "outbox").glob("*.json"):
            payload = cls._read_json_file(path, 2 * 1024 * 1024)
            event = MemoryEvent.from_record(payload)
            pending_count += 1
            pending_bytes += (
                len(canonical_json(payload).encode())
                + sum(ref.size for ref in event.evidence)
                + 4096
            )
            if pending_count > kwargs.get(
                "outbox_event_cap", 256
            ) or pending_bytes > kwargs.get("outbox_byte_cap", 16 * 1024 * 1024):
                raise MemoryUnavailable("restored outbox capacity exhausted")
            cls._atomic_bytes(
                dest / "outbox" / (content_digest(event.event_id) + ".json"),
                canonical_json(payload).encode(),
            )
            marker = path.with_suffix(".conflict")
            if marker.exists():
                marker_data = cls._read_json_file(marker, 4096)
                cls._atomic_bytes(
                    dest / "outbox" / marker.name, canonical_json(marker_data).encode()
                )
        with sqlite3.connect(dest / "catalog.sqlite3") as conn:
            conn.execute(
                "UPDATE metadata SET value=? WHERE key='epoch'",
                (content_digest(uuid.uuid4().bytes),),
            )
            conn.execute(
                "UPDATE metadata SET value=? WHERE key='location'",
                (str(dest.resolve()),),
            )
            conn.execute("UPDATE metadata SET value='0' WHERE key='reconciled'")
            conn.execute("UPDATE metadata SET value='1' WHERE key='requires_authority'")
        cls._fsync_directory(dest)
        return cls(dest, **kwargs)

    def rebuild(self, destination: str | Path | None = None) -> MemoryCatalog:
        if destination is None:
            if self.read_only:
                raise MemoryUnavailable("read-only memory catalog")
            with self._connect() as conn:
                conn.execute("REINDEX")
            return self
        with tempfile.TemporaryDirectory(prefix="memory-backup-") as temporary:
            backup = self.backup(Path(temporary) / "snapshot")
            return self.restore(
                backup,
                destination,
                outbox_event_cap=self.outbox_event_cap,
                outbox_byte_cap=self.outbox_byte_cap,
                artifact_byte_cap=self.artifact_byte_cap,
                artifact_store_byte_cap=self.artifact_store_byte_cap,
                artifact_count_cap=self.artifact_count_cap,
                query_scan_cap=self.query_scan_cap,
            )
