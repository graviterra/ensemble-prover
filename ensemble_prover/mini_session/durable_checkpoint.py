"""Strict, atomic JSON storage for committed MiniSession checkpoints.

Journal records are separate atomic files. A returned append receipt means
the file and containing directory have both been synced. Temporary files are
never receipts; malformed published records stop recovery explicitly.
"""

from __future__ import annotations

from collections import OrderedDict
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import tempfile
import threading
from typing import Any, BinaryIO, Iterator

from ensemble_prover.json_pages import canonical_identity, canonical_parts, strict_loads

from .checkpoint_pages import ENCODING, PageStore

_MAX_RECORD_BYTES = 256 * 1024 * 1024


_PAGE_STORES: OrderedDict[tuple[int, int], PageStore] = OrderedDict()
_PAGE_STORES_LOCK = threading.Lock()


def _page_store(parent: Path, *, directory_fd: int | None = None) -> PageStore:
    if str(parent).startswith("/proc/self/fd/"):
        return PageStore(parent)
    info = parent.stat() if directory_fd is None else os.fstat(directory_fd)
    key = info.st_dev, info.st_ino
    with _PAGE_STORES_LOCK:
        store = _PAGE_STORES.get(key)
        if store is None:
            store = PageStore(parent, parent_identity=key)
            _PAGE_STORES[key] = store
        else:
            # The inode can survive a rename or the removal of an earlier alias.
            # Retain its durability hints while using the caller's current path.
            store.parent = parent
            _PAGE_STORES.move_to_end(key)
        while len(_PAGE_STORES) > 16:
            _PAGE_STORES.popitem(last=False)
    return store


def release_checkpoint_cache(parent: Path) -> None:
    """Release an owner's immutable string/page hints when its generation closes."""
    try:
        info = parent.stat()
    except OSError:
        # Cache hints are optional; inaccessible paths must not retain locks
        # or prevent the owning registry's remaining cleanup.
        return
    with _PAGE_STORES_LOCK:
        _PAGE_STORES.pop((info.st_dev, info.st_ino), None)


def collect_checkpoint_pages(parent: Path) -> None:
    """Optional cleanup after publication under exclusive attempt ownership."""
    try:
        _page_store(parent).collect(record_limit=_MAX_RECORD_BYTES, parent=parent)
    except (OSError, ValueError):
        # A cleanup failure cannot revoke an acknowledged checkpoint.
        pass


def read_checkpoint_record(path: str | Path, *, page_parent: Path | None = None) -> dict[str, Any]:
    """Read old JSON or authenticate and reconstruct independently bounded pages."""
    source = Path(path)
    with source.open("rb") as handle:
        data = handle.read(_MAX_RECORD_BYTES + 1)
    return decode_checkpoint_record(data, page_parent=source.parent if page_parent is None else page_parent)


def decode_checkpoint_record(data: bytes, *, page_parent: Path) -> dict[str, Any]:
    """Decode one physical receipt, preserving its exact bytes for importers."""
    if len(data) > _MAX_RECORD_BYTES:
        raise ValueError("durable checkpoint exceeds record size limit")
    value = strict_loads(data)
    if type(value) is not dict:
        raise ValueError("checkpoint JSON must be an object")
    if "checkpoint_encoding" in value:
        if value["checkpoint_encoding"] != ENCODING:
            raise ValueError("unsupported checkpoint page encoding")
        # The directory may be an already validated provider archive descriptor.
        value = _page_store(page_parent).decode(
            value, limit=min(64 * 1024, _MAX_RECORD_BYTES), parent=page_parent,
        )
    return value


def write_checkpoint_record(path: str | Path, record: dict[str, Any]) -> None:
    """Publish bounded immutable pages before the atomic record commit point."""
    if type(record) is not dict:
        raise ValueError("checkpoint JSON must be an object")
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    directory = os.open(destination.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    pinned_parent = Path(f"/proc/self/fd/{directory}")
    temporary = None
    try:
        content = bytearray()
        threshold = min(64 * 1024, _MAX_RECORD_BYTES)
        for part in canonical_parts(record):
            content.extend(part)
            if len(content) > threshold:
                break
        paged = len(content) > threshold or "checkpoint_encoding" in record
        if paged:
            envelope = _page_store(destination.parent, directory_fd=directory).encode(
                record, limit=_MAX_RECORD_BYTES, parent=pinned_parent,
            )
            content = bytearray().join(canonical_parts(envelope))
        descriptor, temporary = tempfile.mkstemp(prefix=".checkpoint-", suffix=".tmp",
                                                 dir=pinned_parent)
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, pinned_parent / destination.name)
        os.fsync(directory)
        current, original = destination.parent.stat(), os.fstat(directory)
        if (current.st_dev, current.st_ino) != (original.st_dev, original.st_ino):
            raise ValueError("checkpoint record directory was replaced during IO")
        if not paged:
            with _PAGE_STORES_LOCK:
                store = _PAGE_STORES.get((original.st_dev, original.st_ino))
            if store is not None:
                store.clear_string_hints()
    finally:
        try:
            if temporary is not None:
                try:
                    os.unlink(temporary)
                except FileNotFoundError:
                    pass
        finally:
            os.close(directory)


@contextmanager
def _journal_lock(path: Path, *, exclusive: bool) -> Iterator[None]:
    path.mkdir(parents=True, exist_ok=True)
    with (path / ".writer.lock").open("a+b") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH)
        try:
            yield
        finally:
            fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


def _read_journal_unlocked(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    previous_hash = ""
    for sequence, source in enumerate(sorted(path.glob("[0-9]*.json")), 1):
        if source.name != f"{sequence:020d}.json":
            raise ValueError("corrupt journal sequence or filename")
        try:
            entry = read_checkpoint_record(source)
        except ValueError as error:
            raise ValueError(f"corrupt journal record {source.name}") from error
        if (set(entry) != {"schema_version", "sequence", "previous_hash", "kind", "payload", "record_hash"}
                or type(entry["sequence"]) is not int
                or entry["sequence"] != sequence
                or entry["schema_version"] != 1
                or entry["previous_hash"] != previous_hash
                or type(entry["kind"]) is not str or not entry["kind"]
                or type(entry["payload"]) is not dict):
            raise ValueError("corrupt journal record or sequence")
        material = {key: value for key, value in entry.items() if key != "record_hash"}
        digest = canonical_identity(material)[0]
        if entry["record_hash"] != digest:
            raise ValueError("corrupt journal record hash")
        records.append(entry)
        previous_hash = digest
    return records


def read_journal_records(path: str | Path, *, after_sequence: int = 0) -> list[dict[str, Any]]:
    """Validate the complete chain, then return records after a saved watermark."""
    if type(after_sequence) is not int or after_sequence < 0:
        raise ValueError("invalid journal sequence watermark")
    directory = Path(path)
    with _journal_lock(directory, exclusive=False):
        records = _read_journal_unlocked(directory)
    if after_sequence > len(records):
        raise ValueError("journal is missing the checkpoint sequence watermark")
    return records[after_sequence:]


class JournalWriter:
    """Exclusive append owner with a fully validated, process-local chain head.

    Published records are immutable while this owner is live. Every API writer
    takes the ownership lock; readers take only the short publication lock.
    A failed write permanently fences this object because its physical append
    may have reached disk even though its acknowledgement did not return.
    """

    def __init__(self, path: str | Path, *, blocking: bool = False) -> None:
        self.directory = Path(path)
        self.directory.mkdir(parents=True, exist_ok=True)
        self._mutex = threading.Lock()
        self._failed = False
        self._owner: BinaryIO | None = (self.directory / ".owner.lock").open("a+b")
        try:
            operation = fcntl.LOCK_EX | (0 if blocking else fcntl.LOCK_NB)
            try:
                fcntl.flock(self._owner.fileno(), operation)
            except BlockingIOError as error:
                raise RuntimeError("Journal already has an active writer") from error
            with _journal_lock(self.directory, exclusive=True):
                records = _read_journal_unlocked(self.directory)
            self._sequence = len(records)
            self._record_hash = records[-1]["record_hash"] if records else ""
        except BaseException:
            self._owner.close()
            self._owner = None
            raise

    def append(self, *, kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        with self._mutex:
            if self._owner is None or self._failed:
                raise RuntimeError("Journal writer is closed or failed; reopen and validate before appending")
            try:
                if type(kind) is not str or not kind or type(payload) is not dict:
                    raise ValueError("journal kind and payload must be inert typed data")
                sequence = self._sequence + 1
                material = {"schema_version": 1, "sequence": sequence,
                            "previous_hash": self._record_hash,
                            "kind": kind, "payload": payload}
                digest = canonical_identity(material)[0]
                destination = self.directory / f"{sequence:020d}.json"
                with _journal_lock(self.directory, exclusive=True):
                    if destination.exists() or destination.is_symlink():
                        raise ValueError("Journal sequence already exists outside its writer")
                    write_checkpoint_record(destination, {**material, "record_hash": digest})
                self._sequence = sequence
                self._record_hash = digest
                return {"sequence": sequence, "record_hash": digest}
            except BaseException:
                self._failed = True
                raise

    def close(self) -> None:
        with self._mutex:
            if self._owner is not None:
                self._owner.close()
                self._owner = None
                release_checkpoint_cache(self.directory)


def append_journal_record(path: str | Path, *, kind: str, payload: dict[str, Any]) -> dict[str, Any]:
    """Append once with full startup validation and an acknowledged receipt."""
    writer = JournalWriter(path, blocking=True)
    try:
        return writer.append(kind=kind, payload=payload)
    finally:
        writer.close()


def capture_session_record(session: Any) -> dict[str, Any]:
    from .durable_session_record import capture_session_record as capture
    return capture(session)


async def restore_session_record(session: Any, record: dict[str, Any], *, expected_identity: dict[str, Any]) -> None:
    from .durable_session_record import restore_session_record as restore
    await restore(session, record, expected_identity=expected_identity)
