"""Strict, atomic JSON storage for committed MiniSession checkpoints.

Journal records are separate atomic files. A returned append receipt means
the file and containing directory have both been synced. Temporary files are
never receipts; malformed published records stop recovery explicitly.
"""

from __future__ import annotations

from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import tempfile
import threading
from typing import Any, Iterator

from ensemble_prover.state_data import clone_json_value

_MAX_RECORD_BYTES = 256 * 1024 * 1024


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _canonical_bytes(record: dict[str, Any]) -> bytes:
    value = clone_json_value(record, label="durable checkpoint")
    if type(value) is not dict:
        raise ValueError("checkpoint JSON must be an object")

    def validate_keys(item: Any) -> None:
        if type(item) is dict:
            if any(type(key) is not str for key in item):
                raise ValueError("checkpoint JSON object keys must be strings")
            for child in item.values():
                validate_keys(child)
        elif type(item) in {list, tuple}:
            for child in item:
                validate_keys(child)

    validate_keys(value)
    content = json.dumps(value, ensure_ascii=False, allow_nan=False,
                         sort_keys=True, separators=(",", ":")).encode("utf-8")
    if len(content) > _MAX_RECORD_BYTES:
        raise ValueError("durable checkpoint exceeds record size limit")
    return content


def read_checkpoint_record(path: str | Path) -> dict[str, Any]:
    """Read inert JSON, rejecting duplicate keys, truncation and nonfinite data."""
    with Path(path).open("rb") as handle:
        data = handle.read(_MAX_RECORD_BYTES + 1)
    if len(data) > _MAX_RECORD_BYTES:
        raise ValueError("durable checkpoint exceeds record size limit")
    try:
        value = json.loads(data, object_pairs_hook=_unique_object,
                           parse_constant=_reject_constant)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as error:
        raise ValueError("corrupt checkpoint JSON") from error
    if type(value) is not dict:
        raise ValueError("checkpoint JSON must be an object")
    _canonical_bytes(value)
    return value


def write_checkpoint_record(path: str | Path, record: dict[str, Any]) -> None:
    """Atomically publish a complete record; propagate every durability error."""
    content = _canonical_bytes(record)
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=".checkpoint-", suffix=".tmp",
                                             dir=destination.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, destination)
        directory = os.open(destination.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


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
        entry = read_checkpoint_record(source)
        if (set(entry) != {"schema_version", "sequence", "previous_hash", "kind", "payload", "record_hash"}
                or type(entry["sequence"]) is not int
                or entry["sequence"] != sequence
                or entry["schema_version"] != 1
                or entry["previous_hash"] != previous_hash
                or type(entry["kind"]) is not str or not entry["kind"]
                or type(entry["payload"]) is not dict):
            raise ValueError("corrupt journal record or sequence")
        material = {key: value for key, value in entry.items() if key != "record_hash"}
        digest = hashlib.sha256(_canonical_bytes(material)).hexdigest()
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
        self._owner = (self.directory / ".owner.lock").open("a+b")
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
                digest = hashlib.sha256(_canonical_bytes(material)).hexdigest()
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
