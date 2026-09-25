"""Order proof commits, worker readiness and sweep cutoff under one file lock."""

from __future__ import annotations

import fcntl
import hashlib
import json
import math
import os
import re
import secrets
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator, TextIO

CONTROL_ENV = "ENSEMBLE_SWEEP_CONTROL_TOKEN"
_LOCK_TIMEOUT_S = 5.0


def _boot_id() -> str:
    return Path("/proc/sys/kernel/random/boot_id").read_text().strip()


def _timestamp(value: Any, *, earliest: float, now: float) -> float:
    try:
        valid = (not isinstance(value, bool) and isinstance(value, (int, float))
                 and math.isfinite(value) and earliest <= value <= now)
    except OverflowError:
        valid = False
    if not valid:
        raise ValueError("invalid sweep authority timestamp")
    return float(value)


class SweepCutoffCommitted(RuntimeError):
    """The sweep closed this attempt before this action could commit."""


class SweepControl:
    """A capability for one attempt's independently locked authority journal."""

    def __init__(self, path: Path, token: str) -> None:
        self.path = path
        self.token = token
        self.identity = hashlib.sha256(token.encode()).hexdigest()

    @classmethod
    def create(cls, output_dir: Path) -> SweepControl:
        control = cls(output_dir.with_name(output_dir.name + ".sweep_control.jsonl"), secrets.token_hex(32))
        fd = os.open(control.path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(json.dumps({
                "control_identity": control.identity,
                "boot_id": _boot_id(),
                "started_monotonic_s": time.monotonic(),
            }, allow_nan=False) + "\n")
            handle.flush()
            os.fsync(handle.fileno())
        return control

    def environment_value(self) -> str:
        return json.dumps([str(self.path), self.token])

    @classmethod
    def from_environment(cls) -> SweepControl | None:
        raw = os.environ.get(CONTROL_ENV)
        if not raw:
            return None
        value = json.loads(raw)
        if (not isinstance(value, list) or len(value) != 2
                or not all(isinstance(item, str) and item for item in value)):
            raise ValueError("invalid sweep control capability")
        return cls(Path(value[0]), value[1])

    @contextmanager
    def locked(self) -> Iterator[ControlTransaction]:
        fd = os.open(self.path, os.O_RDWR | os.O_NOFOLLOW)
        with os.fdopen(fd, "r+", encoding="utf-8") as handle:
            deadline = time.monotonic() + _LOCK_TIMEOUT_S
            while True:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError("sweep acceptance authority lock unavailable")
                    time.sleep(.01)
            try:
                lines = handle.read().splitlines(keepends=True)
                incomplete = bool(lines and not lines[-1].endswith("\n"))
                complete_lines = lines[:-1] if incomplete else lines
                records = []
                for line in complete_lines:
                    record = json.loads(line)
                    if not isinstance(record, dict):
                        raise ValueError("invalid sweep acceptance authority record")
                    records.append(record)
                if not records or records[0].get("control_identity") != self.identity:
                    raise ValueError("sweep control capability mismatch")
                header = records[0]
                if header.get("boot_id") != _boot_id():
                    raise ValueError("sweep authority belongs to another boot")
                started = _timestamp(header.get("started_monotonic_s"), earliest=0.0, now=time.monotonic())
                transaction = ControlTransaction(handle, records[1:], started=started, identity=self.identity)
                if incomplete:
                    # A torn final append never carried durable authority.
                    # Keep its preceding intent so the proof outbox can retry.
                    handle.seek(len("".join(complete_lines).encode("utf-8")))
                    handle.truncate()
                # A prior writer may have completed write() but failed fsync.
                # Neither monitor nor retry may acknowledge it before this.
                os.fsync(handle.fileno())
                yield transaction
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


class ControlTransaction:
    """Journal operations valid only while the owning control lock is held."""

    def __init__(self, handle: TextIO, records: list[dict[str, Any]], *, started: float, identity: str) -> None:
        self.handle = handle
        self.records = records
        self.started = started
        self.identity = identity
        self._validate(records)

    def _validate(self, records: list[dict[str, Any]]) -> None:
        begun: set[str] = set()
        completed: set[str] = set()
        ready = cutoff = False
        now = time.monotonic()
        for record in records:
            event = record.get("event")
            if not isinstance(event, str):
                raise ValueError("invalid sweep authority event")
            if event in {"ready", "cutoff"}:
                _timestamp(record.get("monotonic_s"), earliest=self.started, now=now)
                if event == "ready":
                    if ready or cutoff:
                        raise ValueError("invalid sweep readiness ordering")
                    ready = True
                else:
                    if (cutoff or begun - completed
                            or not isinstance(record.get("reason"), str)
                            or record["reason"] not in {
                        "first_acceptance_deadline", "second_acceptance_deadline",
                        "startup_deadline", "startup_liveness_deadline",
                    }):
                        raise ValueError("invalid sweep cutoff ordering")
                    cutoff = True
                continue
            transaction_id = record.get("transaction")
            if (cutoff or not isinstance(transaction_id, str)
                    or not re.fullmatch(r"[0-9a-f]{32}", transaction_id)):
                raise ValueError("invalid sweep authority transaction")
            if event == "commit_begin":
                if transaction_id in begun:
                    raise ValueError("duplicate sweep commit intent")
                begun.add(transaction_id)
            elif event == "commit_complete":
                if transaction_id not in begun or transaction_id in completed:
                    raise ValueError("unowned sweep commit completion")
                receipts = record.get("receipts")
                if not isinstance(receipts, list) or not receipts:
                    raise ValueError("missing sweep commit receipts")
                for receipt in receipts:
                    if (not isinstance(receipt, dict)
                            or receipt.get("acceptance_control_identity") != self.identity
                            or receipt.get("acceptance_control_transaction") != transaction_id
                            or receipt.get("phase") != "session_accepted_proof"
                            or receipt.get("verdict") != "accepted_proof_committed"
                            or not isinstance(receipt.get("acceptance_identity"), str)
                            or not re.fullmatch(r"[0-9a-f]{64}", receipt["acceptance_identity"])):
                        raise ValueError("invalid sweep commit receipt")
                    _timestamp(receipt.get("acceptance_monotonic_s"), earliest=self.started, now=now)
                completed.add(transaction_id)
            else:
                raise ValueError("unknown sweep authority event")

    def append(self, record: dict[str, Any]) -> None:
        self._validate([*self.records, record])
        self.handle.write(json.dumps(record, separators=(",", ":"), allow_nan=False) + "\n")
        self.handle.flush()
        os.fsync(self.handle.fileno())
        self.records.append(record)

    @property
    def cutoff(self) -> str:
        return next((str(item["reason"]) for item in self.records if item.get("event") == "cutoff"), "")

    @property
    def ready_at(self) -> float | None:
        return next((float(item["monotonic_s"]) for item in self.records if item.get("event") == "ready"), None)

    @property
    def pending(self) -> set[str]:
        started = {item["transaction"] for item in self.records if item.get("event") == "commit_begin"}
        finished = {item["transaction"] for item in self.records if item.get("event") == "commit_complete"}
        return started - finished

    def accepted_records(self) -> list[dict[str, Any]]:
        return [receipt for item in self.records if item.get("event") == "commit_complete"
                for receipt in item["receipts"]]


def signal_sweep_worker_ready() -> None:
    """Start the proof window once; worker recycling does not reset it."""
    control = SweepControl.from_environment()
    if control is None:
        return
    with control.locked() as transaction:
        if transaction.cutoff:
            raise SweepCutoffCommitted(transaction.cutoff)
        if transaction.ready_at is None:
            transaction.append({"event": "ready", "monotonic_s": time.monotonic()})


@contextmanager
def acceptance_commit_transaction(records: list[dict[str, Any]]) -> Iterator[ControlTransaction | None]:
    """Persist an intent before success, then complete it with actual receipts."""
    control = SweepControl.from_environment() if records else None
    if control is None:
        yield None
        return
    with control.locked() as transaction:
        if transaction.cutoff:
            raise SweepCutoffCommitted(transaction.cutoff)
        transaction_id = secrets.token_hex(16)
        transaction.append({"event": "commit_begin", "transaction": transaction_id})
        for record in records:
            record["acceptance_control_identity"] = control.identity
            record["acceptance_control_transaction"] = transaction_id
        yield transaction


def complete_acceptance_transaction(transaction: ControlTransaction, records: list[dict[str, Any]]) -> None:
    transaction_id = records[0]["acceptance_control_transaction"]
    if transaction_id in transaction.pending:
        transaction.append({"event": "commit_complete", "transaction": transaction_id, "receipts": records})
        return
    completed = next((item for item in transaction.records
                      if item.get("event") == "commit_complete"
                      and item.get("transaction") == transaction_id), None)
    if completed is None:
        raise ValueError("acceptance receipt has no sweep commit intent")
    def original_fields(record: dict[str, Any]) -> dict[str, Any]:
        return {key: value for key, value in record.items()
                if key not in {"acceptance_restored", "acceptance_previous_boot"}}

    saved_receipts = [original_fields(record) for record in completed["receipts"]]
    for record in records:
        if original_fields(record) not in saved_receipts:
            raise ValueError("acceptance retry differs from its committed sweep receipt")


def retry_acceptance_publication(records: list[dict[str, Any]]) -> None:
    control = SweepControl.from_environment()
    if control is None or records[0].get("acceptance_control_identity") != control.identity:
        return
    with control.locked() as transaction:
        complete_acceptance_transaction(transaction, records)
