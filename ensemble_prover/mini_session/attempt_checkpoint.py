"""Exclusive durable ownership of one attempt across fresh run generations.

Session records are immutable committed values. A sibling checkpoint never
walks another live session, whose proof action may still be in flight.
"""
from __future__ import annotations

import asyncio
import fcntl
import hashlib
import inspect
import json
import math
import time
import uuid
from pathlib import Path
from typing import Any

from ..state_data import clone_json_value

_MANIFEST = "attempt_checkpoint.json"
_SCHEMA = 1


def _json(value: Any) -> Any:
    return clone_json_value(value, label="attempt checkpoint")


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode()).hexdigest()


def _read(path: Path) -> dict[str, Any]:
    from .durable_checkpoint import read_checkpoint_record
    return read_checkpoint_record(path)


def _write(path: Path, value: dict[str, Any]) -> None:
    from .durable_checkpoint import write_checkpoint_record
    write_checkpoint_record(path, value)


def _worker_clock_receipt(record: dict[str, Any]) -> tuple[float, float, bool]:
    elapsed = record.get("worker_active_elapsed_s")
    observed = record.get("worker_observed_epoch_s")
    completed = record.get("worker_generation_completed")
    if (type(elapsed) not in {int, float} or not math.isfinite(elapsed) or elapsed < 0
            or type(observed) not in {int, float} or not math.isfinite(observed) or observed < 0
            or type(completed) is not bool):
        raise ValueError("Invalid cumulative worker clock receipt")
    return float(elapsed), float(observed), completed


def worker_elapsed_for_resume(record: dict[str, Any]) -> float:
    """Include the unknown interval after an interrupted worker observation.

    A clean completion receipt excludes subsequent downtime. Without that
    receipt, process death and downtime cannot be distinguished, so the whole
    observation gap is conservatively charged before new work is admitted.
    """
    elapsed, observed, completed = _worker_clock_receipt(record)
    if not completed:
        gap = time.time() - observed
        if not math.isfinite(gap) or gap < 0:
            raise ValueError("Cannot bound interrupted worker time after a wall-clock reversal")
        elapsed += gap
    if not math.isfinite(elapsed):
        raise ValueError("Invalid cumulative worker elapsed time")
    return float(elapsed)


class AttemptCheckpointRegistry:
    """One locked writer and a map of the latest committed session records."""

    def __init__(
        self, directory: Path, *, identity: dict[str, Any],
        resume_from: Path | None = None, recorder: Any = None,
        cost_controller: Any = None,
        startup_artifacts: dict[str, str] | None = None,
        worker_started_monotonic: float | None = None,
        worker_admitted_elapsed_s: float | None = None,
    ) -> None:
        now = time.monotonic()
        if worker_started_monotonic is None:
            worker_started_monotonic = now
        if (type(worker_started_monotonic) not in {int, float}
                or not math.isfinite(worker_started_monotonic)
                or not 0 <= worker_started_monotonic <= now):
            raise ValueError("Invalid worker generation clock origin")
        self._worker_started_monotonic = float(worker_started_monotonic)
        if worker_admitted_elapsed_s is not None and (
            type(worker_admitted_elapsed_s) not in {int, float}
            or not math.isfinite(worker_admitted_elapsed_s) or worker_admitted_elapsed_s < 0
        ):
            raise ValueError("Invalid admitted predecessor worker time")
        self._worker_admitted_elapsed_s = worker_admitted_elapsed_s
        self._restored_worker_active_elapsed_s = float(worker_admitted_elapsed_s or 0.0)
        self.directory = Path(directory).resolve()
        self.identity = _json(identity)
        if type(self.identity) is not dict or not self.identity:
            raise ValueError("Attempt checkpoint identity must be a nonempty object")
        self.recorder = recorder
        self.cost_controller = cost_controller
        self._lock = asyncio.Lock()
        self._journal_lock = asyncio.Lock()
        self._journal_writer = None
        self._sessions: dict[str, dict[str, Any]] = {}
        self._children: dict[str, dict[str, Any]] = {}
        self._outer_state: dict[str, Any] = {}
        self._planner_receipts: dict[str, dict[str, Any]] = {}
        self._bound_sessions: dict[str, Any] = {}
        self._sequence = 0
        self._closed = False
        self._lock_fp = None
        self._restored_cost_record = None
        self._restored_recorder_record = None
        self._restored_journal_watermark = 0
        self._resuming = resume_from is not None
        predecessor = None
        if resume_from is not None:
            predecessor = Path(resume_from).resolve()
            if predecessor == self.directory:
                raise ValueError("Resume requires a new generation directory")
            manifest = self._load_manifest(predecessor)
            if manifest["identity"] != self.identity:
                raise ValueError("Attempt checkpoint configuration identity mismatch")
            self.attempt_id = manifest["attempt_id"]
            self.registry_root = Path(manifest["registry_root"])
        else:
            self.attempt_id = uuid.uuid4().hex
            self.registry_root = self.directory.parent / ".mini_attempts" / self.attempt_id
        self.registry_root.mkdir(parents=True, exist_ok=True)
        self._lock_fp = (self.registry_root / "writer.lock").open("a+b")
        try:
            try:
                fcntl.flock(self._lock_fp.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise RuntimeError("Attempt checkpoint already has an active writer") from error
            if predecessor is not None:
                # Reload under the shared lock: a former writer may have
                # published a later generation while we were acquiring it.
                manifest = self._load_manifest(predecessor)
                head = _read(self.registry_root / "head.json")
                # The candidate per-generation manifest may lead the sole
                # committed shared head after an interrupted publication.
                # Resolve the committed head only within the requested
                # generation; older generations must not regain spending.
                if (
                    head.get("generation_id") != manifest["head"]["generation_id"]
                    or Path(head.get("snapshot_path", "")).parent
                    != predecessor / "checkpoints"
                ):
                    raise ValueError("Stale checkpoint generation; resume the latest attempt head")
                snapshot = _read(Path(head["snapshot_path"]))
                if _digest(snapshot) != head["snapshot_hash"]:
                    raise ValueError("Attempt checkpoint snapshot hash mismatch")
                self._restore_snapshot(snapshot)
            if self.directory.exists() and any(self.directory.iterdir()):
                from ..mini_generation_artifacts import validate_startup_artifact_receipts
                # A recorder may already own this new directory; only its
                # fresh generation artifacts are allowed before registration.
                allowed = {"run.log", "turns.jsonl"} if recorder is not None else set()
                allowed.update(validate_startup_artifact_receipts(self.directory, startup_artifacts))
                if any(path.name not in allowed for path in self.directory.iterdir()):
                    raise ValueError("Checkpoint generation directory is not empty")
            from .durable_checkpoint import JournalWriter
            self._journal_writer = JournalWriter(self.registry_root / "journal")
            self.directory.mkdir(parents=True, exist_ok=True)
            self.generation_id = uuid.uuid4().hex
            self.predecessor = str(predecessor) if predecessor is not None else None
            self._publish(self._snapshot_payload())
        except BaseException:
            self.close()
            raise

    @staticmethod
    def _load_manifest(directory: Path) -> dict[str, Any]:
        record = _read(directory / _MANIFEST)
        required = {"schema_version", "attempt_id", "registry_root", "identity", "head"}
        if type(record) is not dict or set(record) != required or type(record["schema_version"]) is not int or record["schema_version"] != _SCHEMA:
            raise ValueError("Unsupported attempt checkpoint manifest schema")
        attempt_id = record["attempt_id"]
        if type(attempt_id) is not str or len(attempt_id) != 32 or any(c not in "0123456789abcdef" for c in attempt_id):
            raise ValueError("Invalid attempt checkpoint identity")
        root = Path(record["registry_root"])
        if not root.is_absolute() or root.name != attempt_id or root.parent.name != ".mini_attempts":
            raise ValueError("Invalid attempt checkpoint owner directory")
        head = record["head"]
        if type(head) is not dict or set(head) != {"generation_id", "snapshot_path", "snapshot_hash"}:
            raise ValueError("Invalid attempt checkpoint head")
        snapshot_path = Path(head["snapshot_path"])
        if snapshot_path.parent != directory.resolve() / "checkpoints":
            raise ValueError("Attempt checkpoint snapshot escaped its generation")
        return record

    def _restore_snapshot(self, record: dict[str, Any]) -> None:
        required = {"schema_version", "attempt_id", "identity", "sessions", "children", "outer_state", "planner_receipts", "cost_ledger", "recorder", "journal_watermark", "predecessor", "worker_active_elapsed_s", "worker_observed_epoch_s", "worker_generation_completed"}
        if type(record) is not dict or set(record) != required or type(record["schema_version"]) is not int or record["schema_version"] != _SCHEMA:
            raise ValueError("Unsupported attempt checkpoint snapshot schema")
        if record["identity"] != self.identity or record["attempt_id"] != self.attempt_id:
            raise ValueError("Attempt checkpoint snapshot identity mismatch")
        for name in ("sessions", "children", "outer_state", "planner_receipts"):
            if type(record[name]) is not dict:
                raise ValueError("Invalid attempt checkpoint state map")
        watermark = record["journal_watermark"]
        if type(watermark) is not int or watermark < 0:
            raise ValueError("Invalid attempt checkpoint journal watermark")
        admitted = self._worker_admitted_elapsed_s
        if admitted is None:
            self._restored_worker_active_elapsed_s = worker_elapsed_for_resume(record)
        else:
            committed, _, _ = _worker_clock_receipt(record)
            # A subtraction of the supervisor's residual cap can round by a
            # few ulps. It may never lower the actual committed clock floor.
            if admitted < committed and not math.isclose(admitted, committed, rel_tol=0.0, abs_tol=1e-9):
                raise ValueError("Worker lease would erase committed predecessor time")
            self._restored_worker_active_elapsed_s = max(admitted, committed)
        self._sessions = _json(record["sessions"])
        self._children = _json(record["children"])
        self._outer_state = _json(record["outer_state"])
        self._planner_receipts = _json(record["planner_receipts"])
        self._restored_cost_record = _json(record["cost_ledger"])
        self._restored_recorder_record = _json(record["recorder"])
        self._restored_journal_watermark = watermark

    def _snapshot_payload(self) -> dict[str, Any]:
        observed_epoch_s = time.time()
        return {
            "schema_version": _SCHEMA, "attempt_id": self.attempt_id,
            "identity": self.identity, "sessions": self._sessions,
            "children": self._children, "outer_state": self._outer_state,
            "planner_receipts": self._planner_receipts,
            "cost_ledger": self._restored_cost_record,
            "recorder": self._restored_recorder_record,
            "journal_watermark": self._restored_journal_watermark,
            "worker_active_elapsed_s": self._restored_worker_active_elapsed_s + max(
                0.0, time.monotonic() - self._worker_started_monotonic,
            ),
            "worker_observed_epoch_s": observed_epoch_s,
            "worker_generation_completed": False,
            "predecessor": getattr(self, "predecessor", None),
        }

    def _publish(self, record: dict[str, Any]) -> None:
        if self._closed:
            raise RuntimeError("Attempt checkpoint writer is closed")
        next_sequence = self._sequence + 1
        snapshot_path = self.directory / "checkpoints" / f"{next_sequence:012d}.json"
        snapshot = _json(record)
        _write(snapshot_path, snapshot)
        head = {"generation_id": self.generation_id, "snapshot_path": str(snapshot_path),
                "snapshot_hash": _digest(snapshot)}
        manifest = {"schema_version": _SCHEMA, "attempt_id": self.attempt_id,
                    "registry_root": str(self.registry_root), "identity": self.identity,
                    "head": head}
        # The shared head prevents a later restart from silently restoring an
        # older generation's cost capacity. Never fall back past this head.
        _write(self.directory / _MANIFEST, manifest)
        _write(self.registry_root / "head.json", head)
        self._sequence = next_sequence

    @property
    def is_resume(self) -> bool:
        return self._resuming

    @property
    def recorder_resume_state(self) -> dict[str, Any] | None:
        return _json(self._restored_recorder_record)

    @property
    def cost_resume_state(self) -> dict[str, Any] | None:
        return _json(self._restored_cost_record)

    def validated_journal_records(self) -> list[dict[str, Any]]:
        from .durable_checkpoint import read_journal_records
        records = read_journal_records(self.registry_root / "journal")
        watermark = self._restored_journal_watermark
        cost = self._restored_cost_record
        if cost is None:
            if watermark or records:
                raise ValueError("Cost journal has no committed ledger baseline")
            return []
        if (type(cost) is not dict or type(cost.get("journal_sequence")) is not int
                or cost["journal_sequence"] != watermark or watermark > len(records)):
            raise ValueError("Cost ledger and attempt journal watermarks disagree")
        actual_hash = records[watermark - 1]["record_hash"] if watermark else ""
        if cost.get("journal_hash") != actual_hash:
            raise ValueError("Cost journal prefix differs from the saved ledger watermark")
        if watermark and records[watermark - 1]["payload"].get("ledger_id") != cost.get("ledger_id"):
            raise ValueError("Cost journal prefix belongs to another ledger")
        return records[watermark:]

    def planner_receipt_records(self, lane_key: str) -> tuple[dict[str, Any], ...]:
        return tuple(_json(record) for record in self._planner_receipts.get(lane_key, {}).values())

    async def persist_planner_receipt(self, lane_key: str, record: dict[str, Any],
                                     *, publication_guard: Any) -> None:
        from .planner_jobs import planner_result_from_record
        if lane_key not in self._sessions:
            raise ValueError("Planner receipt requires a committed session lane")
        data = _json(record)
        identity = planner_result_from_record(data).identity
        key = _digest([identity.job_id, identity.request_fingerprint])
        await self._commit_update(planner_receipt_updates={lane_key: {key: data}},
                                  publication_guard=publication_guard)

    def lane_record(self, lane_key: str) -> dict[str, Any] | None:
        return _json(self._sessions.get(lane_key))

    def child_record(self, child_lane: str) -> dict[str, Any] | None:
        return _json(self._children.get(child_lane))

    def child_records_for_parent(self, parent_lane: str) -> dict[str, dict[str, Any]]:
        return _json({lane: frame for lane, frame in self._children.items()
                      if frame.get("parent_lane") == parent_lane})

    @property
    def outer_state(self) -> dict[str, Any]:
        return _json(self._outer_state)

    async def bind_session(self, lane_key: str, session: Any) -> None:
        from .durable_checkpoint import restore_session_record
        from .durable_session_record import (
            initialize_theory_checkpoint_context, session_checkpoint_identity,
        )
        if type(lane_key) is not str or not lane_key:
            raise ValueError("Checkpoint lane identity is required")
        if lane_key in self._bound_sessions:
            if self._bound_sessions[lane_key] is session:
                return
            raise ValueError("Checkpoint lane already has a live session owner")
        # Reserve this process-local lane before any fresh Lean check awaits.
        # Parallel restores of distinct lanes remain independent.
        self._bound_sessions[lane_key] = session
        previous_registry = getattr(session, "checkpoint_registry", None)
        previous_lane = getattr(session, "checkpoint_lane_key", "")
        try:
            initialize_theory_checkpoint_context(session)
            # Bind immutable disk inputs before providers or prepasses start.
            # Later synchronous captures reuse this verifier generation's hash.
            await asyncio.to_thread(session_checkpoint_identity, session)
            record = self._sessions.get(lane_key)
            if record is not None:
                await restore_session_record(session, _json(record), expected_identity=record["identity"])
            session.checkpoint_registry = self
            session.checkpoint_lane_key = lane_key
            child_frames = self.child_records_for_parent(lane_key)
            for action in session.actions:
                restore_children = getattr(action, "restore_checkpoint_children", None)
                if callable(restore_children):
                    restored = restore_children(session, child_frames)
                    if inspect.isawaitable(restored):
                        await restored
            if record is None:
                await self.commit_session(lane_key, session)
        except BaseException:
            if self._bound_sessions.get(lane_key) is session:
                self._bound_sessions.pop(lane_key)
            session.checkpoint_registry = previous_registry
            session.checkpoint_lane_key = previous_lane
            raise

    async def commit_session(self, lane_key: str, session: Any) -> None:
        from .durable_checkpoint import capture_session_record
        if self._bound_sessions.get(lane_key) is not session:
            raise ValueError("Checkpoint session does not own its lane")
        record = capture_session_record(session)
        broker = session.planner_job_broker(create=False)
        acknowledged = broker.acknowledged_receipts() if broker is not None else ()
        owner = getattr(session, "_recursive_lane_authority", None) or session
        broker_lane = getattr(owner, "checkpoint_lane_key", "")
        # A descendant cannot commit receipt consumption by its parent broker.
        if owner is not session:
            acknowledged = ()
        removals = {broker_lane: [_digest([item.job_id, item.request_fingerprint])
                                 for item in acknowledged]} if acknowledged else {}
        await self._commit_update(session_updates={lane_key: _json(record)},
                                  planner_receipt_removals=removals)
        if acknowledged:
            broker.confirm_receipts_committed(acknowledged)

    async def _commit_update(self, **updates: Any) -> None:
        # Serialize companion snapshots with the manifest transaction. The
        # accounting lock may await durable_cost_event, which uses only the
        # independent journal lock and never acquires this transaction lock.
        async with self._lock:
            publication_guard = updates.pop("publication_guard", None)
            if publication_guard is not None and not publication_guard():
                raise RuntimeError("Planner publication ownership was revoked")
            planner_updates = updates.pop("planner_receipt_updates", {})
            planner_removals = updates.pop("planner_receipt_removals", {})
            planner_receipts = _json(self._planner_receipts)
            for lane, keys in planner_removals.items():
                for key in keys:
                    planner_receipts.get(lane, {}).pop(key, None)
            for lane, receipts in planner_updates.items():
                destination = planner_receipts.setdefault(lane, {})
                for key, receipt in receipts.items():
                    if key in destination and destination[key] != receipt:
                        raise ValueError("Conflicting completed planner receipt")
                    destination[key] = receipt
            prepared_children = updates.pop("prepared_child_updates", {})
            completed_children = updates.pop("completed_child_updates", {})
            child_updates = updates.pop("child_updates", {})
            for lane, frame in prepared_children.items():
                existing = self._children.get(lane)
                if existing is not None:
                    if {**existing, "result": None} != frame:
                        raise ValueError("Prepared child identity or attempt frame changed")
                    return
                child_updates[lane] = frame
            for lane, result in completed_children.items():
                frame = self._children.get(lane)
                if frame is None:
                    raise ValueError("Unknown prepared child lane")
                if frame["result"] is not None:
                    if frame["result"] != result:
                        raise ValueError("Completed child receipt is immutable")
                    return
                child_updates[lane] = {**frame, "result": result}
            cost_record = (
                await self.cost_controller.to_execution_record()
                if self.cost_controller is not None else self._restored_cost_record
            )
            recorder_record = (
                self.recorder.to_execution_record()
                if self.recorder is not None else self._restored_recorder_record
            )
            # The cost snapshot's own acknowledgement is the exact replay
            # floor. Reading the journal head afterward could skip a newer
            # financial transition which is absent from this snapshot.
            watermark = (
                cost_record["journal_sequence"]
                if cost_record is not None else self._restored_journal_watermark
            )
            snapshot = self._snapshot_payload()
            session_updates = updates.pop("session_updates", {})
            snapshot["sessions"] = {**self._sessions, **session_updates}
            snapshot["children"] = {**self._children, **child_updates}
            snapshot["planner_receipts"] = planner_receipts
            snapshot.update(updates)
            snapshot.update(cost_ledger=cost_record, recorder=recorder_record,
                            journal_watermark=watermark)
            if publication_guard is not None and not publication_guard():
                raise RuntimeError("Planner publication ownership was revoked")
            self._publish(snapshot)
            self._sessions = snapshot["sessions"]
            self._children = snapshot["children"]
            self._outer_state = snapshot["outer_state"]
            self._planner_receipts = planner_receipts
            self._restored_cost_record = cost_record
            self._restored_recorder_record = recorder_record
            self._restored_journal_watermark = watermark

    async def prepare_child(
        self, parent_lane: str, descriptor: dict[str, Any],
        action_runtime: dict[str, Any], selected_work: dict[str, Any],
        *, publication_guard: Any = None,
    ) -> str:
        if publication_guard is not None and not publication_guard():
            raise RuntimeError("Child publication ownership was revoked")
        if parent_lane not in self._sessions:
            raise ValueError("Child needs a committed parent checkpoint")
        descriptor = _json(descriptor)
        child_lane = descriptor.get("child_lane")
        if type(child_lane) is not str or not child_lane or child_lane == parent_lane:
            raise ValueError("Prepared child needs a distinct stable lane identity")
        frame = {"parent_lane": parent_lane, "descriptor": descriptor,
                 "action_runtime": _json(action_runtime), "selected_work": _json(selected_work),
                 "result": None}
        existing = self._children.get(child_lane)
        if existing is not None:
            comparable = {**existing, "result": None}
            if comparable != frame:
                raise ValueError("Prepared child identity or attempt frame changed")
            return child_lane
        await self._commit_update(prepared_child_updates={child_lane: frame},
                                  publication_guard=publication_guard)
        return child_lane

    async def complete_child(self, child_lane: str, result_record: dict[str, Any],
                             *, publication_guard: Any = None) -> None:
        if child_lane not in self._children:
            raise ValueError("Unknown prepared child lane")
        result = _json(result_record)
        if type(result) is not dict:
            raise ValueError("Completed child receipt must be an object")
        await self._commit_update(completed_child_updates={child_lane: result},
                                  publication_guard=publication_guard)

    async def update_outer_state(self, record: dict[str, Any]) -> None:
        await self._commit_update(outer_state=_json(record))

    async def write_snapshot(self) -> None:
        await self._commit_update()

    async def complete_worker_generation(self) -> None:
        """Acknowledge stopped execution after the caller has fenced new work."""
        await self._commit_update(worker_generation_completed=True)

    async def durable_cost_event(self, payload: dict[str, Any]) -> dict[str, Any]:
        async with self._journal_lock:
            if self._closed:
                raise RuntimeError("Attempt checkpoint writer is closed")
            return self._journal_writer.append(kind="cost_ledger", payload=_json(payload))

    def close(self) -> None:
        self._closed = True
        if self._journal_writer is not None:
            self._journal_writer.close()
            self._journal_writer = None
        if self._lock_fp is not None:
            try:
                fcntl.flock(self._lock_fp.fileno(), fcntl.LOCK_UN)
            finally:
                self._lock_fp.close()
                self._lock_fp = None
