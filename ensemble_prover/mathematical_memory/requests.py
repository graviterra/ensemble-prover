"""Bounded durable user requests, separate from proof acceptance and execution."""

from __future__ import annotations

import copy
import fcntl
import hashlib
import json
import math
import os
import re
import time
from pathlib import Path
from typing import Any, Callable

from .evidence import (
    EvidenceUnavailable,
    contained_directory,
    read_contained,
    write_contained,
)


class MemoryRequestError(ValueError):
    pass


_FIELDS = frozenset(
    {
        "request_id",
        "kind",
        "goal_id",
        "candidate_id",
        "environment_id",
        "policy_id",
        "retry_of",
        "text",
        "statement",
        "allocation_id",
        "max_seconds",
    }
)
_TRANSITIONS = {
    "pending": {"admitted", "rejected", "cancelled"},
    "admitted": {"running", "unresolved", "rejected", "cancelled", "completed"},
    "running": {"unresolved", "cancelled", "completed"},
    "unresolved": {"cancelled", "completed", "rejected"},
    "completed": set(),
    "rejected": set(),
    "cancelled": set(),
}


def validate_request(payload: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(payload, dict) or set(payload) - _FIELDS:
        raise MemoryRequestError("invalid_request_fields")
    result: dict[str, Any] = {}
    for key in _FIELDS - {"max_seconds"}:
        value = payload.get(key, "")
        limit = 16384 if key == "statement" else 8192 if key == "text" else 128
        if not isinstance(value, str) or len(value) > limit or "\0" in value:
            raise MemoryRequestError("invalid_request_value")
        if (
            key not in {"text", "statement"}
            and value
            and not re.fullmatch(r"[a-zA-Z0-9_:.@-]+", value)
        ):
            raise MemoryRequestError("invalid_request_identity")
        result[key] = value
    if not result["request_id"] or result["kind"] not in {
        "pin",
        "note",
        "retry",
        "generalization",
    }:
        raise MemoryRequestError("invalid_request_kind_or_id")
    if not result["goal_id"] or not result["policy_id"]:
        raise MemoryRequestError("missing_target_binding")
    if result["kind"] in {"pin", "retry"} and not result["candidate_id"]:
        raise MemoryRequestError("missing_candidate")
    if result["kind"] == "retry" and not result["retry_of"]:
        raise MemoryRequestError("missing_prior_application")
    if result["kind"] != "retry" and result["retry_of"]:
        raise MemoryRequestError("unexpected_prior_application")
    if result["kind"] == "note" and not result["text"].strip():
        raise MemoryRequestError("empty_note")
    if result["kind"] == "generalization" and not result["statement"].strip():
        raise MemoryRequestError("empty_statement")
    seconds = payload.get("max_seconds", 0)
    if (
        type(seconds) not in (int, float)
        or not math.isfinite(seconds)
        or seconds < 0
        or seconds > 86400
    ):
        raise MemoryRequestError("invalid_budget")
    result["max_seconds"] = float(seconds)
    if result["kind"] in {"retry", "generalization"} and (
        seconds <= 0 or not result["allocation_id"] or not result["environment_id"]
    ):
        raise MemoryRequestError("missing_job_allocation")
    return result


class MemoryRequestStore:
    """Atomic file ledger protected by a nonblocking process-shared lock.

    Admission records dispatch intent. The runtime owns permission/budget checks;
    a submitted request alone cannot execute. Resume must reconcile in-flight
    receipts, never blindly launch a persisted admitted/running request.
    """

    def __init__(
        self, run_dir: Path, *, max_records: int = 1024, max_bytes: int = 2_000_000
    ) -> None:
        self.run_dir = Path(run_dir)
        self.max_records = max_records
        self.max_bytes = max_bytes
        self._dispatch_lock: int | None = None

    @property
    def owns_dispatch(self) -> bool:
        return self._dispatch_lock is not None

    def close(self) -> None:
        if self._dispatch_lock is not None:
            os.close(self._dispatch_lock)
            self._dispatch_lock = None

    def __del__(self) -> None:
        self.close()

    def _claim_dispatch(self) -> bool:
        if self.owns_dispatch:
            return True
        with contained_directory(
            self.run_dir, "memory_requests", create=True
        ) as directory:
            lock = os.open(
                "owner.lock",
                os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW,
                0o600,
                dir_fd=directory,
            )
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                os.close(lock)
                return False
            self._dispatch_lock = lock
            return True

    def _transaction(
        self,
        mutate: Callable[[dict[str, Any]], Any],
        *,
        write: bool = True,
        deadline_monotonic: float | None = None,
    ) -> Any:
        try:
            with contained_directory(
                self.run_dir, "memory_requests", create=write
            ) as fd:
                lock = os.open(
                    "lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600, dir_fd=fd
                )
                try:
                    try:
                        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    except BlockingIOError as exc:
                        raise MemoryRequestError("request_store_busy") from exc
                    try:
                        ledger = json.loads(
                            read_contained(
                                fd, "requests.json", self.max_bytes, deadline_monotonic
                            )
                        )
                    except FileNotFoundError:
                        ledger = {
                            "schema_version": 1,
                            "run_identity": str(self.run_dir.absolute()),
                            "requests": {},
                        }
                    if (
                        ledger.get("schema_version") != 1
                        or ledger.get("run_identity") != str(self.run_dir.absolute())
                        or not isinstance(ledger.get("requests"), dict)
                    ):
                        raise MemoryRequestError("request_store_incompatible")
                    for identity, record in ledger["requests"].items():
                        if (
                            not isinstance(record, dict)
                            or record.get("status") not in _TRANSITIONS
                        ):
                            raise MemoryRequestError("request_store_corrupt")
                        request = validate_request(record.get("payload"))
                        digest = hashlib.sha256(
                            json.dumps(
                                request, sort_keys=True, separators=(",", ":")
                            ).encode()
                        ).hexdigest()
                        if (
                            request["request_id"] != identity
                            or record.get("digest") != digest
                        ):
                            raise MemoryRequestError("request_store_corrupt")
                        submitted = record.get("submitted_at")
                        if (
                            type(submitted) not in (int, float)
                            or not math.isfinite(submitted)
                            or submitted < 0
                        ):
                            raise MemoryRequestError("request_store_corrupt")
                    allocations = ledger.get("research_allocations", {})
                    if (
                        not isinstance(allocations, dict)
                        or len(allocations) > self.max_records
                    ):
                        raise MemoryRequestError("research_ledger_corrupt")
                    reserved_requests: set[str] = set()
                    for allocation_id, allocation in allocations.items():
                        if not isinstance(allocation, dict) or not isinstance(
                            allocation.get("reservations"), dict
                        ):
                            raise MemoryRequestError("research_ledger_corrupt")
                        cap = allocation.get("total_seconds")
                        if (
                            type(cap) not in (int, float)
                            or not math.isfinite(cap)
                            or cap <= 0
                        ):
                            raise MemoryRequestError("research_ledger_corrupt")
                        for request_id, reservation in allocation[
                            "reservations"
                        ].items():
                            owner = ledger["requests"].get(request_id)
                            if (
                                request_id in reserved_requests
                                or owner is None
                                or not isinstance(reservation, dict)
                                or owner["payload"]["kind"] != "generalization"
                                or owner["payload"]["allocation_id"] != allocation_id
                                or reservation.get("allocation_id") != allocation_id
                                or reservation.get("request_id") != request_id
                                or reservation.get("attempt_id")
                                != owner.get("attempt_id")
                                or reservation.get("status")
                                not in {"reserved", "settled"}
                            ):
                                raise MemoryRequestError("research_ledger_corrupt")
                            reserved_requests.add(request_id)
                            cost = reservation.get("reserved_seconds")
                            if (
                                type(cost) not in (int, float)
                                or not math.isfinite(cost)
                                or cost <= 0
                                or cost > owner["payload"]["max_seconds"]
                            ):
                                raise MemoryRequestError("research_ledger_corrupt")
                            if reservation["status"] == "settled":
                                cost = reservation.get("actual_seconds")
                                if (
                                    type(cost) not in (int, float)
                                    or not math.isfinite(cost)
                                    or cost < 0
                                ):
                                    raise MemoryRequestError("research_ledger_corrupt")
                            elif "actual_seconds" in reservation:
                                raise MemoryRequestError("research_ledger_corrupt")
                    result = mutate(ledger)
                    if write:
                        encoded = json.dumps(
                            ledger,
                            sort_keys=True,
                            separators=(",", ":"),
                            allow_nan=False,
                        ).encode()
                        if (
                            len(encoded) > self.max_bytes
                            or len(ledger["requests"]) > self.max_records
                        ):
                            raise MemoryRequestError("request_store_full")
                        write_contained(
                            fd, "requests.json", encoded, deadline_monotonic
                        )
                    return copy.deepcopy(result)
                finally:
                    os.close(lock)
        except FileNotFoundError:
            if not write:
                return mutate({"requests": {}})
            raise MemoryRequestError("request_store_unavailable")
        except (OSError, EvidenceUnavailable, ValueError, TypeError) as exc:
            if isinstance(exc, MemoryRequestError):
                raise
            raise MemoryRequestError("request_store_unavailable") from exc

    def submit(
        self, payload: dict[str, Any], *, deadline_monotonic: float | None = None
    ) -> dict[str, Any]:
        request = validate_request(payload)
        digest = hashlib.sha256(
            json.dumps(request, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()

        def insert(ledger: dict[str, Any]) -> dict[str, Any]:
            existing = ledger["requests"].get(request["request_id"])
            if existing:
                if existing.get("digest") != digest:
                    raise MemoryRequestError("request_identity_conflict")
                return existing
            record = {
                "payload": request,
                "digest": digest,
                "status": "pending",
                "submitted_at": time.time(),
                "operation_id": "",
                "attempt_id": "",
                "receipt_id": "",
                "detail": "",
            }
            ledger["requests"][request["request_id"]] = record
            return record

        return self._transaction(insert, deadline_monotonic=deadline_monotonic)

    def list(
        self, *, limit: int = 64, status: str | None = None
    ) -> list[dict[str, Any]]:
        if type(limit) is not int or limit <= 0:
            return []
        return self._transaction(
            lambda ledger: [
                record
                for record in sorted(
                    ledger["requests"].values(), key=lambda item: item["submitted_at"]
                )
                if status is None or record.get("status") == status
            ][-max(0, min(limit, 128)) :],
            write=False,
        )

    def pending(
        self, limit: int = 16, *, deadline_monotonic: float | None = None
    ) -> list[dict[str, Any]]:
        if type(limit) is not int or limit <= 0:
            return []
        return self._transaction(
            lambda ledger: [
                record
                for record in sorted(
                    ledger["requests"].values(), key=lambda item: item["submitted_at"]
                )
                if record.get("status") == "pending"
            ][: min(limit, 128)],
            write=False,
            deadline_monotonic=deadline_monotonic,
        )

    def admit(
        self,
        request_id: str,
        operation_id: str,
        attempt_id: str,
        *,
        deadline_monotonic: float | None = None,
    ) -> dict[str, Any]:
        if (
            not operation_id
            or not attempt_id
            or len(operation_id) > 128
            or len(attempt_id) > 128
        ):
            raise MemoryRequestError("missing_dispatch_identity")

        def admission(ledger: dict[str, Any]) -> dict[str, Any]:
            record = ledger["requests"].get(request_id)
            if record is None or record.get("status") != "pending":
                raise MemoryRequestError("request_not_pending")
            record.update(
                status="admitted",
                operation_id=operation_id,
                attempt_id=attempt_id,
                admitted_at=time.time(),
            )
            return record

        return self._transaction(admission, deadline_monotonic=deadline_monotonic)

    def transition(
        self,
        request_id: str,
        status: str,
        *,
        detail: str = "",
        receipt_id: str = "",
        deadline_monotonic: float | None = None,
    ) -> dict[str, Any]:
        if (
            status not in _TRANSITIONS
            or not isinstance(detail, str)
            or not isinstance(receipt_id, str)
            or len(detail) > 512
            or len(receipt_id) > 128
        ):
            raise MemoryRequestError("invalid_transition")

        def change(ledger: dict[str, Any]) -> dict[str, Any]:
            record = ledger["requests"].get(request_id)
            if record is None:
                raise MemoryRequestError("unknown_request")
            if status == record.get("status"):
                return record
            if status not in _TRANSITIONS.get(record.get("status"), set()):
                raise MemoryRequestError("invalid_transition")
            if (
                record.get("status") == "unresolved"
                and status == "completed"
                and not receipt_id
            ):
                raise MemoryRequestError("reconciliation_receipt_required")
            record.update(
                status=status,
                detail=detail,
                receipt_id=receipt_id,
                updated_at=time.time(),
            )
            return record

        return self._transaction(change, deadline_monotonic=deadline_monotonic)

    def reconcile_inflight(self) -> list[dict[str, Any]]:
        if not self._claim_dispatch():
            return []

        def reconcile(ledger: dict[str, Any]) -> list[dict[str, Any]]:
            changed = []
            for record in ledger["requests"].values():
                if record.get("status") in {"admitted", "running"}:
                    record.update(
                        status="unresolved",
                        detail="Dispatch requires receipt reconciliation before retry.",
                    )
                    changed.append(record)
            return changed

        return self._transaction(reconcile)

    def reserve_research(
        self,
        allocation_id: str,
        total_seconds: float,
        request_id: str,
        max_seconds: float,
        *,
        deadline_monotonic: float | None = None,
    ) -> dict[str, Any]:
        """Reserve the research subset before work; ambiguous interruption keeps its charge.

        Only the elected runtime consumer calls this with an already authorized
        allocation. The HTTP request API cannot create or replenish allocations.
        """
        if not allocation_id or len(allocation_id) > 128:
            raise MemoryRequestError("invalid_research_allocation")
        for value in (total_seconds, max_seconds):
            if (
                type(value) not in (int, float)
                or not math.isfinite(value)
                or value <= 0
            ):
                raise MemoryRequestError("invalid_research_budget")

        def reserve(ledger: dict[str, Any]) -> dict[str, Any]:
            request = ledger["requests"].get(request_id)
            if (
                request is None
                or request["payload"]["kind"] != "generalization"
                or request["status"] not in {"admitted", "running"}
            ):
                raise MemoryRequestError("research_request_not_admitted")
            if request["payload"]["allocation_id"] != allocation_id:
                raise MemoryRequestError("research_allocation_mismatch")
            allocations = ledger.setdefault("research_allocations", {})
            if not isinstance(allocations, dict):
                raise MemoryRequestError("research_ledger_corrupt")
            allocation = allocations.setdefault(
                allocation_id,
                {"total_seconds": float(total_seconds), "reservations": {}},
            )
            if total_seconds > allocation["total_seconds"]:
                raise MemoryRequestError("research_allocation_cannot_grow")
            allocation["total_seconds"] = min(
                allocation["total_seconds"], float(total_seconds)
            )
            reservations = allocation["reservations"]
            previous = reservations.get(request_id)
            if previous:
                if previous["attempt_id"] != request["attempt_id"]:
                    raise MemoryRequestError("research_reservation_conflict")
                return previous
            charged = sum(
                item.get("actual_seconds", item["reserved_seconds"])
                for item in reservations.values()
            )
            remaining = allocation["total_seconds"] - charged
            if deadline_monotonic is not None:
                remaining = min(
                    remaining, max(0.0, deadline_monotonic - time.monotonic())
                )
            seconds = min(
                float(max_seconds), request["payload"]["max_seconds"], remaining
            )
            if seconds <= 0:
                raise MemoryRequestError("research_allocation_exhausted")
            result = {
                "request_id": request_id,
                "allocation_id": allocation_id,
                "attempt_id": request["attempt_id"],
                "reserved_seconds": seconds,
                "status": "reserved",
            }
            reservations[request_id] = result
            return result

        return self._transaction(reserve, deadline_monotonic=deadline_monotonic)

    def settle_research(
        self,
        request_id: str,
        actual_seconds: float,
        *,
        deadline_monotonic: float | None = None,
    ) -> dict[str, Any]:
        """Definitive completion can release unused time; uncertain work stays reserved."""
        if (
            type(actual_seconds) not in (int, float)
            or not math.isfinite(actual_seconds)
            or actual_seconds < 0
        ):
            raise MemoryRequestError("invalid_actual_research_cost")

        def settle(ledger: dict[str, Any]) -> dict[str, Any]:
            request = ledger["requests"].get(request_id)
            if request is None or request["status"] == "unresolved":
                raise MemoryRequestError("research_requires_reconciliation")
            matches = [
                allocation["reservations"][request_id]
                for allocation in ledger.get("research_allocations", {}).values()
                if request_id in allocation["reservations"]
            ]
            if len(matches) != 1:
                raise MemoryRequestError("research_reservation_unavailable")
            reservation = matches[0]
            if (
                reservation["status"] == "settled"
                and reservation["actual_seconds"] != actual_seconds
            ):
                raise MemoryRequestError("research_settlement_conflict")
            reservation.update(actual_seconds=float(actual_seconds), status="settled")
            return reservation

        return self._transaction(settle, deadline_monotonic=deadline_monotonic)
