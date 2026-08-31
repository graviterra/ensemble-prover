"""Durable, lock-protected queue of explicit domain-theory needs."""

from __future__ import annotations

import fcntl
import json
import os
import tempfile
import time
import uuid
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Iterator, Mapping, Optional

from .lease import TheoryLeaseOwner
from .model import TheoryNeed


@dataclass(frozen=True)
class TheoryNeedRecord:
    need: TheoryNeed
    status: str = "pending"
    attempts: int = 0
    # Lifetime attempts remain useful provenance, but scheduling limits are
    # run-scoped.  A tuple keeps the frozen record deterministic/comparable
    # while allowing multiple concurrent runs to retain independent budgets.
    attempts_by_scope: tuple[tuple[str, int], ...] = ()
    bundle_id: str = ""
    validated_bundle_ids: tuple[str, ...] = ()
    diagnostic: str = ""
    superseded_by_need_id: str = ""
    superseded_from_status: str = ""
    superseded_bundle_id: str = ""
    superseded_validated_bundle_ids: tuple[str, ...] = ()
    superseded_diagnostic: str = ""
    active_attempt_id: str = ""
    active_attempt_owner: str = ""
    active_attempt_started_ts: float = 0.0
    active_attempt_bundle_id: str = ""
    active_attempt_scope_id: str = ""
    updated_ts: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return {
            "need": self.need.to_dict(),
            "status": self.status,
            "attempts": self.attempts,
            "attempts_by_scope": dict(self.attempts_by_scope),
            "bundle_id": self.bundle_id,
            "validated_bundle_ids": self.validated_bundle_ids,
            "diagnostic": self.diagnostic,
            "superseded_by_need_id": self.superseded_by_need_id,
            "superseded_from_status": self.superseded_from_status,
            "superseded_bundle_id": self.superseded_bundle_id,
            "superseded_validated_bundle_ids": (
                self.superseded_validated_bundle_ids
            ),
            "superseded_diagnostic": self.superseded_diagnostic,
            "active_attempt_id": self.active_attempt_id,
            "active_attempt_owner": self.active_attempt_owner,
            "active_attempt_started_ts": self.active_attempt_started_ts,
            "active_attempt_bundle_id": self.active_attempt_bundle_id,
            "active_attempt_scope_id": self.active_attempt_scope_id,
            "updated_ts": self.updated_ts,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "TheoryNeedRecord":
        status = str(payload.get("status") or "pending")
        bundle_id = str(payload.get("bundle_id") or "")
        validated_bundle_ids = tuple(
            str(item or "").strip()
            for item in payload.get("validated_bundle_ids") or ()
            if str(item or "").strip()
        )
        if not validated_bundle_ids and bundle_id and status in {
            "resolved",
            "context_available",
        }:
            validated_bundle_ids = (bundle_id,)
        return cls(
            need=TheoryNeed.from_dict(dict(payload.get("need") or {})),
            status=status,
            attempts=int(payload.get("attempts") or 0),
            attempts_by_scope=tuple(
                sorted(
                    (
                        str(scope_id or "").strip(),
                        max(0, int(count or 0)),
                    )
                    for scope_id, count in dict(
                        payload.get("attempts_by_scope") or {}
                    ).items()
                    if str(scope_id or "").strip()
                )
            ),
            bundle_id=bundle_id,
            validated_bundle_ids=validated_bundle_ids,
            diagnostic=str(payload.get("diagnostic") or ""),
            superseded_by_need_id=str(
                payload.get("superseded_by_need_id") or ""
            ),
            superseded_from_status=str(
                payload.get("superseded_from_status") or ""
            ),
            superseded_bundle_id=str(
                payload.get("superseded_bundle_id") or ""
            ),
            superseded_validated_bundle_ids=tuple(
                str(item or "").strip()
                for item in payload.get("superseded_validated_bundle_ids") or ()
                if str(item or "").strip()
            ),
            superseded_diagnostic=str(
                payload.get("superseded_diagnostic") or ""
            ),
            active_attempt_id=str(payload.get("active_attempt_id") or ""),
            active_attempt_owner=str(payload.get("active_attempt_owner") or ""),
            active_attempt_started_ts=float(
                payload.get("active_attempt_started_ts") or 0.0
            ),
            active_attempt_bundle_id=str(
                payload.get("active_attempt_bundle_id") or ""
            ),
            active_attempt_scope_id=str(
                payload.get("active_attempt_scope_id") or ""
            ),
            updated_ts=float(payload.get("updated_ts") or 0.0),
        )


class TheoryNeedStore:
    """Persist need state without a mutable shared index file."""

    def __init__(
        self,
        root: Path,
        *,
        lease_owner: Optional[TheoryLeaseOwner] = None,
        attempt_scope_id: str = "",
    ) -> None:
        self.root = Path(root).expanduser().resolve()
        self.records_root = self.root / "needs"
        self.lock_path = self.root / ".needs.lock"
        self.transaction_path = self.root / ".needs.transaction.json"
        self.records_root.mkdir(parents=True, exist_ok=True)
        owns_lease_owner = lease_owner is None
        self.lease_owner = lease_owner or TheoryLeaseOwner(self.root)
        self.attempt_scope_id = str(attempt_scope_id or "").strip()
        # Complete any all-record supersession transaction left by a process
        # death before exposing the store to callers.
        try:
            with self._lock():
                pass
        except BaseException as primary_error:
            if owns_lease_owner:
                try:
                    self.lease_owner.close()
                except BaseException as cleanup_error:
                    primary_error.add_note(
                        "theory need-store lease cleanup also failed: "
                        f"{type(cleanup_error).__name__}: {cleanup_error}"
                    )
            raise

    def attempts_for_current_scope(self, record: TheoryNeedRecord) -> int:
        """Return the attempt count that governs this store's run.

        Stores without an explicit scope retain the legacy lifetime behavior
        for API compatibility and offline maintenance callers.
        """

        if not self.attempt_scope_id:
            return max(0, int(record.attempts or 0))
        return max(
            0,
            int(dict(record.attempts_by_scope).get(self.attempt_scope_id, 0)),
        )

    @staticmethod
    def _increment_scope_attempt(
        record: TheoryNeedRecord,
        scope_id: str,
    ) -> tuple[tuple[str, int], ...]:
        counts = dict(record.attempts_by_scope)
        clean_scope_id = str(scope_id or "").strip()
        if clean_scope_id:
            counts[clean_scope_id] = max(0, int(counts.get(clean_scope_id, 0))) + 1
        return tuple(sorted(counts.items()))

    def get(self, need_id: str) -> Optional[TheoryNeedRecord]:
        with self._lock():
            return self._get_unlocked(need_id)

    def _get_unlocked(self, need_id: str) -> Optional[TheoryNeedRecord]:
        path = self._path(need_id)
        if not path.is_file():
            return None
        return TheoryNeedRecord.from_dict(json.loads(path.read_text(encoding="utf-8")))

    def canonical_need_id(self, need_id: str) -> str:
        """Follow durable supersession links to the current contract version."""

        with self._lock():
            current = str(need_id or "").strip()
            seen: set[str] = set()
            while current and current not in seen:
                seen.add(current)
                record = self._get_unlocked(current)
                if (
                    record is None
                    or record.status != "superseded"
                    or not record.superseded_by_need_id
                ):
                    return current
                current = record.superseded_by_need_id
            return current

    def upsert(self, need: TheoryNeed) -> TheoryNeedRecord:
        with self._lock():
            existing = self._get_unlocked(need.need_id)
            if existing is not None:
                identity_fields = (
                    "need_id",
                    "domain",
                    "target_statement",
                    "need_kind",
                    "originating_root",
                    "consumer_node_id",
                    "consumer_statement",
                    "required_name_hint",
                    "required_imports",
                )
                existing_payload = existing.need.to_dict()
                incoming_payload = need.to_dict()
                existing_contract = tuple(existing_payload[key] for key in identity_fields)
                incoming_contract = tuple(incoming_payload[key] for key in identity_fields)
                if existing_contract != incoming_contract:
                    raise ValueError(f"theory need identity collision: {need.need_id}")
                if need.dependency_need_ids != existing.need.dependency_need_ids:
                    raise ValueError(
                        "theory need dependency plan changed without a new "
                        f"identity: {need.need_id}"
                    )
                return existing
            record = TheoryNeedRecord(need=need, updated_ts=time.time())
            self._write(record)
            return record

    def claim_build_attempt(
        self,
        need_id: str,
        *,
        max_attempts: int,
    ) -> Optional[TheoryNeedRecord]:
        """Atomically lease one construction attempt without charging it yet."""

        record, _reason = self.claim_build_attempt_with_reason(
            need_id,
            max_attempts=max_attempts,
        )
        return record

    def claim_build_attempt_with_reason(
        self,
        need_id: str,
        *,
        max_attempts: int,
    ) -> tuple[Optional[TheoryNeedRecord], str]:
        """Lease a build and distinguish live contention from terminal refusal."""

        limit = max(1, int(max_attempts or 1))
        previous: Optional[TheoryNeedRecord] = None
        claimed: Optional[TheoryNeedRecord] = None
        try:
            with self._lock():
                existing = self._get_unlocked(need_id)
                if existing is None:
                    raise KeyError(f"unknown theory need: {need_id}")
                if existing.status in {"resolved", "superseded"}:
                    return None, "terminal"
                if existing.active_attempt_id:
                    return None, "active_elsewhere"
                if self.attempts_for_current_scope(existing) >= limit:
                    return None, "exhausted"
                previous = existing
                claimed = replace(
                    existing,
                    active_attempt_id=uuid.uuid4().hex,
                    active_attempt_owner=self.lease_owner.owner_id,
                    active_attempt_started_ts=time.time(),
                    active_attempt_bundle_id="",
                    active_attempt_scope_id=self.attempt_scope_id,
                    updated_ts=time.time(),
                )
                self._write(claimed)
        except BaseException as primary:
            # The claim is not handed to the caller until both the durable
            # write and lock-scope cleanup return cleanly. A post-effect lock
            # exit failure therefore requires the same rollback as a
            # post-effect write failure, but only if our exact lease token is
            # still current.
            if previous is not None and claimed is not None:
                try:
                    self._rollback_unhanded_claim(previous, claimed)
                except BaseException as rollback_error:
                    primary.add_note(
                        "Mini theory claim rollback also failed: "
                        f"{type(rollback_error).__name__}: {rollback_error}"
                    )
            raise
        assert claimed is not None
        return claimed, "claimed"

    def _rollback_unhanded_claim(
        self,
        previous: TheoryNeedRecord,
        claimed: TheoryNeedRecord,
    ) -> None:
        """CAS-release a claim token that never reached its caller."""

        with self._lock():
            current = self._get_unlocked(claimed.need.need_id)
            if (
                current is None
                or not claimed.active_attempt_id
                or current.active_attempt_id != claimed.active_attempt_id
            ):
                return
            if current == claimed:
                restored = previous
            else:
                # Preserve any adjacent mutation made after the original lock
                # was actually released, while withdrawing only the token that
                # this failed handoff created.
                restored = replace(
                    current,
                    active_attempt_id="",
                    active_attempt_owner="",
                    active_attempt_started_ts=0.0,
                    active_attempt_bundle_id="",
                    active_attempt_scope_id="",
                    updated_ts=time.time(),
                )
            self._write(restored)

    def mark_build_attempt_candidate(
        self,
        need_id: str,
        attempt_id: str,
        *,
        bundle_id: str,
    ) -> tuple[TheoryNeedRecord, bool]:
        """CAS-bind the content identity needed for crash recovery."""

        clean_bundle_id = str(bundle_id or "").strip()
        if not clean_bundle_id:
            raise ValueError("theory build candidate bundle id is required")
        with self._lock():
            existing = self._get_unlocked(need_id)
            if existing is None:
                raise KeyError(f"unknown theory need: {need_id}")
            if not attempt_id or existing.active_attempt_id != attempt_id:
                return existing, False
            marked = replace(
                existing,
                active_attempt_bundle_id=clean_bundle_id,
                updated_ts=time.time(),
            )
            self._write(marked)
            return marked, True

    def abandoned_build_attempts(
        self,
        *,
        need_id: str = "",
    ) -> tuple[TheoryNeedRecord, ...]:
        """Snapshot attempts whose owner lock is provably no longer held."""

        with self._lock():
            if need_id:
                record = self._get_unlocked(need_id)
                records = () if record is None else (record,)
            else:
                records = tuple(self._iter_records_unlocked())
            return tuple(
                record
                for record in records
                if record.active_attempt_id
                and self.lease_owner.owner_abandoned(record.active_attempt_owner)
                is True
            )

    def settle_build_attempt(
        self,
        need_id: str,
        attempt_id: str,
        *,
        status: str,
        diagnostic: str,
        bundle_id: str = "",
        bundle_ids: tuple[str, ...] = (),
    ) -> tuple[TheoryNeedRecord, bool]:
        """Charge and settle exactly the caller's active attempt lease."""

        with self._lock():
            existing = self._get_unlocked(need_id)
            if existing is None:
                raise KeyError(f"unknown theory need: {need_id}")
            if not attempt_id or existing.active_attempt_id != attempt_id:
                return existing, False
            (
                settled_status,
                settled_bundle_id,
                settled_bundle_ids,
                settled_diagnostic,
            ) = self._monotonic_outcome_fields(
                existing,
                status=status,
                diagnostic=diagnostic,
                bundle_id=bundle_id,
                bundle_ids=bundle_ids,
            )
            settled = replace(
                existing,
                status=settled_status,
                attempts=existing.attempts + 1,
                attempts_by_scope=self._increment_scope_attempt(
                    existing,
                    existing.active_attempt_scope_id,
                ),
                bundle_id=settled_bundle_id,
                validated_bundle_ids=settled_bundle_ids,
                diagnostic=settled_diagnostic,
                active_attempt_id="",
                active_attempt_owner="",
                active_attempt_started_ts=0.0,
                active_attempt_bundle_id="",
                active_attempt_scope_id="",
                updated_ts=time.time(),
            )
            self._write(settled)
            return settled, True

    @staticmethod
    def _monotonic_outcome_fields(
        existing: TheoryNeedRecord,
        *,
        status: str,
        diagnostic: str,
        bundle_id: str,
        bundle_ids: tuple[str, ...],
    ) -> tuple[str, str, tuple[str, ...], str]:
        """Resolve outcome fields without losing already verified context."""

        if existing.status in {"resolved", "superseded"}:
            return (
                existing.status,
                existing.bundle_id,
                existing.validated_bundle_ids,
                existing.diagnostic,
            )
        incoming_status = str(status or "pending")
        incoming_bundle_ids = tuple(
            dict.fromkeys(
                str(item or "").strip()
                for item in bundle_ids
                if str(item or "").strip()
            )
        )
        clean_bundle_id = str(bundle_id or "").strip()
        if not incoming_bundle_ids and clean_bundle_id:
            incoming_bundle_ids = (clean_bundle_id,)
        incoming_primary_bundle_id = clean_bundle_id or (
            incoming_bundle_ids[-1] if incoming_bundle_ids else ""
        )
        if incoming_status == "resolved":
            if not incoming_bundle_ids:
                raise ValueError(
                    "resolved theory need requires an explicit nonempty "
                    "consumer-validated bundle closure"
                )
            if (
                incoming_primary_bundle_id
                and incoming_primary_bundle_id not in incoming_bundle_ids
            ):
                raise ValueError(
                    "resolved theory need primary bundle must belong to its "
                    "consumer-validated bundle closure"
                )
            # Resolution is an exact observation of the context under which
            # the proof consumer succeeded. A concurrently published
            # refinement is independently verified context, but it was not
            # consumer-validated and must not be certified by blind union.
            return (
                incoming_status,
                incoming_primary_bundle_id,
                incoming_bundle_ids,
                str(diagnostic or ""),
            )
        if existing.status != "context_available":
            return (
                incoming_status,
                incoming_primary_bundle_id,
                incoming_bundle_ids,
                str(diagnostic or ""),
            )
        if incoming_status == "context_available" and incoming_bundle_ids:
            existing_bundle_ids = tuple(existing.validated_bundle_ids or ()) or (
                (existing.bundle_id,) if existing.bundle_id else ()
            )
            if set(existing_bundle_ids).issubset(incoming_bundle_ids):
                merged_bundle_ids = tuple(
                    dict.fromkeys((*incoming_bundle_ids, *existing_bundle_ids))
                )
            else:
                merged_bundle_ids = tuple(
                    dict.fromkeys((*existing_bundle_ids, *incoming_bundle_ids))
                )
            return (
                incoming_status,
                incoming_primary_bundle_id or existing.bundle_id,
                merged_bundle_ids,
                str(diagnostic or existing.diagnostic),
            )
        if incoming_status != "superseded":
            return (
                existing.status,
                existing.bundle_id,
                existing.validated_bundle_ids,
                existing.diagnostic,
            )
        return (
            incoming_status,
            incoming_primary_bundle_id,
            incoming_bundle_ids,
            str(diagnostic or ""),
        )

    def release_build_attempt(
        self,
        need_id: str,
        attempt_id: str,
        *,
        diagnostic: str = "theory_build_attempt_interrupted",
    ) -> tuple[TheoryNeedRecord, bool]:
        """Release an interrupted lease without consuming a durable attempt."""

        with self._lock():
            existing = self._get_unlocked(need_id)
            if existing is None:
                raise KeyError(f"unknown theory need: {need_id}")
            if not attempt_id or existing.active_attempt_id != attempt_id:
                return existing, False
            released = replace(
                existing,
                diagnostic=(
                    existing.diagnostic
                    if existing.status in {"resolved", "superseded"}
                    else str(diagnostic or "theory_build_attempt_interrupted")
                ),
                active_attempt_id="",
                active_attempt_owner="",
                active_attempt_started_ts=0.0,
                active_attempt_bundle_id="",
                active_attempt_scope_id="",
                updated_ts=time.time(),
            )
            self._write(released)
            return released, True

    def supersede_need(
        self,
        old_need_id: str,
        new_need: TheoryNeed,
    ) -> tuple[str, ...]:
        """Install a revised need and recursively invalidate its dependents."""

        requested_old_id = str(old_need_id or "").strip()
        if not requested_old_id:
            self.upsert(new_need)
            return ()
        affected: list[str] = []
        with self._lock():
            records = {
                record.need.need_id: record for record in self._iter_records_unlocked()
            }

            def canonical_from_snapshot(need_id: str) -> str:
                current = str(need_id or "").strip()
                seen: set[str] = set()
                while current and current not in seen:
                    seen.add(current)
                    record = records.get(current)
                    if (
                        record is None
                        or record.status != "superseded"
                        or not record.superseded_by_need_id
                    ):
                        return current
                    current = record.superseded_by_need_id
                return current

            old_id = canonical_from_snapshot(requested_old_id)
            if old_id == new_need.need_id:
                return ()
            if requested_old_id != old_id:
                affected.append(requested_old_id)
            replacement = records.get(new_need.need_id)
            if replacement is None:
                records[new_need.need_id] = TheoryNeedRecord(
                    need=new_need,
                    updated_ts=time.time(),
                )
            elif replacement.status == "superseded":
                records[new_need.need_id] = self._reactivated(
                    replacement,
                    new_need,
                )
            old = records.get(old_id)
            if old is not None and old.status != "superseded":
                records[old_id] = replace(
                    old,
                    status="superseded",
                    bundle_id="",
                    diagnostic=f"superseded_by:{new_need.need_id}",
                    superseded_by_need_id=new_need.need_id,
                    superseded_from_status=old.status,
                    superseded_bundle_id=old.bundle_id,
                    superseded_validated_bundle_ids=(old.validated_bundle_ids),
                    superseded_diagnostic=old.diagnostic,
                    active_attempt_id="",
                    active_attempt_owner="",
                    active_attempt_started_ts=0.0,
                    active_attempt_bundle_id="",
                    active_attempt_scope_id="",
                    updated_ts=time.time(),
                )
                affected.append(old_id)
            queue = [(old_id, new_need.need_id)]
            seen_edges: set[tuple[str, str]] = set()
            while queue:
                replaced_id, replacement_id = queue.pop(0)
                if (replaced_id, replacement_id) in seen_edges:
                    continue
                seen_edges.add((replaced_id, replacement_id))
                for record in tuple(records.values()):
                    if record.status == "superseded":
                        continue
                    dependencies = record.need.dependency_need_ids
                    if replaced_id not in dependencies:
                        continue
                    revised_dependencies = tuple(
                        dict.fromkeys(
                            replacement_id if item == replaced_id else item
                            for item in dependencies
                        )
                    )
                    revised_need = record.need.revised_with_dependencies(
                        revised_dependencies
                    )
                    revised = replace(
                        record,
                        need=revised_need,
                        status="pending",
                        attempts=0,
                        attempts_by_scope=(),
                        bundle_id="",
                        validated_bundle_ids=(),
                        diagnostic=f"dependency_superseded:{replaced_id}",
                        superseded_by_need_id="",
                        superseded_from_status="",
                        superseded_bundle_id="",
                        superseded_validated_bundle_ids=(),
                        superseded_diagnostic="",
                        active_attempt_id="",
                        active_attempt_owner="",
                        active_attempt_started_ts=0.0,
                        active_attempt_bundle_id="",
                        active_attempt_scope_id="",
                        updated_ts=time.time(),
                    )
                    existing_revised = records.get(revised_need.need_id)
                    if existing_revised is None:
                        records[revised_need.need_id] = revised
                    elif existing_revised.status == "superseded":
                        records[revised_need.need_id] = self._reactivated(
                            existing_revised,
                            revised_need,
                        )
                    records[record.need.need_id] = replace(
                        record,
                        status="superseded",
                        bundle_id="",
                        diagnostic=f"superseded_by:{revised_need.need_id}",
                        superseded_by_need_id=revised_need.need_id,
                        superseded_from_status=record.status,
                        superseded_bundle_id=record.bundle_id,
                        superseded_validated_bundle_ids=(
                            record.validated_bundle_ids
                        ),
                        superseded_diagnostic=record.diagnostic,
                        active_attempt_id="",
                        active_attempt_owner="",
                        active_attempt_started_ts=0.0,
                        active_attempt_bundle_id="",
                        active_attempt_scope_id="",
                        updated_ts=time.time(),
                    )
                    if record.need.need_id not in affected:
                        affected.append(record.need.need_id)
                    queue.append((record.need.need_id, revised_need.need_id))
            self._commit_records_transaction_locked(tuple(records.values()))
        return tuple(affected)

    @staticmethod
    def _reactivated(
        record: TheoryNeedRecord,
        need: TheoryNeed,
    ) -> TheoryNeedRecord:
        restored_status = record.superseded_from_status or "pending"
        restored_bundle = (
            record.superseded_bundle_id
            if restored_status in {"resolved", "context_available"}
            else ""
        )
        return replace(
            record,
            need=need,
            status=restored_status,
            bundle_id=restored_bundle,
            validated_bundle_ids=(
                record.superseded_validated_bundle_ids
                if restored_bundle
                else ()
            ),
            diagnostic=(
                record.superseded_diagnostic or "reactivated_prior_contract"
            ),
            superseded_by_need_id="",
            superseded_from_status="",
            superseded_bundle_id="",
            superseded_validated_bundle_ids=(),
            superseded_diagnostic="",
            active_attempt_id="",
            active_attempt_owner="",
            active_attempt_started_ts=0.0,
            active_attempt_bundle_id="",
            active_attempt_scope_id="",
            updated_ts=time.time(),
        )

    def record_outcome(
        self,
        need_id: str,
        *,
        status: str,
        diagnostic: str,
        bundle_id: str = "",
        bundle_ids: tuple[str, ...] = (),
        count_attempt: bool = False,
    ) -> TheoryNeedRecord:
        with self._lock():
            existing = self._get_unlocked(need_id)
            if existing is None:
                raise KeyError(f"unknown theory need: {need_id}")
            if existing.status in {"resolved", "superseded"}:
                return existing
            (
                settled_status,
                settled_bundle_id,
                settled_bundle_ids,
                settled_diagnostic,
            ) = self._monotonic_outcome_fields(
                existing,
                status=status,
                diagnostic=diagnostic,
                bundle_id=bundle_id,
                bundle_ids=bundle_ids,
            )
            record = TheoryNeedRecord(
                need=existing.need,
                status=settled_status,
                attempts=existing.attempts + int(bool(count_attempt)),
                attempts_by_scope=(
                    self._increment_scope_attempt(existing, self.attempt_scope_id)
                    if count_attempt
                    else existing.attempts_by_scope
                ),
                bundle_id=settled_bundle_id,
                validated_bundle_ids=settled_bundle_ids,
                diagnostic=settled_diagnostic,
                superseded_by_need_id=existing.superseded_by_need_id,
                superseded_from_status=existing.superseded_from_status,
                superseded_bundle_id=existing.superseded_bundle_id,
                superseded_validated_bundle_ids=(
                    existing.superseded_validated_bundle_ids
                ),
                superseded_diagnostic=existing.superseded_diagnostic,
                active_attempt_id=(
                    ""
                    if str(status or "pending") in {"resolved", "superseded"}
                    else existing.active_attempt_id
                ),
                active_attempt_owner=(
                    ""
                    if str(status or "pending") in {"resolved", "superseded"}
                    else existing.active_attempt_owner
                ),
                active_attempt_started_ts=(
                    0.0
                    if str(status or "pending") in {"resolved", "superseded"}
                    else existing.active_attempt_started_ts
                ),
                active_attempt_bundle_id=(
                    ""
                    if str(status or "pending") in {"resolved", "superseded"}
                    else existing.active_attempt_bundle_id
                ),
                active_attempt_scope_id=(
                    ""
                    if str(status or "pending") in {"resolved", "superseded"}
                    else existing.active_attempt_scope_id
                ),
                updated_ts=time.time(),
            )
            self._write(record)
            return record

    def invalidate_context(
        self,
        need_id: str,
        *,
        diagnostic: str,
        expected_record: Optional[TheoryNeedRecord] = None,
    ) -> tuple[TheoryNeedRecord, bool]:
        """Force a broken verified context back to a rebuildable state."""

        with self._lock():
            existing = self._get_unlocked(need_id)
            if existing is None:
                raise KeyError(f"unknown theory need: {need_id}")
            if expected_record is not None and existing != expected_record:
                return existing, False
            if existing.status == "superseded":
                return existing, False
            reopened = replace(
                existing,
                status="pending",
                attempts=0,
                attempts_by_scope=(),
                bundle_id="",
                validated_bundle_ids=(),
                diagnostic=str(diagnostic or "theory_context_invalidated"),
                active_attempt_id="",
                active_attempt_owner="",
                active_attempt_started_ts=0.0,
                active_attempt_bundle_id="",
                active_attempt_scope_id="",
                updated_ts=time.time(),
            )
            self._write(reopened)
            return reopened, True

    def iter_records(self) -> Iterator[TheoryNeedRecord]:
        with self._lock():
            records = tuple(self._iter_records_unlocked())
        return iter(records)

    def _iter_records_unlocked(self) -> Iterator[TheoryNeedRecord]:
        for path in sorted(self.records_root.glob("need_*.json")):
            try:
                yield TheoryNeedRecord.from_dict(
                    json.loads(path.read_text(encoding="utf-8"))
                )
            except Exception:
                continue

    def integrity_issues(self) -> tuple[dict[str, str], ...]:
        with self._lock():
            issues: list[dict[str, str]] = []
            for path in sorted(self.records_root.glob("*.json")):
                try:
                    TheoryNeedRecord.from_dict(
                        json.loads(path.read_text(encoding="utf-8"))
                    )
                except Exception as exc:
                    issues.append(
                        {
                            "path": str(path),
                            "error": f"{type(exc).__name__}: {exc}",
                        }
                    )
            return tuple(issues)

    def _path(self, need_id: str) -> Path:
        clean = str(need_id or "").strip()
        if not clean.startswith("need_") or not clean.replace("_", "").isalnum():
            raise ValueError(f"invalid theory need id: {need_id!r}")
        return self.records_root / f"{clean}.json"

    def _write(self, record: TheoryNeedRecord) -> None:
        target = self._path(record.need.need_id)
        descriptor, raw_path = tempfile.mkstemp(
            prefix=f".{record.need.need_id}.",
            suffix=".tmp",
            dir=str(self.records_root),
        )
        path = Path(raw_path)
        primary: Optional[BaseException] = None
        try:
            self._write_json_temp_descriptor(descriptor, record.to_dict())
            try:
                os.replace(path, target)
                self._fsync_directory(self.records_root)
            except Exception:
                # POSIX replacement/fsync may report failure after the rename
                # became visible. If the exact immutable record is readable,
                # the logical write committed and callers must retain its
                # lease/CAS ownership rather than orphaning live work.
                committed = None
                try:
                    committed = TheoryNeedRecord.from_dict(
                        json.loads(target.read_text(encoding="utf-8"))
                    )
                except Exception:
                    pass
                if committed != record:
                    raise
        except BaseException as exc:
            primary = exc
            raise
        finally:
            try:
                path.unlink()
            except OSError:
                pass
            except BaseException as cleanup_error:
                if primary is not None:
                    primary.add_note(
                        "Mini theory record temp-path cleanup also failed: "
                        f"{type(cleanup_error).__name__}: {cleanup_error}"
                    )
                else:
                    raise

    def _commit_records_transaction_locked(
        self,
        records: tuple[TheoryNeedRecord, ...],
    ) -> None:
        """Journal a complete final record set before applying any member."""

        payload = {
            "kind": "mini_theory_need_records_transaction",
            "version": 1,
            "records": [
                record.to_dict()
                for record in sorted(records, key=lambda item: item.need.need_id)
            ],
        }
        descriptor, raw_path = tempfile.mkstemp(
            prefix=".needs.transaction.",
            suffix=".tmp",
            dir=str(self.root),
        )
        path = Path(raw_path)
        primary: Optional[BaseException] = None
        try:
            self._write_json_temp_descriptor(descriptor, payload)
            os.replace(path, self.transaction_path)
            self._fsync_root()
        except BaseException as exc:
            primary = exc
            raise
        finally:
            try:
                path.unlink()
            except OSError:
                pass
            except BaseException as cleanup_error:
                if primary is not None:
                    primary.add_note(
                        "Mini theory transaction temp-path cleanup also failed: "
                        f"{type(cleanup_error).__name__}: {cleanup_error}"
                    )
                else:
                    raise
        self._recover_transaction_locked()

    def _recover_transaction_locked(self) -> None:
        if not self.transaction_path.is_file():
            return
        try:
            payload = json.loads(self.transaction_path.read_text(encoding="utf-8"))
            if (
                payload.get("kind") != "mini_theory_need_records_transaction"
                or int(payload.get("version") or 0) != 1
                or not isinstance(payload.get("records"), list)
            ):
                raise ValueError("invalid Mini theory need transaction journal")
            records = tuple(
                TheoryNeedRecord.from_dict(item)
                for item in payload["records"]
                if isinstance(item, dict)
            )
            if len(records) != len(payload["records"]):
                raise ValueError("invalid record in Mini theory need transaction journal")
        except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
            raise RuntimeError(
                f"cannot recover Mini theory need transaction: {exc}"
            ) from exc
        for record in records:
            self._write(record)
        self.transaction_path.unlink()
        self._fsync_root()

    def _fsync_root(self) -> None:
        self._fsync_directory(self.root)

    @staticmethod
    def _write_json_temp_descriptor(descriptor: int, payload: Any) -> None:
        """Write+fsync an owned temp descriptor without masking a primary stop."""

        try:
            handle = os.fdopen(descriptor, "w", encoding="utf-8")
        except BaseException as primary:
            try:
                os.close(descriptor)
            except BaseException as cleanup_error:
                primary.add_note(
                    "Mini theory temp descriptor acquisition cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise
        try:
            json.dump(
                payload,
                handle,
                ensure_ascii=False,
                sort_keys=True,
                indent=2,
            )
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        except BaseException as primary:
            try:
                handle.close()
            except BaseException as cleanup_error:
                primary.add_note(
                    "Mini theory temp-file descriptor cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise
        else:
            handle.close()

    @staticmethod
    def _fsync_directory(path: Path) -> None:
        directory_fd = os.open(path, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        except BaseException as primary:
            try:
                os.close(directory_fd)
            except BaseException as cleanup_error:
                primary.add_note(
                    "Mini theory directory descriptor cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise
        else:
            os.close(directory_fd)

    def _lock(self):
        store = self

        class _Lock:
            def __enter__(self):
                self.handle = store.lock_path.open("a+b")
                try:
                    fcntl.flock(self.handle.fileno(), fcntl.LOCK_EX)
                    store._recover_transaction_locked()
                except BaseException as primary:
                    for cleanup in (
                        lambda: fcntl.flock(
                            self.handle.fileno(),
                            fcntl.LOCK_UN,
                        ),
                        self.handle.close,
                    ):
                        try:
                            cleanup()
                        except BaseException as cleanup_error:
                            primary.add_note(
                                "Mini theory need-lock cleanup also failed: "
                                f"{type(cleanup_error).__name__}: {cleanup_error}"
                            )
                    raise
                return self

            def __exit__(self, exc_type, exc, traceback):
                cleanup_errors: list[BaseException] = []
                for cleanup in (
                    lambda: fcntl.flock(
                        self.handle.fileno(),
                        fcntl.LOCK_UN,
                    ),
                    self.handle.close,
                ):
                    try:
                        cleanup()
                    except BaseException as cleanup_error:
                        cleanup_errors.append(cleanup_error)
                if exc is not None:
                    for cleanup_error in cleanup_errors:
                        exc.add_note(
                            "Mini theory need-lock cleanup also failed: "
                            f"{type(cleanup_error).__name__}: {cleanup_error}"
                        )
                    return False
                if cleanup_errors:
                    primary_cleanup = next(
                        (
                            cleanup_error
                            for cleanup_error in cleanup_errors
                            if not isinstance(cleanup_error, Exception)
                        ),
                        cleanup_errors[0],
                    )
                    for cleanup_error in cleanup_errors:
                        if cleanup_error is primary_cleanup:
                            continue
                        primary_cleanup.add_note(
                            "Mini theory need-lock cleanup also failed: "
                            f"{type(cleanup_error).__name__}: {cleanup_error}"
                        )
                    raise primary_cleanup
                return False

        return _Lock()
