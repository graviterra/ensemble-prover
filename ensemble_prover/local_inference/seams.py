"""Integration points for the existing guards. Nothing here is called by them yet.

Dollar admission stays in ``CostBudgetController``. After that admission, the
dispatch boundary should acquire one capacity permit per concrete HTTP call,
then ``reserve_budget_for_admitted_permit`` before the request is sent. A
queued permit is not a dispatch and must not reserve the run budget. If the
send is proved not to have happened, ``release_if_not_dispatched`` returns both
the slot and the envelope. After ``mark_dispatched``, neither side refunds the
envelope; cancellation keeps the capacity slot until a receipt, a verified
server-instance reset, or operator reconciliation.

``MiniSession._cost_budget_continuation_enabled`` and
``_grant_cost_governed_continuation_budget`` must treat a false result from
``local_allocation_allows_continuation`` as decisive while a local ledger is
present. ``None`` means the run has no local allocation, so the existing dollar
gate is unchanged. A positive remaining USD balance is not an argument to
either function.

``provider_serving_fingerprint`` remains the cloud lane id. Local deployment
and capacity-group fingerprints are separate and case-preserving. Checkpoint
code should store ``checkpoint_binding`` and omit URLs, auth names, and config
paths from ``public_cli_config``. Resume calls ``apply_checkpoint_decision``
and ``resume_local_budget``; neither resets consumption.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from .budget import LocalComputeLedger
from .capacity import CapacityCoordinator, EndpointDeclaration, GroupDeclaration
from .config import FrozenLocalRequest, ProfileDocument, ResolvedLocalRun
from .errors import LocalInferenceError


def local_allocation_allows_continuation(ledger: LocalComputeLedger | None) -> bool:
    """Local half of ``_cost_budget_continuation_enabled``.

    ``None`` preserves cloud-only behavior. A ledger with no remaining
    dispatch, output envelope, or observed-wall allowance returns false.
    """

    if ledger is None:
        return True
    return ledger.has_unreserved_remainder()


def local_allocation_allows_action_topup(ledger: LocalComputeLedger | None) -> bool:
    """Local half of ``_grant_cost_governed_continuation_budget``."""

    return local_allocation_allows_continuation(ledger)


def register_profile(coordinator: CapacityCoordinator, document: ProfileDocument) -> None:
    if document.coordinator is None:
        raise LocalInferenceError("coordinator_required")
    groups = [
        GroupDeclaration(
            name=name,
            max_inflight=group.max_inflight,
            max_queued=group.max_queued,
            queue_timeout_s=group.queue_timeout_s,
            request_timeout_s=group.request_timeout_s,
        )
        for name, group in document.capacity_groups.items()
    ]
    endpoints = [
        EndpointDeclaration(name=name, group=endpoint.capacity_group, max_inflight=endpoint.max_inflight)
        for name, endpoint in document.endpoints.items()
    ]
    coordinator.register_declarations(
        installation_id=document.coordinator.installation_id,
        scope_id=document.coordinator.scope_id,
        groups=groups,
        endpoints=endpoints,
    )


def reserve_budget_for_admitted_permit(
    budget: LocalComputeLedger,
    permit: dict[str, Any],
    request: FrozenLocalRequest,
    *,
    owner: str,
    requested_wall_ms: int,
    expected_capacity_group: str,
    units: int = 1,
) -> dict[str, Any]:
    """Charge an admission bound to the same resolved endpoint and group.

    The caller obtains ``expected_capacity_group`` from the immutable profile
    that produced ``request``. The transport separately verifies the complete
    request fingerprint when beginning dispatch.
    """

    if permit.get("state") != "admitted":
        raise LocalInferenceError("budget_requires_admitted_permit")
    if units != 1 or request.native_n != "unsupported":
        raise LocalInferenceError("native_batch_unsupported")
    if owner != permit.get("owner_run"):
        raise LocalInferenceError("owner_mismatch")
    if (
        type(expected_capacity_group) is not str or not expected_capacity_group
        or permit.get("endpoint_id") != request.endpoint_id
        or permit.get("group") != expected_capacity_group
    ):
        raise LocalInferenceError("request_binding_mismatch")
    return budget.reserve(
        dispatch_id=permit["dispatch_id"],
        requested_output_tokens=request.requested_output_tokens,
        requested_wall_ms=requested_wall_ms,
        expected_profile_hash=request.profile_hash,
        units=1,
        owner=owner,
    )


def release_if_not_dispatched(
    *,
    capacity: CapacityCoordinator,
    budget: LocalComputeLedger,
    dispatch_id: str,
    now_s: int,
) -> dict[str, Any]:
    permit = capacity.get_permit(dispatch_id)
    reservation = budget.reservation(dispatch_id)
    started = (
        reservation["state"] in {"dispatched", "unknown"}
        or permit["dispatch_started"]
        or permit["state"] in {"dispatched", "cancel_requested", "completion_unknown", "completed"}
    )
    if started:
        if permit["state"] == "dispatched":
            capacity.cancel(dispatch_id, owner_run=permit["owner_run"], now_s=now_s)
        return {"result": "retained", "reset_budget": False}
    if reservation["state"] == "reserved" and permit["state"] in {"queued", "admitted"}:
        cancelled = capacity.cancel(dispatch_id, owner_run=permit["owner_run"], now_s=now_s)
        if cancelled["dispatch_started"] or cancelled["state"] not in {"cancelled", "expired_before_dispatch"}:
            raise LocalInferenceError("admission_state_conflict")
        budget.release_not_dispatched(dispatch_id, owner=reservation["owner"])
        return {"result": "released", "reset_budget": False}
    if reservation["state"] == "released" and permit["state"] in {"cancelled", "expired_before_dispatch"}:
        return {"result": "released", "reset_budget": False}
    if reservation["state"] == "reserved" and permit["state"] in {"cancelled", "expired_before_dispatch"}:
        budget.release_not_dispatched(dispatch_id, owner=reservation["owner"])
        return {"result": "released", "reset_budget": False}
    raise LocalInferenceError("admission_state_conflict")


def resume_local_budget(
    directory: str | Path,
    *,
    ledger_id: str,
    profile_hash: str,
) -> LocalComputeLedger:
    ledger = LocalComputeLedger.open(directory)
    ledger.require_resume_identity(ledger_id=ledger_id, profile_hash=profile_hash)
    return ledger


def apply_checkpoint_decision(
    ledger: LocalComputeLedger,
    decision: dict[str, Any],
    *,
    new_profile_hash: str,
) -> None:
    """Honor resume or explicit reconfiguration. A true reset flag is refused."""

    if decision.get("reset_budget") is not False:
        raise LocalInferenceError("budget_reset_forbidden")
    action = decision.get("action")
    if action == "legacy":
        raise LocalInferenceError("resolved_profile_required")
    if action == "resume":
        if ledger.active_profile_hash != new_profile_hash:
            raise LocalInferenceError("profile_hash_mismatch")
        return
    if action == "reconfigure":
        ledger.reconfigure_profile(new_profile_hash)
        return
    raise LocalInferenceError("invalid_checkpoint_binding")


def resolved_profile_hash(resolved: ResolvedLocalRun) -> str:
    return resolved.profile_hash
