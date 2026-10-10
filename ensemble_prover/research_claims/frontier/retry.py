"""Durable retry budgets and capability-lane guards.

Delay is not a retry. Scheduling waits spend neither attempt allowance.
A model claim that the environment changed does not open a new epoch.
"""

from __future__ import annotations

from typing import Any

from .records import FrontierRefusal, new_id


FAILURE_SCOPES = frozenset({
    "scheduling_deferral",
    "operation_input",
    "lane_failure",
    "revocation",
    "mathematical",
})


def classify_failure(kind: str, *, lane_attributed: bool = False) -> str:
    if kind in {"shared_phase", "fairness", "provider_capacity", "pending_grant", "research_phase_deferred"}:
        return "scheduling_deferral"
    if kind in {"invalid_input", "input_timeout", "memory_limit", "output_limit", "context_overflow"}:
        return "operation_input"
    if kind == "provider_timeout":
        return "lane_failure" if lane_attributed else "operation_input"
    if kind in {"provider_failure", "transport", "authentication", "capability_unavailable"}:
        return "lane_failure"
    if kind in {"revoked", "cancelled", "stale_authorization"}:
        return "revocation"
    if kind in {"rejected_tactic", "counterexample", "inconclusive_computation"}:
        return "mathematical"
    raise FrontierRefusal("unknown_failure_scope")


def _budget(state: dict[str, Any], lineage_id: str) -> dict[str, Any]:
    return state["retries"].setdefault(lineage_id, {
        "lineage_id": lineage_id,
        "execution_admissions": 0,
        "preflight_failures": 0,
        "paused": False,
        "epoch": 1,
        "deadline": None,
        "history": [],
    })


def _lane(state: dict[str, Any], lane_id: str) -> dict[str, Any]:
    return state["lanes"].setdefault(lane_id, {
        "lane_id": lane_id,
        "consecutive": 0,
        "paused": False,
        "costs": 0,
        "recovery_checks": 0,
        "recovery_open": False,
    })


def authorize_execution(state: dict[str, Any], lineage_id: str, *, lane_id: str, now: float, deadline: float | None) -> dict[str, Any]:
    """Count one execution admission, including the first attempt and transport retries."""
    budget = _budget(state, lineage_id)
    lane = _lane(state, lane_id)
    if budget["paused"]:
        raise FrontierRefusal("paused_operational")
    probe = False
    if lane["paused"]:
        if not lane["recovery_open"]:
            raise FrontierRefusal("lane_paused")
        probe = True
    if budget["deadline"] is None:
        budget["deadline"] = deadline
    elif deadline is not None and budget["deadline"] is not None and now > budget["deadline"]:
        budget["paused"] = True
        raise FrontierRefusal("retry_deadline")
    limit = state["policy"]["max_operation_execution_admissions"]
    if budget["execution_admissions"] >= limit:
        budget["paused"] = True
        raise FrontierRefusal("retry_exhausted")
    budget["execution_admissions"] += 1
    if probe:
        lane["recovery_open"] = False
    state["operations"][new_id("operation")] = {
        "lineage_id": lineage_id,
        "lane_id": lane_id,
        "admitted_at": now,
        "epoch": budget["epoch"],
    }
    return budget


def note_preflight_failure(state: dict[str, Any], lineage_id: str) -> str:
    budget = _budget(state, lineage_id)
    budget["preflight_failures"] += 1
    budget["history"].append("preflight_failure")
    if budget["preflight_failures"] >= state["policy"]["max_operation_admission_recoveries"]:
        budget["paused"] = True
        return "paused_operational"
    return "retry"


def note_failure(
    state: dict[str, Any],
    lineage_id: str,
    scope: str,
    *,
    lane_id: str,
) -> str:
    if scope not in FAILURE_SCOPES:
        raise FrontierRefusal("unknown_failure_scope")
    budget = _budget(state, lineage_id)
    if scope == "scheduling_deferral":
        state["history"]["deferred_dispatches"] += 1
        return "defer"
    if scope == "revocation":
        budget["history"].append("revocation")
        return "stop"
    if scope == "mathematical":
        budget["history"].append("mathematical")
        return "mathematical"
    if scope == "operation_input":
        budget["history"].append("operation_input")
        if budget["execution_admissions"] >= state["policy"]["max_operation_execution_admissions"]:
            budget["paused"] = True
            return "paused_operational"
        return "retry"
    lane = _lane(state, lane_id)
    lane["consecutive"] += 1
    lane["costs"] += 1
    budget["history"].append("lane_failure")
    if lane["consecutive"] >= state["policy"]["max_consecutive_lane_failures"]:
        lane["paused"] = True
        lane["recovery_open"] = False
    if budget["execution_admissions"] >= state["policy"]["max_operation_execution_admissions"]:
        budget["paused"] = True
        return "paused_operational"
    if lane["paused"]:
        return "paused_operational"
    return "retry"


def note_success(state: dict[str, Any], lane_id: str) -> None:
    lane = state["lanes"].get(lane_id)
    if lane is not None:
        lane["consecutive"] = 0


def authorize_lane_recovery(state: dict[str, Any], lane_id: str) -> None:
    lane = _lane(state, lane_id)
    if not lane["paused"]:
        return
    if lane["recovery_checks"] >= 1:
        raise FrontierRefusal("lane_recovery_exhausted")
    lane["recovery_checks"] += 1
    lane["recovery_open"] = True


def finish_lane_recovery(state: dict[str, Any], lane_id: str, *, success: bool) -> None:
    lane = _lane(state, lane_id)
    lane["recovery_open"] = False
    if success:
        lane["paused"] = False
        lane["consecutive"] = 0
        lane["recovery_checks"] = 0
        return
    lane["paused"] = True


def new_recovery_epoch(
    state: dict[str, Any],
    lineage_id: str,
    *,
    operator_authorized: bool,
    capability_change: str | bool | None = None,
) -> dict[str, Any]:
    if capability_change is True or (capability_change is not None and not isinstance(capability_change, str) and capability_change is not False):
        raise FrontierRefusal("capability_change_requires_owner_record")
    if capability_change is False:
        capability_change = None
    if isinstance(capability_change, str):
        if capability_change not in state.get("validated_capabilities", []):
            raise FrontierRefusal("capability_change_not_owner_validated")
    if not operator_authorized and not capability_change:
        raise FrontierRefusal("recovery_requires_owner_authorization")
    budget = _budget(state, lineage_id)
    budget["history"].append({"epoch": budget["epoch"], "admissions": budget["execution_admissions"]})
    budget["epoch"] += 1
    budget["execution_admissions"] = 0
    budget["preflight_failures"] = 0
    budget["paused"] = False
    budget["deadline"] = None
    return budget
