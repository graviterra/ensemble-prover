"""Shared trust boundary for mini-prover solved-export telemetry."""

from __future__ import annotations

from typing import Any, Mapping

EXPORT_STATUS_KEYS = ("solved_export_status", "mini_solved_export_status")
EXPORT_FAILURE_COUNTER_KEYS = (
    "mini_solved_export_downgrades_solved",
    "mini_solved_export_kernel_rejected",
    "solved_export_kernel_rejected",
    "mini_solved_export_exceptions",
    "mini_solved_export_skipped",
    "kernel_rejected",
)
EXPORT_BOUNDARY_KEYS = (
    *EXPORT_STATUS_KEYS,
    "solved_export_verified",
    "mini_solved_export_verified",
    "mini_solved_export_attempts",
    "mini_solved_export_successes",
    *EXPORT_FAILURE_COUNTER_KEYS,
)


def export_status_values(summary: Mapping[str, Any]) -> tuple[str, ...]:
    return tuple(
        status
        for key in EXPORT_STATUS_KEYS
        for status in [str(summary.get(key) or "").strip()]
        if status
    )


def export_status_map(summary: Mapping[str, Any]) -> dict[str, str]:
    return {
        key: status
        for key in EXPORT_STATUS_KEYS
        for status in [str(summary.get(key) or "").strip()]
        if status
    }


def export_boundary_present(summary: Mapping[str, Any]) -> bool:
    return bool(any(key in summary for key in EXPORT_BOUNDARY_KEYS))


def counter_positive(summary: Mapping[str, Any], *keys: str) -> bool:
    for key in keys:
        value = summary.get(key)
        if value is True:
            return True
        if isinstance(value, (int, float)) and not isinstance(value, bool) and value > 0:
            return True
    return False


def counter_zero_or_absent(summary: Mapping[str, Any], *keys: str) -> bool:
    for key in keys:
        if key not in summary:
            continue
        value = summary.get(key)
        if value in (None, False):
            continue
        if isinstance(value, (int, float)) and not isinstance(value, bool) and value == 0:
            continue
        return False
    return True


def bool_true(summary: Mapping[str, Any], key: str) -> bool:
    return summary.get(key) is True


def export_status_complete_verified(summary: Mapping[str, Any]) -> bool:
    status_by_key = export_status_map(summary)
    return (
        set(status_by_key) == set(EXPORT_STATUS_KEYS)
        and all(status == "verified" for status in status_by_key.values())
    )


def legacy_mini_export_verified_payload(summary: Mapping[str, Any]) -> bool:
    status_by_key = export_status_map(summary)
    if set(status_by_key) != {"mini_solved_export_status"}:
        return False
    if status_by_key.get("mini_solved_export_status") != "verified":
        return False
    if "solved_export_verified" in summary or "mini_solved_export_verified" in summary:
        return False
    if not counter_positive(summary, "mini_solved_export_attempts"):
        return False
    if not counter_positive(summary, "mini_solved_export_successes"):
        return False
    return counter_zero_or_absent(summary, *EXPORT_FAILURE_COUNTER_KEYS)


def solved_export_verified_payload(summary: Mapping[str, Any]) -> bool:
    if not export_boundary_present(summary):
        return False
    if legacy_mini_export_verified_payload(summary):
        return True
    if not export_status_complete_verified(summary):
        return False
    if summary.get("solved_export_verified") is not True:
        return False
    if not counter_positive(summary, "mini_solved_export_verified"):
        return False
    if not counter_positive(summary, "mini_solved_export_attempts"):
        return False
    if not counter_positive(summary, "mini_solved_export_successes"):
        return False
    return counter_zero_or_absent(summary, *EXPORT_FAILURE_COUNTER_KEYS)


def effective_solved(summary: Mapping[str, Any]) -> bool:
    if summary.get("solved") is not True:
        return False
    # No export boundary means this is a PRE-export summary: trust ``solved``
    # so the exporter picks the run up and runs its independent Lean self-check.
    # That check then records an export status (the boundary), after which a
    # solved claim is only trusted when the self-check verified it. So the
    # system already fails closed — a final summary always carries a boundary.
    if not export_boundary_present(summary):
        return True
    return solved_export_verified_payload(summary)


def failure_counter_present(summary: Mapping[str, Any]) -> bool:
    return not counter_zero_or_absent(summary, *EXPORT_FAILURE_COUNTER_KEYS)


def solved_export_failure_reason(summary: Mapping[str, Any]) -> str:
    status_by_key = export_status_map(summary)
    statuses = tuple(status_by_key.values())
    if statuses and any(status != statuses[0] for status in statuses):
        return "malformed"
    state = statuses[0] if statuses else ""
    if solved_export_verified_payload(summary):
        return "verified"
    if state == "verified" and set(status_by_key) != set(EXPORT_STATUS_KEYS):
        return "malformed"
    if state and state != "verified":
        return state
    if failure_counter_present(summary):
        return "malformed"
    if state == "verified" and not solved_export_verified_payload(summary):
        return "malformed"
    return state or "unverified"
