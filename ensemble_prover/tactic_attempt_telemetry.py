"""Shared, domain-agnostic telemetry for Lean tactic candidate execution.

Tactic result records intentionally keep only a short attempt preview.  Every
producer must therefore compute these counts from the complete in-memory
attempt list before truncation.  Consumers prefer the explicit counts and use
the preview only for backward compatibility with historical records.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import Any, Callable, Dict


_TIMEOUT_ERROR_TYPES = {
    "deadline_exceeded",
    "lean_timeout",
    "llm_turn_elapsed_budget_exhausted",
    "tactic_timeout",
    "timeout",
}
_FORCED_TERMINATION_ERROR_TYPES = {
    "forced_termination",
    "hard_cancelled",
    "process_terminated",
}
_CANCELLATION_ERROR_TYPES = {"cancelled", "cancellederror", "task_cancelled"}
_INFRASTRUCTURE_ERROR_TYPES = {
    "exception",
    "infra_failure",
    "infrastructure_error",
    "lean_infra_error",
    "process_error",
    "runner_exception",
    "spawn_error",
    "transport_error",
}


TACTIC_PHASE_LANES: Dict[str, str] = {
    "proof_state_child_tactic": "proof_state_child_tactic",
    "proof_state_root_assembly": "proof_state_root_tactic",
    "mini_recursive_root_tactic": "mini_recursive_root_tactic",
    "graph_route_assembly_root_tactic": "graph_route_root_tactic",
    "helper_salvage_root_tactic": "salvage_root_tactic",
    "helper_only_salvage_root_tactic": "salvage_root_tactic",
    "root_tactic_prepass": "direct_root_tactic",
}

LEAN_ATTEMPT_LANE_METRICS: Dict[str, str] = {
    "proof_state_child_tactic": "mini_proof_state_child_tactic_attempts",
    "proof_state_root_tactic": "mini_proof_state_root_tactic_attempts",
    "proof_state_decl_application": "mini_proof_state_decl_application_attempts",
    "proof_state_assembly": "mini_proof_state_assembly_attempts",
    "mini_recursive_root_tactic": "mini_recursive_root_tactic_attempts",
    "graph_route_root_tactic": "mini_graph_route_root_tactic_attempts",
    "salvage_root_tactic": "mini_salvage_root_tactic_attempts",
    "direct_root_tactic": "mini_direct_root_tactic_attempts",
    "other_root_tactic": "mini_other_root_tactic_attempts",
    "mini_recursive_claim_tactic": "mini_recursive_claim_tactic_attempts",
    "cast_normalization_tactic": "mini_cast_normalization_tactic_attempts",
    "finset_reindexing_tactic": "mini_finset_reindexing_tactic_attempts",
}

_PROOF_STATE_LANES = {
    "proof_state_child_tactic",
    "proof_state_root_tactic",
    "proof_state_decl_application",
    "proof_state_assembly",
}

MONOTONIC_LEAN_ATTEMPT_METRICS = frozenset(
    {
        "mini_total_lean_attempts",
        "mini_proof_state_total_lean_attempts",
        *LEAN_ATTEMPT_LANE_METRICS.values(),
        *(
            f"{metric.removesuffix('_attempts')}_{suffix}"
            for metric in LEAN_ATTEMPT_LANE_METRICS.values()
            for suffix in (
                "contexts",
                "candidates_generated",
                "certificates_accepted",
            )
        ),
        *(
            f"{metric.removesuffix('_attempts')}_{suffix}"
            for metric in LEAN_ATTEMPT_LANE_METRICS.values()
            for suffix in (
                "completed",
                "cancellations",
                "timeouts",
                "forced_terminations",
                "infrastructure_failures",
                "successes",
            )
        ),
    }
)

LeanAttemptObserver = Callable[[str, Mapping[str, Any]], None]


def _text(value: Any) -> str:
    return str(value or "").strip().lower()


def _attempt_kind(attempt: Mapping[str, Any]) -> str:
    error_type = _text(attempt.get("error_type"))
    diagnostic = _text(attempt.get("diagnostic"))
    exception = _text(attempt.get("exception"))
    exit_reason = _text(attempt.get("exit_reason"))
    combined = " ".join((error_type, diagnostic, exception, exit_reason))
    if (
        error_type in _CANCELLATION_ERROR_TYPES
        or bool(attempt.get("cancelled"))
    ):
        return "cancellation"
    if (
        error_type in _FORCED_TERMINATION_ERROR_TYPES
        or bool(attempt.get("forced_termination"))
        or bool(attempt.get("hard_cancelled"))
    ):
        return "forced_termination"
    if (
        error_type in _TIMEOUT_ERROR_TYPES
        or "timeouterror" in combined
        or "timed out" in combined
        or " timeout" in f" {combined}"
    ):
        return "timeout"
    if error_type in _INFRASTRUCTURE_ERROR_TYPES or exception:
        return "infrastructure_failure"
    return "completed"


def tactic_attempt_telemetry_fields(
    attempts: Sequence[Mapping[str, Any]] | None,
) -> Dict[str, int]:
    """Return truthful counts from the complete tactic-attempt sequence."""

    clean = [item for item in list(attempts or ()) if isinstance(item, Mapping)]
    counts = {
        "tactic_attempt_count": len(clean),
        "tactic_completed_count": 0,
        "tactic_cancelled_count": 0,
        "tactic_timeout_count": 0,
        "tactic_forced_termination_count": 0,
        "tactic_infrastructure_failure_count": 0,
        "tactic_success_count": 0,
    }
    for attempt in clean:
        if bool(attempt.get("ok") or attempt.get("active_target_ok")):
            counts["tactic_success_count"] += 1
        kind = _attempt_kind(attempt)
        if kind == "cancellation":
            counts["tactic_cancelled_count"] += 1
        elif kind == "timeout":
            counts["tactic_timeout_count"] += 1
        elif kind == "forced_termination":
            counts["tactic_forced_termination_count"] += 1
        elif kind == "infrastructure_failure":
            counts["tactic_infrastructure_failure_count"] += 1
        else:
            counts["tactic_completed_count"] += 1
    return counts


def tactic_record_telemetry(record: Mapping[str, Any]) -> Dict[str, int]:
    """Read counts without presenting a truncated legacy preview as exact."""

    preview = [
        item
        for item in list(record.get("tactic_attempts") or ())
        if isinstance(item, Mapping)
    ]
    fallback = tactic_attempt_telemetry_fields(preview)
    out: Dict[str, int] = {}
    explicit_parse_valid: Dict[str, bool] = {}
    for key, value in fallback.items():
        if key not in record:
            out[key] = int(value)
            explicit_parse_valid[key] = False
            continue
        try:
            parsed = int(record.get(key))
            if parsed < 0:
                raise ValueError("negative tactic count")
            out[key] = parsed
            explicit_parse_valid[key] = True
        except (TypeError, ValueError):
            out[key] = int(value)
            explicit_parse_valid[key] = False
    preview_count = len(preview)
    explicit_count = "tactic_attempt_count" in record
    explicit_counts_complete = all(key in record for key in fallback)
    candidate_count_present = bool(
        "candidate_count" in record or "tactic_candidate_count" in record
    )
    candidate_count_valid = not candidate_count_present
    try:
        candidate_count = max(
            0,
            int(
                record.get("candidate_count")
                or record.get("tactic_candidate_count")
                or 0
            ),
        )
        raw_candidate_count = (
            record.get("candidate_count")
            if "candidate_count" in record
            else record.get("tactic_candidate_count")
        )
        candidate_count_valid = bool(
            not candidate_count_present or int(raw_candidate_count) >= 0
        )
    except (TypeError, ValueError):
        candidate_count = 0
        candidate_count_valid = False
    preview_declared_truncated = bool(
        record.get("tactic_attempts_truncated")
        or record.get("tactic_attempt_preview_truncated")
    )
    preview_inferred_truncated = candidate_count > len(preview)
    preview_exact = bool(
        "tactic_attempts" in record
        and not (preview_declared_truncated or preview_inferred_truncated)
    )
    explicit_attempt_count_valid = bool(
        explicit_count
        and explicit_parse_valid["tactic_attempt_count"]
        and out["tactic_attempt_count"] >= preview_count
        and candidate_count_valid
        and (
            not candidate_count_present
            or out["tactic_attempt_count"] <= candidate_count
        )
    )
    terminal_total = sum(
        out[key]
        for key in (
            "tactic_completed_count",
            "tactic_cancelled_count",
            "tactic_timeout_count",
            "tactic_forced_termination_count",
            "tactic_infrastructure_failure_count",
        )
    )
    explicit_partition_valid = bool(
        explicit_counts_complete
        and all(explicit_parse_valid.values())
        and explicit_attempt_count_valid
        and terminal_total == out["tactic_attempt_count"]
        and out["tactic_success_count"] <= out["tactic_attempt_count"]
    )
    has_any_explicit_count = any(key in record for key in fallback)
    out["tactic_counts_exact"] = int(
        explicit_partition_valid
        if has_any_explicit_count
        else preview_exact
    )
    out["tactic_attempt_count_exact"] = int(
        explicit_attempt_count_valid if explicit_count else preview_exact
    )
    out["tactic_count_lower_bound"] = max(
        preview_count,
        int(out["tactic_attempt_count"]),
    )
    out["tactic_attempt_count"] = out["tactic_count_lower_bound"]
    return out


def summarize_tactic_records(
    records: Sequence[Mapping[str, Any]] | None,
) -> Dict[str, Dict[str, int]]:
    """Aggregate current or historical tactic records without false precision."""

    summary: Dict[str, Dict[str, int]] = {}
    for record in list(records or ()):
        if not isinstance(record, Mapping):
            continue
        phase = str(record.get("phase") or "unknown").strip() or "unknown"
        bucket = summary.setdefault(
            phase,
            {
                "contexts": 0,
                "candidates_generated": 0,
                "attempts_observed_lower_bound": 0,
                "exact_records": 0,
                "inexact_records": 0,
            },
        )
        telemetry = tactic_record_telemetry(record)
        try:
            candidates = max(
                0,
                int(
                    record.get("candidate_count")
                    or record.get("tactic_candidate_count")
                    or 0
                ),
            )
        except (TypeError, ValueError):
            candidates = 0
        bucket["contexts"] += 1
        bucket["candidates_generated"] += candidates
        bucket["attempts_observed_lower_bound"] += int(
            telemetry["tactic_count_lower_bound"]
        )
        if telemetry["tactic_attempt_count_exact"]:
            bucket["exact_records"] += 1
        else:
            bucket["inexact_records"] += 1
    return summary


def tactic_lane_for_phase(phase: Any) -> str:
    text = str(phase or "").strip()
    if text in TACTIC_PHASE_LANES:
        return TACTIC_PHASE_LANES[text]
    if text.endswith("root_tactic"):
        return "other_root_tactic"
    return ""


def _increment_metric(dossier: Any, key: str, amount: int = 1) -> None:
    increment = getattr(dossier, "increment_tool_metric", None)
    if callable(increment):
        increment(key, int(amount))


def record_dossier_lean_attempt_event(
    dossier: Any,
    *,
    lane: str,
    event: str,
    attempt: Mapping[str, Any] | None = None,
) -> None:
    """Record a monotonic attempt event in the dossier's durable audit metrics."""

    metric = LEAN_ATTEMPT_LANE_METRICS.get(str(lane or "").strip())
    if dossier is None or not metric:
        return
    clean_event = str(event or "").strip()
    if clean_event == "portfolio":
        _increment_metric(
            dossier,
            f"{metric.removesuffix('_attempts')}_contexts",
        )
        try:
            candidate_count = max(0, int(dict(attempt or {}).get("candidate_count", 0) or 0))
        except (TypeError, ValueError):
            candidate_count = 0
        if candidate_count:
            _increment_metric(
                dossier,
                f"{metric.removesuffix('_attempts')}_candidates_generated",
                candidate_count,
            )
        return
    if clean_event == "certificate_accepted":
        _increment_metric(
            dossier,
            f"{metric.removesuffix('_attempts')}_certificates_accepted",
        )
        return
    if clean_event == "started":
        _increment_metric(dossier, metric)
        _increment_metric(dossier, "mini_total_lean_attempts")
        if lane in _PROOF_STATE_LANES:
            _increment_metric(dossier, "mini_proof_state_total_lean_attempts")
        return
    if clean_event != "finished":
        return
    payload = dict(attempt or {})
    if bool(payload.get("ok")):
        _increment_metric(dossier, f"{metric.removesuffix('_attempts')}_successes")
    kind = _attempt_kind(payload)
    suffix = {
        "completed": "completed",
        "cancellation": "cancellations",
        "timeout": "timeouts",
        "forced_termination": "forced_terminations",
        "infrastructure_failure": "infrastructure_failures",
    }[kind]
    _increment_metric(dossier, f"{metric.removesuffix('_attempts')}_{suffix}")


def dossier_lean_attempt_observer(dossier: Any, lane: str) -> LeanAttemptObserver:
    """Build a non-throwing execution-boundary observer for one exact lane."""

    clean_lane = str(lane or "").strip()

    def observe(event: str, attempt: Mapping[str, Any]) -> None:
        try:
            record_dossier_lean_attempt_event(
                dossier,
                lane=clean_lane,
                event=event,
                attempt=attempt,
            )
        except Exception:
            # Telemetry must not perturb proof search.
            return

    return observe


def notify_lean_attempt_observer(
    observer: LeanAttemptObserver | None,
    event: str,
    attempt: Mapping[str, Any] | None = None,
) -> None:
    if observer is None:
        return
    try:
        observer(str(event or ""), dict(attempt or {}))
    except Exception:
        return
