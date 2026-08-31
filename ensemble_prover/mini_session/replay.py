"""Provider-free replay, validation, and classification of run artifacts.

This module deliberately works from recorder artifacts only.  It does not
call Lean, a provider, or mini-session actions.  The first purpose is to turn
``turns.jsonl`` into a stable failure story.  The second is to replay narrow
controller invariants from logged decision frames, for example whether a
repair-ticket state was followed by the required conversation repair action.
Replay does not re-run proof search or treat logged model text as proof.

Usage::

    python -m ensemble_prover.mini_session.replay /path/to/run
    python -m ensemble_prover.mini_session.replay runs/mini_prover --recent 10
"""

from __future__ import annotations

import argparse
import copy
import dataclasses
import json
import math
import sys
import types
from dataclasses import asdict, dataclass, is_dataclass
from pathlib import Path
from types import SimpleNamespace
from typing import (
    Any,
    Dict,
    Iterable,
    Iterator,
    List,
    Mapping,
    MutableMapping,
    Optional,
    Sequence,
)

from ..solved_export_policy import (
    EXPORT_BOUNDARY_KEYS as POLICY_EXPORT_BOUNDARY_KEYS,
    EXPORT_FAILURE_COUNTER_KEYS as POLICY_EXPORT_FAILURE_COUNTER_KEYS,
    counter_positive as policy_counter_positive,
    counter_zero_or_absent as policy_counter_zero_or_absent,
    export_boundary_present as policy_export_boundary_present,
    export_status_values as policy_export_status_values,
    solved_export_verified_payload as policy_solved_export_verified_payload,
)
from ..mini_recursive_outcome import is_resumable_mini_recursive_yield
from ..state_data import mappingproxy_backing_dict
from .action import ActionBudget, RepairTicket
from .capability_policy import field_is_runtime_capability


JSONDict = Dict[str, Any]
_EXPORT_FAILURE_COUNTER_KEYS = POLICY_EXPORT_FAILURE_COUNTER_KEYS
_EXPORT_BOUNDARY_KEYS = POLICY_EXPORT_BOUNDARY_KEYS


class InvalidActionBudgetRecord(ValueError):
    """A durable action-budget record is not safe to restore."""


class InvalidSessionScalarState(ValueError):
    """Durable scheduler scalar state is not safe to restore."""


class InvalidSessionStateShape(ValueError):
    """Durable scheduler collection state is not safe to restore."""


_MAX_DURABLE_COUNTER = (1 << 63) - 1
_MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES = 4096


def _durable_budget_counter(
    value: Any,
    *,
    field: str,
    default: int,
    allow_unbounded_sentinel: bool = False,
) -> int:
    if value is None:
        value = default
    if isinstance(value, bool) or not isinstance(value, int):
        raise InvalidActionBudgetRecord(
            f"action budget {field} must be an integer"
        )
    if allow_unbounded_sentinel and value == -1:
        return -1
    if value < 0:
        raise InvalidActionBudgetRecord(
            f"action budget {field} must be nonnegative"
        )
    if value > _MAX_DURABLE_COUNTER:
        raise InvalidActionBudgetRecord(
            f"action budget {field} exceeds the durable counter limit"
        )
    return value


def _durable_budget_seconds(value: Any, *, field: str) -> float:
    if value is None:
        value = 0.0
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise InvalidActionBudgetRecord(
            f"action budget {field} must be a finite number"
        )
    try:
        decoded = float(value)
    except (OverflowError, TypeError, ValueError) as exc:
        raise InvalidActionBudgetRecord(
            f"action budget {field} must be a finite number"
        ) from exc
    if not math.isfinite(decoded):
        raise InvalidActionBudgetRecord(
            f"action budget {field} must be finite"
        )
    if decoded < 0.0:
        raise InvalidActionBudgetRecord(
            f"action budget {field} must be nonnegative"
        )
    return decoded


_SESSION_SCALAR_STATE_KEYS: tuple[str, ...] = (
    "iteration",
    "max_iterations",
    "stagnation_counter",
    "max_stagnation",
    "fallback_actions_attempted",
    "pending_fallback_action_id",
    "strict_progress_accounting",
    "soft_progress_streak",
    "max_soft_progress_streak",
    "final_proof",
    "last_lean_verdict",
    "last_llm_content",
    "last_giveup_cluster",
    "last_giveup_match",
    "last_wall_signature",
    "repeated_wall_count",
    "hard_pivot_count",
    "last_lean_infra_error",
    "consecutive_lean_infra_errors",
    "max_consecutive_lean_infra_errors",
    "terminal_failure_reason",
    "terminal_failure_kind",
    "max_no_applicable_recoveries",
    "no_applicable_recovery_budget_increment",
    "no_applicable_recovery_count",
    "cost_governed_continuations_without_action",
    "max_cost_governed_continuations_without_action",
    "last_cost_governed_continuation_progress_signature",
    "conversation_budget_topups_enabled",
    "last_durable_progress_signature",
    "progress_continuation_grants",
    "max_frontier_progress_retries",
    "max_model_call_deferred_frontier_retries",
    "max_model_call_deferred_static_retries",
    "recursive_pass_budget_remaining",
    "adaptive_recursive_pass_budget_remaining",
    "graph_recursive_decompose_remaining",
    "recursion_depth",
    "max_recursion_depth",
    "_conversation_turn_count",
    "provider_calls_completed_total",
    "provider_dispatches_started_total",
    "repair_first_until_conversation_turn",
    "repair_first_reason",
    "_repair_first_selected_local_forced",
    "_repair_first_selected_signature_key",
    "_repair_ticket_selected_id",
    "repair_policy_narrowing_required",
    "repair_policy_narrowing_reason",
    "local_repair_quota_remaining",
    "local_repair_quota_limit",
    "local_repair_quota_used",
    "local_repair_quota_reason",
    "local_repair_quota_failure_signature",
    "policy_repair_redirect_limit",
    "policy_repair_redirect_global_limit",
    "policy_repair_redirect_selected_action_id",
    "max_repair_ticket_chain_depth",
    "max_materialization_pending_no_applicable_recoveries",
    "persistent_infrastructure_retry_base_s",
    "persistent_infrastructure_retry_max_s",
    "max_identical_no_progress_actions",
    "identical_no_progress_actions",
    "identical_no_progress_search_signature",
    "max_no_progress_semantic_signature_recurrences",
    "max_no_progress_semantic_signatures",
    "max_proof_work_no_progress_attempts",
    "max_proof_work_no_progress_identities",
    "run_wall_clock_budget_s",
    "no_strong_progress_budget_s",
    "run_governor_elapsed_s",
    "run_governor_last_strong_progress_elapsed_s",
    "run_governor_actions_since_strong_progress",
    "run_governor_terminal_recorded",
    "root_finalized",
    "scope",
)

_SESSION_BOOLEAN_STATE_KEYS = frozenset(
    {
        "fallback_actions_attempted",
        "strict_progress_accounting",
        "conversation_budget_topups_enabled",
        "_repair_first_selected_local_forced",
        "repair_policy_narrowing_required",
        "root_finalized",
        "run_governor_terminal_recorded",
    }
)
_SESSION_NONNEGATIVE_COUNTER_STATE_KEYS = frozenset(
    {
        "iteration",
        "max_iterations",
        "stagnation_counter",
        "max_stagnation",
        "soft_progress_streak",
        "max_soft_progress_streak",
        "repeated_wall_count",
        "hard_pivot_count",
        "provider_calls_completed_total",
        "provider_dispatches_started_total",
        "consecutive_lean_infra_errors",
        "max_consecutive_lean_infra_errors",
        "max_no_applicable_recoveries",
        "no_applicable_recovery_budget_increment",
        "no_applicable_recovery_count",
        "cost_governed_continuations_without_action",
        "max_cost_governed_continuations_without_action",
        "progress_continuation_grants",
        "max_frontier_progress_retries",
        "max_model_call_deferred_frontier_retries",
        "max_model_call_deferred_static_retries",
        "recursive_pass_budget_remaining",
        "adaptive_recursive_pass_budget_remaining",
        "graph_recursive_decompose_remaining",
        "recursion_depth",
        "max_recursion_depth",
        "_conversation_turn_count",
        "repair_first_until_conversation_turn",
        "local_repair_quota_remaining",
        "local_repair_quota_limit",
        "local_repair_quota_used",
        "policy_repair_redirect_limit",
        "policy_repair_redirect_global_limit",
        "max_repair_ticket_chain_depth",
        "max_materialization_pending_no_applicable_recoveries",
        "run_governor_actions_since_strong_progress",
        "max_identical_no_progress_actions",
        "identical_no_progress_actions",
        "max_no_progress_semantic_signature_recurrences",
        "max_no_progress_semantic_signatures",
        "max_proof_work_no_progress_attempts",
        "max_proof_work_no_progress_identities",
    }
)
_SESSION_STRING_STATE_KEYS = frozenset(
    {
        "pending_fallback_action_id",
        "last_llm_content",
        "last_giveup_match",
        "last_wall_signature",
        "terminal_failure_reason",
        "terminal_failure_kind",
        "last_cost_governed_continuation_progress_signature",
        "last_durable_progress_signature",
        "repair_first_reason",
        "_repair_first_selected_signature_key",
        "_repair_ticket_selected_id",
        "repair_policy_narrowing_reason",
        "local_repair_quota_reason",
        "local_repair_quota_failure_signature",
        "policy_repair_redirect_selected_action_id",
        "identical_no_progress_search_signature",
    }
)
_SESSION_OPTIONAL_STRING_STATE_KEYS = frozenset(
    {
        "final_proof",
        "last_giveup_cluster",
        "last_lean_infra_error",
    }
)
_SESSION_NONNEGATIVE_SECONDS_STATE_KEYS = frozenset(
    {
        "run_wall_clock_budget_s",
        "no_strong_progress_budget_s",
        "run_governor_elapsed_s",
        "run_governor_last_strong_progress_elapsed_s",
        "persistent_infrastructure_retry_base_s",
        "persistent_infrastructure_retry_max_s",
    }
)
_SESSION_OPAQUE_SCALAR_STATE_KEYS = frozenset({"last_lean_verdict"})
_SESSION_SCOPE_VALUES = frozenset(
    {"problem", "attempt", "sample", "subgoal", "branch"}
)


def validate_durable_session_scalar_state(state: Mapping[str, Any]) -> None:
    """Reject malformed scheduler authority instead of normalizing it."""

    classified = (
        _SESSION_BOOLEAN_STATE_KEYS
        | _SESSION_NONNEGATIVE_COUNTER_STATE_KEYS
        | _SESSION_STRING_STATE_KEYS
        | _SESSION_OPTIONAL_STRING_STATE_KEYS
        | _SESSION_NONNEGATIVE_SECONDS_STATE_KEYS
        | _SESSION_OPAQUE_SCALAR_STATE_KEYS
        | {"scope"}
    )
    unclassified = set(_SESSION_SCALAR_STATE_KEYS) - classified
    if unclassified:
        raise RuntimeError(
            "unclassified durable session scalar fields: "
            + ", ".join(sorted(unclassified))
        )
    for key in _SESSION_BOOLEAN_STATE_KEYS:
        if key in state and not isinstance(state[key], bool):
            raise InvalidSessionScalarState(
                f"session state {key} must be a boolean"
            )
    for key in _SESSION_NONNEGATIVE_COUNTER_STATE_KEYS:
        if key not in state:
            continue
        value = state[key]
        if isinstance(value, bool) or not isinstance(value, int):
            raise InvalidSessionScalarState(
                f"session state {key} must be an integer"
            )
        if value < 0:
            raise InvalidSessionScalarState(
                f"session state {key} must be nonnegative"
            )
        if value > _MAX_DURABLE_COUNTER:
            raise InvalidSessionScalarState(
                f"session state {key} exceeds the durable counter limit"
            )
    for key in _SESSION_STRING_STATE_KEYS:
        if key in state and not isinstance(state[key], str):
            raise InvalidSessionScalarState(
                f"session state {key} must be a string"
            )
    for key in _SESSION_OPTIONAL_STRING_STATE_KEYS:
        if key in state and state[key] is not None and not isinstance(state[key], str):
            raise InvalidSessionScalarState(
                f"session state {key} must be a string or null"
            )
    for key in _SESSION_NONNEGATIVE_SECONDS_STATE_KEYS:
        if key not in state:
            continue
        value = state[key]
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise InvalidSessionScalarState(
                f"session state {key} must be a finite number"
            )
        try:
            seconds = float(value)
        except (OverflowError, TypeError, ValueError) as exc:
            raise InvalidSessionScalarState(
                f"session state {key} must be a finite number"
            ) from exc
        if not math.isfinite(seconds):
            raise InvalidSessionScalarState(
                f"session state {key} must be finite"
            )
        if seconds < 0.0:
            raise InvalidSessionScalarState(
                f"session state {key} must be nonnegative"
            )
    if "scope" in state:
        scope = state["scope"]
        if not isinstance(scope, str) or scope not in _SESSION_SCOPE_VALUES:
            raise InvalidSessionScalarState(
                "session state scope is unsupported"
            )

_SESSION_MAPPING_STATE_KEYS: tuple[str, ...] = (
    "_conversation_role_turn_counts",
    "local_repair_quota_used_by_signature",
    "local_repair_quota_selected_work_record",
    "repair_policy_narrowing_selected_work_record",
    "repair_policy_narrowing_scope_identity",
    "repair_self_check_continuation_counts",
    "last_action_outcome_metadata",
    "durable_progress_tool_continuation",
    "policy_repair_redirect_selected_record",
    "recursive_inflight_reservations",
    "model_call_deferred_static_action_metadata",
    "model_call_deferred_static_retry_counts",
    "no_progress_semantic_signature_counts",
    "no_progress_semantic_signature_action_families",
    "proof_work_no_progress_attempt_counts",
    "proof_work_no_progress_peak_attempt_counts",
    "proof_work_no_progress_last_signatures",
    "proof_work_no_progress_signature_history",
    "proof_work_root_alias_identities_by_base",
    "proof_work_closed_root_alias_identities",
)

_DURABLE_CONTINUATION_PAYLOAD_KEYS = frozenset(
    {
        "schema_version",
        "provider_turn_lane_identity",
        "tool_calls_used",
        "max_tool_calls_per_turn",
        "pending_tool_replay",
        "pending_tool_replay_is_paid_retry",
        "pending_tool_replay_disposition",
        "durable_progress_tool_continuation_identity",
        "durable_progress_tool_continuation_role",
        "durable_progress_tool_continuation_target",
        "durable_progress_tool_continuation_helper_receipts",
    }
)
_MAX_DURABLE_CONTINUATION_CALLS = 4096
_MAX_DURABLE_CONTINUATION_ARGUMENT_CHARS = 4_000_000
_MAX_DURABLE_CONTINUATION_TOTAL_ARGUMENT_CHARS = 16_000_000


def _validate_durable_progress_tool_continuation_snapshot(value: dict) -> None:
    """Reject malformed or unbounded closing work before it becomes live."""

    if not value:
        return
    if set(value) - {
        "identity",
        "action_id",
        "selected_work_item_record",
        "replay_payload",
    }:
        raise InvalidSessionStateShape(
            "session state durable_progress_tool_continuation has unknown fields"
        )
    identity = value.get("identity")
    action_id = value.get("action_id")
    selected_work = value.get("selected_work_item_record")
    payload = value.get("replay_payload")
    if (
        not isinstance(identity, str)
        or not identity
        or len(identity) > 128
        or not isinstance(action_id, str)
        or not action_id
        or len(action_id) > 512
        or not isinstance(selected_work, dict)
        or any(not isinstance(key, str) for key in selected_work)
        or not isinstance(payload, dict)
        or set(payload) != _DURABLE_CONTINUATION_PAYLOAD_KEYS
    ):
        raise InvalidSessionStateShape(
            "session state durable_progress_tool_continuation is malformed"
        )

    schema_version = payload.get("schema_version")
    used = payload.get("tool_calls_used")
    maximum = payload.get("max_tool_calls_per_turn")
    pending = payload.get("pending_tool_replay")
    receipts = payload.get("durable_progress_tool_continuation_helper_receipts")
    if (
        isinstance(schema_version, bool)
        or schema_version != 4
        or isinstance(used, bool)
        or not isinstance(used, int)
        or used < 0
        or isinstance(maximum, bool)
        or not isinstance(maximum, int)
        or maximum < 1
        or used > maximum
        or not isinstance(payload.get("pending_tool_replay_is_paid_retry"), bool)
        or payload.get("pending_tool_replay_disposition")
        != "durable_progress_cutpoint"
        or not isinstance(pending, list)
        or not pending
        or len(pending) > _MAX_DURABLE_CONTINUATION_CALLS
        or len(pending) > maximum - used
        or not isinstance(receipts, list)
        or len(receipts) > _MAX_DURABLE_CONTINUATION_CALLS
    ):
        raise InvalidSessionStateShape(
            "session state durable progress replay payload is malformed"
        )

    bounded_strings = (
        ("provider_turn_lane_identity", 256, False),
        ("durable_progress_tool_continuation_identity", 128, True),
        ("durable_progress_tool_continuation_role", 128, True),
        ("durable_progress_tool_continuation_target", 4_000_000, True),
    )
    for field, limit, required in bounded_strings:
        item = payload.get(field)
        if (
            not isinstance(item, str)
            or (required and not item)
            or len(item) > limit
        ):
            raise InvalidSessionStateShape(
                f"session state durable progress replay {field} is malformed"
            )
    if payload["durable_progress_tool_continuation_identity"] != identity:
        raise InvalidSessionStateShape(
            "session state durable progress replay identity does not match owner"
        )

    total_argument_chars = 0
    for call in pending:
        if not isinstance(call, dict) or set(call) - {"id", "type", "function"}:
            raise InvalidSessionStateShape(
                "session state durable progress replay contains a malformed call"
            )
        call_id = call.get("id", "")
        call_type = call.get("type", "")
        function = call.get("function")
        if (
            not isinstance(call_id, str)
            or len(call_id) > 512
            or not isinstance(call_type, str)
            or len(call_type) > 64
            or not isinstance(function, dict)
            or set(function) - {"name", "arguments"}
        ):
            raise InvalidSessionStateShape(
                "session state durable progress replay contains a malformed call"
            )
        name = function.get("name")
        arguments = function.get("arguments")
        if (
            not isinstance(name, str)
            or not name
            or len(name) > 128
            or arguments is not None
            and (
                not isinstance(arguments, str)
                or len(arguments) > _MAX_DURABLE_CONTINUATION_ARGUMENT_CHARS
            )
        ):
            raise InvalidSessionStateShape(
                "session state durable progress replay contains malformed tool data"
            )
        total_argument_chars += len(arguments or "")
    if total_argument_chars > _MAX_DURABLE_CONTINUATION_TOTAL_ARGUMENT_CHARS:
        raise InvalidSessionStateShape(
            "session state durable progress replay exceeds its argument bound"
        )

    for receipt in receipts:
        if not isinstance(receipt, dict) or set(receipt) != {"name", "source_hash"}:
            raise InvalidSessionStateShape(
                "session state durable progress replay contains a malformed receipt"
            )
        name = receipt.get("name")
        source_hash = receipt.get("source_hash")
        if (
            not isinstance(name, str)
            or not name
            or len(name) > 1024
            or not isinstance(source_hash, str)
            or not source_hash
            or len(source_hash) > 256
        ):
            raise InvalidSessionStateShape(
                "session state durable progress replay contains a malformed receipt"
            )

_SESSION_SEQUENCE_STATE_KEYS: tuple[str, ...] = (
    "graph_recursive_decompose_stack",
    "_tactic_close_source_suppression_records",
    "no_progress_semantic_signature_order",
    "proof_work_no_progress_attempt_order",
)

_SESSION_SET_STATE_KEYS: tuple[str, ...] = (
    "fallback_action_ids",
    "consumed_frontier_work_keys",
    "skipped_frontier_work_keys",
    "consumed_frontier_action_keys",
    "skipped_frontier_action_keys",
    "ready_root_route_drain_granted_action_keys",
    "model_call_deferred_frontier_action_keys",
    "materialization_pending_frontier_action_keys",
    "materialization_pending_frontier_logical_keys",
    "materialization_pending_no_applicable_recovery_logical_keys",
    "frontier_progress_signatures_seen",
    "frontier_progress_grants_seen",
)

_OPTIONAL_REPLAY_ATTR_KEYS: tuple[str, ...] = (
    "graph_recursive_decompose_remaining",
    "graph_recursive_decompose_stack",
)


@dataclass(frozen=True)
class MiniRunClassification:
    """Compact, evidence-bearing summary for one mini-prover run directory."""

    run_dir: str
    event_count: int
    malformed_event_count: int
    replay_eligible: bool
    summary_present: bool
    root_solved: bool
    status: str
    helper_accept_count: int
    lean_rejection_count: int
    repair_ticket_count: int
    repair_prompt_injected_count: int
    no_applicable_terminal_count: int
    route_contract_blocked_count: int
    answer_unsafe_count: int
    terminal_reason: str
    dominant_category: str
    cost_usd: float
    max_cost_usd: float
    estimated_unknown_cost_usd: float
    llm_budget_accounted_cost_usd: float
    evidence: str
    last_turn_index: int
    last_elapsed_s: Optional[float]
    last_phase: str
    last_verdict: str


@dataclass(frozen=True)
class TraceLoadResult:
    """Loaded recorder trace plus corruption/liveness diagnostics."""

    events: List[JSONDict]
    malformed_line_count: int = 0
    missing_trace: bool = False


@dataclass(frozen=True)
class ReplayDecision:
    """One replayed controller invariant from a trace window."""

    trigger_turn_index: int
    trigger_elapsed_s: Optional[float]
    trigger_phase: str
    trigger_verdict: str
    expected_next_action: str
    actual_next_action: str
    ok: bool
    category: str
    evidence: str


def _budget_to_record(budget: ActionBudget) -> JSONDict:
    return {
        "max_invocations": int(budget.max_invocations),
        "max_total_seconds": float(budget.max_total_seconds),
        "invocations": int(budget.invocations),
        "total_seconds": float(budget.total_seconds),
        "last_failure_reason": str(budget.last_failure_reason or ""),
        "scope": str(budget.scope or "session"),
        "max_aggregate_invocations": int(budget.max_aggregate_invocations),
        "max_aggregate_seconds": float(budget.max_aggregate_seconds),
        "unproductive_seconds": float(budget.unproductive_seconds),
    }


def _budget_from_record(record: Any) -> ActionBudget:
    if not isinstance(record, Mapping):
        raise InvalidActionBudgetRecord("action budget record must be a mapping")
    try:
        return ActionBudget(
            max_invocations=_durable_budget_counter(
                record.get("max_invocations"),
                field="max_invocations",
                default=1,
                allow_unbounded_sentinel=True,
            ),
            max_total_seconds=_durable_budget_seconds(
                record.get("max_total_seconds"),
                field="max_total_seconds",
            ),
            invocations=_durable_budget_counter(
                record.get("invocations"),
                field="invocations",
                default=0,
            ),
            total_seconds=_durable_budget_seconds(
                record.get("total_seconds"),
                field="total_seconds",
            ),
            last_failure_reason=str(record.get("last_failure_reason") or ""),
            scope=str(record.get("scope") or "session"),
            max_aggregate_invocations=_durable_budget_counter(
                record.get("max_aggregate_invocations"),
                field="max_aggregate_invocations",
                default=-1,
                allow_unbounded_sentinel=True,
            ),
            max_aggregate_seconds=_durable_budget_seconds(
                record.get("max_aggregate_seconds"),
                field="max_aggregate_seconds",
            ),
            unproductive_seconds=_durable_budget_seconds(
                record.get("unproductive_seconds"),
                field="unproductive_seconds",
            ),
        )
    except InvalidActionBudgetRecord:
        raise
    except (TypeError, ValueError) as exc:
        raise InvalidActionBudgetRecord(f"invalid action budget record: {exc}") from exc


def _repair_ticket_to_record(ticket: RepairTicket) -> JSONDict:
    return {
        "ticket_id": ticket.ticket_id,
        "proof": ticket.proof,
        "lean_output": ticket.lean_output,
        "feedback_text": ticket.feedback_text,
        "feedback_source": ticket.feedback_source,
        "error_type": ticket.error_type,
        "failure_signature": ticket.failure_signature,
        "target_id": ticket.target_id,
        "target_statement": ticket.target_statement,
        "route_id": ticket.route_id,
        "obligation_id": ticket.obligation_id,
        "work_type": ticket.work_type,
        "proof_attempt_id": ticket.proof_attempt_id,
        "strategy_lineage_id": ticket.strategy_lineage_id,
        "statement_identity": ticket.statement_identity,
        "proof_candidate_id": ticket.proof_candidate_id,
        "lean_residual_id": ticket.lean_residual_id,
        "helper_blocks": list(ticket.helper_blocks),
        "helper_names": list(ticket.helper_names),
        "source_action_id": ticket.source_action_id,
        "turn_index": int(ticket.turn_index),
        "max_attempts": int(ticket.max_attempts),
        "attempts_used": int(ticket.attempts_used),
        "policy_attempts_used": int(getattr(ticket, "policy_attempts_used", 0) or 0),
        "max_policy_attempts": int(getattr(ticket, "max_policy_attempts", 0) or 0),
        "root_ticket_id": ticket.root_ticket_id,
        "repair_depth": int(ticket.repair_depth),
        "max_chain_depth": int(ticket.max_chain_depth),
        "metadata": dict(ticket.metadata or {}),
    }


def _repair_ticket_from_record(record: Any) -> Optional[RepairTicket]:
    if not isinstance(record, Mapping):
        return None
    ticket_id = str(record.get("ticket_id") or "").strip()
    proof = str(record.get("proof") or "")
    if not ticket_id or not proof:
        return None
    return RepairTicket(
        ticket_id=ticket_id,
        proof=proof,
        lean_output=str(record.get("lean_output") or ""),
        feedback_text=str(record.get("feedback_text") or ""),
        feedback_source=str(record.get("feedback_source") or ""),
        error_type=str(record.get("error_type") or ""),
        failure_signature=str(record.get("failure_signature") or ""),
        target_id=str(record.get("target_id") or "root"),
        target_statement=str(record.get("target_statement") or ""),
        route_id=str(record.get("route_id") or ""),
        obligation_id=str(record.get("obligation_id") or ""),
        work_type=str(record.get("work_type") or ""),
        proof_attempt_id=str(record.get("proof_attempt_id") or ""),
        strategy_lineage_id=str(record.get("strategy_lineage_id") or ""),
        statement_identity=str(record.get("statement_identity") or ""),
        proof_candidate_id=str(record.get("proof_candidate_id") or ""),
        lean_residual_id=str(record.get("lean_residual_id") or ""),
        helper_blocks=tuple(str(item) for item in list(record.get("helper_blocks") or [])),
        helper_names=tuple(str(item) for item in list(record.get("helper_names") or [])),
        source_action_id=str(record.get("source_action_id") or ""),
        turn_index=_safe_int(record.get("turn_index"), default=0),
        max_attempts=max(1, _safe_int(record.get("max_attempts"), default=1)),
        attempts_used=max(0, _safe_int(record.get("attempts_used"), default=0)),
        policy_attempts_used=max(
            0,
            _safe_int(record.get("policy_attempts_used"), default=0),
        ),
        max_policy_attempts=max(
            1,
            _safe_int(record.get("max_policy_attempts"), default=1),
        ),
        root_ticket_id=str(record.get("root_ticket_id") or ""),
        repair_depth=max(0, _safe_int(record.get("repair_depth"), default=0)),
        max_chain_depth=max(1, _safe_int(record.get("max_chain_depth"), default=3)),
        metadata=dict(record.get("metadata") or {}),
    )


_REPAIR_TICKET_SNAPSHOT_STRING_FIELDS = frozenset(
    {
        "ticket_id",
        "proof",
        "lean_output",
        "feedback_text",
        "feedback_source",
        "error_type",
        "failure_signature",
        "target_id",
        "target_statement",
        "route_id",
        "obligation_id",
        "work_type",
        "proof_attempt_id",
        "strategy_lineage_id",
        "statement_identity",
        "proof_candidate_id",
        "lean_residual_id",
        "source_action_id",
        "root_ticket_id",
    }
)
_REPAIR_TICKET_SNAPSHOT_SEQUENCE_FIELDS = frozenset(
    {"helper_blocks", "helper_names"}
)
# Checkpoints emitted between 490af8f66f and 52c1ef2b7 used zero as the
# max_policy_attempts sentinel; RepairTicket's decoder migrates it to one.
_REPAIR_TICKET_SNAPSHOT_NONNEGATIVE_INT_FIELDS = frozenset(
    {
        "turn_index",
        "attempts_used",
        "policy_attempts_used",
        "max_policy_attempts",
        "repair_depth",
    }
)
_REPAIR_TICKET_SNAPSHOT_POSITIVE_INT_FIELDS = frozenset(
    {"max_attempts", "max_chain_depth"}
)
_REPAIR_TICKET_SNAPSHOT_KEYS = (
    _REPAIR_TICKET_SNAPSHOT_STRING_FIELDS
    | _REPAIR_TICKET_SNAPSHOT_SEQUENCE_FIELDS
    | _REPAIR_TICKET_SNAPSHOT_NONNEGATIVE_INT_FIELDS
    | _REPAIR_TICKET_SNAPSHOT_POSITIVE_INT_FIELDS
    | {"metadata"}
)


def _repair_ticket_from_snapshot_record(record: Any) -> RepairTicket:
    """Decode one persisted ticket without normalizing corrupt authority."""

    if not isinstance(record, Mapping) or set(record) - _REPAIR_TICKET_SNAPSHOT_KEYS:
        raise InvalidSessionStateShape("session repair ticket is malformed")
    if any(
        key in record and not isinstance(record.get(key), str)
        for key in _REPAIR_TICKET_SNAPSHOT_STRING_FIELDS
    ):
        raise InvalidSessionStateShape("session repair-ticket strings are malformed")
    if not str(record.get("ticket_id") or "").strip() or not str(
        record.get("proof") or ""
    ):
        raise InvalidSessionStateShape("session repair ticket is incomplete")
    for key in _REPAIR_TICKET_SNAPSHOT_SEQUENCE_FIELDS:
        value = record.get(key, [])
        if not isinstance(value, list) or any(
            not isinstance(item, str) for item in value
        ):
            raise InvalidSessionStateShape(
                f"session repair-ticket {key} is malformed"
            )
    for key in _REPAIR_TICKET_SNAPSHOT_NONNEGATIVE_INT_FIELDS:
        value = record.get(key, 0)
        if type(value) is not int or value < 0 or value > _MAX_DURABLE_COUNTER:
            raise InvalidSessionStateShape(
                f"session repair-ticket {key} is malformed"
            )
    for key in _REPAIR_TICKET_SNAPSHOT_POSITIVE_INT_FIELDS:
        value = record.get(key, 1)
        if type(value) is not int or value < 1 or value > _MAX_DURABLE_COUNTER:
            raise InvalidSessionStateShape(
                f"session repair-ticket {key} is malformed"
            )
    metadata = record.get("metadata", {})
    if not isinstance(metadata, Mapping) or any(
        not isinstance(key, str) for key in metadata
    ):
        raise InvalidSessionStateShape("session repair-ticket metadata is malformed")
    advisory_continuation_count = metadata.get(
        "repair_advisory_without_artifact_continuations",
        0,
    )
    if (
        type(advisory_continuation_count) is not int
        or advisory_continuation_count not in {0, 1}
    ):
        raise InvalidSessionStateShape("session repair-ticket metadata is malformed")
    recheck_binding = metadata.get(
        "answer_safe_recheck_repair_ticket_binding"
    )
    if recheck_binding is not None:
        expected_binding_keys = {
            "schema_version",
            "ticket_id",
            "action_id",
            "recheck_identity",
        }
        if (
            not isinstance(recheck_binding, Mapping)
            or set(recheck_binding) != expected_binding_keys
            or type(recheck_binding.get("schema_version")) is not int
            or recheck_binding.get("schema_version") != 1
            or any(
                not isinstance(recheck_binding.get(key), str)
                or not str(recheck_binding.get(key) or "").strip()
                for key in ("ticket_id", "action_id", "recheck_identity")
            )
            or str(recheck_binding.get("ticket_id") or "").strip()
            != str(record.get("ticket_id") or "").strip()
        ):
            raise InvalidSessionStateShape(
                "session repair-ticket metadata is malformed"
            )
    decoded = _repair_ticket_from_record(record)
    if decoded is None:
        raise InvalidSessionStateShape("session repair ticket is incomplete")
    return decoded


def _jsonable_tuple_set(value: Any) -> List[List[str]]:
    if not isinstance(value, set):
        return []
    rows: List[List[str]] = []
    for item in value:
        if isinstance(item, tuple):
            rows.append([str(part) for part in item])
        else:
            rows.append([str(item)])
    return sorted(rows)


def _restore_tuple_set(rows: Any) -> set[tuple[str, ...]]:
    restored: set[tuple[str, ...]] = set()
    for row in list(rows or []):
        if isinstance(row, (list, tuple)):
            restored.add(tuple(str(part) for part in row))
        elif row is not None:
            restored.add((str(row),))
    return restored


def _jsonable_string_set(value: Any) -> List[str]:
    if not isinstance(value, set):
        return []
    return sorted(str(item) for item in value)


def _restore_string_set(rows: Any) -> set[str]:
    if not isinstance(rows, (list, tuple, set, frozenset)):
        return set()
    return {str(item) for item in rows}


def _restore_string_tuple(rows: Any) -> tuple[str, ...]:
    if not isinstance(rows, (list, tuple)):
        return ()
    return tuple(str(item) for item in rows)


def _jsonable_string_int_mapping(value: Any) -> List[List[Any]]:
    if not isinstance(value, Mapping):
        return []
    return sorted(
        [str(key), _safe_int(count, default=0)]
        for key, count in value.items()
    )


def _restore_string_int_mapping(rows: Any) -> dict[str, int]:
    restored: dict[str, int] = {}
    for row in list(rows or []):
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            continue
        key, count = row
        restored[str(key)] = _safe_int(count, default=0)
    return restored


def _jsonable_string_tuple_mapping(value: Any) -> List[List[Any]]:
    if not isinstance(value, Mapping):
        return []
    return sorted(
        [
            str(key),
            [str(item) for item in tuple(mapped or ())],
        ]
        for key, mapped in value.items()
    )


def _restore_string_tuple_mapping(rows: Any) -> dict[str, tuple[str, ...]]:
    restored: dict[str, tuple[str, ...]] = {}
    for row in list(rows or []):
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            continue
        key, mapped = row
        if not isinstance(mapped, (list, tuple)):
            continue
        restored[str(key)] = tuple(str(item) for item in mapped)
    return restored


def _jsonable_tuple_string_mapping(value: Any) -> List[List[Any]]:
    if not isinstance(value, Mapping):
        return []
    return sorted(
        [
            [str(part) for part in tuple(key)],
            str(mapped),
        ]
        for key, mapped in value.items()
        if isinstance(key, tuple)
    )


def _restore_tuple_string_mapping(rows: Any) -> dict[tuple[str, ...], str]:
    restored: dict[tuple[str, ...], str] = {}
    for row in list(rows or []):
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            continue
        key, mapped = row
        if not isinstance(key, (list, tuple)):
            continue
        restored[tuple(str(part) for part in key)] = str(mapped)
    return restored


def _jsonable_tuple_int_mapping(value: Any) -> List[List[Any]]:
    if not isinstance(value, Mapping):
        return []
    rows: List[List[Any]] = []
    for key, count in value.items():
        if isinstance(key, tuple):
            key_row = [str(part) for part in key]
        elif isinstance(key, (list, tuple)):
            key_row = [str(part) for part in key]
        else:
            key_row = [str(key)]
        rows.append([key_row, _safe_int(count, default=0)])
    return sorted(rows)


def _restore_tuple_int_mapping(rows: Any) -> dict[tuple[str, ...], int]:
    restored: dict[tuple[str, ...], int] = {}
    if isinstance(rows, Mapping):
        for key, count in rows.items():
            if isinstance(key, tuple):
                tuple_key = tuple(str(part) for part in key)
            else:
                tuple_key = (str(key),)
            restored[tuple_key] = _safe_int(count, default=0)
        return restored
    for row in list(rows or []):
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            continue
        key_row, count = row
        if isinstance(key_row, (list, tuple)):
            tuple_key = tuple(str(part) for part in key_row)
        else:
            tuple_key = (str(key_row),)
        restored[tuple_key] = _safe_int(count, default=0)
    return restored


def _jsonable_tuple_dict_mapping(value: Any) -> List[List[Any]]:
    if not isinstance(value, Mapping):
        return []
    rows: List[List[Any]] = []
    for key, mapped in value.items():
        if not isinstance(key, tuple) or not isinstance(mapped, Mapping):
            continue
        rows.append(
            [
                [str(part) for part in key],
                copy.deepcopy(dict(mapped)),
            ]
        )
    return sorted(rows, key=lambda row: row[0])


def _restore_tuple_dict_mapping(
    rows: Any,
) -> dict[tuple[str, ...], Dict[str, Any]]:
    restored: dict[tuple[str, ...], Dict[str, Any]] = {}
    if isinstance(rows, Mapping):
        for key, mapped in rows.items():
            if not isinstance(key, tuple) or not isinstance(mapped, Mapping):
                continue
            restored[tuple(str(part) for part in key)] = copy.deepcopy(dict(mapped))
        return restored
    for row in list(rows or []):
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            continue
        key_row, mapped = row
        if not isinstance(key_row, (list, tuple)) or not isinstance(mapped, Mapping):
            continue
        restored[tuple(str(part) for part in key_row)] = copy.deepcopy(dict(mapped))
    return restored


def _jsonable_tuple_tuple_mapping(value: Any) -> List[List[List[str]]]:
    if not isinstance(value, Mapping):
        return []
    rows: List[List[List[str]]] = []
    for key, mapped in value.items():
        key_row = [str(part) for part in key] if isinstance(key, tuple) else [str(key)]
        mapped_row = (
            [str(part) for part in mapped]
            if isinstance(mapped, tuple)
            else [str(mapped)]
        )
        rows.append([key_row, mapped_row])
    return sorted(rows)


def _restore_tuple_tuple_mapping(rows: Any) -> dict[tuple[str, ...], tuple[str, ...]]:
    restored: dict[tuple[str, ...], tuple[str, ...]] = {}
    if isinstance(rows, Mapping):
        for key, mapped in rows.items():
            tuple_key = tuple(str(part) for part in key) if isinstance(key, tuple) else (str(key),)
            tuple_mapped = (
                tuple(str(part) for part in mapped)
                if isinstance(mapped, tuple)
                else (str(mapped),)
            )
            restored[tuple_key] = tuple_mapped
        return restored
    for row in list(rows or []):
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            continue
        key_row, mapped_row = row
        tuple_key = (
            tuple(str(part) for part in key_row)
            if isinstance(key_row, (list, tuple))
            else (str(key_row),)
        )
        tuple_mapped = (
            tuple(str(part) for part in mapped_row)
            if isinstance(mapped_row, (list, tuple))
            else (str(mapped_row),)
        )
        restored[tuple_key] = tuple_mapped
    return restored


_SESSION_TUPLE_SET_ARITIES: Mapping[str, tuple[int, ...]] = {
    "consumed_frontier_work_keys": (3, 5),
    "skipped_frontier_work_keys": (3, 5),
    "consumed_frontier_action_keys": (3, 6),
    "skipped_frontier_action_keys": (3, 6),
    "ready_root_route_drain_granted_action_keys": (6,),
    "model_call_deferred_frontier_action_keys": (3, 6),
    "materialization_pending_frontier_action_keys": (6,),
    "materialization_pending_frontier_logical_keys": (5,),
    "materialization_pending_no_applicable_recovery_logical_keys": (5,),
    "frontier_progress_signatures_seen": (7,),
    "frontier_progress_grants_seen": (7,),
}
_SESSION_STRING_SET_KEYS = frozenset(
    {
        "theory_context_hit_need_ids",
        "durable_progress_signatures_seen",
        "static_prepass_headroom_signatures_seen",
        "model_call_deferred_static_action_ids",
        "provider_turn_retired_lane_identities",
        "recursive_helper_cleanup_continuation_identities",
        "primary_verifier_continuation_identities",
        "paid_tool_continuation_identities",
        "durable_progress_tool_continuation_identities",
        "theory_attempted_need_ids",
        "identical_no_progress_action_families_seen",
    }
)
_SESSION_STRING_COUNTER_MAPPING_KEYS = frozenset(
    {
        "_conversation_role_turn_counts",
        "local_repair_quota_used_by_signature",
        "repair_self_check_continuation_counts",
        "model_call_deferred_static_retry_counts",
        "theory_need_attempt_counts",
        "no_progress_semantic_signature_counts",
        "proof_work_no_progress_attempt_counts",
        "proof_work_no_progress_peak_attempt_counts",
        "proof_work_closed_root_alias_identities",
    }
)


def _valid_durable_counter(value: Any) -> bool:
    return bool(
        isinstance(value, int)
        and not isinstance(value, bool)
        and 0 <= value <= _MAX_DURABLE_COUNTER
    )


def _valid_string_tuple(value: Any, *, arity: Optional[int] = None) -> bool:
    return bool(
        isinstance(value, tuple)
        and (arity is None or len(value) == arity)
        and all(isinstance(item, str) for item in value)
    )


def _valid_snapshot_string_row(value: Any, *, arity: Optional[int] = None) -> bool:
    return bool(
        isinstance(value, list)
        and (arity is None or len(value) == arity)
        and all(isinstance(item, str) for item in value)
    )


def _validate_string_counter_mapping(
    value: Any,
    *,
    field: str,
    max_key_chars: int = 0,
) -> None:
    if not isinstance(value, dict):
        raise InvalidSessionStateShape(f"session state {field} must be a mapping")
    if any(
        not isinstance(key, str)
        or (max_key_chars > 0 and len(key) > max_key_chars)
        or not _valid_durable_counter(count)
        for key, count in value.items()
    ):
        raise InvalidSessionStateShape(
            f"session state {field} must map strings to nonnegative integers"
        )


def _validate_snapshot_string_counter_rows(value: Any, *, field: str) -> None:
    if not isinstance(value, list) or any(
        not isinstance(row, list)
        or len(row) != 2
        or not isinstance(row[0], str)
        or not _valid_durable_counter(row[1])
        for row in value
    ):
        raise InvalidSessionStateShape(
            f"session state {field} must contain string/counter rows"
        )


def _validate_tuple_counter_mapping(
    value: Any,
    *,
    field: str,
    arity: int,
    snapshot_encoding: bool,
) -> None:
    if snapshot_encoding:
        if not isinstance(value, list) or any(
            not isinstance(row, list)
            or len(row) != 2
            or not _valid_snapshot_string_row(row[0], arity=arity)
            or not _valid_durable_counter(row[1])
            for row in value
        ):
            raise InvalidSessionStateShape(
                f"session state {field} must contain tuple/counter rows"
            )
        return
    if not isinstance(value, dict) or any(
        not _valid_string_tuple(key, arity=arity)
        or not _valid_durable_counter(count)
        for key, count in value.items()
    ):
        raise InvalidSessionStateShape(
            f"session state {field} must map string tuples to nonnegative integers"
        )


def validate_durable_session_state_shapes(
    state: Mapping[str, Any],
    *,
    snapshot_encoding: bool = False,
) -> None:
    """Validate scheduler collections before they become live authority."""

    validate_durable_session_scalar_state(state)
    for key in _SESSION_SET_STATE_KEYS:
        if key not in state:
            continue
        value = state[key]
        if key == "fallback_action_ids":
            valid = (
                isinstance(value, list)
                and all(_valid_snapshot_string_row(row, arity=1) for row in value)
                if snapshot_encoding
                else isinstance(value, set)
                and all(isinstance(item, str) for item in value)
            )
        else:
            arities = _SESSION_TUPLE_SET_ARITIES[key]
            valid = (
                isinstance(value, list)
                and all(
                    any(
                        _valid_snapshot_string_row(row, arity=arity)
                        for arity in arities
                    )
                    for row in value
                )
                if snapshot_encoding
                else isinstance(value, set)
                and all(
                    any(
                        _valid_string_tuple(item, arity=arity)
                        for arity in arities
                    )
                    for item in value
                )
            )
        if not valid:
            raise InvalidSessionStateShape(
                f"session state {key} has an invalid durable set shape"
            )
    for key in _SESSION_STRING_SET_KEYS:
        if key not in state:
            continue
        value = state[key]
        valid = (
            isinstance(value, list) and all(isinstance(item, str) for item in value)
            if snapshot_encoding
            else isinstance(value, set)
            and all(isinstance(item, str) for item in value)
        )
        if not valid:
            raise InvalidSessionStateShape(
                f"session state {key} must be a set of strings"
            )
        if key == "identical_no_progress_action_families_seen" and (
            len(value) > 128
            or any(len(str(item)) > 128 for item in value)
        ):
            raise InvalidSessionStateShape(
                "session state identical_no_progress_action_families_seen "
                "exceeds its durable bound"
            )
    for key in _SESSION_MAPPING_STATE_KEYS:
        if key not in state:
            continue
        value = state[key]
        if not isinstance(value, dict) or any(
            not isinstance(item_key, str) for item_key in value
        ):
            raise InvalidSessionStateShape(
                f"session state {key} must be a string-keyed mapping"
            )
        if key == "durable_progress_tool_continuation":
            _validate_durable_progress_tool_continuation_snapshot(value)
        if key in _SESSION_STRING_COUNTER_MAPPING_KEYS:
            if key in {
                "no_progress_semantic_signature_counts",
                "proof_work_no_progress_attempt_counts",
                "proof_work_no_progress_peak_attempt_counts",
            } and len(value) > _MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES:
                raise InvalidSessionStateShape(
                    f"session state {key} exceeds the durable identity limit"
                )
            _validate_string_counter_mapping(
                value,
                field=key,
                max_key_chars=(
                    64
                    if key
                    in {
                        "no_progress_semantic_signature_counts",
                        "proof_work_no_progress_attempt_counts",
                        "proof_work_no_progress_peak_attempt_counts",
                        "proof_work_closed_root_alias_identities",
                    }
                    else 0
                ),
            )
        if key == "no_progress_semantic_signature_action_families" and (
            len(value) > _MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES
            or any(
                len(item_key) > 64
                or not isinstance(families, list)
                or len(families) > 128
                or any(
                    not isinstance(family, str) or len(family) > 128
                    for family in families
                )
                for item_key, families in value.items()
            )
        ):
            raise InvalidSessionStateShape(
                "session state no_progress_semantic_signature_action_families "
                "must map bounded signatures to action-family lists"
            )
        if key == "proof_work_no_progress_last_signatures" and (
            len(value) > _MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES
            or any(
                len(item_key) > 64
                or not isinstance(signature, str)
                or not signature
                or len(signature) > 128
                for item_key, signature in value.items()
            )
            or any(
                item_key
                not in dict(
                    state.get("proof_work_no_progress_attempt_counts") or {}
                )
                for item_key in value
            )
        ):
            raise InvalidSessionStateShape(
                "session state proof_work_no_progress_last_signatures must "
                "map bounded identities to bounded signatures"
            )
        if key == "proof_work_no_progress_peak_attempt_counts" and any(
            item_key
            not in dict(state.get("proof_work_no_progress_attempt_counts") or {})
            for item_key in value
        ):
            raise InvalidSessionStateShape(
                "session state proof_work_no_progress_peak_attempt_counts "
                "must reference recorded identities"
            )
        if key == "proof_work_closed_root_alias_identities" and any(
            item_key
            not in dict(state.get("proof_work_no_progress_attempt_counts") or {})
            for item_key in value
        ):
            raise InvalidSessionStateShape(
                "session state proof_work_closed_root_alias_identities must "
                "reference recorded identities"
            )
        if key == "proof_work_root_alias_identities_by_base" and (
            len(value) > _MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES
            or any(
                len(base) > 64
                or base
                not in dict(
                    state.get("proof_work_no_progress_attempt_counts") or {}
                )
                or not isinstance(aliases, list)
                or len(aliases) > _MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES
                or any(
                    not isinstance(alias, str)
                    or len(alias) > 64
                    or alias
                    not in dict(
                        state.get("proof_work_no_progress_attempt_counts") or {}
                    )
                    for alias in aliases
                )
                for base, aliases in value.items()
            )
        ):
            raise InvalidSessionStateShape(
                "session state proof_work_root_alias_identities_by_base is "
                "malformed"
            )
        if key == "proof_work_no_progress_signature_history" and (
            len(value) > _MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES
            or any(
                len(item_key) > 64
                or not isinstance(history, list)
                or len(history) > 32
                or any(
                    not isinstance(signature, str)
                    or not signature
                    or len(signature) > 128
                    for signature in history
                )
                for item_key, history in value.items()
            )
            or any(
                item_key
                not in dict(
                    state.get("proof_work_no_progress_attempt_counts") or {}
                )
                for item_key in value
            )
        ):
            raise InvalidSessionStateShape(
                "session state proof_work_no_progress_signature_history must "
                "map bounded identities to bounded signature lists"
            )
    if "model_call_deferred_frontier_action_metadata" in state:
        value = state["model_call_deferred_frontier_action_metadata"]
        if snapshot_encoding:
            valid = isinstance(value, list) and all(
                isinstance(row, list)
                and len(row) == 2
                and any(
                    _valid_snapshot_string_row(row[0], arity=arity)
                    for arity in (3, 6)
                )
                and isinstance(row[1], dict)
                and all(isinstance(key, str) for key in row[1])
                for row in value
            )
        else:
            valid = isinstance(value, dict) and all(
                any(
                    _valid_string_tuple(key, arity=arity)
                    for arity in (3, 6)
                )
                and isinstance(mapped, dict)
                and all(isinstance(field, str) for field in mapped)
                for key, mapped in value.items()
            )
        if not valid:
            raise InvalidSessionStateShape(
                "session state model_call_deferred_frontier_action_metadata "
                "has an invalid durable mapping shape"
            )
    if "repair_policy_narrowing_scope_identity" in state and any(
        not isinstance(value, str)
        for value in state["repair_policy_narrowing_scope_identity"].values()
    ):
        raise InvalidSessionStateShape(
            "session state repair_policy_narrowing_scope_identity must map strings to strings"
        )
    reservations = state.get("recursive_inflight_reservations")
    if reservations is not None:
        for action_id, record in reservations.items():
            if (
                not isinstance(action_id, str)
                or not isinstance(record, dict)
                or not isinstance(record.get("pool_attr"), str)
                or not _valid_durable_counter(record.get("reserved_passes"))
                or (
                    "credited_extension_grants" in record
                    and not _valid_durable_counter(
                        record.get("credited_extension_grants")
                    )
                )
            ):
                raise InvalidSessionStateShape(
                    "session state recursive_inflight_reservations is malformed"
                )
            consumed_key = record.get("consumed_frontier_action_key")
            if consumed_key is not None and not (
                any(
                    _valid_snapshot_string_row(consumed_key, arity=arity)
                    for arity in (3, 6)
                )
                if snapshot_encoding
                else any(
                    _valid_string_tuple(consumed_key, arity=arity)
                    for arity in (3, 6)
                )
            ):
                raise InvalidSessionStateShape(
                    "session state recursive_inflight_reservations has an invalid frontier key"
                )
    for key in _SESSION_SEQUENCE_STATE_KEYS:
        if key not in state:
            continue
        value = state[key]
        if not isinstance(value, list):
            raise InvalidSessionStateShape(
                f"session state {key} must be a list"
            )
        if key == "graph_recursive_decompose_stack" and any(
            not isinstance(item, str) for item in value
        ):
            raise InvalidSessionStateShape(
                "session state graph_recursive_decompose_stack must contain strings"
            )
        if key == "_tactic_close_source_suppression_records" and any(
            not isinstance(item, dict) for item in value
        ):
            raise InvalidSessionStateShape(
                "session state _tactic_close_source_suppression_records must contain mappings"
            )
        if key in {
            "no_progress_semantic_signature_order",
            "proof_work_no_progress_attempt_order",
        } and (
            len(value) > _MAX_DURABLE_SEMANTIC_LEDGER_IDENTITIES
            or any(
                not isinstance(item, str) or len(item) > 64
                for item in value
            )
        ):
            raise InvalidSessionStateShape(
                f"session state {key} must contain bounded strings"
            )
    for key in ("theory_imported_bundle_ids", "no_applicable_recovery_action_ids"):
        if key not in state:
            continue
        value = state[key]
        valid = (
            isinstance(value, list) and all(isinstance(item, str) for item in value)
            if snapshot_encoding
            else _valid_string_tuple(value)
        )
        if not valid:
            raise InvalidSessionStateShape(
                f"session state {key} must contain strings"
            )
    for key in _SESSION_STRING_COUNTER_MAPPING_KEYS:
        if key not in state or key in _SESSION_MAPPING_STATE_KEYS:
            continue
        if snapshot_encoding:
            _validate_snapshot_string_counter_rows(state[key], field=key)
        else:
            _validate_string_counter_mapping(state[key], field=key)
    for key, arity in (
        ("materialization_pending_no_applicable_recovery_counts", 5),
        ("frontier_progress_retry_counts", 6),
        ("model_call_deferred_frontier_retry_counts", 6),
    ):
        if key in state:
            _validate_tuple_counter_mapping(
                state[key],
                field=key,
                arity=arity,
                snapshot_encoding=snapshot_encoding,
            )
    bundle_map = state.get("theory_consumer_bundle_ids_by_need_id")
    if bundle_map is not None:
        valid = (
            isinstance(bundle_map, list)
            and all(
                isinstance(row, list)
                and len(row) == 2
                and isinstance(row[0], str)
                and _valid_snapshot_string_row(row[1])
                for row in bundle_map
            )
            if snapshot_encoding
            else isinstance(bundle_map, dict)
            and all(
                isinstance(key, str) and _valid_string_tuple(value)
                for key, value in bundle_map.items()
            )
        )
        if not valid:
            raise InvalidSessionStateShape(
                "session state theory_consumer_bundle_ids_by_need_id is malformed"
            )
    frontier_need_map = state.get("theory_need_ids_by_frontier_key")
    if frontier_need_map is not None:
        valid = (
            isinstance(frontier_need_map, list)
            and all(
                isinstance(row, list)
                and len(row) == 2
                and _valid_snapshot_string_row(row[0])
                and isinstance(row[1], str)
                for row in frontier_need_map
            )
            if snapshot_encoding
            else isinstance(frontier_need_map, dict)
            and all(
                _valid_string_tuple(key) and isinstance(value, str)
                for key, value in frontier_need_map.items()
            )
        )
        if not valid:
            raise InvalidSessionStateShape(
                "session state theory_need_ids_by_frontier_key is malformed"
            )
    action_logical_map = state.get(
        "materialization_pending_frontier_action_logical_keys"
    )
    if action_logical_map is not None:
        valid = (
            isinstance(action_logical_map, list)
            and all(
                isinstance(row, list)
                and len(row) == 2
                and _valid_snapshot_string_row(row[0], arity=6)
                and _valid_snapshot_string_row(row[1], arity=5)
                for row in action_logical_map
            )
            if snapshot_encoding
            else isinstance(action_logical_map, dict)
            and all(
                _valid_string_tuple(key, arity=6)
                and _valid_string_tuple(value, arity=5)
                for key, value in action_logical_map.items()
            )
        )
        if not valid:
            raise InvalidSessionStateShape(
                "session state materialization_pending_frontier_action_logical_keys is malformed"
            )
    ticket = state.get("pending_repair_ticket")
    if "pending_repair_ticket" in state and ticket is not None and not (
        isinstance(ticket, Mapping) if snapshot_encoding else isinstance(ticket, RepairTicket)
    ):
        raise InvalidSessionStateShape(
            "session state pending_repair_ticket is malformed"
        )
    ticket_queue = state.get("pending_repair_ticket_queue")
    if ticket_queue is not None and (
        not isinstance(ticket_queue, list)
        or any(
            not (isinstance(item, Mapping) if snapshot_encoding else isinstance(item, RepairTicket))
            for item in ticket_queue
        )
    ):
        raise InvalidSessionStateShape(
            "session state pending_repair_ticket_queue is malformed"
        )


def _migrate_legacy_no_applicable_recovery_state(
    session: Any,
    state: MutableMapping[str, Any],
) -> None:
    """Upgrade the former implicit two-recovery policy on exact resume.

    Old checkpoints identify the policy unambiguously as ``max=2`` with a
    multi-turn increment.  Preserve the consumed count, but use the live
    factory's turn-budget-derived authority and one-step increment.  Current
    checkpoints already store a one-step increment, so the legacy signature
    remains unambiguous even when the live session has only two turns.
    """

    try:
        saved_max = int(state.get("max_no_applicable_recoveries", 0) or 0)
        saved_increment = int(
            state.get("no_applicable_recovery_budget_increment", 0) or 0
        )
        live_max = int(getattr(session, "max_no_applicable_recoveries", 0) or 0)
        live_increment = int(
            getattr(session, "no_applicable_recovery_budget_increment", 0) or 0
        )
    except (TypeError, ValueError, OverflowError):
        return
    if saved_max == 2 and saved_increment > 1:
        state["max_no_applicable_recoveries"] = live_max
        state["no_applicable_recovery_budget_increment"] = min(
            1,
            max(0, live_increment),
        )


def _action_specs(session: Any) -> List[JSONDict]:
    specs: List[JSONDict] = []
    runtime_attr_names = {"calls", "call_count", "run_count"}
    for action in getattr(session, "actions", []):
        action_id = str(getattr(action, "id", "") or "")
        if not action_id:
            continue
        attrs: JSONDict = {}
        explicit_config = getattr(action, "replay_config", None)
        if callable(explicit_config):
            converted = _jsonable_config_value(explicit_config())
            if not isinstance(converted, Mapping):
                raise ValueError(
                    f"action {action_id!r} replay_config must be a mapping"
                )
            attrs["replay_config"] = dict(converted)
        for key, value in sorted(dict(getattr(action, "__dict__", {}) or {}).items()):
            if (
                key in {"id", "priority", "cost_estimate_s"}
                or key in runtime_attr_names
                or key.startswith("_")
                or field_is_runtime_capability(key)
            ):
                continue
            jsonable = _jsonable_config_value(value)
            if jsonable is not None:
                attrs[str(key)] = jsonable
        spec = {
            "id": action_id,
            "priority": _safe_int(getattr(action, "priority", 0), default=0),
            "cost_estimate_s": float(
                getattr(action, "cost_estimate_s", 0.0) or 0.0
            ),
            "class": type(action).__name__,
            "attrs": attrs,
        }
        # A small number of actions expose execution-pacing knobs whose
        # values must affect the live scheduler but not deterministic replay
        # identity. Let those actions name the exact excluded leaves.
        for raw_path in (
            getattr(action, "REPLAY_OPERATIONAL_SPEC_PATHS", ()) or ()
        ):
            path = tuple(
                part for part in str(raw_path or "").split(".") if part
            )
            if not path:
                continue
            owner: Any = spec
            for part in path[:-1]:
                if not isinstance(owner, dict) or part not in owner:
                    owner = None
                    break
                owner = owner[part]
            if isinstance(owner, dict):
                owner.pop(path[-1], None)
        specs.append(spec)
    return specs


def _action_runtime_states(session: Any) -> JSONDict:
    """Capture explicitly exported provider-free action cursors."""

    states: JSONDict = {}
    for action in getattr(session, "actions", []):
        action_id = str(getattr(action, "id", "") or "").strip()
        export = getattr(action, "scheduler_runtime_state", None)
        if not action_id or not callable(export):
            continue
        prepare = getattr(action, "prepare_scheduler_runtime_state", None)
        if callable(prepare):
            prepare(session)
        converted = _jsonable_config_value(export())
        if not isinstance(converted, Mapping):
            raise ValueError(
                f"action {action_id!r} scheduler_runtime_state must be a mapping"
            )
        states[action_id] = {
            "class": type(action).__name__,
            "state": dict(converted),
        }
    return states


def _action_specs_compatibility(
    saved_specs: Any,
    live_specs: Any,
) -> tuple[bool, tuple[str, ...]]:
    """Require exact action identity for deterministic replay."""

    return (list(saved_specs or []) == list(live_specs or []), ())


_UNSUPPORTED_CONFIG_VALUE = object()


def _jsonable_config_value(value: Any) -> Any:
    converted = _jsonable_config_value_inner(value)
    return None if converted is _UNSUPPORTED_CONFIG_VALUE else converted


def _jsonable_config_value_inner(value: Any) -> Any:
    if value is None or type(value) in {str, int, float, bool}:
        return value
    if is_dataclass(value) and not isinstance(value, type):
        # ``dataclasses.asdict`` deep-copies every non-dataclass leaf. Action
        # configuration dataclasses may legitimately hold live clients,
        # metering controllers, locks, or subprocess handles; attempting to
        # pickle those while merely computing a compatibility manifest can
        # crash a fresh production run. Walk fields without copying and let
        # the normal unsupported-value sentinel reject runtime-bearing
        # dataclasses. Actions that need a stable projection expose the
        # explicit ``replay_config`` protocol.
        out: JSONDict = {}
        for field in dataclasses.fields(value):
            converted = _jsonable_config_value_inner(
                object.__getattribute__(value, field.name)
            )
            if converted is _UNSUPPORTED_CONFIG_VALUE:
                return _UNSUPPORTED_CONFIG_VALUE
            out[str(field.name)] = converted
        return out
    if isinstance(value, (list, tuple)):
        out = []
        iterator = (
            list.__iter__(value)
            if isinstance(value, list)
            else tuple.__iter__(value)
        )
        for item in iterator:
            converted = _jsonable_config_value_inner(item)
            if converted is _UNSUPPORTED_CONFIG_VALUE:
                return _UNSUPPORTED_CONFIG_VALUE
            out.append(converted)
        return out
    source: Optional[dict[Any, Any]] = None
    if isinstance(value, dict):
        source = value
    elif type(value) is types.MappingProxyType:
        try:
            source = mappingproxy_backing_dict(value)
        except TypeError:
            return _UNSUPPORTED_CONFIG_VALUE
    if source is not None:
        out: JSONDict = {}
        for key, item in sorted(
            tuple(dict.items(source)),
            key=lambda pair: str(pair[0]),
        ):
            converted = _jsonable_config_value_inner(item)
            if converted is _UNSUPPORTED_CONFIG_VALUE:
                return _UNSUPPORTED_CONFIG_VALUE
            out[str(key)] = converted
        return out
    return _UNSUPPORTED_CONFIG_VALUE


def _compact_proof_state_record(proof_state: Any) -> JSONDict:
    if proof_state is None:
        return {}
    try:
        nodes = getattr(proof_state, "nodes", None)
        if not isinstance(nodes, dict):
            return {"snapshot_status": "compact_unavailable"}
        root_node_id = str(getattr(proof_state, "root_node_id", "root") or "root")
        frontier = []
        for node_id, node in nodes.items():
            status = str(getattr(node, "status", "") or "")
            if status in {"open", "blocked"}:
                frontier.append(str(node_id))
            if len(frontier) >= 8:
                break
        return {
            "snapshot_status": "compact_ok",
            "root_node_id": root_node_id,
            "node_count": len(nodes),
            "open_nodes": sum(
                1
                for node in nodes.values()
                if str(getattr(node, "status", "") or "") == "open"
            ),
            "proved_nodes": sum(
                1
                for node in nodes.values()
                if str(getattr(node, "status", "") or "") == "proved"
            ),
            "frontier": frontier,
            "work_frontier": [],
            "work_frontier_status": "not_materialized_in_live_snapshot",
        }
    except Exception as exc:  # noqa: BLE001 - replay capture must not perturb runs
        return {
            "snapshot_status": "failed",
            "snapshot_error": f"{type(exc).__name__}: {exc}",
        }


def _snapshot_has_nested_failure(snapshot: Mapping[str, Any]) -> bool:
    proof_state = snapshot.get("proof_state")
    return (
        isinstance(proof_state, Mapping)
        and str(proof_state.get("snapshot_status") or "") == "failed"
    )


def scheduler_snapshot(
    session: Any,
    *,
    case_id: str = "",
    expected: Optional[Mapping[str, Any]] = None,
    include_proof_state: bool = True,
    compact_proof_state: bool = False,
) -> JSONDict:
    """Capture the provider-free state needed before ``select_next_action``.

    The snapshot intentionally records scheduler state, not provider or Lean
    internals.  A caller must still supply a session with the desired action
    registry and proof-state object before replaying the selection.
    """

    session_state: JSONDict = {
        key: getattr(session, key)
        for key in _SESSION_SCALAR_STATE_KEYS
        if hasattr(session, key)
    }
    for key in _SESSION_SET_STATE_KEYS:
        if hasattr(session, key):
            session_state[key] = _jsonable_tuple_set(getattr(session, key))
    session_state["theory_context_hit_need_ids"] = _jsonable_string_set(
        getattr(session, "theory_context_hit_need_ids", set())
    )
    session_state["durable_progress_signatures_seen"] = _jsonable_string_set(
        getattr(session, "durable_progress_signatures_seen", set())
    )
    session_state["static_prepass_headroom_signatures_seen"] = (
        _jsonable_string_set(
            getattr(session, "static_prepass_headroom_signatures_seen", set())
        )
    )
    session_state["model_call_deferred_static_action_ids"] = _jsonable_string_set(
        getattr(session, "model_call_deferred_static_action_ids", set())
    )
    session_state["provider_turn_retired_lane_identities"] = (
        _jsonable_string_set(
            getattr(session, "provider_turn_retired_lane_identities", set())
        )
    )
    session_state["recursive_helper_cleanup_continuation_identities"] = (
        _jsonable_string_set(
            getattr(
                session,
                "recursive_helper_cleanup_continuation_identities",
                set(),
            )
        )
    )
    session_state["primary_verifier_continuation_identities"] = (
        _jsonable_string_set(
            getattr(
                session,
                "primary_verifier_continuation_identities",
                set(),
            )
        )
    )
    session_state["paid_tool_continuation_identities"] = (
        _jsonable_string_set(
            getattr(session, "paid_tool_continuation_identities", set())
        )
    )
    session_state["durable_progress_tool_continuation_identities"] = (
        _jsonable_string_set(
            getattr(
                session,
                "durable_progress_tool_continuation_identities",
                set(),
            )
        )
    )
    session_state["identical_no_progress_action_families_seen"] = (
        _jsonable_string_set(
            getattr(
                session,
                "identical_no_progress_action_families_seen",
                set(),
            )
        )
    )
    session_state["theory_attempted_need_ids"] = _jsonable_string_set(
        getattr(session, "theory_attempted_need_ids", set())
    )
    session_state["theory_need_attempt_counts"] = _jsonable_string_int_mapping(
        getattr(session, "theory_need_attempt_counts", {})
    )
    session_state["theory_consumer_bundle_ids_by_need_id"] = (
        _jsonable_string_tuple_mapping(
            getattr(session, "theory_consumer_bundle_ids_by_need_id", {})
        )
    )
    session_state["theory_imported_bundle_ids"] = [
        str(item)
        for item in tuple(getattr(session, "theory_imported_bundle_ids", ()) or ())
    ]
    session_state["theory_need_ids_by_frontier_key"] = (
        _jsonable_tuple_string_mapping(
            getattr(session, "theory_need_ids_by_frontier_key", {})
        )
    )
    if hasattr(session, "materialization_pending_no_applicable_recovery_counts"):
        session_state["materialization_pending_no_applicable_recovery_counts"] = (
            _jsonable_tuple_int_mapping(
                getattr(
                    session,
                    "materialization_pending_no_applicable_recovery_counts",
                )
            )
        )
    if hasattr(session, "frontier_progress_retry_counts"):
        session_state["frontier_progress_retry_counts"] = (
            _jsonable_tuple_int_mapping(
                getattr(session, "frontier_progress_retry_counts")
            )
        )
    if hasattr(session, "model_call_deferred_frontier_retry_counts"):
        session_state["model_call_deferred_frontier_retry_counts"] = (
            _jsonable_tuple_int_mapping(
                getattr(session, "model_call_deferred_frontier_retry_counts")
            )
        )
    if hasattr(session, "model_call_deferred_frontier_action_metadata"):
        session_state["model_call_deferred_frontier_action_metadata"] = (
            _jsonable_tuple_dict_mapping(
                getattr(session, "model_call_deferred_frontier_action_metadata")
            )
        )
    if hasattr(session, "materialization_pending_frontier_action_logical_keys"):
        session_state["materialization_pending_frontier_action_logical_keys"] = (
            _jsonable_tuple_tuple_mapping(
                getattr(session, "materialization_pending_frontier_action_logical_keys")
            )
        )
    for key in _SESSION_MAPPING_STATE_KEYS:
        value = getattr(session, key, None)
        if isinstance(value, Mapping):
            if key == "policy_repair_redirect_selected_record" and not value:
                continue
            session_state[key] = dict(value)
    for key in _SESSION_SEQUENCE_STATE_KEYS:
        value = getattr(session, key, None)
        if isinstance(value, (list, tuple)):
            session_state[key] = list(value)
    if hasattr(session, "no_applicable_recovery_action_ids"):
        session_state["no_applicable_recovery_action_ids"] = [
            str(item)
            for item in tuple(getattr(session, "no_applicable_recovery_action_ids") or ())
        ]
    ticket = getattr(session, "pending_repair_ticket", None)
    if isinstance(ticket, RepairTicket):
        session_state["pending_repair_ticket"] = _repair_ticket_to_record(ticket)
    queued_tickets = [
        _repair_ticket_to_record(item)
        for item in list(getattr(session, "pending_repair_ticket_queue", []) or [])
        if isinstance(item, RepairTicket)
    ]
    if queued_tickets:
        session_state["pending_repair_ticket_queue"] = queued_tickets
    proof_state = getattr(session, "proof_state", None)
    proof_state_record: JSONDict = {}
    if include_proof_state:
        if compact_proof_state:
            proof_state_record = _compact_proof_state_record(proof_state)
        else:
            to_record = getattr(proof_state, "to_record", None)
            if callable(to_record):
                try:
                    candidate = to_record()
                    if isinstance(candidate, dict):
                        proof_state_record = candidate
                except Exception as exc:  # noqa: BLE001 - replay capture must not perturb runs
                    proof_state_record = {
                        "snapshot_status": "failed",
                        "snapshot_error": f"{type(exc).__name__}: {exc}",
                    }
    replay_state_gaps: List[str] = []
    if getattr(session, "last_turn_extraction", None) is not None:
        replay_state_gaps.append(
            "last_turn_extraction is present but is not serialized by this snapshot"
        )
    if include_proof_state and compact_proof_state and proof_state is not None:
        if callable(getattr(proof_state, "work_frontier", None)):
            replay_state_gaps.append(
                "compact proof_state omits work_frontier; scheduler replay requires "
                "a matching external proof_state"
            )
        if str(proof_state_record.get("snapshot_status") or "") == "failed":
            replay_state_gaps.append("proof_state snapshot failed")
    controller = getattr(session, "cost_controller", None)
    cost_budget_record: JSONDict = {"enabled": False, "snapshot_status": "absent"}
    if controller is not None and callable(getattr(controller, "summary", None)):
        try:
            cost_budget_record = dict(controller.summary())
            cost_budget_record["enabled"] = bool(
                cost_budget_record.get("llm_cost_budget_enabled")
            )
            cost_budget_record["snapshot_status"] = "recorded"
        except Exception as exc:  # noqa: BLE001 - replay capture must not perturb runs
            cost_budget_record = {
                "enabled": False,
                "snapshot_status": "failed",
                "error": f"{type(exc).__name__}: {exc}",
            }
            replay_state_gaps.append("cost budget snapshot failed")
    replay_requires = [
        "MiniSession action registry",
        "matching proof_state/dossier graph when frontier work matters",
    ]
    if (
        getattr(session, "model_call_deferred_frontier_retry_counts", {})
        or getattr(session, "model_call_deferred_static_retry_counts", {})
    ):
        replay_requires.append(
            "matching Lean capability generation for deferred-retry selection"
        )
    return {
        "schema_version": 1,
        "case_id": str(case_id or ""),
        "cutpoint": "pre_select",
        "replay_scope": "scheduler_selection",
        "replay_requires": replay_requires,
        "actions": [
            str(getattr(action, "id", "") or "")
            for action in getattr(session, "actions", [])
        ],
        "action_specs": _action_specs(session),
        "action_runtime_states": _action_runtime_states(session),
        "budgets": {
            str(action_id): _budget_to_record(budget)
            for action_id, budget in dict(getattr(session, "budgets", {}) or {}).items()
            if isinstance(budget, ActionBudget)
        },
        "cost_budget": cost_budget_record,
        "session_state": session_state,
        "proof_state": proof_state_record,
        "replay_state_complete": not replay_state_gaps,
        "replay_state_gaps": replay_state_gaps,
        "expected": dict(expected or {}),
    }


def _capture_scheduler_replay_state(session: Any) -> JSONDict:
    state = scheduler_snapshot(
        session,
        include_proof_state=False,
        compact_proof_state=True,
    )
    state["_selected_work_item"] = getattr(session, "selected_work_item", None)
    state["_selected_work_item_action_id"] = str(
        getattr(session, "selected_work_item_action_id", "") or ""
    )
    state["_selected_work_item_record"] = dict(
        getattr(session, "selected_work_item_record", {}) or {}
    )
    state["_policy_repair_redirect_selected_work_item"] = getattr(
        session,
        "policy_repair_redirect_selected_work_item",
        None,
    )
    state["_recorder"] = getattr(session, "recorder", None)
    state["_on_event"] = getattr(session, "on_event", None)
    state["_repair_ticket_history"] = [
        dict(item)
        for item in list(getattr(session, "repair_ticket_history", []) or [])
        if isinstance(item, Mapping)
    ]
    dossier = getattr(session, "dossier", None)
    tool_metrics = getattr(dossier, "tool_metrics", None)
    if isinstance(tool_metrics, Mapping):
        state["_dossier_tool_metrics"] = dict(tool_metrics)
    return state


def _restore_scheduler_replay_state(session: Any, snapshot: Mapping[str, Any]) -> None:
    apply_scheduler_snapshot(session, snapshot)
    session.selected_work_item = snapshot.get("_selected_work_item")
    session.selected_work_item_action_id = str(
        snapshot.get("_selected_work_item_action_id") or ""
    )
    selected_work_record = dict(
        snapshot.get("_selected_work_item_record") or {}
    )
    sanitize_selected_work = getattr(
        session,
        "_sanitize_selected_work_record_answer_aliases",
        None,
    )
    session.selected_work_item_record = (
        dict(sanitize_selected_work(selected_work_record) or {})
        if callable(sanitize_selected_work)
        else selected_work_record
    )
    session.policy_repair_redirect_selected_work_item = snapshot.get(
        "_policy_repair_redirect_selected_work_item"
    )
    session.recorder = snapshot.get("_recorder")
    session.on_event = snapshot.get("_on_event")
    session.repair_ticket_history = [
        dict(item)
        for item in list(snapshot.get("_repair_ticket_history") or [])
        if isinstance(item, Mapping)
    ]
    dossier = getattr(session, "dossier", None)
    saved_metrics = snapshot.get("_dossier_tool_metrics")
    if isinstance(saved_metrics, Mapping) and hasattr(dossier, "tool_metrics"):
        try:
            dossier.tool_metrics.clear()
            dossier.tool_metrics.update(dict(saved_metrics))
        except Exception:  # noqa: BLE001 - replay restore must be best-effort
            pass


def apply_scheduler_snapshot(session: Any, snapshot: Mapping[str, Any]) -> None:
    """Apply scheduler state from ``scheduler_snapshot`` to a session.

    This is intentionally narrow: it restores selection-related fields and
    budgets, while leaving heavyweight objects such as the action registry,
    provider clients, Lean runner, dossier, and proof_state supplied by the
    test harness or factory.
    """

    if not isinstance(snapshot, Mapping):
        raise InvalidSessionStateShape("scheduler snapshot is malformed")
    raw_state = snapshot.get("session_state", {})
    if not isinstance(raw_state, Mapping):
        raise InvalidSessionStateShape("session state is malformed")
    state = dict(raw_state)
    _migrate_legacy_no_applicable_recovery_state(session, state)
    validate_durable_session_state_shapes(state, snapshot_encoding=True)
    runtime_states = snapshot.get("action_runtime_states", {})
    if runtime_states is not None and not isinstance(runtime_states, Mapping):
        raise InvalidSessionStateShape("action runtime states are malformed")
    actions_by_id = {
        str(getattr(action, "id", "") or ""): action
        for action in getattr(session, "actions", [])
        if str(getattr(action, "id", "") or "")
    }
    raw_budgets = snapshot.get("budgets", {})
    if not isinstance(raw_budgets, Mapping):
        raise InvalidActionBudgetRecord("action budgets are malformed")
    prepared_budgets: Optional[Dict[str, ActionBudget]] = {
        str(action_id): _budget_from_record(record)
        for action_id, record in raw_budgets.items()
    }
    # Resolve registered-action authority before any runtime cursor is
    # mutated. A malformed/raising budget contract must leave the entire
    # snapshot transaction untouched.
    declared_scope = getattr(session, "_declared_action_budget_scope", None)
    declared_ceiling = getattr(
        session,
        "_declared_action_budget_aggregate_seconds",
        None,
    )
    for action in tuple(getattr(session, "actions", ()) or ()):
        budget = prepared_budgets.get(str(getattr(action, "id", "") or ""))
        if budget is None:
            continue
        if callable(declared_scope):
            budget.scope = declared_scope(action)
        if callable(declared_ceiling):
            ceiling = float(declared_ceiling(action) or 0.0)
            if ceiling > 0.0:
                budget.max_aggregate_seconds = ceiling
    # Repair-ticket shape validation is intentionally deeper than the
    # durable-state envelope check: sequence and metadata fields are decoded
    # here, before any action-owned runtime cursor is replaced.  A malformed
    # late field must not turn a rejected snapshot into a partial restore.
    try:
        raw_pending_ticket = state.get("pending_repair_ticket")
        prepared_pending_repair_ticket = (
            _repair_ticket_from_snapshot_record(raw_pending_ticket)
            if raw_pending_ticket is not None
            else None
        )
        prepared_pending_repair_ticket_queue = []
        for raw_ticket in list(state.get("pending_repair_ticket_queue") or []):
            ticket = _repair_ticket_from_snapshot_record(raw_ticket)
            prepared_pending_repair_ticket_queue.append(ticket)
    except (TypeError, ValueError, OverflowError) as exc:
        raise InvalidSessionStateShape(
            "session repair-ticket state is malformed"
        ) from exc
    try:
        # Exercise every remaining persisted collection decoder before the
        # action restore transaction begins.  Some decoders intentionally
        # copy nested metadata; a depth/pathology failure there must reject
        # the snapshot while the live action cursors are still untouched.
        for key in _SESSION_SET_STATE_KEYS:
            _restore_tuple_set(state.get(key) if key in state else [])
        _restore_string_set(state.get("theory_context_hit_need_ids", []))
        _restore_string_set(state.get("durable_progress_signatures_seen", []))
        _restore_string_set(state.get("static_prepass_headroom_signatures_seen", []))
        _restore_string_set(state.get("model_call_deferred_static_action_ids", []))
        prepared_provider_turn_retired_lane_identities = _restore_string_set(
            state.get("provider_turn_retired_lane_identities", [])
        )
        _restore_string_set(
            state.get("recursive_helper_cleanup_continuation_identities", [])
        )
        _restore_string_set(state.get("primary_verifier_continuation_identities", []))
        _restore_string_set(state.get("paid_tool_continuation_identities", []))
        _restore_string_set(
            state.get("durable_progress_tool_continuation_identities", [])
        )
        _restore_string_set(state.get("identical_no_progress_action_families_seen", []))
        _restore_string_set(state.get("theory_attempted_need_ids", []))
        _restore_string_int_mapping(state.get("theory_need_attempt_counts", []))
        _restore_string_tuple_mapping(
            state.get("theory_consumer_bundle_ids_by_need_id", [])
        )
        _restore_string_tuple(state.get("theory_imported_bundle_ids", []))
        _restore_tuple_string_mapping(state.get("theory_need_ids_by_frontier_key", []))
        _restore_tuple_int_mapping(
            state.get("materialization_pending_no_applicable_recovery_counts", [])
        )
        _restore_tuple_int_mapping(state.get("frontier_progress_retry_counts", []))
        _restore_tuple_int_mapping(
            state.get("model_call_deferred_frontier_retry_counts", [])
        )
        _restore_tuple_dict_mapping(
            state.get("model_call_deferred_frontier_action_metadata", [])
        )
        _restore_tuple_tuple_mapping(
            state.get("materialization_pending_frontier_action_logical_keys", [])
        )
        _restore_tuple_set(state.get("fallback_action_ids", []))
    except (TypeError, ValueError, OverflowError, RecursionError) as exc:
        raise InvalidSessionStateShape("session collection state is malformed") from exc
    prior_runtime_states: Dict[str, Any] = {}
    restore_plan: List[tuple[str, Any, Any, Any]] = []
    applied: List[tuple[str, Any, Any, Any]] = []
    prior_answer_safe_recheck_pending = copy.deepcopy(
        getattr(session, "answer_safe_recheck_pending", None)
    )
    conv = getattr(session, "conv", None)
    prior_provider_quantum_state = copy.deepcopy(
        getattr(conv, "_provider_call_quantum_state", None)
    )
    had_provider_quantum_state = bool(
        conv is not None and hasattr(conv, "_provider_call_quantum_state")
    )
    prior_provider_repair_cycle = copy.deepcopy(
        getattr(conv, "_provider_turn_repair_cycle_identity", None)
    )
    had_provider_repair_cycle = bool(
        conv is not None
        and hasattr(conv, "_provider_turn_repair_cycle_identity")
    )
    prior_conversation_history = copy.deepcopy(
        getattr(conv, "history", None)
    )
    prior_selected_work_item = getattr(session, "selected_work_item", None)
    prior_selected_work_item_action_id = str(
        getattr(session, "selected_work_item_action_id", "") or ""
    )
    prior_selected_work_item_record = copy.deepcopy(
        dict(getattr(session, "selected_work_item_record", {}) or {})
    )
    prior_selected_proof_idea_context_digest = copy.deepcopy(
        getattr(session, "_selected_proof_idea_context_digest", None)
    )
    had_selected_proof_idea_context_digest = hasattr(
        session,
        "_selected_proof_idea_context_digest",
    )
    prior_pending_repair_ticket = getattr(session, "pending_repair_ticket", None)
    prior_pending_repair_ticket_queue = list(
        getattr(session, "pending_repair_ticket_queue", []) or []
    )
    prior_repair_ticket_selected_id = str(
        getattr(session, "_repair_ticket_selected_id", "") or ""
    )
    had_provider_quantum_selected_work_restored = hasattr(
        session,
        "_provider_quantum_selected_work_restored",
    )
    prior_provider_quantum_selected_work_restored = bool(
        getattr(session, "_provider_quantum_selected_work_restored", False)
    )
    prior_provider_turn_retired_lane_identities = set(
        getattr(session, "provider_turn_retired_lane_identities", set()) or set()
    )
    try:
        session.pending_repair_ticket = prepared_pending_repair_ticket
        session.pending_repair_ticket_queue = list(
            prepared_pending_repair_ticket_queue
        )
        restored_repair_ticket_selected_id = str(
            state.get("_repair_ticket_selected_id") or ""
        )
        active_repair_ticket_id = str(
            getattr(prepared_pending_repair_ticket, "ticket_id", "") or ""
        )
        session._repair_ticket_selected_id = (
            restored_repair_ticket_selected_id
            if restored_repair_ticket_selected_id == active_repair_ticket_id
            else ""
        )
        # Non-refundable provider retirement authenticates action-owned
        # checkpoints. Restore it before any action publishes a checkpoint
        # into the shared Conversation or selected-work mirror.
        session.provider_turn_retired_lane_identities = set(
            prepared_provider_turn_retired_lane_identities
        )
        for action_id, raw_record in dict(runtime_states or {}).items():
            if not isinstance(raw_record, Mapping):
                raise InvalidSessionStateShape(
                    f"action runtime state {action_id!r} is malformed"
                )
            action = actions_by_id.get(str(action_id or ""))
            if action is None:
                continue
            expected_class = str(raw_record.get("class") or "")
            if expected_class and expected_class != type(action).__name__:
                raise InvalidSessionStateShape(
                    f"action runtime state {action_id!r} has incompatible class"
                )
            restore = getattr(action, "apply_scheduler_runtime_state", None)
            export = getattr(action, "scheduler_runtime_state", None)
            if not callable(restore) or not callable(export):
                raise InvalidSessionStateShape(
                    f"action runtime state {action_id!r} has no restore contract"
                )
            clean_action_id = str(action_id or "")
            prior_runtime_states[clean_action_id] = copy.deepcopy(export())
            restore_plan.append(
                (clean_action_id, action, restore, raw_record.get("state"))
            )
        session.answer_safe_recheck_pending = None
        for record in restore_plan:
            action_id, action, restore, state_to_restore = record
            applied.append(record)
            restore(state_to_restore)
            synchronize = getattr(
                action,
                "synchronize_scheduler_runtime_state",
                None,
            )
            if callable(synchronize):
                synchronize(session)
    except BaseException as primary_error:
        rollback_errors: List[BaseException] = []
        for action_id, _action, restore, _state in reversed(applied):
            prior_state = prior_runtime_states.get(action_id)
            if prior_state is None:
                continue
            try:
                restore(prior_state)
            except BaseException as rollback_error:
                rollback_errors.append(rollback_error)
        try:
            session.answer_safe_recheck_pending = (
                prior_answer_safe_recheck_pending
            )
            session.selected_work_item = prior_selected_work_item
            session.selected_work_item_action_id = (
                prior_selected_work_item_action_id
            )
            session.selected_work_item_record = prior_selected_work_item_record
        except BaseException as rollback_error:
            rollback_errors.append(rollback_error)
        try:
            if had_selected_proof_idea_context_digest:
                session._selected_proof_idea_context_digest = (
                    prior_selected_proof_idea_context_digest
                )
            elif hasattr(session, "_selected_proof_idea_context_digest"):
                delattr(session, "_selected_proof_idea_context_digest")
        except BaseException as rollback_error:
            rollback_errors.append(rollback_error)
        try:
            session.pending_repair_ticket = prior_pending_repair_ticket
            session.pending_repair_ticket_queue = prior_pending_repair_ticket_queue
            session._repair_ticket_selected_id = prior_repair_ticket_selected_id
        except BaseException as rollback_error:
            rollback_errors.append(rollback_error)
        try:
            if had_provider_quantum_selected_work_restored:
                session._provider_quantum_selected_work_restored = (
                    prior_provider_quantum_selected_work_restored
                )
            elif hasattr(session, "_provider_quantum_selected_work_restored"):
                delattr(session, "_provider_quantum_selected_work_restored")
        except BaseException as rollback_error:
            rollback_errors.append(rollback_error)
        try:
            session.provider_turn_retired_lane_identities = set(
                prior_provider_turn_retired_lane_identities
            )
        except BaseException as rollback_error:
            rollback_errors.append(rollback_error)
        if conv is not None:
            try:
                if had_provider_quantum_state:
                    conv._provider_call_quantum_state = prior_provider_quantum_state
                elif hasattr(conv, "_provider_call_quantum_state"):
                    delattr(conv, "_provider_call_quantum_state")
                if had_provider_repair_cycle:
                    conv._provider_turn_repair_cycle_identity = (
                        prior_provider_repair_cycle
                    )
                elif hasattr(conv, "_provider_turn_repair_cycle_identity"):
                    delattr(conv, "_provider_turn_repair_cycle_identity")
                if prior_conversation_history is not None:
                    conv.history = prior_conversation_history
            except BaseException as rollback_error:
                rollback_errors.append(rollback_error)
        for rollback_error in rollback_errors:
            primary_error.add_note(
                "scheduler snapshot rollback also failed: "
                f"{type(rollback_error).__name__}: {rollback_error}"
            )
        raise
    for key in _SESSION_SCALAR_STATE_KEYS:
        if key == "_repair_ticket_selected_id":
            # Restored transactionally above only after authenticating it
            # against the exact active ticket.
            continue
        if key in state:
            setattr(session, key, state[key])
        elif key in {
            "provider_calls_completed_total",
            "provider_dispatches_started_total",
        }:
            # Legacy snapshots predate these cumulative exposure ledgers.
            # Missing authority must restore empty rather than retain stale
            # values from a reused session object.
            setattr(session, key, 0)
    for key in _SESSION_SET_STATE_KEYS:
        setattr(session, key, _restore_tuple_set(state.get(key) if key in state else []))
    session.theory_context_hit_need_ids = _restore_string_set(
        state.get("theory_context_hit_need_ids", [])
    )
    session.durable_progress_signatures_seen = _restore_string_set(
        state.get("durable_progress_signatures_seen", [])
    )
    session.static_prepass_headroom_signatures_seen = _restore_string_set(
        state.get("static_prepass_headroom_signatures_seen", [])
    )
    session.model_call_deferred_static_action_ids = _restore_string_set(
        state.get("model_call_deferred_static_action_ids", [])
    )
    session.provider_turn_retired_lane_identities = _restore_string_set(
        state.get("provider_turn_retired_lane_identities", [])
    )
    session.recursive_helper_cleanup_continuation_identities = (
        _restore_string_set(
            state.get(
                "recursive_helper_cleanup_continuation_identities",
                [],
            )
        )
    )
    session.primary_verifier_continuation_identities = _restore_string_set(
        state.get("primary_verifier_continuation_identities", [])
    )
    session.paid_tool_continuation_identities = _restore_string_set(
        state.get("paid_tool_continuation_identities", [])
    )
    session.durable_progress_tool_continuation_identities = (
        _restore_string_set(
            state.get("durable_progress_tool_continuation_identities", [])
        )
    )
    session.identical_no_progress_action_families_seen = _restore_string_set(
        state.get("identical_no_progress_action_families_seen", [])
    )
    session.theory_attempted_need_ids = _restore_string_set(
        state.get("theory_attempted_need_ids", [])
    )
    session.theory_need_attempt_counts = _restore_string_int_mapping(
        state.get("theory_need_attempt_counts", [])
    )
    session.theory_consumer_bundle_ids_by_need_id = (
        _restore_string_tuple_mapping(
            state.get("theory_consumer_bundle_ids_by_need_id", [])
        )
    )
    session.theory_imported_bundle_ids = _restore_string_tuple(
        state.get("theory_imported_bundle_ids", [])
    )
    session.theory_need_ids_by_frontier_key = _restore_tuple_string_mapping(
        state.get("theory_need_ids_by_frontier_key", [])
    )
    if "materialization_pending_no_applicable_recovery_counts" in state:
        setattr(
            session,
            "materialization_pending_no_applicable_recovery_counts",
            _restore_tuple_int_mapping(
                state.get("materialization_pending_no_applicable_recovery_counts")
            ),
        )
    else:
        legacy_recovered = _restore_tuple_set(
            state.get("materialization_pending_no_applicable_recovery_logical_keys")
            if "materialization_pending_no_applicable_recovery_logical_keys" in state
            else []
        )
        setattr(
            session,
            "materialization_pending_no_applicable_recovery_counts",
            {key: 1 for key in legacy_recovered},
        )
    setattr(
        session,
        "frontier_progress_retry_counts",
        _restore_tuple_int_mapping(
            state.get("frontier_progress_retry_counts")
            if "frontier_progress_retry_counts" in state
            else []
        ),
    )
    setattr(
        session,
        "model_call_deferred_frontier_retry_counts",
        _restore_tuple_int_mapping(
            state.get("model_call_deferred_frontier_retry_counts")
            if "model_call_deferred_frontier_retry_counts" in state
            else []
        ),
    )
    setattr(
        session,
        "model_call_deferred_frontier_action_metadata",
        _restore_tuple_dict_mapping(
            state.get("model_call_deferred_frontier_action_metadata")
            if "model_call_deferred_frontier_action_metadata" in state
            else []
        ),
    )
    setattr(
        session,
        "materialization_pending_frontier_action_logical_keys",
        _restore_tuple_tuple_mapping(
            state.get("materialization_pending_frontier_action_logical_keys")
            if "materialization_pending_frontier_action_logical_keys" in state
            else []
        ),
    )
    for key in _SESSION_MAPPING_STATE_KEYS:
        if key in state and isinstance(state.get(key), Mapping):
            setattr(session, key, dict(state.get(key) or {}))
        elif key in {
            "no_progress_semantic_signature_counts",
            "no_progress_semantic_signature_action_families",
            "proof_work_no_progress_attempt_counts",
            "proof_work_no_progress_peak_attempt_counts",
            "proof_work_no_progress_last_signatures",
            "proof_work_no_progress_signature_history",
            "proof_work_root_alias_identities_by_base",
            "proof_work_closed_root_alias_identities",
        }:
            setattr(session, key, {})
    for key in _SESSION_SEQUENCE_STATE_KEYS:
        if key in state and isinstance(state.get(key), (list, tuple)):
            setattr(session, key, list(state.get(key) or []))
        elif key in {
            "no_progress_semantic_signature_order",
            "proof_work_no_progress_attempt_order",
        }:
            setattr(session, key, [])
    if "fallback_action_ids" in state:
        setattr(
            session,
            "fallback_action_ids",
            {item[0] for item in _restore_tuple_set(state.get("fallback_action_ids")) if item},
        )
    if "no_applicable_recovery_action_ids" in state:
        setattr(
            session,
            "no_applicable_recovery_action_ids",
            tuple(str(item) for item in list(state.get("no_applicable_recovery_action_ids") or [])),
        )
    if "pending_repair_ticket" in state:
        setattr(
            session,
            "pending_repair_ticket",
            prepared_pending_repair_ticket,
        )
    else:
        setattr(session, "pending_repair_ticket", None)
    if "pending_repair_ticket_queue" in state:
        setattr(
            session,
            "pending_repair_ticket_queue",
            prepared_pending_repair_ticket_queue,
        )
    else:
        setattr(session, "pending_repair_ticket_queue", [])
    if prepared_budgets is not None:
        session.budgets = prepared_budgets
    policy_record = state.get("policy_repair_redirect_selected_record")
    if isinstance(policy_record, Mapping) and policy_record:
        action_id = str(state.get("policy_repair_redirect_selected_action_id") or "")
        session.policy_repair_redirect_selected_work_item = SimpleNamespace(
            **dict(policy_record)
        )
        session.policy_repair_redirect_selected_action_id = action_id
        session.policy_repair_redirect_selected_record = dict(policy_record)
    else:
        session.policy_repair_redirect_selected_work_item = None
        session.policy_repair_redirect_selected_action_id = ""
        session.policy_repair_redirect_selected_record = {}
    clear_selected = getattr(session, "_clear_selected_work_item", None)
    provider_quantum_selected_work_restored = bool(
        getattr(session, "_provider_quantum_selected_work_restored", False)
    )
    if callable(clear_selected) and not provider_quantum_selected_work_restored:
        clear_selected()
    if hasattr(session, "_provider_quantum_selected_work_restored"):
        delattr(session, "_provider_quantum_selected_work_restored")
    for key in _OPTIONAL_REPLAY_ATTR_KEYS:
        if key not in state and hasattr(session, key):
            try:
                delattr(session, key)
            except AttributeError:
                pass


def replay_scheduler_selection(session: Any, snapshot: Mapping[str, Any]) -> JSONDict:
    """Apply a pre-selection snapshot and run ``select_next_action`` once."""

    expected = snapshot.get("expected") if isinstance(snapshot, Mapping) else {}
    if not isinstance(expected, Mapping):
        expected = {}
    expected_action_id = str(expected.get("action_id") or "")
    expected_selected = expected.get("selected_work_item")
    replay_asserted = bool(expected_action_id or isinstance(expected_selected, Mapping))
    snapshot_actions = [
        str(action_id or "")
        for action_id in list(snapshot.get("actions") or [])
        if str(action_id or "")
    ] if isinstance(snapshot, Mapping) else []
    actual_actions = [
        str(getattr(action_obj, "id", "") or "")
        for action_obj in getattr(session, "actions", [])
        if str(getattr(action_obj, "id", "") or "")
    ]
    snapshot_action_specs = (
        list(snapshot.get("action_specs") or [])
        if isinstance(snapshot, Mapping)
        else []
    )
    actual_action_specs = _action_specs(session)
    state_complete = bool(
        snapshot.get("replay_state_complete", True)
        if isinstance(snapshot, Mapping)
        else True
    )
    replay_state_gaps = (
        list(snapshot.get("replay_state_gaps") or [])
        if isinstance(snapshot, Mapping)
        else []
    )

    def refused(reason: str) -> JSONDict:
        gaps = list(replay_state_gaps)
        if reason:
            gaps.append(reason)
        return {
            "schema_version": 1,
            "case_id": (
                str(snapshot.get("case_id") or "")
                if isinstance(snapshot, Mapping)
                else ""
            ),
            "cutpoint": "pre_select",
            "expected_action_id": expected_action_id,
            "actual_action_id": "",
            "replay_asserted": replay_asserted,
            "replay_state_complete": False,
            "replay_state_gaps": gaps,
            "action_registry_match": False,
            "snapshot_actions": snapshot_actions,
            "actual_actions": actual_actions,
            "action_specs_match": False,
            "snapshot_action_specs": snapshot_action_specs,
            "actual_action_specs": actual_action_specs,
            "missing_actions": [
                action_id for action_id in snapshot_actions if action_id not in actual_actions
            ],
            "unexpected_actions": [
                action_id for action_id in actual_actions if action_id not in snapshot_actions
            ],
            "selected_work_item": {},
            "ok": False,
        }

    if not isinstance(snapshot, Mapping):
        return refused("snapshot is not a mapping")
    if _safe_int(snapshot.get("schema_version"), default=0) != 1:
        return refused("unsupported scheduler snapshot schema_version")
    if str(snapshot.get("cutpoint") or "") != "pre_select":
        return refused("unsupported scheduler snapshot cutpoint")
    if str(snapshot.get("replay_scope") or "") != "scheduler_selection":
        return refused("unsupported scheduler snapshot replay_scope")
    if not state_complete:
        return refused("scheduler snapshot state is incomplete")
    cost_budget = snapshot.get("cost_budget")
    if isinstance(cost_budget, Mapping) and bool(
        cost_budget.get("llm_cost_budget_exhausted")
    ):
        reason = str(
            cost_budget.get("llm_cost_budget_terminal_reason")
            or "llm_cost_budget_exhausted"
        )
        return refused(f"scheduler snapshot cost budget exhausted: {reason}")

    # Run selection on an isolated coordinator, not on the live session and
    # then attempt to enumerate every mutation for rollback.  Selection owns
    # mutable scheduler fields and action applicability may mutate action-local
    # cooldown/cache state.  New fields must therefore default to isolation.
    shared_runtime_keys = {
        "lean",
        "prover_client",
        "refiner_client",
        "searcher",
        "proof_cache",
        "cost_controller",
        "_static_action_receipt_authority",
        "_recursive_lane_authority",
        "_recursive_conversation_lane_ledger",
    }
    # Replay deliberately suppresses external observability.  Do not clone
    # these capabilities first: a production RunRecorder owns open streams
    # and is correctly not deepcopyable.
    disabled_runtime_keys = {"recorder", "on_event"}
    try:
        replay_session = copy.copy(session)
        # Preserve self/cyclic references while ensuring mutable parent
        # session scope is cloned rather than shared with the live search.
        deepcopy_memo: Dict[int, Any] = {id(session): replay_session}
        for key in shared_runtime_keys:
            value = getattr(session, key, None)
            if value is not None:
                deepcopy_memo[id(value)] = value
        for key in disabled_runtime_keys:
            value = getattr(session, key, None)
            if value is not None:
                deepcopy_memo[id(value)] = None
        for key, value in vars(session).items():
            if key in disabled_runtime_keys:
                setattr(replay_session, key, None)
            elif key in shared_runtime_keys:
                setattr(replay_session, key, value)
            else:
                # Reuse one memo for the entire object graph.  Production
                # actions retain aliases to session-level clients/searchers;
                # their local mutable fields must be cloned without trying to
                # clone those runtime capabilities or breaking alias identity.
                setattr(replay_session, key, copy.deepcopy(value, deepcopy_memo))
    except Exception as exc:  # noqa: BLE001 - diagnostic replay fails closed
        return refused(
            "scheduler replay isolation failed: "
            f"{type(exc).__name__}: {exc}"
        )
    try:
        apply_scheduler_snapshot(replay_session, snapshot)
        action = replay_session.select_next_action()
        actual_action_id = str(getattr(action, "id", "") or "")
        selected_work_item = dict(
            getattr(replay_session, "selected_work_item_record", {}) or {}
        )
    except Exception as exc:  # noqa: BLE001 - diagnostic replay fails closed
        return refused(
            "scheduler replay selection failed: "
            f"{type(exc).__name__}: {exc}"
        )
    ok = replay_asserted
    if expected_action_id:
        ok = ok and actual_action_id == expected_action_id
    if isinstance(expected_selected, Mapping):
        for key, value in expected_selected.items():
            ok = ok and selected_work_item.get(key) == value
    registry_match = True
    missing_actions: List[str] = []
    unexpected_actions: List[str] = []
    if snapshot_actions:
        registry_match = snapshot_actions == actual_actions
        missing_actions = [
            action_id for action_id in snapshot_actions if action_id not in actual_actions
        ]
        unexpected_actions = [
            action_id for action_id in actual_actions if action_id not in snapshot_actions
        ]
        ok = ok and registry_match
    action_specs_match = True
    action_spec_migrations: tuple[str, ...] = ()
    if snapshot_action_specs:
        action_specs_match, action_spec_migrations = _action_specs_compatibility(
            snapshot_action_specs,
            actual_action_specs,
        )
        ok = ok and action_specs_match
    return {
        "schema_version": 1,
        "case_id": str(snapshot.get("case_id") or "") if isinstance(snapshot, Mapping) else "",
        "cutpoint": "pre_select",
        "expected_action_id": expected_action_id,
        "actual_action_id": actual_action_id,
        "replay_asserted": replay_asserted,
        "replay_state_complete": state_complete,
        "replay_state_gaps": replay_state_gaps,
        "action_registry_match": registry_match,
        "snapshot_actions": snapshot_actions,
        "actual_actions": actual_actions,
        "action_specs_match": action_specs_match,
        "action_spec_migrations": list(action_spec_migrations),
        "snapshot_action_specs": snapshot_action_specs,
        "actual_action_specs": actual_action_specs,
        "missing_actions": missing_actions,
        "unexpected_actions": unexpected_actions,
        "selected_work_item": selected_work_item,
        "ok": ok,
    }


def _safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _safe_float(value: Any) -> Optional[float]:
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _is_true(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "y"}
    return False


def _read_json(path: Path) -> JSONDict:
    if not path.exists():
        return {}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return raw if isinstance(raw, dict) else {}


def load_turn_trace(run_dir: str | Path) -> TraceLoadResult:
    """Load ``turns.jsonl`` records with malformed-line diagnostics.

    The recorder is append-only and live runs may end mid-write.  A replay
    harness should be robust to that instead of failing the entire analysis.
    """

    path = Path(run_dir) / "turns.jsonl"
    events: List[JSONDict] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return TraceLoadResult(events=[], missing_trace=True)
    except UnicodeDecodeError:
        return TraceLoadResult(events=[], malformed_line_count=1)
    malformed = 0
    for line in lines:
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            malformed += 1
            continue
        if isinstance(record, dict):
            events.append(record)
        else:
            malformed += 1
    return TraceLoadResult(events=events, malformed_line_count=malformed)


def load_turn_events(run_dir: str | Path) -> List[JSONDict]:
    """Load ``turns.jsonl`` records, tolerating malformed live-tail lines."""

    return load_turn_trace(run_dir).events


def _event_text(record: Mapping[str, Any]) -> str:
    keys = (
        "phase",
        "verdict",
        "reason",
        "failure_reason",
        "action_id",
        "lean_verdict",
        "lean_error_type",
        "rejection_reason",
        "session_scope",
    )
    return " ".join(str(record.get(key) or "") for key in keys).lower()


def _is_answer_unsafe_marker(value: Any) -> bool:
    text = str(value or "").strip().lower()
    if not text:
        return False
    normalized = (
        text.replace("-", "_")
        .replace(" ", "_")
        .replace(":", "_")
        .replace("/", "_")
    )
    if "answer_unsafe" not in normalized:
        return False
    if any(
        marker in normalized
        for marker in (
            "answer_unsafe_target_quarantined",
            "claim_rejected_answer_unsafe_statement",
            "claim_rejected_answer_unsafe_dependency",
        )
    ):
        return False
    if any(
        marker in normalized
        for marker in (
            "no_answer_unsafe",
            "not_answer_unsafe",
            "without_answer_unsafe",
            "answer_unsafe_free",
        )
    ):
        return False
    return True


def _is_answer_unsafe_summary_policy_key(key: Any) -> bool:
    normalized = (
        str(key or "")
        .strip()
        .lower()
        .replace("-", "_")
        .replace(" ", "_")
        .replace(":", "_")
        .replace("/", "_")
    )
    if "answer_unsafe" not in normalized:
        return False
    if any(
        marker in normalized
        for marker in (
            "answer_unsafe_skipped",
            "answer_unsafe_skip",
            "answer_unsafe_target_quarantined",
            "answer_unsafe_quarantined",
            "answer_unsafe_quarantine",
            "claim_rejected_answer_unsafe",
            "answer_unsafe_dependency",
            "answer_unsafe_statement",
        )
    ):
        return False
    return _is_answer_unsafe_marker(normalized)


def _summary_root_certificate(summary: Mapping[str, Any]) -> Mapping[str, Any]:
    raw = summary.get("root_proof_certificate")
    if isinstance(raw, Mapping):
        return raw
    dossier = summary.get("proof_dossier")
    if isinstance(dossier, Mapping):
        raw = dossier.get("root_proof_certificate")
        if isinstance(raw, Mapping):
            return raw
    return {}


def _summary_has_root_solution_evidence(summary: Mapping[str, Any]) -> bool:
    certificate = _summary_root_certificate(summary)
    if str(certificate.get("proof") or "").strip():
        return True
    if str(summary.get("final_proof") or "").strip():
        return True
    dossier = summary.get("proof_dossier")
    if isinstance(dossier, Mapping):
        if str(dossier.get("final_proof_hash") or "").strip():
            return True
        if str(dossier.get("final_proof") or "").strip():
            return True
    return False


def _summary_kernel_rejected_export(summary: Mapping[str, Any]) -> bool:
    return bool(
        _is_true(summary.get("mini_solved_export_kernel_rejected"))
        or _is_true(summary.get("solved_export_kernel_rejected"))
        or _is_true(summary.get("kernel_rejected"))
    )


def _summary_export_counter_positive(summary: Mapping[str, Any], *keys: str) -> bool:
    return policy_counter_positive(summary, *keys)


def _summary_export_counter_zero_or_absent(
    summary: Mapping[str, Any],
    *keys: str,
) -> bool:
    return policy_counter_zero_or_absent(summary, *keys)


def _summary_export_status_values(summary: Mapping[str, Any]) -> tuple[str, ...]:
    return policy_export_status_values(summary)


def _summary_verified_solved_export(summary: Mapping[str, Any]) -> bool:
    return policy_solved_export_verified_payload(summary)


def _summary_unverified_solved_export(summary: Mapping[str, Any]) -> bool:
    if not policy_export_boundary_present(summary):
        return False
    if _summary_verified_solved_export(summary):
        return False
    return True


def _is_root_solved(events: Sequence[Mapping[str, Any]], summary: Mapping[str, Any]) -> bool:
    if _summary_kernel_rejected_export(summary) or _summary_unverified_solved_export(summary):
        return False
    if summary.get("solved") is True and _summary_has_root_solution_evidence(summary):
        return True
    if "solved" in summary and summary.get("solved") is not True:
        return False
    dossier = summary.get("proof_dossier")
    if isinstance(dossier, dict) and str(dossier.get("final_proof_hash") or "").strip():
        return True
    finalized_root_verdicts = {
        "root_finalization_accepted",
        "root_finalization_already_applied",
    }
    for record in events:
        if str(record.get("session_scope") or "").strip() == "subgoal":
            continue
        phase = str(record.get("phase") or "")
        if (
            phase == "session_root_solved"
            and str(record.get("verdict") or "") == "solved"
            and str(record.get("root_finalization_verdict") or "").strip()
            in finalized_root_verdicts
            and (
                _is_true(record.get("accepted"))
                or bool(str(record.get("accepted_proof") or "").strip())
            )
        ):
            return True
        if (
            phase in {"session_action_outcome", "session_root_finalization"}
            and _is_true(record.get("solved"))
            and _is_true(record.get("root_finalization_accepted"))
        ):
            return True
        if (
            phase == "session_root_finalization"
            and (
                _is_true(record.get("root_solved"))
                or _is_true(record.get("effective_solved"))
            )
            and _is_true(record.get("root_finalization_accepted"))
        ):
            return True
    return False


def _helper_accept_events(events: Sequence[Mapping[str, Any]]) -> List[Mapping[str, Any]]:
    helpers: List[Mapping[str, Any]] = []
    for record in events:
        if str(record.get("phase") or "") == "mini_recursive_helper_accept":
            helpers.append(record)
            continue
        if str(record.get("verdict") or "") in {"helper_accepted", "accepted_helper"}:
            helpers.append(record)
            continue
        if _safe_int(record.get("helpers_added_count")) > 0:
            helpers.append(record)
    return helpers


def _terminal_events(events: Sequence[Mapping[str, Any]]) -> List[Mapping[str, Any]]:
    terminals: List[Mapping[str, Any]] = []
    for record in events:
        phase = str(record.get("phase") or "")
        verdict = str(record.get("verdict") or "")
        reason = str(record.get("reason") or record.get("failure_reason") or "")
        budget_reason = str(record.get("budget_rejection_reason") or "")
        if verdict.startswith("terminal_"):
            terminals.append(record)
        elif (
            phase == "mini_recursive_complete"
            and not bool(record.get("ok"))
            and reason != "recursive_progress_fixed_point"
            and not is_resumable_mini_recursive_yield(reason)
        ):
            terminals.append(record)
        elif phase == "session_cost_budget":
            terminals.append(record)
        elif (
            phase == "llm_usage"
            and verdict == "cost_budget_rejected"
            and (
                bool(record.get("budget_rejection_terminal"))
                or budget_reason
                in {
                    "llm_cost_budget_exhausted",
                    "llm_cost_budget_unknown_pricing",
                    "cost_budget_exhausted",
                    "unknown_pricing",
                }
            )
        ):
            terminals.append(record)
        elif reason in {
            "recursive_passes_exhausted",
            "claim_exhausted",
            "recovery_budget_exhausted",
            "no_registered_recovery_actions",
            "answer_unsafe",
        }:
            terminals.append(record)
    return terminals


def _contains_answer_unsafe(events: Sequence[Mapping[str, Any]], summary: Mapping[str, Any]) -> int:
    event_keys = (
        "phase",
        "verdict",
        "reason",
        "failure_reason",
        "lean_error_type",
        "rejection_reason",
    )
    count = 0
    for record in events:
        if any(_is_answer_unsafe_marker(record.get(key)) for key in event_keys):
            count += 1
    summary_reason = " ".join(
        str(summary.get(key) or "")
        for key in ("failure_reason", "root_failure_reason", "terminal_reason")
    )
    if _is_answer_unsafe_marker(summary_reason):
        count += 1
    for key, value in summary.items():
        if not _is_answer_unsafe_summary_policy_key(key):
            continue
        if isinstance(value, bool) and value:
            count += 1
        elif isinstance(value, (int, float)) and value > 0:
            count += 1
    return count


def _contains_route_contract_block(events: Sequence[Mapping[str, Any]]) -> int:
    count = 0
    for record in events:
        text = _event_text(record)
        if "route_contract" in text and (
            "not_ready" in text or "missing" in text or "blocked" in text
        ):
            count += 1
    return count


def _terminal_reason(
    terminal_events: Sequence[Mapping[str, Any]],
    summary: Mapping[str, Any],
    *,
    include_summary_terminal: bool = True,
) -> str:
    for record in reversed(list(terminal_events or ())):
        if str(record.get("phase") or "") == "llm_usage" and str(
            record.get("verdict") or ""
        ) == "cost_budget_rejected":
            reason = str(record.get("budget_rejection_reason") or "").strip()
            if reason == "unknown_pricing":
                return "llm_cost_budget_unknown_pricing"
            if reason == "cost_budget_exhausted":
                return "llm_cost_budget_exhausted"
            if reason:
                return reason
    if include_summary_terminal and bool(summary.get("llm_cost_budget_exhausted")):
        return (
            str(summary.get("llm_cost_budget_terminal_reason") or "").strip()
            or "llm_cost_budget_exhausted"
        )
    summary_reason = (
        str(summary.get("failure_reason") or "").strip()
        if include_summary_terminal
        else ""
    )
    if summary_reason and not is_resumable_mini_recursive_yield(summary_reason):
        return summary_reason
    if not terminal_events:
        return ""
    last = terminal_events[-1]
    return (
        str(last.get("reason") or "").strip()
        or str(last.get("failure_reason") or "").strip()
        or str(last.get("terminal_failure_reason") or "").strip()
        or str(last.get("budget_rejection_reason") or "").strip()
        or str(last.get("verdict") or "").strip()
        or str(last.get("phase") or "").strip()
    )


def _summary_or_terminal_float(
    key: str,
    summary: Mapping[str, Any],
    terminal_events: Sequence[Mapping[str, Any]],
) -> float:
    value = _safe_float(summary.get(key))
    if value is not None:
        return value
    for record in reversed(list(terminal_events or ())):
        value = _safe_float(record.get(key))
        if value is not None:
            return value
    return 0.0


def _dominant_category(
    *,
    root_solved: bool,
    summary_present: bool,
    events: Sequence[Mapping[str, Any]],
    helper_accept_count: int,
    lean_rejection_count: int,
    repair_ticket_count: int,
    terminal_reason: str,
    no_applicable_terminal_count: int,
    route_contract_blocked_count: int,
    answer_unsafe_count: int,
) -> str:
    if root_solved:
        return "root_solved"
    if (
        "cost_budget" in str(terminal_reason or "")
        or any(
            str(record.get("phase") or "") == "session_cost_budget"
            or (
                str(record.get("phase") or "") == "llm_usage"
                and str(record.get("verdict") or "") == "cost_budget_rejected"
                and bool(record.get("budget_rejection_terminal"))
            )
            for record in events
        )
    ):
        return "llm_cost_budget_exhausted"
    terminal_answer_unsafe = _is_answer_unsafe_marker(terminal_reason)
    if terminal_answer_unsafe:
        return "answer_unsafe_policy"
    if answer_unsafe_count and not terminal_reason:
        return "answer_unsafe_policy"
    if events:
        last = events[-1]
        last_verdict = str(last.get("verdict") or "")
        last_phase = str(last.get("phase") or "")
        nonterminal_tail = (
            not last_verdict.startswith("terminal_")
            and last_phase != "mini_recursive_complete"
        )
        if nonterminal_tail and not terminal_reason:
            return "live_or_incomplete"
        if nonterminal_tail and not summary_present:
            return "live_or_incomplete"
        if (
            not terminal_reason
            and last_phase == "mini_recursive_complete"
            and is_resumable_mini_recursive_yield(
                last.get("reason") or last.get("failure_reason")
            )
        ):
            return "live_or_incomplete"
    if helper_accept_count and terminal_reason in {
        "recursive_passes_exhausted",
        "recovery_budget_exhausted",
        "no_registered_recovery_actions",
        "terminal_no_applicable_action",
    }:
        return "post_helper_terminal"
    if no_applicable_terminal_count:
        return "no_applicable_terminal"
    if route_contract_blocked_count:
        return "route_contract_blocked"
    if repair_ticket_count >= 3 and lean_rejection_count >= 3:
        return "ineffective_repair_loop"
    if terminal_reason:
        return terminal_reason
    if answer_unsafe_count:
        return "answer_unsafe_policy"
    if not summary_present:
        last = events[-1] if events else {}
        if str(last.get("verdict") or "").startswith("terminal_"):
            return "terminal_without_summary"
        return "live_or_incomplete"
    if lean_rejection_count:
        return "lean_rejections_no_terminal_reason"
    return "unknown_unsolved"


def _evidence(
    *,
    events: Sequence[Mapping[str, Any]],
    terminal_events: Sequence[Mapping[str, Any]],
    helpers: Sequence[Mapping[str, Any]],
    category: str,
    terminal_reason: str,
) -> str:
    if category == "live_or_incomplete" and events:
        last = events[-1]
        return (
            f"last phase={last.get('phase')} verdict={last.get('verdict')} "
            f"turn={last.get('turn_index')} elapsed={last.get('elapsed_s')}"
        )
    if helpers and category == "post_helper_terminal":
        helper = helpers[-1]
        return (
            f"helper accepted at turn={helper.get('turn_index')} "
            f"elapsed={helper.get('elapsed_s')}; terminal_reason={terminal_reason}"
        )
    if terminal_events:
        terminal = terminal_events[-1]
        cost_bits = ""
        if category == "llm_cost_budget_exhausted":
            cost_bits = (
                f" cost={terminal.get('cost_usd')} "
                f"accounted={terminal.get('llm_budget_accounted_cost_usd')} "
                f"budget={terminal.get('max_cost_usd')}"
            )
        return (
            f"terminal phase={terminal.get('phase')} verdict={terminal.get('verdict')} "
            f"reason={terminal.get('reason') or terminal.get('failure_reason')} "
            f"turn={terminal.get('turn_index')}{cost_bits}"
        )
    if events:
        last = events[-1]
        return (
            f"last phase={last.get('phase')} verdict={last.get('verdict')} "
            f"turn={last.get('turn_index')} elapsed={last.get('elapsed_s')}"
        )
    return "no turns.jsonl events"


def classify_run(run_dir: str | Path) -> MiniRunClassification:
    """Classify one mini-prover run directory from recorder artifacts."""

    run_path = Path(run_dir)
    trace = load_turn_trace(run_path)
    events = trace.events
    summary = _read_json(run_path / "summary.json")
    summary_present = bool(summary)
    root_solved = _is_root_solved(events, summary)
    helpers = _helper_accept_events(events)
    terminal_records = _terminal_events(events)
    summary_reason = str(summary.get("failure_reason") or "").strip()
    last_terminal_index = max(
        (
            index
            for index, record in enumerate(events)
            if any(record is terminal for terminal in terminal_records)
        ),
        default=-1,
    )
    last_resumable_index = max(
        (
            index
            for index, record in enumerate(events)
            if str(record.get("phase") or "") == "mini_recursive_complete"
            and is_resumable_mini_recursive_yield(
                record.get("reason") or record.get("failure_reason")
            )
        ),
        default=-1,
    )
    summary_failure_detail = str(
        summary.get("failure_reason_detail") or ""
    ).strip()
    summary_is_external_terminal = bool(
        summary.get("mini_session_worker_timeout")
        or summary_reason.startswith("mini_session_worker_")
        or "watchdog_worker_" in summary_failure_detail
    )
    summary_terminal_superseded = bool(
        is_resumable_mini_recursive_yield(summary_reason)
        or (
            not summary_is_external_terminal
            and last_resumable_index > last_terminal_index
        )
    )
    if summary_terminal_superseded:
        terminal_records = []
    terminal_reason = _terminal_reason(
        terminal_records,
        summary,
        include_summary_terminal=not summary_terminal_superseded,
    )
    lean_rejection_count = sum(
        1
        for record in events
        if str(record.get("lean_verdict") or "") == "lean_rejected"
        or str(record.get("verdict") or "") == "lean_rejected"
    )
    repair_ticket_count = sum(
        1
        for record in events
        if str(record.get("phase") or "") == "session_repair_ticket"
    )
    repair_prompt_injected_count = sum(
        1
        for record in events
        if str(record.get("phase") or "") == "session_repair_ticket"
        and str(record.get("verdict") or "") == "repair_prompt_injected"
    )
    no_applicable_terminal_count = sum(
        1
        for record in events
        if str(record.get("phase") or "") == "session_no_applicable_recovery"
        and str(record.get("verdict") or "") == "terminal_no_applicable_action"
    )
    answer_unsafe_count = _contains_answer_unsafe(events, summary)
    route_contract_blocked_count = _contains_route_contract_block(events)
    dominant_category = _dominant_category(
        root_solved=root_solved,
        summary_present=summary_present,
        events=events,
        helper_accept_count=len(helpers),
        lean_rejection_count=lean_rejection_count,
        repair_ticket_count=repair_ticket_count,
        terminal_reason=terminal_reason,
        no_applicable_terminal_count=no_applicable_terminal_count,
        route_contract_blocked_count=route_contract_blocked_count,
        answer_unsafe_count=answer_unsafe_count,
    )
    if dominant_category == "live_or_incomplete" and not summary_present:
        terminal_reason = ""
    last = events[-1] if events else {}
    if root_solved:
        status = "solved"
    elif events and dominant_category == "live_or_incomplete":
        status = "live_or_incomplete"
    elif summary_present or terminal_records:
        status = "failed"
    elif events:
        status = "live_or_incomplete"
    else:
        status = "missing_trace"
    return MiniRunClassification(
        run_dir=str(run_path),
        event_count=len(events),
        malformed_event_count=int(trace.malformed_line_count),
        replay_eligible=(not trace.missing_trace and trace.malformed_line_count == 0),
        summary_present=summary_present,
        root_solved=root_solved,
        status=status,
        helper_accept_count=len(helpers),
        lean_rejection_count=lean_rejection_count,
        repair_ticket_count=repair_ticket_count,
        repair_prompt_injected_count=repair_prompt_injected_count,
        no_applicable_terminal_count=no_applicable_terminal_count,
        route_contract_blocked_count=route_contract_blocked_count,
        answer_unsafe_count=answer_unsafe_count,
        terminal_reason=terminal_reason,
        dominant_category=dominant_category,
        cost_usd=_summary_or_terminal_float("cost_usd", summary, terminal_records),
        max_cost_usd=_summary_or_terminal_float("max_cost_usd", summary, terminal_records),
        estimated_unknown_cost_usd=(
            _summary_or_terminal_float(
                "estimated_unknown_cost_usd",
                summary,
                terminal_records,
            )
        ),
        llm_budget_accounted_cost_usd=(
            _summary_or_terminal_float(
                "llm_budget_accounted_cost_usd",
                summary,
                terminal_records,
            )
        ),
        evidence=_evidence(
            events=events,
            terminal_events=terminal_records,
            helpers=helpers,
            category=dominant_category,
            terminal_reason=terminal_reason,
        ),
        last_turn_index=_safe_int(last.get("turn_index"), default=0),
        last_elapsed_s=_safe_float(last.get("elapsed_s")),
        last_phase=str(last.get("phase") or ""),
        last_verdict=str(last.get("verdict") or ""),
    )


def classify_recent_runs(root: str | Path, *, limit: int = 20) -> List[MiniRunClassification]:
    """Classify the most recently modified run directories under ``root``."""

    root_path = Path(root)
    if not root_path.exists() or not root_path.is_dir():
        return []
    candidates = [
        path
        for path in root_path.iterdir()
        if path.is_dir() and (path / "turns.jsonl").exists()
    ]
    candidates.sort(key=lambda path: path.stat().st_mtime, reverse=True)
    return [classify_run(path) for path in candidates[: max(0, int(limit))]]


def _next_session_action_after(
    events: Sequence[Mapping[str, Any]],
    start_index: int,
) -> Mapping[str, Any]:
    for record in events[start_index + 1 :]:
        if str(record.get("phase") or "") == "session_action_selected":
            return record
        if str(record.get("phase") or "") == "session_no_applicable_recovery":
            return record
    return {}


def _next_session_outcome_after(
    events: Sequence[Mapping[str, Any]],
    start_index: int,
) -> Mapping[str, Any]:
    for record in events[start_index + 1 :]:
        phase = str(record.get("phase") or "")
        if phase == "session_action_outcome":
            return record
        if phase in {"session_action_selected", "session_no_applicable_recovery"}:
            return record
    return {}


def _next_repair_ticket_followup_after(
    events: Sequence[Mapping[str, Any]],
    start_index: int,
) -> Mapping[str, Any]:
    for record in events[start_index + 1 :]:
        phase = str(record.get("phase") or "")
        verdict = str(record.get("verdict") or "")
        if phase == "session_repair_ticket":
            if verdict == "created":
                continue
            return record
        if phase in {"session_action_selected", "session_no_applicable_recovery"}:
            return record
    return {}


def _forced_repair_ticket_pending_at(
    events: Sequence[Mapping[str, Any]],
    index: int,
) -> bool:
    for record in reversed(events[:index]):
        phase = str(record.get("phase") or "")
        verdict = str(record.get("verdict") or "")
        if phase != "session_repair_ticket":
            continue
        if verdict == "conversation_turn_forced":
            return True
        if verdict in {
            "repair_prompt_injected",
            "created",
        }:
            continue
        return False
    return False


_REPAIR_SELF_CHECK_POLICY_STATUSES = {
    "no_try_lean_call",
    "no_accepted_try_lean",
    "tool_budget_exhausted",
    "accepted_try_lean_mismatch",
    "proof_policy_rejected",
}
_REPAIR_SELF_CHECK_NON_POLICY_STATUSES = {
    "accepted",
    "helper_only_decomposition",
    "try_lean_infrastructure_error",
    "try_lean_malformed_arguments",
    "try_lean_preflight_error",
}


def _repair_self_check_requires_ticket_resolution(value: Any) -> bool:
    reason = str(value or "").strip()
    if not reason:
        return False
    normalized = reason
    if normalized.startswith("repair_self_check_"):
        normalized = normalized[len("repair_self_check_") :]
    if normalized in _REPAIR_SELF_CHECK_NON_POLICY_STATUSES:
        return False
    if normalized in _REPAIR_SELF_CHECK_POLICY_STATUSES:
        return True
    return reason.startswith("repair_self_check_")


def _conversation_outcome_requires_ticket_resolution(
    record: Mapping[str, Any],
) -> bool:
    if str(record.get("phase") or "") != "session_action_outcome":
        return False
    if str(record.get("action_id") or "") not in {
        "conversation_turn_refine",
        "conversation_turn_prove",
    }:
        return False
    if bool(record.get("policy_repair_redirect")):
        return True
    metadata = record.get("outcome_metadata")
    metadata_record = metadata if isinstance(metadata, Mapping) else {}
    for source in (record, metadata_record):
        for key in ("rejection_reason", "lean_error_type", "error"):
            reason = str(source.get(key) or "").strip()
            if _repair_self_check_requires_ticket_resolution(reason):
                return True
        for key in ("repair_self_check_status", "repair_self_check_missing_kind"):
            reason = str(source.get(key) or "").strip()
            if _repair_self_check_requires_ticket_resolution(reason):
                return True
    return False


def replay_repair_decisions(
    events: Sequence[Mapping[str, Any]],
    *,
    terminal_trace: bool = False,
) -> List[ReplayDecision]:
    """Replay narrow repair invariants from a trace.

    ``conversation_turn_forced`` is the scheduler commitment: the next
    selected session action must be a conversation action.  A later
    ``repair_prompt_injected`` record is emitted inside that LLM turn, so the
    next session action after the turn may legitimately be graph work.  For
    injected prompts we only verify that the current trace eventually records
    a conversation outcome.  A tail injection is pending only for live or
    incomplete traces; if the run is already terminal, the prompt was injected
    but no repair attempt actually completed.
    """

    decisions: List[ReplayDecision] = []
    for index, record in enumerate(events):
        phase = str(record.get("phase") or "")
        verdict = str(record.get("verdict") or "")
        if (
            phase == "session_repair_ticket"
            and verdict == "repair_turn_unresolved_retry_remaining"
        ):
            rejection_reason = str(record.get("rejection_reason") or "").strip()
            outcome_verdict = str(record.get("outcome_verdict") or "").strip()
            attempts_used = _safe_int(record.get("attempts_used"), default=0)
            max_attempts = _safe_int(record.get("max_attempts"), default=0)
            if rejection_reason.startswith("repair_self_check_") or (
                outcome_verdict == "proof_policy_rejected"
            ):
                decisions.append(
                    ReplayDecision(
                        trigger_turn_index=_safe_int(
                            record.get("turn_index"),
                            default=0,
                        ),
                        trigger_elapsed_s=_safe_float(record.get("elapsed_s")),
                        trigger_phase=phase,
                        trigger_verdict=verdict,
                        expected_next_action="repair_ticket_retry_or_exhaustion",
                        actual_next_action=verdict,
                        ok=False,
                        category="forced_repair_ticket_unresolved_policy_rejection",
                        evidence=(
                            "policy/self-check repair rejection did not consume "
                            f"a ticket attempt; reason={rejection_reason or outcome_verdict} "
                            f"attempts_used={record.get('attempts_used')} "
                            f"max_attempts={record.get('max_attempts')}"
                        ),
                    )
                )
                continue
            if attempts_used < 1 or (max_attempts > 0 and attempts_used >= max_attempts):
                decisions.append(
                    ReplayDecision(
                        trigger_turn_index=_safe_int(
                            record.get("turn_index"),
                            default=0,
                        ),
                        trigger_elapsed_s=_safe_float(record.get("elapsed_s")),
                        trigger_phase=phase,
                        trigger_verdict=verdict,
                        expected_next_action="repair_ticket_attempt_consumed_or_exhausted",
                        actual_next_action=verdict,
                        ok=False,
                        category="forced_repair_ticket_unresolved_without_attempt_consumption",
                        evidence=(
                            "generic unresolved repair retry did not reflect a "
                            "bounded consumed attempt; "
                            f"outcome_verdict={outcome_verdict} "
                            f"attempts_used={attempts_used} max_attempts={max_attempts}"
                        ),
                    )
                )
                continue
        if phase == "session_repair_ticket" and verdict == "created":
            actual = _next_repair_ticket_followup_after(events, index)
            actual_phase = str(actual.get("phase") or "")
            actual_verdict = str(actual.get("verdict") or "")
            actual_action = str(actual.get("action_id") or "")
            allowed_ticket_verdicts = {
                "conversation_turn_forced",
                "blocked_unscoped_root_authoring",
                "blocked_no_conversation_action",
                "exhausted",
                "scheduler_blocked_until_repair",
                "repair_turn_consumed",
                "repair_turn_rejected_retry_remaining",
                "repair_turn_policy_rejected_retry_remaining",
                "repair_turn_unresolved_retry_remaining",
                "repair_turn_unresolved_exhausted",
                "unscoped_root_repair_replanned",
            }
            if actual_phase == "session_repair_ticket":
                ok = actual_verdict in allowed_ticket_verdicts
                actual_next = actual_verdict or actual_action
                evidence = (
                    f"next repair-ticket verdict={actual_verdict} "
                    f"turn={actual.get('turn_index')} iteration={actual.get('iteration')}"
                )
            elif actual_phase in {"session_action_selected", "session_no_applicable_recovery"}:
                ok = False
                actual_next = actual_action or actual_phase
                evidence = (
                    f"next session event phase={actual_phase} action_id={actual_action} "
                    f"verdict={actual_verdict}"
                )
            else:
                ok = not terminal_trace
                actual_next = "pending" if ok else "terminal_without_ticket_followup"
                evidence = (
                    "no subsequent repair-ticket decision recorded; "
                    + (
                        "trace may be live/incomplete"
                        if ok
                        else "terminal run ended with unresolved ticket"
                    )
                )
            decisions.append(
                ReplayDecision(
                    trigger_turn_index=_safe_int(record.get("turn_index"), default=0),
                    trigger_elapsed_s=_safe_float(record.get("elapsed_s")),
                    trigger_phase=phase,
                    trigger_verdict=verdict,
                    expected_next_action=(
                        "repair_ticket_followup|conversation_turn_refine|"
                        "conversation_turn_prove"
                    ),
                    actual_next_action=actual_next,
                    ok=ok,
                    category="created_repair_ticket_followup",
                    evidence=evidence,
                )
            )
            continue
        if phase in {
            "session_repair_ticket",
            "session_repair_first",
            "session_local_repair_turn",
        } and verdict == "conversation_turn_forced":
            actual = _next_session_action_after(events, index)
            actual_phase = str(actual.get("phase") or "")
            actual_action = str(actual.get("action_id") or "")
            if actual_phase == "session_action_selected":
                ok = actual_action in {"conversation_turn_refine", "conversation_turn_prove"}
                evidence = (
                    f"next action_id={actual_action} turn={actual.get('turn_index')} "
                    f"iteration={actual.get('iteration')}"
                )
            elif actual_phase == "session_no_applicable_recovery":
                ok = False
                actual_action = "session_no_applicable_recovery"
                evidence = (
                    f"next terminal/recovery verdict={actual.get('verdict')} "
                    f"reason={actual.get('reason')}"
                )
            else:
                ok = not terminal_trace
                actual_action = "pending" if ok else "terminal_without_repair_action"
                evidence = (
                    "no subsequent session decision recorded; "
                    + (
                        "trace may be live/incomplete"
                        if ok
                        else "terminal run ended before forced repair action"
                    )
                )
            decisions.append(
                ReplayDecision(
                    trigger_turn_index=_safe_int(record.get("turn_index"), default=0),
                    trigger_elapsed_s=_safe_float(record.get("elapsed_s")),
                    trigger_phase=phase,
                    trigger_verdict=verdict,
                    expected_next_action="conversation_turn_refine|conversation_turn_prove",
                    actual_next_action=actual_action,
                    ok=ok,
                    category="forced_repair_next_action",
                    evidence=evidence,
                )
            )
            continue
        if _conversation_outcome_requires_ticket_resolution(
            record
        ) and _forced_repair_ticket_pending_at(events, index):
            actual = _next_repair_ticket_followup_after(events, index)
            actual_phase = str(actual.get("phase") or "")
            actual_verdict = str(actual.get("verdict") or "")
            actual_action = str(actual.get("action_id") or "")
            allowed_ticket_verdicts = {
                "exhausted",
                "repair_turn_consumed",
                "repair_turn_rejected_retry_remaining",
                "repair_turn_policy_rejected_retry_remaining",
            }
            if actual_phase == "session_repair_ticket":
                ok = actual_verdict in allowed_ticket_verdicts
                actual_next = actual_verdict or actual_action
                evidence = (
                    f"next repair-ticket verdict={actual_verdict} "
                    f"turn={actual.get('turn_index')} iteration={actual.get('iteration')}"
                )
            elif actual_phase in {"session_action_selected", "session_no_applicable_recovery"}:
                ok = False
                actual_next = actual_action or actual_phase
                evidence = (
                    f"next session event phase={actual_phase} action_id={actual_action} "
                    f"verdict={actual_verdict}"
                )
            else:
                ok = not terminal_trace
                actual_next = "pending" if ok else "terminal_without_ticket_resolution"
                evidence = (
                    "no subsequent repair-ticket resolution recorded; "
                    + (
                        "trace may be live/incomplete"
                        if ok
                        else "terminal run ended with unresolved forced repair ticket"
                    )
                )
            decisions.append(
                ReplayDecision(
                    trigger_turn_index=_safe_int(record.get("turn_index"), default=0),
                    trigger_elapsed_s=_safe_float(record.get("elapsed_s")),
                    trigger_phase=phase,
                    trigger_verdict=verdict,
                    expected_next_action="repair_ticket_resolution",
                    actual_next_action=actual_next,
                    ok=ok,
                    category="forced_repair_ticket_resolution",
                    evidence=evidence,
                )
            )
            continue
        if phase != "session_repair_ticket" or verdict != "repair_prompt_injected":
            continue
        actual = _next_session_outcome_after(events, index)
        actual_phase = str(actual.get("phase") or "")
        actual_action = str(actual.get("action_id") or "")
        if actual_phase == "session_action_outcome":
            ok = actual_action in {"conversation_turn_refine", "conversation_turn_prove"}
            evidence = (
                f"next outcome action_id={actual_action} turn={actual.get('turn_index')} "
                f"iteration={actual.get('iteration')}"
            )
        elif actual:
            ok = False
            actual_action = actual_action or actual_phase
            evidence = (
                f"next session event before conversation outcome phase={actual_phase} "
                f"action_id={actual.get('action_id')} verdict={actual.get('verdict')}"
            )
        elif terminal_trace:
            ok = False
            actual_action = "terminal_without_repair_outcome"
            evidence = (
                "repair prompt has no subsequent session outcome before "
                "terminal run end"
            )
        else:
            ok = True
            actual_action = "pending"
            evidence = "no subsequent session outcome recorded; trace may be live/incomplete"
        decisions.append(
            ReplayDecision(
                trigger_turn_index=_safe_int(record.get("turn_index"), default=0),
                trigger_elapsed_s=_safe_float(record.get("elapsed_s")),
                trigger_phase=str(record.get("phase") or ""),
                trigger_verdict=str(record.get("verdict") or ""),
                expected_next_action="conversation_turn_refine|conversation_turn_prove",
                actual_next_action=actual_action,
                ok=ok,
                category="repair_prompt_completion",
                evidence=evidence,
            )
        )
    return decisions


def replay_run_decisions(run_dir: str | Path) -> List[ReplayDecision]:
    """Load a run and replay supported decision invariants."""

    trace = load_turn_trace(run_dir)
    classification = classify_run(run_dir)
    if trace.missing_trace or trace.malformed_line_count:
        evidence = (
            "missing turns.jsonl"
            if trace.missing_trace
            else f"turns.jsonl contains {trace.malformed_line_count} malformed line(s)"
        )
        return [
            ReplayDecision(
                trigger_turn_index=0,
                trigger_elapsed_s=None,
                trigger_phase="trace_load",
                trigger_verdict="not_replayable",
                expected_next_action="well_formed_trace",
                actual_next_action="trace_not_replayable",
                ok=False,
                category="trace_not_replayable",
                evidence=evidence,
            )
        ]
    return replay_repair_decisions(
        trace.events,
        terminal_trace=classification.status in {"failed", "solved"},
    )


def iter_classification_dicts(
    classifications: Iterable[MiniRunClassification],
) -> Iterator[JSONDict]:
    for item in classifications:
        yield asdict(item)


def _print_table(classifications: Sequence[MiniRunClassification]) -> None:
    headers = [
        "run",
        "status",
        "helpers",
        "category",
        "terminal_reason",
        "evidence",
    ]
    rows = []
    for item in classifications:
        rows.append([
            Path(item.run_dir).name,
            item.status,
            str(item.helper_accept_count),
            item.dominant_category,
            item.terminal_reason or "-",
            item.evidence,
        ])
    widths = [
        max(len(headers[index]), *(len(row[index]) for row in rows))
        if rows
        else len(headers[index])
        for index in range(len(headers))
    ]
    print("  ".join(header.ljust(widths[index]) for index, header in enumerate(headers)))
    for row in rows:
        print("  ".join(row[index].ljust(widths[index]) for index in range(len(row))))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", help="mini_prover run directory or runs/mini_prover root")
    parser.add_argument("--recent", type=int, default=0, help="classify N recent child runs")
    parser.add_argument("--json", action="store_true", help="emit JSON instead of a table")
    parser.add_argument(
        "--replay-decisions",
        action="store_true",
        help="emit repair-next-action replay decisions for a single run",
    )
    args = parser.parse_args(argv)
    path = Path(args.path)
    if not path.exists():
        print(f"error: path does not exist: {path}", file=sys.stderr)
        return 2
    if args.recent and not path.is_dir():
        print(f"error: --recent requires a directory: {path}", file=sys.stderr)
        return 2
    if args.replay_decisions:
        decisions = replay_run_decisions(path)
        print(json.dumps([asdict(item) for item in decisions], indent=2, sort_keys=True))
        return 0
    if args.recent:
        classifications = classify_recent_runs(path, limit=args.recent)
    else:
        classifications = [classify_run(path)]
    if args.json:
        print(
            json.dumps(
                list(iter_classification_dicts(classifications)),
                indent=2,
                sort_keys=True,
            )
        )
    else:
        _print_table(classifications)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
