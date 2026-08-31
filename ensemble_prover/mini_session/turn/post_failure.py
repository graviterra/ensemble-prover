"""Coordinate bounded recovery after a candidate fails Lean verification.

The cascade records the failure, retrieves repair context, attempts child
closure, salvages and assembles independently verifiable helpers, retries
deterministic root closure, and composes typed feedback. Shared proof-state and
salvage primitives remain responsible for their own evidence and isolation
contracts.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import inspect
import re
from typing import Any, Dict, List, Optional, Sequence

from ensemble_prover.formalization_guardrails import is_parse_error_failure
from ensemble_prover.mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ensemble_prover.proof_dossier import (
    _prompt_safe_inline_text,
    _prompt_safe_lean_diagnostic_text,
    active_root_target_statement,
    effective_solution_placeholder_suppression,
    helper_decl_body,
    helper_decl_name,
    helper_decl_statement,
)
from ensemble_prover.proof_state_cache import store_verified_helper_for_dossier
from ensemble_prover.target_integrity import (
    classify_target_integrity_signals,
    target_integrity_feedback,
)
from ensemble_prover.tactic_attempt_telemetry import (
    dossier_lean_attempt_observer,
    tactic_attempt_telemetry_fields,
)


def _strip_lean_comments(text: str) -> str:
    no_block = re.sub(r"/-[\s\S]*?-/", "", str(text or ""))
    return re.sub(r"--[^\n]*", "", no_block)


def _helper_has_concrete_proof_attempt(helper_block: str) -> bool:
    """Whether a helper declaration contains a real non-placeholder body."""

    source = str(helper_block or "").strip()
    if not source:
        return False
    if not helper_decl_name(source) or not helper_decl_statement(source):
        return False
    body = helper_decl_body(source) or ""
    body_no_comments = _strip_lean_comments(body)
    body_norm = " ".join(body_no_comments.split()).lower()
    if not body_norm or body_norm in {"by", "by sorry", "by admit", "sorry", "admit"}:
        return False
    if re.search(r"(?<![A-Za-z0-9_'.])(sorry|admit)(?![A-Za-z0-9_'.])", body_no_comments):
        return False
    return "?_" not in body_no_comments


def _concrete_giveup_helper_candidates(
    helpers: Sequence[str],
    lemma_dag_candidate_helpers: Sequence[str],
) -> List[str]:
    """Keep only real helper attempts from give-up/off-ramp responses.

    Give-up prose often comes with ``by sorry`` declarations that name the
    avoided bridge. Those should not become durable child goals. A declaration
    with a concrete body, however, is useful evidence: Lean rejected the
    combined block, but the helper statement can still be scheduled as a child.
    """

    out: List[str] = []
    seen = set()
    for helper_block in list(helpers or ()) + list(lemma_dag_candidate_helpers or ()):
        source = str(helper_block or "").strip()
        if not source or source in seen:
            continue
        seen.add(source)
        if _helper_has_concrete_proof_attempt(source):
            out.append(source)
    return out


def _repair_goal_statement_for_retrieval(
    *,
    explicit_goal_statement: str = "",
    dossier: Any = None,
    conv: Any = None,
) -> str:
    explicit = str(explicit_goal_statement or "").strip()
    if explicit:
        return explicit
    active = active_root_target_statement(
        dossier,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    if active:
        return active
    return str(getattr(conv, "goal_statement", "") or "").strip()


def _selected_work_suppresses_root_target_fallback(
    selected_work: Dict[str, Any],
    *,
    selected_work_type: str = "",
) -> bool:
    work_type = str(selected_work_type or selected_work.get("work_type") or "").strip()
    return bool(
        work_type
        in {
            "formalize_claim",
            "formalize_missing_obligation",
            "prove_claim_variant",
            "mine_missing_obligation",
            "route_replan",
            "target_integrity_adjudication",
            "materialize_replay_source",
        }
        or selected_work.get("formalization_required")
        or selected_work.get("materialization_required")
        or selected_work.get("formalization_statement_pending")
    )


def _diagnostic_location_label(diag: Dict[str, Any]) -> str:
    parts: List[str] = []
    line = diag.get("line")
    col = diag.get("col")
    if line not in (None, ""):
        parts.append(f"line {line}")
    if col not in (None, ""):
        parts.append(f"col {col}")
    return ", ".join(parts)


def _local_repair_diagnostic_span_block(
    analysis: Dict[str, Any],
    *,
    feedback_result: Any = None,
    format_raw_feedback: Any = None,
    max_diagnostics: int = 3,
    max_message_chars: int = 900,
) -> str:
    """Return raw Lean output, falling back to compact structured diagnostics."""

    if feedback_result is not None and callable(format_raw_feedback):
        try:
            raw_feedback = str(format_raw_feedback(feedback_result) or "").strip()
        except Exception:
            raw_feedback = ""
        if raw_feedback:
            if len(raw_feedback) > 6000:
                raw_feedback = raw_feedback[:5940].rstrip()
                raw_feedback += "\n... (sanitized raw Lean output truncated)"
            return "Sanitized raw Lean output for this local repair:\n" + raw_feedback

    diagnostics = [
        dict(item)
        for item in list((analysis or {}).get("diagnostics") or [])
        if isinstance(item, dict)
    ]
    if not diagnostics:
        return ""
    lines = ["Structured Lean diagnostic details for this local repair:"]
    for diag in diagnostics[: max(1, int(max_diagnostics or 1))]:
        message = str(diag.get("message") or diag.get("summary") or "").strip()
        if not message:
            continue
        message = " ".join(message.split())
        if len(message) > max_message_chars:
            message = message[: max(0, max_message_chars - 24)].rstrip()
            message += " ... (truncated)"
        message = _prompt_safe_lean_diagnostic_text(
            message,
            limit=max_message_chars,
        )
        location = _diagnostic_location_label(diag)
        if location:
            lines.append(f"- {location}: {message}")
        else:
            lines.append(f"- {message}")
    return "\n".join(lines) if len(lines) > 1 else ""


@dataclass
class PostFailureResult:
    """Typed bundle returned by ``run_post_failure_cascade``."""

    solved: bool = False
    proof: Optional[str] = None
    feedback_text: str = ""
    # "structured" | "raw" | "structured_fallback_no_feedback_result"
    # | "giveup_active_proof_redirect" (set when the give-up gate fires
    # before helper triage and replaces generic feedback with a proof/pivot
    # redirect — see ``giveup_cluster`` below).
    feedback_mode: str = ""
    local_repair_giveup_suppressed: bool = False
    suppressed_giveup_cluster: str = ""
    suppressed_giveup_match: str = ""
    local_repair_diagnostics_included: bool = False
    salvaged_helper_names: List[str] = field(default_factory=list)
    proof_state_helpers: List[str] = field(default_factory=list)
    proof_state_update: Optional[Dict[str, Any]] = None
    proof_state_retrieval: List[Dict[str, Any]] = field(default_factory=list)
    repair_retrieval_block: str = ""
    repair_retrieval_record: Optional[Dict[str, Any]] = None
    failure_analysis: Dict[str, Any] = field(default_factory=dict)
    # H3 fix (2026-05-08): identify which cascade phase produced the
    # solve so the caller can emit the matching legacy verdict
    # (``solved_after_proof_state_child`` / ``solved_after_helper_salvage``
    # / ``tactic_solved``) instead of collapsing them all to one event.
    # Values: "" (not solved) | "proof_state_child" | "helper_salvage_assembly" |
    # "helper_salvage_root_tactic"
    solved_via: str = ""
    # H4 fix (2026-05-08): the helper-salvage Phase-7 root-tactic-close
    # arm runs ``try_close_with_tactics`` but legacy mini_prover.py:4884-4907
    # also emits a ``recorder.record_turn(verdict=tactic_solved/_rejected/
    # _skipped)`` event with attempt details. Carry the result back so
    # the caller (or the cascade itself) can emit it without
    # re-implementing the call.
    helper_salvage_root_tactic_record: Optional[Dict[str, Any]] = None
    # Decomposition-request redirect (2026-05-09):
    # When the LLM's reply matches a give-up signal cluster
    # (helpers_insufficient / answer_opaque / lemma_not_found /
    # no_sorry_allowed / scaffold_reject / environment_hedge),
    # ``feedback_text`` is overridden with a cluster-specific nudge
    # forcing decomposition into named helpers. The cluster id is
    # surfaced here so the caller's recorder event can tag which
    # branch fired. None when no give-up was detected.
    giveup_cluster: Optional[str] = None
    giveup_match: str = ""
    target_integrity_signals: List[Dict[str, Any]] = field(default_factory=list)
    target_integrity_bypass_local_repair: bool = False
    target_integrity_disable_proof_state_repair: bool = False
    target_integrity_obligation_node_ids: List[str] = field(default_factory=list)
    target_integrity_replan_node_ids: List[str] = field(default_factory=list)
    target_integrity_adjudication_materialized: bool = False
    # Rejected-complete-helper triage (2026-05-11): when a normal
    # helpers+main-proof response fails Lean, independently run the
    # helper declarations through the lemma-DAG helper path so rejected
    # helper statements become durable child_goal nodes instead of
    # disappearing into generic root feedback.
    rejected_helper_triage_accepted: List[str] = field(default_factory=list)
    rejected_helper_child_node_ids: List[str] = field(default_factory=list)
    rejected_helper_linked_child_node_ids: List[str] = field(default_factory=list)
    deferred_rejected_helper_children_to_recursive_helper: bool = False
    failure_residual_obligation_node_ids: List[str] = field(default_factory=list)
    failure_residual_replan_node_ids: List[str] = field(default_factory=list)
    deterministic_search_deferred: bool = False


def _residual_goal_obligation_statement(goal: Dict[str, Any]) -> str:
    target = str(goal.get("target") or "").strip()
    if not target:
        return ""
    hypotheses = [
        " ".join(str(item or "").split()).strip()
        for item in list(goal.get("hypotheses") or [])
        if " ".join(str(item or "").split()).strip()
    ]
    statement = target
    for hyp in reversed(hypotheses):
        if ":=" in hyp:
            if hyp.startswith("let "):
                statement = f"{hyp}; {statement}"
            else:
                statement = f"let {hyp}; {statement}"
        else:
            statement = f"∀ ({hyp}), {statement}"
    return statement


def _increment_tool_metric(dossier: Any, key: str, amount: int = 1) -> None:
    inc = getattr(dossier, "increment_tool_metric", None)
    if callable(inc):
        try:
            inc(str(key), int(amount or 0))
            return
        except Exception:
            pass
    metrics = getattr(dossier, "tool_metrics", None)
    if isinstance(metrics, dict):
        metrics[str(key)] = int(metrics.get(str(key), 0) or 0) + int(amount or 0)


def _is_active_root_lift_feedback_source(feedback_source: str) -> bool:
    return str(feedback_source or "") in {
        "active_root_lift_check",
        "active_root_lift_answer_safe_check",
    }


_ACTIVE_ROOT_LIFT_FEEDBACK_LINE_RE = re.compile(
    r"(?im)^.*(?:h_active|active-root|root-shell|shell stitch).*$"
)


def _suppress_active_root_lift_feedback_text(text: str) -> str:
    raw = str(text or "")
    if not raw:
        return ""
    kept = [
        line
        for line in raw.splitlines()
        if not _ACTIVE_ROOT_LIFT_FEEDBACK_LINE_RE.search(line)
    ]
    cleaned = "\n".join(kept).strip()
    return cleaned or (
        "The submitted proof checked the active target, but the internal "
        "root-shell finalization step failed. Continue proving the active "
        "target directly; do not mention or repair internal wrapper names."
    )


def _record_failure_residual_obligations(
    *,
    dossier: Any,
    proof_state_update: Optional[Dict[str, Any]],
    failure_analysis: Dict[str, Any],
    phase: str,
    turn_index: int,
    feedback_source: str = "",
) -> tuple[List[str], List[str]]:
    """Record failure-mined residuals as quarantined diagnostics.

    These residual goals come from Lean's rejection of a proof script. They are
    not certified facts and may be artifacts of a bad route, missing side
    condition, or local tactic context. Keep them visible in the graph, but do
    not schedule them as proof obligations unless a later validated reduction
    promotes the intended bridge explicitly.
    """

    if _is_active_root_lift_feedback_source(feedback_source):
        return [], []

    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    if graph is None or not isinstance(proof_state_update, dict):
        return [], []
    goals = [
        dict(item)
        for item in list(
            proof_state_update.get("quarantined_remaining_goals") or []
        )
        if isinstance(item, dict)
    ]
    if not goals:
        return [], []
    root_id = str(getattr(graph, "root_node_id", "") or "").strip()
    error_type = str(failure_analysis.get("error_type") or "lean_rejected").strip()
    route = graph.record_strategy_route(
        name=f"failed_proof_residue_{int(turn_index or 0)}",
        description=(
            "Failure-mined residual obligations from a rejected proof attempt."
        ),
        route_key=f"failed_proof_residue:{phase}:{int(turn_index or 0)}:{error_type}",
        score=0.2,
        phase=phase,
        turn_index=turn_index,
        metadata={
            "route_scope": "partial_route",
            "source": "post_failure_residual_work_item",
            "error_type": error_type,
        },
    )
    obligation_ids: List[str] = []
    replan_ids: List[str] = []
    for goal in goals[:4]:
        statement = _residual_goal_obligation_statement(goal)
        if not statement:
            continue
        index = goal.get("index")
        obligation = graph.record_missing_obligation(
            statement=statement,
            reason=f"failed proof residual goal {index or len(obligation_ids) + 1}",
            source_node_id=root_id,
            route_id=route.node_id,
            phase=phase,
            turn_index=turn_index,
            error_type=error_type,
            metadata={
                "source": "post_failure_residual_work_item",
                "residual_goal": dict(goal),
                "certified_fact": False,
                "formalization_required": True,
                "obligation_trust": "untrusted_failed_proof_residual",
                "schedulable": False,
                "residual_goal_quarantined": True,
                "quarantine_reason": "unvalidated_failed_proof_residue",
                **dossier.statement_environment_metadata(),
            },
        )
        replan = graph.record_replan_item(
            source_node_id=root_id,
            route_id=route.node_id,
            obligation_id=obligation.node_id,
            reason=f"prove failed-proof residual obligation {index or len(replan_ids) + 1}",
            phase=phase,
            turn_index=turn_index,
            priority=0.4,
            metadata={
                "source": "post_failure_residual_work_item",
                "residual_goal": dict(goal),
                "certified_fact": False,
                "formalization_required": True,
                "obligation_trust": "untrusted_failed_proof_residual",
                "schedulable": False,
                "residual_goal_quarantined": True,
                "quarantine_reason": "unvalidated_failed_proof_residue",
            },
        )
        replan.metadata["schedulable"] = False
        obligation_ids.append(obligation.node_id)
        replan_ids.append(replan.node_id)
    if obligation_ids or replan_ids:
        _increment_tool_metric(
            dossier,
            "mini_session_failure_residual_obligations_quarantined_unscheduled",
            len(obligation_ids),
        )
    return obligation_ids, replan_ids


def _record_target_integrity_adjudication(
    *,
    dossier: Any,
    target_statement: str,
    signals: Sequence[Dict[str, Any]],
    phase: str,
    turn_index: int,
    selected_work_type: str = "",
    selected_work_record: Optional[Dict[str, Any]] = None,
) -> tuple[List[str], List[str], bool]:
    """Materialize target-integrity redirects as graph-native work.

    A target-integrity signal means the rejected proof is unsafe as ordinary
    repair material; it does not certify that the active target is false. Keep
    the active target schedulable under an explicit adjudication route so the
    next turns prove, replace, or Lean-refute the target from clean state.
    """

    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    target = str(target_statement or "").strip()
    signal_records = [dict(item) for item in list(signals or []) if isinstance(item, dict)]
    if graph is None or not target or not signal_records:
        return [], [], False
    source_record = dict(selected_work_record or {})
    source_route_id = str(source_record.get("route_id") or "").strip()
    source_obligation_id = str(
        source_record.get("obligation_id")
        or source_record.get("node_id")
        or source_record.get("graph_node_id")
        or ""
    ).strip()
    source_graph_node_id = str(
        source_record.get("graph_node_id")
        or source_record.get("node_id")
        or source_obligation_id
        or ""
    ).strip()
    source_repair_ticket_id = str(
        source_record.get("repair_ticket_id")
        or source_record.get("ticket_id")
        or ""
    ).strip()

    signal_kinds = [
        str(signal.get("kind") or "").strip()
        for signal in signal_records
        if str(signal.get("kind") or "").strip()
    ]
    signal_matches = [
        str(signal.get("match") or "").strip()
        for signal in signal_records
        if str(signal.get("match") or "").strip()
    ][:4]
    root_id = str(getattr(graph, "root_node_id", "") or "").strip()
    error_type = "target_integrity_adjudication_required"
    identity_key = ":".join(
        item
        for item in [
            "target_integrity",
            str(phase or ""),
            target,
            ",".join(signal_kinds),
            str(selected_work_type or ""),
        ]
        if item
    )
    existing_obligations = [
        node
        for node in list(getattr(graph, "nodes_by_kind", lambda _kind: [])("missing_obligation") or [])
        if bool((getattr(node, "metadata", {}) or {}).get("target_integrity_adjudication"))
        and str((getattr(node, "metadata", {}) or {}).get("identity_key") or "") == identity_key
    ]
    if existing_obligations:
        existing_obligation_ids = [node.node_id for node in existing_obligations]
        existing_replan_ids = [
            node.node_id
            for node in list(getattr(graph, "nodes_by_kind", lambda _kind: [])("replan_queue_item") or [])
            if bool((getattr(node, "metadata", {}) or {}).get("target_integrity_adjudication"))
            and str((getattr(node, "metadata", {}) or {}).get("identity_key") or "") == identity_key
        ]
        return existing_obligation_ids, existing_replan_ids, False
    route = graph.record_strategy_route(
        name=f"target_integrity_adjudication_{int(turn_index or 0)}",
        description=(
            "Adjudicate a Lean-rejected target after unverified refutation "
            "commentary or semantic bridge-direction diagnostics."
        ),
        route_key=identity_key,
        score=0.6,
        phase=phase,
        turn_index=turn_index,
        metadata={
            "route_scope": "partial_route",
            "source": "target_integrity_adjudication",
            "target_integrity_adjudication": True,
            "target_integrity_signal_kinds": list(dict.fromkeys(signal_kinds)),
            "selected_work_type": str(selected_work_type or ""),
            "source_route_id": source_route_id,
            "source_obligation_id": source_obligation_id,
            "source_graph_node_id": source_graph_node_id,
            "source_repair_ticket_id": source_repair_ticket_id,
            "error_type": error_type,
        },
    )
    reason = (
        "adjudicate target integrity: Lean rejected the proof while the "
        "attempt contained unverified refutation commentary or an invalid "
        "bridge-direction calculation; prove the target from accepted "
        "micro-lemmas, replace the bad bridge with a verified smaller lemma, "
        "or Lean-check a counterexample/negation before retiring it"
    )
    shared_metadata = {
        "source": "target_integrity_adjudication",
        "target_integrity_adjudication": True,
        "target_integrity_signal_kinds": list(dict.fromkeys(signal_kinds)),
        "target_integrity_signal_matches": signal_matches,
        "target_integrity_signals": signal_records,
        "selected_work_type": str(selected_work_type or ""),
        "source_route_id": source_route_id,
        "source_obligation_id": source_obligation_id,
        "source_graph_node_id": source_graph_node_id,
        "source_repair_ticket_id": source_repair_ticket_id,
        "identity_key": identity_key,
        "formalization_required": True,
        "allow_root_equivalent_target_integrity_adjudication": True,
        **dossier.statement_environment_metadata(),
    }
    obligation = graph.record_missing_obligation(
        statement=target,
        reason=reason,
        source_node_id=root_id,
        route_id=route.node_id,
        phase=phase,
        turn_index=turn_index,
        error_type=error_type,
        metadata=shared_metadata,
    )
    replan = graph.record_replan_item(
        source_node_id=root_id,
        route_id=route.node_id,
        obligation_id=obligation.node_id,
        reason=reason,
        phase=phase,
        turn_index=turn_index,
        priority=0.75,
        metadata={
            **shared_metadata,
            "target_statement": target,
            "route_replan_requires_obligation": True,
        },
    )
    _increment_tool_metric(
        dossier,
        "mini_session_target_integrity_adjudication_materialized",
        1,
    )
    return [obligation.node_id], [replan.node_id], True


def _legacy_imports():
    from ensemble_prover.helper_salvage import HelperSalvager
    from ensemble_prover.mini_prover import (
        _analyze_lean_failure,
        _classify_giveup_signal,
        _format_lean_failure_feedback,
        _format_raw_lean_feedback,
        _giveup_decomposition_nudge,
        _helper_blocks_for_names,
        _helper_names_from_blocks,
        _lean_failure_all_goals_are_direct_local_closes,
        _manual_lean_failure_analysis,
        _prepend_repeated_failure_notice,
        _retrieve_repair_candidates,
    )
    from ensemble_prover.mini_tactic_closer import try_close_with_tactics
    from ensemble_prover.mini_repair import _retrieve_repair_candidates_async
    from ensemble_prover.proof_state_executor import (
        _proof_state_acceptance_preamble,
        _try_proof_state_child_closures,
        _try_proof_state_lemma_dag_helpers,
        _try_proof_state_salvaged_helper_assembly,
        _with_turn_budget_footer,
    )
    from ensemble_prover.proof_state_scheduler import (
        _retrieve_proof_state_node_candidates,
        _retrieve_proof_state_node_candidates_async,
    )

    return {
        "HelperSalvager": HelperSalvager,
        "analyze_lean_failure": _analyze_lean_failure,
        "classify_giveup_signal": _classify_giveup_signal,
        "format_lean_failure_feedback": _format_lean_failure_feedback,
        "format_raw_lean_feedback": _format_raw_lean_feedback,
        "giveup_decomposition_nudge": _giveup_decomposition_nudge,
        "helper_blocks_for_names": _helper_blocks_for_names,
        "helper_names_from_blocks": _helper_names_from_blocks,
        "lean_failure_all_goals_are_direct_local_closes": _lean_failure_all_goals_are_direct_local_closes,
        "manual_lean_failure_analysis": _manual_lean_failure_analysis,
        "prepend_repeated_failure_notice": _prepend_repeated_failure_notice,
        "retrieve_repair_candidates": _retrieve_repair_candidates,
        "retrieve_repair_candidates_async": _retrieve_repair_candidates_async,
        "try_close_with_tactics": try_close_with_tactics,
        "proof_state_acceptance_preamble": _proof_state_acceptance_preamble,
        "try_proof_state_child_closures": _try_proof_state_child_closures,
        "try_proof_state_lemma_dag_helpers": _try_proof_state_lemma_dag_helpers,
        "try_proof_state_salvaged_helper_assembly": _try_proof_state_salvaged_helper_assembly,
        "with_turn_budget_footer": _with_turn_budget_footer,
        "retrieve_proof_state_node_candidates": _retrieve_proof_state_node_candidates,
        "retrieve_proof_state_node_candidates_async": (
            _retrieve_proof_state_node_candidates_async
        ),
    }


def _record_turn_safely(recorder: Any, record: Dict[str, Any]) -> None:
    if recorder is None or not hasattr(recorder, "record_turn"):
        return
    try:
        recorder.record_turn(dict(record))
    except Exception:
        pass


def _supported_keyword_arguments(
    callable_obj: Any,
    values: Dict[str, Any],
) -> Dict[str, Any]:
    """Keep each supported compatibility keyword without retry-by-exception."""

    try:
        parameters = inspect.signature(callable_obj).parameters
    except (TypeError, ValueError):
        return dict(values)
    if any(
        parameter.kind is inspect.Parameter.VAR_KEYWORD
        for parameter in parameters.values()
    ):
        return dict(values)
    return {
        key: value
        for key, value in values.items()
        if key in parameters
        and parameters[key].kind
        in {
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
            inspect.Parameter.KEYWORD_ONLY,
        }
    }


async def run_post_failure_cascade(
    *,
    conv: Any,
    lean: Any,
    dossier: Any,
    proof_state: Any,
    proof: str,
    helpers: Sequence[str],
    lemma_dag_candidate_helpers: Sequence[str],
    check_lemmas: Sequence[str],
    context_helpers: Sequence[str],
    feedback_result: Any,
    feedback_source: str,
    proof_cache: Any = None,
    searcher: Any = None,
    repair_retrieval_enabled: bool = True,
    repair_retrieval_top_k: int = 6,
    proof_state_child_tactics_enabled: bool = True,
    proof_state_child_tactic_timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
    proof_state_child_tactic_max_candidates: int = 32,
    proof_state_child_goal_limit: int = 3,
    proof_state_decl_application_limit: int = 6,
    proof_state_batch_parallelism: int = 1,
    raw_feedback: bool = False,
    lean_check_tool_enabled: bool = True,
    recorder: Any = None,
    trace_prefix: str = "",
    turn: int = 0,
    max_turns: int = 0,
    role: str = "prove",
    llm_output: str = "",
    opaque_mode: bool = False,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
    allow_helper_decomposition: bool = True,
    recursion_depth: int = 0,
    max_recursion_depth: int = 3,
    defer_fresh_helper_children_to_llm: bool = False,
    proof_state_failure_context_enabled: bool = True,
    defer_proof_state_child_search: bool = False,
    repair_goal_statement: str = "",
    selected_work_item: Optional[Dict[str, Any]] = None,
    target_statement: str = "",
    event_context: Optional[Dict[str, Any]] = None,
    suppress_nonstructural_giveup_for_repair: bool = False,
    include_local_repair_diagnostic_spans: bool = False,
) -> PostFailureResult:
    """Run the post-failure cascade after a Lean rejection.

    Returns a ``PostFailureResult``. When ``solved`` is True, the
    caller should return ``(True, result.proof)`` immediately.
    Otherwise the caller appends ``result.feedback_text`` to ``conv``
    via ``conv.append_user(...)`` for the next turn.
    """

    primitives = _legacy_imports()
    effective_official_answer_payload_present = (
        official_answer_payload_present
        if official_answer_payload_present is not None
        else getattr(
            conv,
            "official_answer_payload_present",
            getattr(dossier, "official_answer_payload_present", None),
        )
    )
    result = PostFailureResult()
    result.deterministic_search_deferred = bool(defer_proof_state_child_search)
    synthetic_active_root_lift_feedback = _is_active_root_lift_feedback_source(
        feedback_source
    )
    proof_state_repair_enabled = bool(
        proof_state is not None
        and proof_state_failure_context_enabled
        and not synthetic_active_root_lift_feedback
    )
    proof_state_child_closure_enabled = bool(proof_state_repair_enabled)

    # ---- Phase 1: Failure analysis ----------------------------------
    if feedback_result is not None:
        result.failure_analysis = primitives["analyze_lean_failure"](feedback_result)
    else:
        note = (
            "answer-safe Lean feedback check accepted while the full check "
            "rejected; avoid relying on `_solution` unfolding"
            if feedback_source
            in {"answer_safe_check_accepted", "primary_check_with_answer_safe_pass"}
            else (
                "answer-safe Lean recheck was unavailable because verifier "
                "infrastructure failed; retry the check without diagnosing "
                "the submitted mathematics"
            )
        )
        result.failure_analysis = primitives["manual_lean_failure_analysis"](
            "answer_safe_recheck_infrastructure",
            note,
        )
    code_generation_failure = is_parse_error_failure(result.failure_analysis)
    if code_generation_failure and proof_state_repair_enabled:
        proof_state_repair_enabled = False
        proof_state_child_closure_enabled = False
        _record_turn_safely(
            recorder,
            {
                "phase": "post_failure_code_generation",
                "turn_in_phase": turn,
                "role": role,
                "error_type": str(result.failure_analysis.get("error_type") or ""),
                "verdict": "proof_state_repair_disabled_for_parse_error",
            },
        )

    selected_work = dict(selected_work_item or {})
    selected_work_type = str(selected_work.get("work_type") or "").strip()
    suppress_root_target_fallback = _selected_work_suppresses_root_target_fallback(
        selected_work,
        selected_work_type=selected_work_type,
    )
    event_base = dict(event_context or {})
    explicit_integrity_target = str(
        target_statement
        or repair_goal_statement
        or selected_work.get("target_statement")
        or ""
    ).strip()
    integrity_target = explicit_integrity_target
    if not integrity_target and not suppress_root_target_fallback:
        integrity_target = str(
            getattr(conv, "goal_statement", "")
            or getattr(dossier, "root_statement", "")
            or ""
        ).strip()
    result.target_integrity_signals = (
        classify_target_integrity_signals(
            llm_output=str(llm_output or ""),
            proof=str(proof or ""),
            failure_analysis=dict(result.failure_analysis or {}),
            target_statement=integrity_target,
            selected_work_type=selected_work_type,
        )
        if integrity_target
        else []
    )
    if result.target_integrity_signals:
        result.target_integrity_bypass_local_repair = any(
            bool(item.get("bypass_local_repair"))
            for item in result.target_integrity_signals
        )
        result.target_integrity_disable_proof_state_repair = any(
            bool(item.get("disable_proof_state_repair"))
            for item in result.target_integrity_signals
        )
        _increment_tool_metric(
            dossier,
            "mini_session_target_integrity_signals",
            len(result.target_integrity_signals),
        )
        for signal in result.target_integrity_signals:
            metric = str(signal.get("metric") or "").strip()
            if metric:
                _increment_tool_metric(dossier, metric, 1)
            _record_turn_safely(
                recorder,
                {
                    **event_base,
                    "phase": "target_integrity_signal",
                    "turn_in_phase": turn,
                    "role": role,
                    "kind": str(signal.get("kind") or ""),
                    "target_integrity_signal_kind": str(signal.get("kind") or ""),
                    "target_integrity_signal_kinds": [
                        str(item.get("kind") or "")
                        for item in result.target_integrity_signals
                    ],
                    "target_integrity_signals": list(
                        result.target_integrity_signals
                    ),
                    "match": str(signal.get("match") or ""),
                    "selected_work_type": selected_work_type,
                    "target_statement": integrity_target,
                    "verdict": "detected",
                },
            )
        (
            result.target_integrity_obligation_node_ids,
            result.target_integrity_replan_node_ids,
            result.target_integrity_adjudication_materialized,
        ) = _record_target_integrity_adjudication(
            dossier=dossier,
            target_statement=integrity_target,
            signals=result.target_integrity_signals,
            phase=role,
            turn_index=turn,
            selected_work_type=selected_work_type,
            selected_work_record=selected_work,
        )
        if (
            result.target_integrity_obligation_node_ids
            or result.target_integrity_replan_node_ids
        ):
            adjudication_verdict = (
                "materialized"
                if result.target_integrity_adjudication_materialized
                else "already_materialized"
            )
            _record_turn_safely(
                recorder,
                {
                    **event_base,
                    "phase": "target_integrity_adjudication",
                    "turn_in_phase": turn,
                    "role": role,
                    "selected_work_type": selected_work_type,
                    "target_statement": integrity_target,
                    "source_route_id": str(selected_work.get("route_id") or ""),
                    "source_obligation_id": str(
                        selected_work.get("obligation_id")
                        or selected_work.get("node_id")
                        or selected_work.get("graph_node_id")
                        or ""
                    ),
                    "source_graph_node_id": str(
                        selected_work.get("graph_node_id")
                        or selected_work.get("node_id")
                        or ""
                    ),
                    "obligation_node_ids": list(
                        result.target_integrity_obligation_node_ids
                    ),
                    "replan_node_ids": list(result.target_integrity_replan_node_ids),
                    "signal_kinds": [
                        str(signal.get("kind") or "")
                        for signal in result.target_integrity_signals
                    ],
                    "target_integrity_signal_kinds": [
                        str(signal.get("kind") or "")
                        for signal in result.target_integrity_signals
                    ],
                    "target_integrity_signals": list(
                        result.target_integrity_signals
                    ),
                    "verdict": adjudication_verdict,
                },
            )
        if result.target_integrity_disable_proof_state_repair:
            if proof_state_repair_enabled:
                _increment_tool_metric(
                    dossier,
                    "mini_session_target_integrity_proof_state_repair_bypassed",
                    1,
                )
                _record_turn_safely(
                    recorder,
                    {
                        **event_base,
                        "phase": "target_integrity_proof_state_repair",
                        "turn_in_phase": turn,
                        "role": role,
                        "selected_work_type": selected_work_type,
                        "target_statement": integrity_target,
                        "target_integrity_signal_kinds": [
                            str(signal.get("kind") or "")
                            for signal in result.target_integrity_signals
                        ],
                        "target_integrity_signals": list(
                            result.target_integrity_signals
                        ),
                        "verdict": "proof_state_repair_bypassed",
                    },
                )
            proof_state_repair_enabled = False

    # ---- Phase 2: Repair retrieval ----------------------------------
    if (
        repair_retrieval_enabled
        and (
            not suppress_root_target_fallback
            or bool(
                str(
                    repair_goal_statement
                    or target_statement
                    or selected_work.get("target_statement")
                    or ""
                ).strip()
            )
        )
        and not synthetic_active_root_lift_feedback
        and searcher is not None
        and not raw_feedback
    ):
        explicit_repair_query_goal = str(
            repair_goal_statement
            or target_statement
            or selected_work.get("target_statement")
            or ""
        ).strip()
        repair_query_goal = _repair_goal_statement_for_retrieval(
            explicit_goal_statement=explicit_repair_query_goal,
            dossier=dossier,
            conv=conv,
        )
        async_retrieve = primitives.get("retrieve_repair_candidates_async")
        redact_repair_solution_refs = (
            effective_solution_placeholder_suppression(
                suppress_solution_placeholders=bool(
                    getattr(dossier, "suppress_solution_placeholders", True)
                ),
                opaque_mode=bool(
                    getattr(dossier, "opaque_mode", opaque_mode)
                ),
                allow_official_answer_visibility=bool(
                    getattr(
                        dossier,
                        "allow_official_answer_visibility",
                        allow_official_answer_visibility,
                    )
                ),
                official_answer_payload_present=(
                    getattr(
                        dossier,
                        "official_answer_payload_present",
                        effective_official_answer_payload_present,
                    )
                ),
            )
            if dossier is not None
            else True
        )
        if callable(async_retrieve):
            async_kwargs = _supported_keyword_arguments(
                async_retrieve,
                {
                    "max_results": repair_retrieval_top_k,
                    "goal_statement_override": repair_query_goal,
                    "timeout_s": float(
                        getattr(searcher, "operation_timeout_s", 30.0) or 30.0
                    ),
                    "redact_solution_refs": redact_repair_solution_refs,
                },
            )
            block, record = await async_retrieve(
                searcher,
                conv,
                result.failure_analysis,
                **async_kwargs,
            )
        else:
            sync_retrieve = primitives["retrieve_repair_candidates"]
            sync_kwargs = _supported_keyword_arguments(
                sync_retrieve,
                {
                    "max_results": repair_retrieval_top_k,
                    "goal_statement_override": repair_query_goal,
                    "redact_solution_refs": redact_repair_solution_refs,
                },
            )
            block, record = sync_retrieve(
                searcher,
                conv,
                result.failure_analysis,
                **sync_kwargs,
            )
        result.repair_retrieval_block = block
        result.repair_retrieval_record = record

    # ---- Phase 3: Update proof_state with failure -------------------
    if proof_state_repair_enabled:
        result.proof_state_update = proof_state.record_failure(
            phase=role,
            turn_index=turn,
            analysis=result.failure_analysis,
            repair_retrieval=result.repair_retrieval_record,
        )
        (
            result.failure_residual_obligation_node_ids,
            result.failure_residual_replan_node_ids,
        ) = _record_failure_residual_obligations(
            dossier=dossier,
            proof_state_update=result.proof_state_update,
            failure_analysis=result.failure_analysis,
            phase=role,
            turn_index=turn,
            feedback_source=feedback_source,
        )
        node_retrieval_top_k = max(
            0,
            min(6, int(repair_retrieval_top_k or 0)),
        )
        local_helper_blocks = (
            dossier.verified_helper_blocks()
            if dossier is not None
            else ()
        )
        retrieval_searcher = searcher if repair_retrieval_enabled else None
        if node_retrieval_top_k <= 0 and local_helper_blocks:
            node_retrieval_top_k = 3
        if (
            (retrieval_searcher is not None or local_helper_blocks)
            and node_retrieval_top_k > 0
        ):
            async_proof_state_retrieve = primitives.get(
                "retrieve_proof_state_node_candidates_async"
            )
            if callable(async_proof_state_retrieve):
                result.proof_state_retrieval = list(
                    await async_proof_state_retrieve(
                        retrieval_searcher,
                        proof_state,
                        max_nodes=proof_state_child_goal_limit,
                        max_results=node_retrieval_top_k,
                        local_helper_blocks=local_helper_blocks,
                        timeout_s=float(
                            getattr(searcher, "operation_timeout_s", 30.0)
                            or 30.0
                        ),
                    )
                )
            else:
                result.proof_state_retrieval = list(
                    primitives["retrieve_proof_state_node_candidates"](
                        retrieval_searcher,
                        proof_state,
                        max_nodes=proof_state_child_goal_limit,
                        max_results=node_retrieval_top_k,
                        local_helper_blocks=local_helper_blocks,
                    )
                )
        proof_state.sync_to_graph(
            dossier,
            phase="proof_state_update",
            turn_index=turn,
        )

    # ---- Phase 3a: give-up/off-ramp classifier ---------------------
    # This must run BEFORE helper triage/salvage. Otherwise a response
    # whose substance is "full formalization would proceed later" can
    # still materialize its sorry-stub "missing prerequisite" as a durable
    # child_goal before the classifier notices the off-ramp language.
    giveup = None
    giveup_feedback_text = ""
    concrete_giveup_candidates: List[str] = []
    try:
        if suppress_nonstructural_giveup_for_repair:
            relaxed_giveup = primitives["classify_giveup_signal"](
                str(llm_output or ""),
                proof,
                require_structural_collapse=False,
            )
            giveup = primitives["classify_giveup_signal"](
                str(llm_output or ""),
                proof,
                require_structural_collapse=True,
            )
            if relaxed_giveup is not None and giveup is None:
                result.local_repair_giveup_suppressed = True
                result.suppressed_giveup_cluster = str(
                    relaxed_giveup.get("cluster") or ""
                )
                result.suppressed_giveup_match = str(
                    relaxed_giveup.get("match") or ""
                )
                _record_turn_safely(
                    recorder,
                    {
                        "phase": "post_failure_giveup_suppressed",
                        "turn_in_phase": turn,
                        "role": role,
                        "giveup_cluster": result.suppressed_giveup_cluster,
                        "giveup_match": result.suppressed_giveup_match,
                        "verdict": "local_repair_takes_precedence",
                    },
                )
        else:
            giveup = primitives["classify_giveup_signal"](
                str(llm_output or ""),
                proof,
                require_structural_collapse=False,
            )
    except Exception as exc:  # noqa: BLE001 — telemetry only; cascade continues
        if recorder is not None and hasattr(recorder, "record_turn"):
            try:
                recorder.record_turn({
                    "phase": "giveup_classifier",
                    "turn_in_phase": turn,
                    "role": role,
                    "exception_type": type(exc).__name__,
                    "exception_text": str(exc)[:500],
                    "verdict": "giveup_classifier_error",
                })
            except Exception:
                pass
    if giveup is not None:
        result.giveup_cluster = giveup["cluster"]
        result.giveup_match = giveup["match"]
        concrete_giveup_candidates = _concrete_giveup_helper_candidates(
            helpers,
            lemma_dag_candidate_helpers,
        )
        try:
            nudge = primitives["giveup_decomposition_nudge"](
                giveup["cluster"],
                opaque_mode=bool(opaque_mode),
                allow_official_answer_visibility=bool(
                    allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    effective_official_answer_payload_present
                ),
                allow_helper_decomposition=bool(allow_helper_decomposition),
                matched_phrase=giveup["match"],
                recursion_depth=int(recursion_depth or 0),
                max_recursion_depth=int(
                    max_recursion_depth if max_recursion_depth is not None else 3
                ),
                role=role,
            )
        except TypeError:
            nudge = primitives["giveup_decomposition_nudge"](
                giveup["cluster"],
                opaque_mode=bool(opaque_mode),
                allow_official_answer_visibility=bool(
                    allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    effective_official_answer_payload_present
                ),
                allow_helper_decomposition=bool(allow_helper_decomposition),
                matched_phrase=giveup["match"],
                recursion_depth=int(recursion_depth or 0),
                max_recursion_depth=int(
                    max_recursion_depth if max_recursion_depth is not None else 3
                ),
            )
        result.feedback_text = primitives["with_turn_budget_footer"](
            nudge,
            role=role,
            turn=turn,
            max_turns=max_turns,
        )
        giveup_feedback_text = result.feedback_text
        result.feedback_mode = "giveup_active_proof_redirect"
        if not (
            proof_state_repair_enabled
            and dossier is not None
            and bool(allow_helper_decomposition)
            and concrete_giveup_candidates
        ):
            return result

    # ---- Phase 3b: Rejected complete-helper triage ------------------
    # When the LLM emits helper declarations plus a main proof, the
    # combined Lean check can fail even if the helper declarations are
    # mathematically useful. HelperSalvager only persists helpers that
    # already compile. The missing piece was rejected-but-well-formed
    # helpers: their statements should become durable child_goal nodes
    # so RecursiveHelperProverAction can attack them in fresh scoped
    # sub-sessions.
    triage_candidates: List[str] = []
    seen_triage_candidates = set()
    candidate_sources = (
        concrete_giveup_candidates
        if giveup is not None
        else list(helpers or ()) + list(lemma_dag_candidate_helpers or ())
    )
    for helper_block in candidate_sources:
        source = str(helper_block or "").strip()
        if not source or source in seen_triage_candidates:
            continue
        seen_triage_candidates.add(source)
        triage_candidates.append(source)
    if (
        proof_state_repair_enabled
        and dossier is not None
        and triage_candidates
        and bool(allow_helper_decomposition)
    ):
        ensure_task = getattr(proof_state, "ensure_decomposition_task_open", None)
        if callable(ensure_task):
            child_ids_before = {
                str(node_id)
                for node_id, node in (getattr(proof_state, "nodes", {}) or {}).items()
                if getattr(node, "kind", "") == "child_goal"
            }
            decomposition_links_before = {
                str(node_id): set(
                    str(child_id)
                    for child_id in getattr(node, "child_node_ids", ()) or ()
                )
                for node_id, node in (getattr(proof_state, "nodes", {}) or {}).items()
                if getattr(node, "kind", "") == "decomposition_task"
            }
            task_id = ""
            try:
                task_id = str(
                    ensure_task(
                        source=f"rejected_complete_helpers:{role}:turn={turn}",
                        blocker=(
                            "Lean rejected a helpers+main-proof response; "
                            "triage helper declarations as durable child goals"
                        ),
                        reuse_closed_structural=False,
                    )
                    or ""
                )
            except TypeError:
                # Older/minimal proof_state test doubles may not know
                # the reuse_closed_structural option. Retry the legacy
                # call shape rather than dropping helper triage.
                try:
                    task_id = str(
                        ensure_task(
                            source=f"rejected_complete_helpers:{role}:turn={turn}",
                            blocker=(
                                "Lean rejected a helpers+main-proof response; "
                                "triage helper declarations as durable child goals"
                            ),
                        )
                        or ""
                    )
                except Exception as exc:  # noqa: BLE001 — telemetry only
                    _record_turn_safely(
                        recorder,
                        {
                            "phase": "proof_state_rejected_helper_triage",
                            "turn_in_phase": turn,
                            "exception_type": type(exc).__name__,
                            "exception_text": str(exc)[:500],
                            "verdict": "rejected_helper_triage_task_open_failed",
                        },
                    )
            except Exception as exc:  # noqa: BLE001 — telemetry only; cascade continues
                _record_turn_safely(
                    recorder,
                    {
                        "phase": "proof_state_rejected_helper_triage",
                        "turn_in_phase": turn,
                        "exception_type": type(exc).__name__,
                        "exception_text": str(exc)[:500],
                        "verdict": "rejected_helper_triage_task_open_failed",
                    },
                )
            task = (getattr(proof_state, "nodes", {}) or {}).get(task_id)
            if (
                task_id
                and task is not None
                and getattr(task, "kind", "") == "decomposition_task"
                and getattr(task, "status", "") == "open"
            ):
                accepted_helpers: List[str] = []
                try:
                    accepted_helpers = await primitives[
                        "try_proof_state_lemma_dag_helpers"
                    ](
                        conv=conv,
                        lean=lean,
                        dossier=dossier,
                        proof_state=proof_state,
                        helpers=triage_candidates,
                        recorder=recorder,
                        trace_prefix=trace_prefix,
                        turn=turn,
                        timeout_s=proof_state_child_tactic_timeout_s,
                        proof_cache=proof_cache,
                        target_task_id=task_id,
                    )
                except Exception as exc:  # noqa: BLE001 — telemetry only; cascade continues
                    _record_turn_safely(
                        recorder,
                        {
                            "phase": "proof_state_rejected_helper_triage",
                            "turn_in_phase": turn,
                            "task_node_id": task_id,
                            "exception_type": type(exc).__name__,
                            "exception_text": str(exc)[:500],
                            "verdict": "rejected_helper_triage_failed",
                        },
                    )
                child_ids_after = {
                    str(node_id)
                    for node_id, node in (getattr(proof_state, "nodes", {}) or {}).items()
                    if getattr(node, "kind", "") == "child_goal"
                }
                new_child_ids = sorted(child_ids_after - child_ids_before)
                linked_child_ids = sorted(
                    {
                        str(child_id)
                        for node_id, node in (
                            getattr(proof_state, "nodes", {}) or {}
                        ).items()
                        if getattr(node, "kind", "") == "decomposition_task"
                        for child_id in getattr(node, "child_node_ids", ()) or ()
                        if str(child_id) in child_ids_before
                        and str(child_id)
                        not in decomposition_links_before.get(str(node_id), set())
                    }
                )
                actionable_child_ids = sorted(set(new_child_ids) | set(linked_child_ids))
                if accepted_helpers:
                    result.rejected_helper_triage_accepted.extend(accepted_helpers)
                    result.proof_state_helpers.extend(accepted_helpers)
                if actionable_child_ids:
                    result.rejected_helper_child_node_ids.extend(actionable_child_ids)
                if linked_child_ids:
                    result.rejected_helper_linked_child_node_ids.extend(linked_child_ids)
                if accepted_helpers or actionable_child_ids:
                    proof_state.sync_to_graph(
                        dossier,
                        phase="proof_state_rejected_helper_triage",
                        turn_index=turn,
                    )
                if actionable_child_ids and defer_fresh_helper_children_to_llm:
                    result.deferred_rejected_helper_children_to_recursive_helper = True
                    _record_turn_safely(
                        recorder,
                        {
                            "phase": "proof_state_rejected_helper_triage_child_routing",
                            "turn_in_phase": turn,
                            "new_child_node_ids": list(actionable_child_ids),
                            "linked_child_node_ids": list(linked_child_ids),
                            "verdict": "deferred_to_recursive_helper_prover",
                        },
                    )
            elif task_id:
                _record_turn_safely(
                    recorder,
                    {
                        "phase": "proof_state_rejected_helper_triage",
                        "turn_in_phase": turn,
                        "task_node_id": task_id,
                        "task_kind": getattr(task, "kind", ""),
                        "task_status": getattr(task, "status", ""),
                        "verdict": "rejected_helper_triage_task_not_open",
                    },
                )
    if giveup is not None and not (
        result.rejected_helper_triage_accepted
        or result.rejected_helper_child_node_ids
    ):
        result.feedback_text = giveup_feedback_text
        result.feedback_mode = "giveup_active_proof_redirect"
        return result

    helper_decomposition_enabled = bool(allow_helper_decomposition)
    if not helper_decomposition_enabled and (
        proof_state_child_tactics_enabled
        or helpers
        or lemma_dag_candidate_helpers
    ):
        _record_turn_safely(
            recorder,
            {
                "phase": "proof_only_post_failure_guard",
                "turn_in_phase": turn,
                "role": role,
                "helper_candidate_count": len(list(helpers or ())),
                "lemma_dag_candidate_count": len(
                    list(lemma_dag_candidate_helpers or ())
                ),
                "proof_state_child_tactics_enabled": bool(
                    proof_state_child_tactics_enabled
                ),
                "verdict": "helper_decomposition_skipped",
            },
        )

    # ---- Phase 4: Proof-state child closures (may solve root) -------
    if (
        helper_decomposition_enabled
        and proof_state_child_closure_enabled
        and proof_state_child_tactics_enabled
        and not result.deterministic_search_deferred
    ):
        target_node_ids = None
        if result.deferred_rejected_helper_children_to_recursive_helper:
            deferred_child_ids = set(result.rejected_helper_child_node_ids)
            nondeferred_open_child_ids = [
                str(node_id)
                for node_id, node in (getattr(proof_state, "nodes", {}) or {}).items()
                if getattr(node, "kind", "") == "child_goal"
                and getattr(node, "status", "") == "open"
                and str(node_id) not in deferred_child_ids
            ]
            if not nondeferred_open_child_ids:
                target_node_ids = ()
            else:
                target_node_ids = tuple(nondeferred_open_child_ids)
        if target_node_ids == ():
            state_ok, state_proof, ps_helpers = False, None, []
        else:
            state_ok, state_proof, ps_helpers = await primitives["try_proof_state_child_closures"](
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                recorder=recorder,
                trace_prefix=trace_prefix,
                turn=turn,
                timeout_s=proof_state_child_tactic_timeout_s,
                max_candidates=proof_state_child_tactic_max_candidates,
                max_nodes=proof_state_child_goal_limit,
                max_decl_applications=proof_state_decl_application_limit,
                batch_parallelism=proof_state_batch_parallelism,
                proof_cache=proof_cache,
                target_node_ids=target_node_ids,
            )
        result.proof_state_helpers.extend(ps_helpers or ())
        proof_state.sync_to_graph(
            dossier,
            phase="proof_state_child_closure",
            turn_index=turn,
        )
        if state_ok and state_proof:
            result.solved = True
            result.proof = state_proof
            result.solved_via = "proof_state_child"
            return result
    elif (
        helper_decomposition_enabled
        and proof_state_child_closure_enabled
        and proof_state_child_tactics_enabled
        and result.deterministic_search_deferred
    ):
        _record_turn_safely(
            recorder,
            {
                "phase": "post_failure_repair_first",
                "turn_in_phase": turn,
                "role": role,
                "verdict": "proof_state_child_search_deferred",
            },
        )

    # ---- Phase 5: Helper salvage ------------------------------------
    salvage_candidates = list(helpers or lemma_dag_candidate_helpers or [])
    helper_probe_timeout = float(proof_state_child_tactic_timeout_s or 0.0)
    helper_probe_candidates = int(proof_state_child_tactic_max_candidates or 0)
    salvage_result = None
    if (
        helper_decomposition_enabled
        and salvage_candidates
        and dossier is not None
        and helper_probe_timeout > 0.0
    ):
        from ensemble_prover.helper_salvage import collect_open_child_targets
        from ensemble_prover.proof_state_executor import _proof_state_check_preamble

        salvager = primitives["HelperSalvager"](
            lean,
            preamble=_proof_state_check_preamble(conv),
            answer_safe_preamble=str(getattr(conv, "preamble", "") or ""),
            timeout_s=helper_probe_timeout,
            relevance_gate_root_statement=str(
                getattr(dossier, "root_statement", "") or ""
            ),
            relevance_gate_open_targets=collect_open_child_targets(proof_state),
        )
        salvage_result = await salvager.salvage(
            salvage_candidates,
            dossier=dossier,
            phase=role,
            turn_index=turn,
        )
        invalidated_helpers = [
            *list(getattr(salvage_result, "replaced", []) or []),
            *list(getattr(salvage_result, "evicted", []) or []),
        ]
        if invalidated_helpers and proof_state is not None:
            try:
                proof_state.reconcile_with_dossier(dossier)
                proof_state.invalidate_assembly_contracts_for_helpers(
                    invalidated_helpers,
                    phase=role,
                    turn_index=turn,
                    conservative=True,
                )
            except Exception:
                pass
        if salvage_result.accepted:
            result.salvaged_helper_names = list(salvage_result.accepted)
            if proof_cache is not None:
                for helper_name in salvage_result.accepted:
                    helper_record = dossier.verified_helpers.get(helper_name)
                    if helper_record is not None:
                        from ensemble_prover.proof_state_executor import (
                            _proof_state_check_preamble,
                        )

                        store_verified_helper_for_dossier(
                            proof_cache,
                            helper_record.source,
                            preamble=_proof_state_check_preamble(conv),
                            dossier=dossier,
                            phase=f"{role}:helper_salvage",
                        )

            # ---- Phase 6: Salvaged helper assembly ------------------
            if (
                proof_state_child_closure_enabled
                and proof_state_child_tactics_enabled
            ):
                state_ok, state_proof, salvaged_state_helpers = await primitives[
                    "try_proof_state_salvaged_helper_assembly"
                ](
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    helper_names=salvage_result.accepted,
                    recorder=recorder,
                    trace_prefix=trace_prefix,
                    turn=turn,
                    timeout_s=helper_probe_timeout,
                    max_nodes=proof_state_child_goal_limit,
                    proof_cache=proof_cache,
                    phase="helper_salvage",
                )
                result.proof_state_helpers.extend(salvaged_state_helpers or ())
                proof_state.sync_to_graph(
                    dossier,
                    phase="helper_salvage_proof_state_assembly",
                    turn_index=turn,
                )
                if state_ok and state_proof:
                    result.solved = True
                    result.proof = state_proof
                    result.solved_via = "helper_salvage_assembly"
                    return result

            # ---- Phase 7: Helper-salvage root tactic close ----------
            if helper_probe_candidates > 0 and not suppress_root_target_fallback:
                root_tactic = await primitives["try_close_with_tactics"](
                    lean,
                    conv.goal_statement,
                    primitives["proof_state_acceptance_preamble"](conv),
                    dossier.verified_helper_blocks(),
                    timeout_s=helper_probe_timeout,
                    max_candidates=max(1, helper_probe_candidates),
                    opaque_mode=bool(getattr(conv, "opaque_mode", True)),
                    allow_official_answer_visibility=bool(
                        getattr(conv, "allow_official_answer_visibility", False)
                    ),
                    official_answer_payload_present=(
                        effective_official_answer_payload_present
                    ),
                    attempt_observer=dossier_lean_attempt_observer(
                        dossier,
                        "salvage_root_tactic",
                    ),
                )
                # H4 fix (2026-05-08): emit the legacy recorder event so
                # tactic_solved / tactic_rejected / tactic_skipped tags
                # don't disappear from the JSONL stream. Mirror
                # mini_prover.py:4884-4907.
                success_attempt = next(
                    (
                        attempt
                        for attempt in getattr(root_tactic, "attempts", []) or []
                        if isinstance(attempt, dict) and attempt.get("ok")
                    ),
                    None,
                )
                helper_salvage_record = {
                    "phase": "helper_salvage_root_tactic",
                    "turn_in_phase": turn,
                    "accepted_helpers": list(salvage_result.accepted),
                    "tactic_candidate_count": getattr(root_tactic, "candidate_count", 0),
                    **tactic_attempt_telemetry_fields(
                        getattr(root_tactic, "attempts", []) or []
                    ),
                    "tactic_attempts": (getattr(root_tactic, "attempts", []) or [])[:10],
                    "tactic_success_attempt": success_attempt,
                    "tactic_elapsed_s": getattr(root_tactic, "elapsed_s", 0.0),
                    "tactic_exit_reason": getattr(root_tactic, "exit_reason", ""),
                    "verdict": (
                        "tactic_solved" if root_tactic.ok else "tactic_rejected"
                    ),
                }
                root_tactic_contract_status: Dict[str, Any] = {}
                root_tactic_finalization_rejected = False

                def _emit_helper_salvage_root_tactic_record() -> None:
                    result.helper_salvage_root_tactic_record = helper_salvage_record
                    if recorder is not None and hasattr(recorder, "record_turn"):
                        try:
                            recorder.record_turn(dict(helper_salvage_record))
                        except Exception:
                            pass

                if root_tactic.ok and root_tactic.proof:
                    from ensemble_prover.mini_root_tactic import (
                        root_tactic_success_contract_status,
                    )

                    root_tactic_contract_status = root_tactic_success_contract_status(
                        dossier,
                        proof=root_tactic.proof,
                        helper_blocks=dossier.verified_helper_blocks(),
                        success_attempt=success_attempt,
                        phase="helper_salvage_root_tactic",
                        turn_index=turn,
                        target_statement=conv.goal_statement,
                    )
                    helper_salvage_record["route_assembly_contract_status"] = (
                        root_tactic_contract_status
                    )
                    if not bool(root_tactic_contract_status.get("ready")):
                        helper_salvage_record["verdict"] = (
                            "root_route_contract_not_ready"
                        )
                        helper_salvage_record["route_contract_verdict"] = str(
                            root_tactic_contract_status.get("verdict") or ""
                        )
                if (
                    root_tactic.ok
                    and root_tactic.proof
                    and bool(root_tactic_contract_status.get("ready"))
                ):
                    from ensemble_prover.root_finalization import (
                        finalize_root_solution,
                        root_verification_certificate,
                    )

                    route_helper_names = [
                        str(name or "").strip()
                        for name in list(
                            root_tactic_contract_status.get("helper_names") or []
                        )
                        if str(name or "").strip()
                    ]
                    helper_blocks_for_names = primitives.get(
                        "helper_blocks_for_names",
                        lambda blocks, names: [
                            block
                            for block in list(blocks or [])
                            if any(str(name or "") in str(block or "") for name in names)
                        ],
                    )
                    replay_helpers = helper_blocks_for_names(
                        dossier.verified_helper_blocks(),
                        route_helper_names,
                    )
                    helper_names = route_helper_names or primitives[
                        "helper_names_from_blocks"
                    ](replay_helpers)
                    finalization = finalize_root_solution(
                        dossier=dossier,
                        proof_state=proof_state,
                        proof=root_tactic.proof,
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        phase="helper_salvage_root_tactic",
                        turn_index=turn,
                        route_id=str(
                            root_tactic_contract_status.get("route_id")
                            or root_tactic_contract_status.get("created_route_id")
                            or ""
                        ),
                        dependency_node_ids=tuple(
                            str(node_id or "").strip()
                            for node_id in list(
                                root_tactic_contract_status.get("dependency_node_ids")
                                or root_tactic_contract_status.get("required_node_ids")
                                or []
                            )
                            if str(node_id or "").strip()
                        ),
                        target_statement=str(
                            getattr(dossier, "root_statement", "")
                            or getattr(conv, "goal_statement", "")
                            or ""
                        ),
                        # Helper-free closes have no route to bind; requiring a
                        # route contract would reject a Lean-accepted proof.
                        require_route_contract=(
                            str(root_tactic_contract_status.get("verdict") or "")
                            != "root_tactic_no_helper_dependencies"
                        ),
                        verification_certificate=root_verification_certificate(
                            accepted=True,
                            proof=root_tactic.proof,
                            phase="helper_salvage_root_tactic",
                            turn_index=turn,
                            target_statement=str(
                                getattr(dossier, "root_statement", "")
                                or getattr(conv, "goal_statement", "")
                                or ""
                            ),
                            replay_helpers=replay_helpers,
                            helper_names=helper_names,
                            output=str(
                                (success_attempt or {}).get("output")
                                or (success_attempt or {}).get("output_preview")
                                or ""
                            ),
                            source="post_failure_helper_salvage_root_tactic",
                        ),
                        require_verification_certificate=True,
                    )
                    if not finalization.accepted:
                        helper_salvage_record["verdict"] = (
                            "root_finalization_rejected"
                        )
                        helper_salvage_record["root_finalization_verdict"] = (
                            finalization.verdict
                        )
                        root_tactic_finalization_rejected = True
                        _emit_helper_salvage_root_tactic_record()
                    else:
                        _emit_helper_salvage_root_tactic_record()
                        result.solved = True
                        result.proof = root_tactic.proof
                        result.solved_via = "helper_salvage_root_tactic"
                        return result
                if (
                    root_tactic.ok
                    and root_tactic.proof
                    and not root_tactic_finalization_rejected
                    and not bool(root_tactic_contract_status.get("ready"))
                ):
                    replay_helpers = dossier.verified_helper_blocks()
                    helper_names = primitives["helper_names_from_blocks"](replay_helpers)
                    dossier.record_attempt(
                        phase="helper_salvage_root_tactic",
                        turn_index=turn,
                        proof=root_tactic.proof,
                        helper_names=helper_names,
                        verdict="root_route_contract_not_ready",
                        metadata={
                            "route_assembly_contract_status": (
                                root_tactic_contract_status
                            ),
                        },
                    )
                if result.helper_salvage_root_tactic_record is None:
                    _emit_helper_salvage_root_tactic_record()
            elif helper_probe_candidates <= 0:
                # H4 fix: legacy mini_prover.py:4855-4875 emits a
                # tactic_skipped record when the budget zeros it out.
                helper_salvage_record = {
                    "phase": "helper_salvage_root_tactic",
                    "turn_in_phase": turn,
                    "accepted_helpers": list(salvage_result.accepted),
                    "tactic_candidate_count": 0,
                    "tactic_attempts": [],
                    "tactic_exit_reason": "tactic_budget_disabled",
                    "verdict": "tactic_skipped",
                }
                result.helper_salvage_root_tactic_record = helper_salvage_record
                if recorder is not None and hasattr(recorder, "record_turn"):
                    try:
                        recorder.record_turn(dict(helper_salvage_record))
                    except Exception:
                        pass

    # ---- Phase 8: Compose feedback text -----------------------------
    if raw_feedback and feedback_result is not None:
        lean_feedback = primitives["format_raw_lean_feedback"](feedback_result)
        result.feedback_mode = "raw"
    else:
        # Fix 2 follow-up (2026-05-22): the session-path cascade is the
        # actually-exercised feedback emitter (the legacy mini_prover.py
        # call site is NOT reached through prove_problem_via_session).
        # Pass ``dossier`` so the helper-inventory injection in
        # ``FailureAnalyzer.format_feedback`` actually fires when the
        # LLM cites a hallucinated mini_* identifier. Without this kwarg
        # the prior fix was dead in production despite the unit tests.
        try:
            lean_feedback = primitives["format_lean_failure_feedback"](
                result.failure_analysis,
                search_enabled=searcher is not None,
                check_enabled=lean_check_tool_enabled,
                role=role,
                dossier=dossier,
            )
        except TypeError:
            try:
                lean_feedback = primitives["format_lean_failure_feedback"](
                    result.failure_analysis,
                    search_enabled=searcher is not None,
                    check_enabled=lean_check_tool_enabled,
                    dossier=dossier,
                )
            except TypeError:
                lean_feedback = primitives["format_lean_failure_feedback"](
                    result.failure_analysis,
                    search_enabled=searcher is not None,
                    check_enabled=lean_check_tool_enabled,
                )
        prepend_repeat_notice = primitives.get(
            "prepend_repeated_failure_notice",
            lambda feedback, _conv, _analysis: feedback,
        )
        lean_feedback = prepend_repeat_notice(
            lean_feedback,
            conv,
            result.failure_analysis,
        )
        result.feedback_mode = (
            "structured_fallback_no_feedback_result"
            if raw_feedback
            else "structured"
        )
    if result.repair_retrieval_block and not synthetic_active_root_lift_feedback:
        lean_feedback = lean_feedback.rstrip() + "\n\n" + result.repair_retrieval_block
    if include_local_repair_diagnostic_spans and not synthetic_active_root_lift_feedback:
        diagnostic_block = _local_repair_diagnostic_span_block(
            result.failure_analysis,
            feedback_result=feedback_result,
            format_raw_feedback=primitives.get("format_raw_lean_feedback"),
        )
        if diagnostic_block:
            lean_feedback = lean_feedback.rstrip() + "\n\n" + diagnostic_block
            result.local_repair_diagnostics_included = True
    if synthetic_active_root_lift_feedback:
        lean_feedback = _suppress_active_root_lift_feedback_text(lean_feedback)
    if result.local_repair_giveup_suppressed:
        matched = _prompt_safe_inline_text(
            result.suppressed_giveup_match or result.suppressed_giveup_cluster,
            limit=160,
        )
        lean_feedback = (
            lean_feedback.rstrip()
            + "\n\n"
            + "Local repair priority: Lean produced concrete diagnostics for "
            + "the submitted proof, so repair this exact proof before pivoting "
            + "to decomposition or give-up language."
        )
        if matched:
            lean_feedback += f" The non-terminal off-ramp phrase was: `{matched}`."
    integrity_feedback = target_integrity_feedback(result.target_integrity_signals)
    if integrity_feedback:
        lean_feedback = lean_feedback.rstrip() + "\n\n" + integrity_feedback
    lean_feedback = primitives["with_turn_budget_footer"](
        lean_feedback,
        role=role,
        turn=turn,
        max_turns=max_turns,
    )
    if result.salvaged_helper_names:
        lean_feedback = (
            lean_feedback.rstrip()
            + "\n\n"
            + "Verified helper salvage: the following helper declarations "
            + "compiled in the answer-safe Lean environment and will be "
            + "available in future turns: "
            + ", ".join(
                f"`{_prompt_safe_inline_text(name, limit=120)}`"
                for name in result.salvaged_helper_names
            )
            + "."
        )
    if result.proof_state_helpers:
        lean_feedback = (
            lean_feedback.rstrip()
            + "\n\n"
            + "Proof-state scheduler proved these child helper(s), but "
            + "root assembly still needs one more step: "
            + ", ".join(
                f"`{_prompt_safe_inline_text(name, limit=120)}`"
                for name in result.proof_state_helpers
            )
            + ". Use them directly in the next root proof."
        )
    if result.rejected_helper_child_node_ids:
        if result.deferred_rejected_helper_children_to_recursive_helper:
            child_note = (
                "Proof-state scheduler recorded the helper declarations from "
                "this rejected block as open child goals. Recursive helper "
                "proving is enabled, so the scheduler will attack those child "
                "goals before returning to root assembly."
            )
        else:
            child_note = (
                "Proof-state scheduler recorded the helper declarations from "
                "this rejected block as open child goals for subsequent "
                "retrieval, tactic search, or recursive helper proving."
            )
        lean_feedback = lean_feedback.rstrip() + "\n\n" + child_note
        if result.giveup_cluster:
            result.feedback_mode = "giveup_helper_decomposition_triaged"
    result.feedback_text = lean_feedback
    return result
