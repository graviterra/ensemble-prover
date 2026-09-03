"""Execute one bounded, typed LLM conversation turn.

The action runs the tool loop, extracts helpers and a candidate proof, applies
structural policy gates, verifies candidates with Lean, and invokes the
post-failure repair/salvage cascade when needed. It updates conversation and
dossier state and returns root-finalization candidates to ``MiniSession``;
centralized session application owns budgets, stagnation, and normalized event
accounting. Absolute turn indexes remain stable in recorded outcomes.
"""

from __future__ import annotations

import asyncio
import copy
import hashlib
import json
import math
import re
import time
import uuid
from dataclasses import replace, is_dataclass
from itertools import combinations, islice
from types import SimpleNamespace
from typing import (
    Any,
    Callable,
    ClassVar,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Tuple,
)

from ensemble_prover.contract_identity import has_lean_contract_identity
from ensemble_prover.mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ensemble_prover.formalization_guardrails import (
    is_parse_error_failure,
    needs_unknown_identifier_api_search,
    parse_error_repair_reason,
    repeated_unknown_identifier_without_api_search,
    tool_log_has_api_grounding,
    unknown_identifier_name,
)
from ensemble_prover.llm_error_policy import classify_llm_error_text, llm_failure_scope
from ensemble_prover.mini_policy import (
    _GRAPH_SELECTED_WORK_SCOPE_KEY,
    _REPAIR_FEEDBACK,
    _conversation_official_answer_visible,
    _is_history_compaction_summary,
    _is_stable_handoff_message,
    _message_repair_semantics,
    _repair_self_check_durable_submission_evidence,
    _repair_self_check_matches_submission as _policy_repair_self_check_matches_submission,
    _repair_self_check_non_verdict_is_compliant,
)
from ensemble_prover.lean_syntax import split_lean_top_level_implications
from ensemble_prover.mini_temperature import MiniPhaseTemperatures
from ensemble_prover.proof_dossier import (
    _prompt_safe_inline_text,
    active_root_disproof_certificate_is_valid,
    active_root_target_statement,
    active_root_targets_for_frame,
    helper_decl_name,
    is_answer_unsafe_statement_text,
    selected_work_has_explicit_cognition,
    text_hash,
    verified_helper_semantic_statement_changed,
    verified_helper_surface_statement_changed,
)
from ensemble_prover.proof_state_cache import store_verified_helper_for_dossier
from ensemble_prover.pricing import (
    lookup_openrouter_reasoning_capabilities,
    provider_for_base_url,
)
from ensemble_prover.provider_tool_protocol import mini_request_envelope_policy
from ensemble_prover.proof_graph import (
    graph_negated_statement_key,
    graph_node_frontier_quarantined,
    graph_statement_closed_premises,
    graph_statement_contract_ambiguities,
    graph_statement_contract_profile,
    graph_statement_has_circular_premise,
    graph_statement_is_executable,
    graph_statement_key,
    graph_statement_leading_contract,
    graph_statement_leading_telescope_is_universal,
    graph_statement_parent_existential_payload_premise,
    graph_statement_root_equivalent,
    helper_decl_body,
    helper_decl_kind,
    helper_decl_statement,
)
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ensemble_prover.proof_lineage import (
    ProofLineageEnvelope,
    lean_residual_identity,
    proof_candidate_identity,
    structural_statement_identity,
)
from ensemble_prover.target_integrity import (
    classify_target_integrity_signals,
    target_integrity_feedback,
)
from ensemble_prover.tactic_attempt_telemetry import (
    dossier_lean_attempt_observer,
    tactic_attempt_telemetry_fields,
)
from ..tactic_source_suppression import tactic_source_suppression_records
from ensemble_prover.utils import (
    _binder_segment_declared_names,
    _is_lean_identifier_continue_char,
    _split_binder_segments,
    canonical_lean_identifier,
    has_sorry_or_admit,
    strip_lean_comments_and_string_literals,
)

from ..action import MiniOutcome, RepairTicket, require_current_action_dispatch
from ..graph_sync import sync_proof_state_to_graph
from ..process_watchdog import begin_process_deadline
from ..state_codec import StateSnapshotCompatibilityError


_GENERATED_SOLUTION_REF_ALIAS_RE = re.compile(
    r"\bsolution_ref_hidden_[A-Za-z0-9_]+\b"
)
_PROVIDER_BLOCKED_REASON_BY_KIND = {
    "provider_capability_conflict": "provider_capability_conflict",
    "llm_required_prompt_context_overflow": (
        "llm_required_prompt_context_overflow"
    ),
}


def _provider_repair_cycle_identity(
    session: Any,
    selected_work: Mapping[str, Any],
) -> str:
    """Return immutable scheduler authority for one provider repair lane."""

    ticket = getattr(session, "pending_repair_ticket", None)
    selected_ticket_id = str(
        getattr(session, "_repair_ticket_selected_id", "") or ""
    ).strip()
    ticket_id = str(getattr(ticket, "ticket_id", "") or "").strip()
    ticket_active = bool(ticket_id and ticket_id == selected_ticket_id)
    record = dict(selected_work or {})
    # The graph scope below binds the exact execution target, environment,
    # contract, and cognition consumer.  Do not add the projected-context
    # digest here: it includes append-only observations produced by this very
    # tool round.  Exact prompt validation still checks that digest directly
    # before every provider dispatch.
    durable_evidence_fn = getattr(
        session,
        "_durable_formal_progress_evidence",
        None,
    )
    durable_evidence = (
        tuple(str(item or "") for item in durable_evidence_fn())
        if callable(durable_evidence_fn)
        else ()
    )
    payload = {
        "work_type": str(record.get("work_type") or "").strip(),
        "node_id": str(
            record.get("node_id")
            or record.get("graph_node_id")
            or ""
        ).strip(),
        "variant_id": str(record.get("variant_id") or "").strip(),
        "route_id": str(record.get("route_id") or "").strip(),
        "obligation_id": str(record.get("obligation_id") or "").strip(),
        "target_hash": str(record.get("target_hash") or "").strip(),
        "graph_scope_key": str(
            _graph_selected_work_scope_key(session, record) or ""
        ),
        # An exhausted wall lease owns only the exact formal environment that
        # consumed it. Newly verified helpers/proved nodes must open a fresh
        # provider lane, while observation-only scheduler churn must not.
        "durable_formal_evidence_hash": hashlib.sha256(
            json.dumps(
                sorted(durable_evidence),
                ensure_ascii=True,
                separators=(",", ":"),
            ).encode("utf-8", errors="replace")
        ).hexdigest(),
        "repair_ticket_id": ticket_id if ticket_active else "",
        "proof_candidate_id": (
            str(getattr(ticket, "proof_candidate_id", "") or "").strip()
            if ticket_active
            else ""
        ),
        "lean_residual_id": (
            str(getattr(ticket, "lean_residual_id", "") or "").strip()
            if ticket_active
            else ""
        ),
    }
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8", errors="replace")
    return hashlib.sha256(encoded).hexdigest()


def _provider_lane_identity_for_session(
    session: Any,
    *,
    role: Optional[str] = None,
) -> str:
    """Return the exact provider lane currently exposed to an action."""

    conv = getattr(session, "conv", None)
    if conv is None:
        return ""
    selected_record = dict(
        getattr(session, "selected_work_item_record", {}) or {}
    )
    graph_target = _selected_graph_native_proof_target(session)
    target = str(graph_target.get("statement") or "").strip()
    if not target and _selected_assemble_route_authoring_ready(session):
        target = str(_selected_assemble_route_goal_statement(session) or "").strip()
    if not target:
        target = str(getattr(conv, "goal_statement", "") or "").strip()
    from ensemble_prover.mini_session.turn.tool_loop import (
        _provider_turn_lane_identity,
    )

    return _provider_turn_lane_identity(
        conv,
        target,
        repair_cycle_identity=_provider_repair_cycle_identity(
            session,
            selected_record,
        ),
        role_override=role,
    )


def _accepted_negation_preamble(conv: Any) -> str:
    """Lazily share the root-acceptance context without an import cycle."""

    from ensemble_prover.proof_state_executor import (
        _proof_state_acceptance_preamble,
    )

    return _proof_state_acceptance_preamble(conv)


def _accepted_negation_feedback_context(
    conv: Any,
    helpers: Sequence[str],
) -> Tuple[Optional[str], Tuple[str, ...]]:
    """Return the prompt-visible replay world for negative artifacts."""

    from ensemble_prover.mini_session.child_goal_falsification import (
        answer_safe_negation_feedback_context,
    )

    return answer_safe_negation_feedback_context(
        conv,
        acceptance_preamble=_accepted_negation_preamble(conv),
        helpers=helpers,
    )


def _pending_residual_request_snapshot(
    proof_state: Any,
) -> Dict[str, str]:
    """Map each exact pending typed-residual request hash to its parent.

    Node IDs alone cannot distinguish an already-pending retry from a newly
    paid proof stub replacing it on the same parent. Valid durable pending
    frames always carry ``request_context_hash``; malformed frames are omitted
    so they cannot manufacture an iteration-neutral continuation.
    """

    nodes = getattr(proof_state, "nodes", {}) or {}
    if not isinstance(nodes, Mapping):
        return {}
    snapshot: Dict[str, str] = {}
    for raw_node_id, node in nodes.items():
        pending = getattr(node, "pending_residual_goal_extraction", {}) or {}
        if not isinstance(pending, Mapping):
            continue
        request_hash = str(pending.get("request_context_hash") or "").strip()
        if not re.fullmatch(r"[0-9a-f]{64}", request_hash):
            continue
        node_id = str(
            pending.get("parent_node_id")
            or getattr(node, "node_id", "")
            or raw_node_id
            or ""
        ).strip()
        if node_id:
            snapshot[request_hash] = node_id
    return snapshot


def _pending_helper_acceptance_snapshot(
    proof_state: Any,
) -> Dict[str, str]:
    """Map each exact durable helper candidate identity to its target node."""

    nodes = getattr(proof_state, "nodes", {}) or {}
    if not isinstance(nodes, Mapping):
        return {}
    snapshot: Dict[str, str] = {}
    for raw_node_id, node in nodes.items():
        pending = getattr(node, "pending_helper_acceptance", {}) or {}
        if not isinstance(pending, Mapping):
            continue
        helper_block = str(pending.get("helper_block") or "").strip()
        target = str(getattr(node, "target", "") or "")
        if (
            not helper_block
            or str(pending.get("target_hash") or "") != text_hash(target)
        ):
            continue
        node_id = str(getattr(node, "node_id", "") or raw_node_id or "").strip()
        if not node_id:
            continue
        identity = text_hash(
            json.dumps(
                {
                    "node_id": node_id,
                    "helper_block": helper_block,
                    "source": str(pending.get("source") or ""),
                    "target_hash": str(pending.get("target_hash") or ""),
                    "context_hash": str(pending.get("context_hash") or ""),
                },
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=True,
            )
        )
        snapshot[identity] = node_id
    return snapshot


def _root_falsification_terminal_metadata(
    session: Any,
    falsified_statement: str,
) -> Dict[str, Any]:
    """Stop a session when Lean disproves that session's exact root.

    Graph-child falsifications merely retire one route and must leave the
    containing session free to choose another.  A subgoal session's own root,
    however, has no positive work left: terminate that child immediately.  Its
    local-only reason is deliberately not a run-terminal LLM reason, allowing
    the recursive caller to convert the durable certificate into
    ``ClaimProofResult.invalid_reason`` and replan the parent.

    This is a mathematical-disproof boundary, so only the strict canonical
    statement key is authoritative here.  The looser graph root-equivalence
    relation is a scheduling heuristic and can intentionally erase type-level
    distinctions that are unsound for terminalization.
    """

    falsified = str(falsified_statement or "").strip()
    dossier = getattr(session, "dossier", None)
    problem = getattr(session, "problem", None)
    local_child = str(getattr(session, "scope", "") or "") == "subgoal"
    proof_state = getattr(session, "proof_state", None)
    proof_nodes = getattr(proof_state, "nodes", {}) or {}
    proof_root = proof_nodes.get(
        str(getattr(proof_state, "root_node_id", "") or "")
    )
    # Recursive child sessions deliberately retain the parent's ``problem``
    # object for provenance while owning a different dossier/proof-state root.
    # Treating that parent statement as a child root creates a permanent
    # conflict and suppresses exact child falsification.  Every available
    # durable source in the applicable scope must still agree; a dossier-only
    # lightweight session remains supported.
    authoritative_root_sources = (
        getattr(dossier, "root_statement", ""),
        getattr(proof_root, "target", ""),
    )
    if not local_child:
        authoritative_root_sources = (
            *authoritative_root_sources,
            getattr(problem, "statement_type", ""),
        )
    authoritative_root_candidates = tuple(
        dict.fromkeys(
            str(value or "").strip()
            for value in authoritative_root_sources
            if str(value or "").strip()
        )
    )
    # ``conv.goal_statement`` follows selected work in some lanes and is never
    # authoritative enough to terminalize mathematical search on its own.
    root_candidates = authoritative_root_candidates
    if not falsified or not root_candidates:
        return {}
    falsified_key = graph_statement_key(falsified)
    root_candidate_keys = {
        key
        for candidate in root_candidates
        if (key := graph_statement_key(candidate))
    }
    # Conflicting durable roots are a state-integrity problem, not permission
    # to choose whichever one matches the certificate.
    if (
        not falsified_key
        or len(root_candidate_keys) != 1
        or falsified_key not in root_candidate_keys
    ):
        return {}
    return {
        "terminal_failure": True,
        "terminal_failure_reason": (
            "local_root_authoritatively_falsified"
            if local_child
            else "root_disproved_by_audited_lean_certificate"
        ),
        "terminal_failure_kind": "mathematical_disproof",
        "authoritative_falsification_terminal_scope": (
            "child_root" if local_child else "problem_root"
        ),
    }


def _negation_certification_conflicted(
    dossier: Any,
    certificate_hash: str,
) -> bool:
    """Recognize the typed fail-closed result from the authority boundary."""

    return bool(
        str(certificate_hash or "").strip()
        and str(getattr(dossier, "session_failure_kind", "") or "").strip()
        == "proof_disproof_conflict"
        and str(getattr(dossier, "session_failure_reason", "") or "").strip()
        == "falsification_trust_boundary_conflict"
    )


def _proof_disproof_conflict_metadata(dossier: Any) -> Dict[str, Any]:
    return {
        "terminal_failure": True,
        "terminal_failure_reason": str(
            getattr(dossier, "session_failure_reason", "") or ""
        ).strip()
        or "falsification_trust_boundary_conflict",
        "terminal_failure_kind": "proof_disproof_conflict",
        "strong_progress": False,
    }


class SelectedProofIdeaContextError(RuntimeError):
    """Selected cognition was explicit but could not be resolved exactly."""

    mini_selected_proof_idea_context_error = True


def _selected_proof_idea_context_for_prompt(
    session: Any,
    selected_work: Mapping[str, Any],
    *,
    audience: str,
) -> str:
    """Resolve and render the selected lifecycle without global fallback.

    Legacy/root execution records that carry no cognition coordinates remain
    execution-only.  Once a producer supplies consumer bindings, however,
    ambiguity or staleness is a controller error: silently replacing that
    route-local memory with a global top-N summary would change the task.
    """

    dossier = getattr(session, "dossier", None)
    resolver = getattr(dossier, "resolve_proof_idea_context", None)
    projector = getattr(dossier, "project_proof_idea_context", None)
    if not callable(resolver) or not callable(projector):
        setattr(session, "_selected_proof_idea_dispatch_packet", {})
        setattr(session, "_selected_proof_idea_context_digest", "")
        return ""
    record = dict(selected_work or {})
    explicit_cognition = selected_work_has_explicit_cognition(record)
    resolution = resolver(record, policy="exact_selected")
    status = str(getattr(resolution, "status", "") or "").strip()
    if status != "resolved":
        if explicit_cognition:
            reason = str(getattr(resolution, "reason", "") or status or "unbound")
            raise SelectedProofIdeaContextError(
                "graph-selected proof cognition could not be resolved exactly: "
                f"{status or 'unknown'}: {reason}"
            )
        setattr(session, "_selected_proof_idea_dispatch_packet", {})
        setattr(session, "_selected_proof_idea_context_digest", "")
        return ""
    projection = projector(resolution, audience=audience)
    render = getattr(projection, "render", None)
    if not callable(render):
        raise TypeError("proof-idea context projection has no renderer")
    setattr(
        session,
        "_selected_proof_idea_dispatch_packet",
        copy.deepcopy(record),
    )
    setattr(
        session,
        "_selected_proof_idea_context_digest",
        str(getattr(resolution, "context_digest", "") or ""),
    )
    return str(render() or "")


_GRAPH_NATIVE_MAX_TOKEN_CAPS: Dict[str, int] = {
    "formalize_claim": 4096,
    "formalize_missing_obligation": 4096,
    "materialize_replay_source": 4096,
    "mine_missing_obligation": 4096,
    "prove_claim_variant": 6144,
    "route_replan": 4096,
    "target_integrity_adjudication": 2048,
}

# A backend's advertised output capacity is not an appropriate per-turn
# default. In particular, DeepSeek's 384K capability made every transport
# retry reserve another 384K-token completion and stranded an otherwise cheap
# Mini run behind its cost guard. Most models fit comfortably in 20K. DeepSeek
# v4 at provider-default or high/max reasoning is different: observed
# completions can use most of their tokens for hidden reasoning. Give that mode
# 96K so the reasoning still has measured headroom
# to reach a tool/final payload, while bounding one dispatch to one quarter of
# the raw 384K capability.
_DEFAULT_CONVERSATION_MAX_TOKENS = 20_480
_HIDDEN_REASONING_MAX_TOKENS = 32_768
_MANDATORY_QWEN_REASONING_MAX_TOKENS = 48_000
_DEEPSEEK_HIGH_REASONING_MAX_TOKENS = 96_000


def _reasoning_aware_conversation_cap(cfg: Any) -> int:
    model = str(getattr(cfg, "model", "") or "").strip().lower().rsplit("/", 1)[-1]
    provider = provider_for_base_url(
        str(getattr(cfg, "base_url", "") or "")
    )
    effort = str(getattr(cfg, "reasoning_effort", "") or "").strip().lower()
    required = bool(getattr(cfg, "reasoning_control_required", False))
    thinking_enabled = bool(getattr(cfg, "thinking_enabled", False))
    capability = lookup_openrouter_reasoning_capabilities(
        str(getattr(cfg, "base_url", "") or ""),
        str(getattr(cfg, "model", "") or ""),
    )
    # DeepSeek v4 defaults to thinking when no explicit control is supplied
    # (see models._resolved_reasoning_effort). Treat that provider-default mode
    # as reasoning-capable too; otherwise the ordinary 20K cap can truncate a
    # default-thinking response just as surely as an explicit max response.
    # ``thinking_enabled=False`` is an actual default-thinking opt-out only on
    # the direct DeepSeek adapter.  OpenRouter may be unable to send a disable
    # control, so conservatively preserve reasoning headroom for routed V4 even
    # when the role required a control which its catalog route cannot honor.
    deepseek_default_thinking = bool(
        provider == "openrouter" or (not effort and not required)
    )
    if model.startswith("deepseek-v4") and (
        effort in {"high", "max"}
        or thinking_enabled and effort not in {"none", "low", "medium"}
        or deepseek_default_thinking
    ):
        return _DEEPSEEK_HIGH_REASONING_MAX_TOKENS
    # OpenAI reasoning models count hidden reasoning inside
    # ``max_completion_tokens``.  Qwen's routed max endpoint likewise mandates
    # reasoning even when callers request ``none``.  Applying the tiny
    # graph-native visible-output cap to either family can consume the entire
    # allowance before a tool call or Lean payload is emitted.
    if capability is not None and capability.mandatory is True:
        return _MANDATORY_QWEN_REASONING_MAX_TOKENS
    if model.startswith("qwen3.8-max"):
        return _MANDATORY_QWEN_REASONING_MAX_TOKENS
    if (
        capability is not None
        and capability.supports_reasoning
        and effort != "none"
    ):
        return _HIDDEN_REASONING_MAX_TOKENS
    if (
        model.startswith("gpt-5")
        # Tool-bearing MiniSession calls request at least medium reasoning when
        # the role leaves effort unspecified.  Treat only an explicit ``none``
        # as reasoning-off; inspecting cfg alone otherwise underestimates the
        # actual per-call envelope.
        and effort != "none"
    ):
        return _HIDDEN_REASONING_MAX_TOKENS
    return _DEFAULT_CONVERSATION_MAX_TOKENS


def _conversation_client_role_configs(client: Any) -> Tuple[Any, ...]:
    """Return every concrete role config reachable through a wrapper."""

    configs: List[Any] = []
    seen_configs: set[int] = set()
    seen_values: set[int] = set()

    def visit(value: Any) -> None:
        if value is None or id(value) in seen_values:
            return
        seen_values.add(id(value))
        cfg = getattr(value, "cfg", None) if value is not None else None
        if cfg is None and value is not None and hasattr(value, "model"):
            cfg = value
        if cfg is not None and id(cfg) not in seen_configs:
            seen_configs.add(id(cfg))
            configs.append(cfg)
        for nested_cfg in list(getattr(value, "configs", None) or []):
            visit(nested_cfg)
        for child in list(getattr(value, "clients", None) or []):
            visit(child)
        for member in list(getattr(value, "members", None) or []):
            visit(member)
            visit(getattr(member, "client", None))
            visit(getattr(member, "cfg", None))

    visit(client)
    return tuple(configs)


def _selected_work_max_tokens_override(session: Any, client: Any) -> Optional[int]:
    """Return the explicit or work-aware output ceiling for one turn."""

    explicit_session_cap = getattr(
        session,
        "conversation_max_tokens_override",
        None,
    )
    try:
        session_explicit_cap = int(explicit_session_cap)
    except Exception:
        session_explicit_cap = 0
    selected = getattr(session, "selected_work_item_record", None)
    if not isinstance(selected, dict):
        selected = {}
    work_type = str(selected.get("work_type") or "").strip()
    configs = _conversation_client_role_configs(client)
    if not configs:
        configs = (getattr(client, "cfg", None),)
    config_explicit_caps: List[int] = []
    for cfg in configs:
        try:
            value = int(
                getattr(cfg, "conversation_max_tokens_override", 0) or 0
            )
        except Exception:
            value = 0
        if value > 0:
            config_explicit_caps.append(value)
    config_explicit_cap = max(config_explicit_caps, default=0)
    explicit_cap = (
        session_explicit_cap
        if session_explicit_cap > 0
        else config_explicit_cap
    )
    if explicit_cap > 0:
        # ``max_tokens_override`` is a real per-request control in every Mini
        # client adapter. Do not re-clamp it to the role default, or operators
        # can lower graph caps but can never deliberately raise them.
        return int(explicit_cap)
    automatic_caps: List[int] = []
    for cfg in configs:
        reasoning_cap = _reasoning_aware_conversation_cap(cfg)
        cap = (
            reasoning_cap
            if reasoning_cap > _DEFAULT_CONVERSATION_MAX_TOKENS
            else _GRAPH_NATIVE_MAX_TOKEN_CAPS.get(work_type, reasoning_cap)
        )
        try:
            cfg_limit = int(getattr(cfg, "max_tokens", 0) or 0)
        except Exception:
            cfg_limit = 0
        automatic_caps.append(
            max(1, min(int(cap), cfg_limit))
            if cfg_limit > 0
            else int(cap)
        )
    return max(automatic_caps, default=_DEFAULT_CONVERSATION_MAX_TOKENS)


def _selected_work_request_envelope_policy(session: Any) -> Any:
    """Build an unresolved policy without inspecting sibling model configs."""

    explicit_session_cap = getattr(
        session,
        "conversation_max_tokens_override",
        None,
    )
    selected = getattr(session, "selected_work_item_record", None)
    if not isinstance(selected, dict):
        selected = {}
    return mini_request_envelope_policy(
        work_type=str(selected.get("work_type") or ""),
        session_max_tokens_override=explicit_session_cap,
    )


def _can_bank_rejected_proposed_helpers(conv: Any) -> bool:
    return bool(getattr(conv, "allow_helper_decomposition", True))


def _classify_turn_giveup(
    content: str,
    proof: Optional[str],
    helpers: Optional[Sequence[str]] = None,
) -> Optional[Dict[str, str]]:
    try:
        from ensemble_prover.mini_prover import (
            _classify_giveup_signal,
            _sorry_stub_helper_names,
        )

        has_sorry_stub_helper = bool(_sorry_stub_helper_names(list(helpers or ())))

        return _classify_giveup_signal(
            str(content or ""),
            proof,
            require_structural_collapse=(
                proof is not None and not has_sorry_stub_helper
            ),
        )
    except Exception:
        return None


def _proof_is_structural_collapse_safe(proof: Optional[str]) -> bool:
    try:
        from ensemble_prover.mini_prover import _proof_is_structural_collapse

        return bool(_proof_is_structural_collapse(proof))
    except Exception:
        return False


def _local_micro_theory_suppresses_library_tools(session: Any) -> bool:
    active = getattr(session, "local_micro_theory_library_suppression_active", None)
    if not callable(active) or not bool(active()):
        return False
    requires_api = getattr(
        session,
        "local_micro_theory_selected_ticket_requires_api_grounding",
        None,
    )
    return not (callable(requires_api) and bool(requires_api()))


def _analyze_feedback_for_local_micro_theory_grounding(
    lean_verdict: Any,
) -> Dict[str, Any]:
    """Return Lean failure analysis for deciding a narrow API-grounding escape."""

    feedback_result = getattr(lean_verdict, "feedback_result", None)
    if feedback_result is None:
        return {}
    try:
        from ensemble_prover.mini_prover import _analyze_lean_failure

        analysis = _analyze_lean_failure(feedback_result)
    except Exception:
        return {}
    return dict(analysis or {}) if isinstance(analysis, dict) else {}


def _local_micro_theory_allows_post_failure_api_grounding(
    session: Any,
    failure_analysis: Dict[str, Any],
    *,
    target_statement: str = "",
) -> Tuple[bool, str]:
    """Return whether unknown-identifier repair may use Mathlib/API lookup."""

    if not bool(
        getattr(
            session,
            "premise_zero_hit_allow_api_grounding_after_lean_failure",
            True,
        )
    ):
        return False, ""
    if bool((failure_analysis or {}).get("generated_check_wrapper_unknown")):
        return False, ""
    error_type = str((failure_analysis or {}).get("error_type") or "").strip()
    if error_type != "unknown_identifier":
        return False, ""
    unknown_identifier = unknown_identifier_name(failure_analysis)
    if not unknown_identifier:
        return False, ""
    if _unknown_identifier_is_target_binder(
        unknown_identifier,
        target_statement=(
            str(target_statement or "").strip()
            or str(
                getattr(getattr(session, "conv", None), "goal_statement", "")
                or ""
            ).strip()
        ),
    ):
        return False, ""
    return True, unknown_identifier


def _unknown_identifier_is_target_binder(
    unknown_identifier: str,
    *,
    target_statement: str,
) -> bool:
    """Whether Lean's unknown name belongs to the target's binder telescope.

    A missing ``intro`` makes target-bound variables look like unknown global
    declarations to Lean.  Such failures are local proof-shape errors; forcing
    Mathlib/API lookup for the binder manufactures an impossible repair target.
    The shared proof-graph parser is the authority for the selected target's
    leading telescope, and parser uncertainty remains fail-closed (grounding
    is still required).
    """

    name = str(unknown_identifier or "").strip()
    statement = str(target_statement or "").strip()
    if not name or not statement:
        return False
    try:
        _body, bound_names, _premises = graph_statement_leading_contract(statement)
    except Exception:
        return False
    def identifier_surface(identifier: str) -> str:
        clean = str(identifier or "").strip()
        if clean.startswith("«") and clean.endswith("»"):
            return clean[1:-1]
        return clean

    target_name = identifier_surface(name)
    return bool(target_name) and target_name in {
        identifier_surface(bound_name) for bound_name in bound_names
    }


_PROOF_LOCAL_BINDER_RE = re.compile(
    r"(?:^|[;\n])\s*(?:by\s+)?"
    r"(?:haveI|letI|have|let|suffices)\s+"
    r"(?P<name>«[^»\n]+»|[A-Za-z_][A-Za-z0-9_']*)"
    r"(?=\s|:|:=)",
    re.MULTILINE,
)

def _unknown_identifier_is_proof_local_binder(
    unknown_identifier: str,
    *,
    proof: str,
) -> bool:
    """Whether a failed name is declared by the submitted tactic proof.

    Lean may report a scratch ``let``/``have`` name as unknown when the local
    declaration itself is malformed or out of scope.  Searching Mathlib for
    that name cannot repair the proof.  This scan is deliberately narrow: it
    recognizes only explicit tactic-local declarations and strips comments
    and string literals before matching, so ordinary global identifiers still
    require API grounding.
    """

    name = str(unknown_identifier or "").strip()
    source = strip_lean_comments_and_string_literals(str(proof or ""))
    if not name or not source:
        return False

    def identifier_surface(identifier: str) -> str:
        clean = str(identifier or "").strip()
        if clean.startswith("«") and clean.endswith("»"):
            return clean[1:-1]
        return clean

    target_name = identifier_surface(name)
    return bool(target_name) and any(
        identifier_surface(match.group("name")) == target_name
        for match in _PROOF_LOCAL_BINDER_RE.finditer(source)
    )


def _has_concrete_local_repair_target(
    *,
    proof: str,
    helpers: Sequence[str],
    lemma_dag_candidate_helpers: Sequence[str],
) -> bool:
    if not str(proof or "").strip():
        return False
    if _proof_is_structural_collapse_safe(proof):
        return False
    return True


def _extractable_helper_blocks_for_giveup_recovery(
    helpers: Sequence[str],
    lemma_dag_candidate_helpers: Sequence[str],
) -> List[str]:
    """Concrete helper declarations should survive no-proof give-up prose."""

    blocks: List[str] = []
    seen_names: set[str] = set()
    for block in [*list(helpers or ()), *list(lemma_dag_candidate_helpers or ())]:
        text = str(block or "").strip()
        if not text or has_sorry_or_admit(text):
            continue
        name = helper_decl_name(text)
        if not name or name in seen_names:
            continue
        seen_names.add(name)
        blocks.append(text)
    return blocks


_NO_PROOF_GIVEUP_RECOVERY_METADATA_KEYS: tuple[str, ...] = (
    "giveup_suppressed_by_extractable_helpers",
    "extractable_helper_count_under_giveup",
    "extractable_helper_names_under_giveup",
)


def _no_proof_giveup_recovery_metadata(
    payload: Dict[str, Any],
) -> Dict[str, Any]:
    return {
        key: payload[key]
        for key in _NO_PROOF_GIVEUP_RECOVERY_METADATA_KEYS
        if key in payload
    }


def _mark_no_proof_giveup_extractable_helper_recovery(
    *,
    session: Any,
    common_payload: Dict[str, Any],
    turn_giveup: Dict[str, Any],
    recoverable_giveup_helpers: Sequence[str],
) -> None:
    if common_payload.get("giveup_suppressed_by_extractable_helpers"):
        return
    common_payload["giveup_suppressed_by_extractable_helpers"] = True
    common_payload["extractable_helper_count_under_giveup"] = len(
        recoverable_giveup_helpers
    )
    common_payload["extractable_helper_names_under_giveup"] = [
        helper_decl_name(block) or ""
        for block in recoverable_giveup_helpers
        if helper_decl_name(block)
    ]
    increment = getattr(session, "_increment_dossier_metric", None)
    if callable(increment):
        increment(
            "mini_session_no_proof_giveup_extractable_helpers_recovered",
            1,
        )
    _emit_record(session, {
        **common_payload,
        "giveup_cluster": str(turn_giveup.get("cluster") or ""),
        "giveup_match": str(turn_giveup.get("match") or ""),
        "verdict": "no_proof_giveup_suppressed_by_extractable_helpers",
    })


def _propagate_route_scoped_tool_helpers(
    *,
    source_dossier: Any,
    target_dossier: Any,
) -> List[str]:
    """Copy helpers proved inside a route-scoped dossier back to the real dossier."""

    if source_dossier is None or target_dossier is None or source_dossier is target_dossier:
        return []
    source_helpers = getattr(source_dossier, "verified_helpers", None)
    target_helpers = getattr(target_dossier, "verified_helpers", None)
    if not isinstance(source_helpers, dict) or not isinstance(target_helpers, dict):
        return []
    importer = getattr(target_dossier, "record_imported_verified_helper", None)
    if not callable(importer):
        return []
    added: List[str] = []
    for name, helper in list(source_helpers.items()):
        helper_name = str(name or "").strip()
        if not helper_name:
            continue
        source = str(getattr(helper, "source", "") or "").strip()
        if not source:
            continue
        resolver = getattr(target_dossier, "resolve_verified_helper_name", None)
        existing_helper_name = (
            str(resolver(helper_name) or helper_name).strip()
            if callable(resolver)
            else helper_name
        )
        existing = target_helpers.get(existing_helper_name)
        if existing is not None:
            if (
                str(getattr(existing, "source_hash", "") or "").strip()
                == str(getattr(helper, "source_hash", "") or "").strip()
            ):
                continue
            increment = getattr(target_dossier, "increment_tool_metric", None)
            if callable(increment):
                try:
                    increment(
                        "mini_session_route_scoped_helper_name_collision_rejected",
                        1,
                    )
                except Exception:
                    pass
            continue
        preflight = getattr(
            target_dossier,
            "preflight_imported_verified_helper",
            None,
        )
        if callable(preflight):
            plan = preflight(helper)
            if not isinstance(plan, Mapping):
                continue
            planned_existing_name = str(
                plan.get("existing_helper_name") or helper_name
            ).strip()
            if canonical_lean_identifier(planned_existing_name) != (
                canonical_lean_identifier(helper_name)
            ):
                increment = getattr(
                    target_dossier,
                    "increment_tool_metric",
                    None,
                )
                if callable(increment):
                    try:
                        increment(
                            "mini_session_route_scoped_helper_name_collision_rejected",
                            1,
                        )
                    except Exception:
                        pass
                continue
        recorded = importer(
            helper,
            phase=str(getattr(helper, "phase", "") or "route_scoped_tool"),
            turn_index=int(getattr(helper, "turn_index", 0) or 0),
        )
        if recorded is not None:
            recorded_name = str(getattr(recorded, "name", "") or "").strip()
            landed = target_helpers.get(recorded_name) if recorded_name else None
            if (
                landed is not recorded
                or recorded_name != helper_name
                or str(getattr(recorded, "source_hash", "") or "").strip()
                != str(getattr(helper, "source_hash", "") or "").strip()
            ):
                continue
            visible = getattr(target_dossier, "is_verified_helper_context_visible", None)
            if callable(visible) and not bool(visible(recorded)):
                increment = getattr(target_dossier, "increment_tool_metric", None)
                if callable(increment):
                    try:
                        increment(
                            "mini_session_route_scoped_advisory_helpers_suppressed",
                            1,
                        )
                    except Exception:
                        pass
                continue
            added.append(recorded_name)
    return added


def _merge_route_scoped_tool_helper_blocks(
    existing_blocks: Sequence[str],
    *,
    helper_names: Sequence[str],
    dossier: Any,
) -> List[str]:
    """Return route helper blocks plus same-turn helpers proved by tools."""

    blocks = [
        str(block or "").strip()
        for block in list(existing_blocks or ())
        if str(block or "").strip()
    ]
    seen = {helper_decl_name(block) for block in blocks if helper_decl_name(block)}
    verified_helpers = getattr(dossier, "verified_helpers", {}) or {}
    if not isinstance(verified_helpers, dict):
        return blocks
    for raw_name in list(helper_names or ()):
        name = str(raw_name or "").strip()
        if not name or name in seen:
            continue
        helper = verified_helpers.get(name)
        source = str(getattr(helper, "source", "") or "").strip()
        if not source:
            continue
        blocks.append(source)
        seen.add(name)
    return blocks


def _extend_route_contract_with_tool_helpers(
    *,
    dossier: Any,
    route_id: str,
    helper_names: Sequence[str],
    target_statement: str,
    phase: str,
    turn_index: int,
) -> Dict[str, Any]:
    """Make same-turn route-scoped tool helpers part of the route contract."""

    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    clean_route_id = str(route_id or "").strip()
    if graph is None or not clean_route_id:
        return {}
    status_getter = getattr(graph, "route_assembly_contract_status", None)
    setter = getattr(graph, "set_route_assembly_contract", None)
    helper_map = getattr(graph, "helper_name_to_node_id", {}) or {}
    if not callable(status_getter) or not callable(setter) or not isinstance(helper_map, dict):
        return {}
    try:
        status = dict(
            status_getter(
                clean_route_id,
                target_statement=str(target_statement or ""),
            )
            or {}
        )
    except Exception:
        status = {}
    required_node_ids: List[str] = []
    for raw_id in list(
        status.get("required_node_ids")
        or status.get("dependency_node_ids")
        or []
    ):
        node_id = str(raw_id or "").strip()
        if node_id and node_id not in required_node_ids:
            required_node_ids.append(node_id)
    added_node_ids: List[str] = []
    for raw_name in list(helper_names or ()):
        name = str(raw_name or "").strip()
        node_id = str(helper_map.get(name) or "").strip()
        if node_id and node_id not in required_node_ids:
            required_node_ids.append(node_id)
            added_node_ids.append(node_id)
    if not added_node_ids:
        return status
    contract_metadata = dict(status.get("contract_metadata") or {})
    route_scope = str(status.get("route_scope") or "").strip()
    try:
        setter_kwargs = {
            "required_node_ids": required_node_ids,
            "target_statement": str(target_statement or ""),
            "phase": str(phase or "route_scoped_tool"),
            "turn_index": int(turn_index or 0),
            "metadata": contract_metadata,
        }
        if route_scope:
            setter_kwargs["scope"] = route_scope
        setter(clean_route_id, **setter_kwargs)
    except Exception:
        return status
    try:
        updated = dict(
            status_getter(
                clean_route_id,
                target_statement=str(target_statement or ""),
            )
            or {}
        )
    except Exception:
        updated = {}
    route = getattr(graph, "nodes", {}).get(clean_route_id)
    metadata = getattr(route, "metadata", None)
    signature_getter = getattr(graph, "route_dependency_signature_hash", None)
    if isinstance(metadata, dict) and callable(signature_getter):
        try:
            signature_hash = str(signature_getter(clean_route_id) or "").strip()
        except Exception:
            signature_hash = ""
        if signature_hash:
            metadata["route_root_tactic_authoring_ready_signature_hash"] = signature_hash
        for key in (
            "route_root_tactic_authoring_helper_names",
            "route_root_tactic_helper_names",
        ):
            names = [
                str(name or "").strip()
                for name in list(metadata.get(key) or [])
                if str(name or "").strip()
            ]
            for raw_name in list(helper_names or ()):
                name = str(raw_name or "").strip()
                if name and name not in names:
                    names.append(name)
            if names:
                metadata[key] = names
    return updated or status


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


def _repair_ticket_from_lean_rejection(
    *,
    session: Any,
    action_id: str,
    proof: str,
    check_lemmas: Sequence[str],
    lean_output: str,
    feedback_text: str,
    feedback_source: str,
    error_type: str,
    failure_signature: str,
    turn_index: int,
    metadata: Optional[Dict[str, Any]] = None,
) -> Optional[RepairTicket]:
    proof_text = str(proof or "").strip()
    if not proof_text:
        return None
    if _is_active_root_lift_feedback_source(feedback_source):
        return None
    parent_ticket = getattr(session, "pending_repair_ticket", None)
    selected_ticket_id = str(
        getattr(session, "_repair_ticket_selected_id", "") or ""
    ).strip()
    parent_is_selected = bool(
        parent_ticket is not None
        and selected_ticket_id
        and str(getattr(parent_ticket, "ticket_id", "") or "") == selected_ticket_id
    )
    max_chain_depth = int(
        getattr(
            parent_ticket,
            "max_chain_depth",
            getattr(session, "max_repair_ticket_chain_depth", 3),
        )
        or 3
    )
    repair_depth = (
        int(getattr(parent_ticket, "repair_depth", 0) or 0) + 1
        if parent_is_selected
        else 0
    )
    if repair_depth >= max(1, max_chain_depth):
        recorder = getattr(session, "_record_event", None)
        if callable(recorder):
            recorder({
                "phase": "session_repair_ticket",
                "iteration": getattr(session, "iteration", 0),
                "parent_ticket_id": selected_ticket_id,
                "repair_depth": repair_depth,
                "max_chain_depth": max_chain_depth,
                "verdict": "chain_depth_exhausted",
            })
        return None
    selected = dict(getattr(session, "selected_work_item_record", {}) or {})
    graph_record = dict(selected.get("graph_record") or {})
    selected_work_type = str(
        selected.get("work_type") or graph_record.get("work_type") or ""
    ).strip()
    route_id = str(
        selected.get("route_id")
        or graph_record.get("route_id")
        or (
            selected.get("node_id")
            if selected_work_type == "assemble_route"
            else ""
        )
        or ""
    ).strip()
    obligation_id = str(
        selected.get("obligation_id")
        or graph_record.get("obligation_id")
        or (
            selected.get("node_id")
            if selected_work_type
            in {"mine_missing_obligation", "formalize_claim", "prove_claim_variant"}
            else ""
        )
        or ""
    ).strip()
    target_id = str(
        selected.get("node_id")
        or selected.get("graph_node_id")
        or obligation_id
        or route_id
        or "root"
    ).strip()
    graph_native_target = _selected_graph_native_proof_target(session)
    assemble_route_statement = (
        _selected_assemble_route_goal_statement(session)
        if selected_work_type == "assemble_route"
        else ""
    )
    selected_target_statement = str(selected.get("target_statement") or "").strip()
    selected_target_executable = (
        bool(selected_target_statement)
        and selected_work_type != "route_replan"
        and graph_statement_is_executable(selected_target_statement)
    )
    active_root_target = active_root_target_statement(
        getattr(session, "dossier", None),
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    explicit_parent_fallback_target = str(
        selected.get("materialization_parent_statement")
        or selected.get("formalization_bridge_parent_statement")
        or selected.get("parent_repair_target_statement")
        or ""
    ).strip()
    ambient_root_fallback_target = str(
        active_root_target
        or getattr(getattr(session, "conv", None), "goal_statement", "")
        or getattr(getattr(session, "dossier", None), "root_statement", "")
        or ""
    ).strip()
    selected_root_repair_target = (
        active_root_target
        if selected_work_type == "root_repair" and active_root_target
        else ""
    )
    if selected_work_type in {
        "formalize_claim",
        "formalize_missing_obligation",
        "mine_missing_obligation",
        "prove_claim_variant",
    }:
        parent_fallback_repair_target = explicit_parent_fallback_target
        if (
            not parent_fallback_repair_target
            and selected_work_type == "formalize_missing_obligation"
        ):
            parent_fallback_repair_target = _formalization_parent_statement(
                session,
                selected,
            )
    else:
        parent_fallback_repair_target = ""
    ambient_root_repair_target = (
        ambient_root_fallback_target
        if selected_work_type in {"", "root_repair"}
        else ""
    )
    target_statement = str(
        graph_native_target.get("statement")
        or assemble_route_statement
        or selected_root_repair_target
        or (selected_target_statement if selected_target_executable else "")
        or parent_fallback_repair_target
        or ambient_root_repair_target
        or ""
    )
    helper_blocks = tuple(
        str(block or "").strip()
        for block in list(check_lemmas or ())
        if str(block or "").strip()
    )
    helper_names = tuple(
        name
        for block in helper_blocks
        for name in [helper_decl_name(block)]
        if name
    )
    base_metadata = dict(metadata or {})
    failure_analysis = dict(base_metadata.get("failure_analysis") or {})
    if not failure_analysis and str(error_type or "").strip():
        failure_analysis = {"error_type": str(error_type or "").strip()}
    tool_call_log = list(base_metadata.get("tool_call_log") or ())
    canonical_error_type = str(
        error_type or failure_analysis.get("error_type") or ""
    ).strip()
    generated_check_wrapper_unknown = bool(
        failure_analysis.get("generated_check_wrapper_unknown")
    )
    unknown_name = (
        unknown_identifier_name(failure_analysis)
        if canonical_error_type == "unknown_identifier"
        and not generated_check_wrapper_unknown
        else ""
    )
    unknown_identifier_repair = bool(unknown_name)
    unknown_identifier_is_target_binder = _unknown_identifier_is_target_binder(
        unknown_name,
        target_statement=target_statement,
    )
    unknown_identifier_is_proof_local_binder = (
        _unknown_identifier_is_proof_local_binder(
            unknown_name,
            proof=proof_text,
        )
    )
    unknown_identifier_is_local_binder = bool(
        unknown_identifier_is_target_binder
        or unknown_identifier_is_proof_local_binder
    )
    unknown_identifier_requires_api_search = bool(
        unknown_identifier_repair
        and not unknown_identifier_is_local_binder
    )
    repeated_unknown_without_api = bool(
        unknown_identifier_requires_api_search
        and repeated_unknown_identifier_without_api_search(
            failure_analysis,
            parent_ticket=parent_ticket if parent_is_selected else None,
            tool_call_log=tool_call_log,
        )
    )
    parse_error_failure = (
        is_parse_error_failure(failure_analysis)
        or str(error_type or "").strip() == "parse_error"
    )
    formalization_failure_class = str(
        base_metadata.get("formalization_failure_class") or ""
    ).strip()
    if parse_error_failure:
        formalization_failure_class = "code_generation"
    elif (
        generated_check_wrapper_unknown
        and canonical_error_type in {"unknown_identifier", "lean_rejected"}
    ):
        formalization_failure_class = "code_generation"
    elif unknown_identifier_requires_api_search:
        formalization_failure_class = "api_grounding"
    elif unknown_identifier_is_local_binder:
        # Keep this distinct from parse/code-generation failures: recorder
        # metrics intentionally count that class as a parser failure.
        formalization_failure_class = "binder_scope"
    elif not formalization_failure_class:
        formalization_failure_class = "proof_search"
    ticket_max_attempts = 2 if unknown_identifier_repair else 1
    ticket_metadata: Dict[str, Any] = {
        **base_metadata,
        "selected_work_item": selected,
        "repair_scope": (
            "route"
            if route_id
            else ("obligation" if obligation_id else "root")
        ),
        "formalization_failure_class": formalization_failure_class,
        "proof_attempt_id": "",
        "original_root_statement": str(
            getattr(getattr(session, "conv", None), "goal_statement", "")
            or getattr(getattr(session, "dossier", None), "root_statement", "")
            or ""
        ).strip(),
    }
    if unknown_identifier_repair:
        ticket_metadata.update({
            "unknown_identifier": unknown_name,
            "unknown_identifier_is_target_binder": bool(
                unknown_identifier_is_target_binder
            ),
            "unknown_identifier_is_proof_local_binder": bool(
                unknown_identifier_is_proof_local_binder
            ),
            "requires_api_search_for_unknown_identifier": bool(
                unknown_identifier_requires_api_search
            ),
            "api_grounding_seen": tool_log_has_api_grounding(tool_call_log),
            "repeated_unknown_identifier_without_api_search": bool(
                repeated_unknown_without_api
            ),
        })
        if unknown_identifier_requires_api_search:
            ticket_metadata["api_grounding_tools"] = [
                "search_mathlib",
                "check_lean",
                "apply_decl_to_goal",
            ]
    if generated_check_wrapper_unknown:
        ticket_metadata.update({
            "generated_check_wrapper_unknown": True,
            "generated_declaration_name": str(
                failure_analysis.get("generated_declaration_name") or ""
            ).strip(),
        })
    if parse_error_failure:
        ticket_metadata.update({
            "parse_error_code_generation_failure": True,
            "code_generation_repair_reason": (
                parse_error_repair_reason(failure_analysis)
                or "parse_error_code_generation_failure"
            ),
            "proof_state_repair_disabled": True,
        })
    seed = "\n".join(
        [
            str(action_id or ""),
            str(turn_index or 0),
            target_id,
            proof_text,
            str(lean_output or ""),
            str(failure_signature or ""),
        ]
    )
    ticket_id = hashlib.sha256(seed.encode("utf-8")).hexdigest()[:16]
    proof_attempt_id = hashlib.sha256(
        ("attempt\n" + seed).encode("utf-8")
    ).hexdigest()[:16]
    ticket_metadata["proof_attempt_id"] = proof_attempt_id
    selected_lineage = ProofLineageEnvelope.from_metadata(selected)
    if isinstance(graph_record, dict):
        graph_lineage = ProofLineageEnvelope.from_metadata(graph_record)
        selected_lineage = selected_lineage.updated(
            **{
                field_name: getattr(graph_lineage, field_name)
                for field_name in graph_lineage.__dataclass_fields__
                if getattr(graph_lineage, field_name)
                and not getattr(selected_lineage, field_name)
            }
        )
    statement_identity = (
        selected_lineage.statement_identity
        or structural_statement_identity(
            target_statement,
            contract_identity=str(
                selected.get("contract_identity")
                or graph_record.get("contract_identity")
                or ""
            ),
        )
    )
    proof_candidate_id = proof_candidate_identity(
        target_id=target_id,
        proof_hash=text_hash(proof_text),
    )
    lean_residual_id = lean_residual_identity(
        proof_candidate_id=proof_candidate_id,
        error_type=error_type,
        failure_signature=failure_signature,
    )
    ticket_lineage = selected_lineage.updated(
        route_id=route_id or selected_lineage.route_id,
        statement_identity=statement_identity,
        proof_candidate_id=proof_candidate_id,
        lean_residual_id=lean_residual_id,
        repair_ticket_id=ticket_id,
    )
    ticket_metadata.update(ticket_lineage.merged_metadata(ticket_metadata))
    root_ticket_id = (
        str(getattr(parent_ticket, "root_ticket_id", "") or "")
        or str(getattr(parent_ticket, "ticket_id", "") or "")
        if parent_is_selected
        else ticket_id
    )
    return RepairTicket(
        ticket_id=ticket_id,
        proof=proof_text,
        lean_output=str(lean_output or ""),
        feedback_text=str(feedback_text or ""),
        feedback_source=str(feedback_source or ""),
        error_type=str(error_type or ""),
        failure_signature=str(failure_signature or ""),
        target_id=target_id,
        target_statement=target_statement,
        helper_blocks=helper_blocks,
        helper_names=helper_names,
        route_id=route_id,
        obligation_id=obligation_id,
        work_type=selected_work_type,
        proof_attempt_id=proof_attempt_id,
        strategy_lineage_id=ticket_lineage.strategy_lineage_id,
        statement_identity=ticket_lineage.statement_identity,
        proof_candidate_id=ticket_lineage.proof_candidate_id,
        lean_residual_id=ticket_lineage.lean_residual_id,
        source_action_id=str(action_id or ""),
        turn_index=int(turn_index or 0),
        max_attempts=ticket_max_attempts,
        max_policy_attempts=2 if unknown_identifier_repair else 1,
        root_ticket_id=root_ticket_id,
        repair_depth=repair_depth,
        max_chain_depth=max(1, max_chain_depth),
        metadata=ticket_metadata,
    )


def _truncate_ticket_text(text: str, *, limit: int = 16000) -> str:
    value = str(text or "").strip()
    if len(value) <= limit:
        return value
    head = max(0, limit - 160)
    return value[:head].rstrip() + "\n... (truncated; full diagnostic is in the run record)"


def _fenced_ticket_block(text: str, *, language: str = "") -> str:
    body = str(text or "")
    longest = 0
    current = 0
    for char in body:
        if char == "`":
            current += 1
            longest = max(longest, current)
        else:
            current = 0
    fence = "`" * max(3, longest + 1)
    suffix = str(language or "").strip()
    opener = fence + suffix
    return "\n".join([opener, body, fence])


def _inline_ticket_code(text: str) -> str:
    value = str(text or "").strip().replace("`", "\\`")
    return f"`{value}`"


def _format_repair_ticket_prompt(ticket: RepairTicket) -> str:
    metadata = dict(getattr(ticket, "metadata", {}) or {})
    selected_work = (
        dict(metadata.get("selected_work_item") or {})
        if isinstance(metadata.get("selected_work_item"), dict)
        else {}
    )
    work_type = str(getattr(ticket, "work_type", "") or "").strip()
    declaration_repair = work_type in {
        "formalize_claim",
        "formalize_missing_obligation",
        "mine_missing_obligation",
    } and bool(
        metadata.get("formalization_required")
        or metadata.get("materialization_required")
        or selected_work.get("formalization_required")
        or selected_work.get("materialization_required")
    )
    helper_names = [
        str(name or "").strip()
        for name in list(getattr(ticket, "helper_names", ()) or ())
        if str(name or "").strip()
    ]
    parts = [
        "Repair the smallest failing local obligation exposed by this Lean rejection before changing route.",
        "",
        (
            "Use the previous declaration attempt as the edit base. Submit a revised complete Lean `theorem` or `lemma` declaration for the same graph formalization task, and use try_lean/check_lean on that declaration before final submission. If an auxiliary helper is needed, put it before the final declaration; the final declaration must explicitly connect the helper to the selected obligation or parent-anchored bridge. Do not submit a bare `by ...` proof body."
            if declaration_repair
            else "Use the previous proof as the edit base. Submit a revised complete Lean proof for the same active goal, and use try_lean/check_lean on the repaired proof before final submission. First patch the failing line; if that needs a bridge fact, manufacture the smallest Lean-checkable local `have`/helper statement under the same hypotheses and use it in the revised proof."
        ),
        "",
        "Previous rejected proof:",
        _fenced_ticket_block(
            _truncate_ticket_text(ticket.proof, limit=20000),
            language="lean",
        ),
    ]
    lineage_bits = [
        ("strategy", str(getattr(ticket, "strategy_lineage_id", "") or "")),
        ("route", str(getattr(ticket, "route_id", "") or "")),
        ("statement", str(getattr(ticket, "statement_identity", "") or "")),
        ("candidate", str(getattr(ticket, "proof_candidate_id", "") or "")),
        ("residual", str(getattr(ticket, "lean_residual_id", "") or "")),
        ("repair", str(getattr(ticket, "ticket_id", "") or "")),
    ]
    rendered_lineage = ", ".join(
        f"{label}={_inline_ticket_code(value[-24:])}"
        for label, value in lineage_bits
        if value
    )
    if rendered_lineage:
        parts[2:2] = [
            "Active proof lineage: " + rendered_lineage,
            (
                "Keep this repair attached to the same route consumer and "
                "residual; do not silently restart an equivalent cold route."
            ),
            "",
        ]
    lean_output = _truncate_ticket_text(ticket.lean_output, limit=16000)
    if lean_output:
        parts.extend([
            "",
            "Lean rejection output:",
            _fenced_ticket_block(lean_output, language="text"),
        ])
    feedback = _truncate_ticket_text(ticket.feedback_text, limit=12000)
    if feedback and feedback not in lean_output:
        parts.extend([
            "",
            "Structured repair feedback:",
            _fenced_ticket_block(feedback, language="text"),
        ])
    if helper_names:
        parts.extend([
            "",
            "Helpers in scope: "
            + ", ".join(_inline_ticket_code(n) for n in helper_names),
        ])
    unknown_identifier = str(metadata.get("unknown_identifier") or "").strip()
    if metadata.get("requires_api_search_for_unknown_identifier") and unknown_identifier:
        parts.extend([
            "",
            "API grounding required:",
            (
                "The previous Lean rejection used unknown identifier "
                f"{_inline_ticket_code(unknown_identifier)}. Before submitting "
                "another repair, call `search_mathlib`, `check_lean`, or "
                "`apply_decl_to_goal` to ground the declaration name. A blind "
                "retry against the same unknown identifier is a policy failure."
            ),
        ])
    elif (
        metadata.get("unknown_identifier_is_target_binder")
        or metadata.get("unknown_identifier_is_proof_local_binder")
    ) and unknown_identifier:
        parts.extend([
            "",
            "Local binder-scope repair required:",
            (
                f"{_inline_ticket_code(unknown_identifier)} is declared by the "
                "active target, not by Mathlib. Do not search the API for it. "
                "Introduce the target binders (or use an equivalent `fun`/"
                "`rintro` proof shape) before referencing that local name."
            ),
        ])
    if metadata.get("parse_error_code_generation_failure"):
        parts.extend([
            "",
            "Code-generation repair required:",
            (
                "The previous Lean rejection was a parse/code-generation "
                "failure. Repair the syntax and declaration shape locally; "
                "do not decompose residual proof-search goals produced by the "
                "malformed block."
            ),
        ])
    scope_lines = []
    route_id = str(getattr(ticket, "route_id", "") or "").strip()
    obligation_id = str(getattr(ticket, "obligation_id", "") or "").strip()
    proof_attempt_id = str(getattr(ticket, "proof_attempt_id", "") or "").strip()
    if work_type:
        scope_lines.append(f"- work_type: {_inline_ticket_code(work_type)}")
    if route_id:
        scope_lines.append(f"- route_id: {_inline_ticket_code(route_id)}")
    if obligation_id:
        scope_lines.append(f"- obligation_id: {_inline_ticket_code(obligation_id)}")
    if proof_attempt_id:
        scope_lines.append(
            f"- proof_attempt_id: {_inline_ticket_code(proof_attempt_id)}"
        )
    if scope_lines:
        parts.extend([
            "",
            "Repair scope:",
            *scope_lines,
            "Do not broaden this into an unrelated root proof.",
        ])
    target = str(getattr(ticket, "target_statement", "") or "").strip()
    if target:
        parts.extend([
            "",
            "Active target:",
            _fenced_ticket_block(
                _truncate_ticket_text(target, limit=6000),
                language="lean",
            ),
        ])
    return "\n".join(parts)


def _format_unknown_identifier_api_search_feedback(ticket: RepairTicket) -> str:
    metadata = dict(getattr(ticket, "metadata", {}) or {})
    unknown_identifier = str(metadata.get("unknown_identifier") or "").strip()
    name_text = (
        f"`{_prompt_safe_inline_text(unknown_identifier, limit=160)}`"
        if unknown_identifier
        else "the same unknown identifier"
    )
    return (
        "[API grounding required]\n"
        f"The selected repair ticket is blocked on {name_text}. The previous "
        "Lean rejection already showed this declaration name was not known in "
        "the current environment, so another proof edit without Mathlib/API "
        "grounding is not a meaningful repair. Call `search_mathlib`, "
        "`check_lean`, or `apply_decl_to_goal` to discover or verify the "
        "declaration name, then submit the repaired Lean block."
    )


def _inject_selected_repair_ticket_prompt(
    *,
    session: Any,
    conv: Any,
    repair_semantics: str,
) -> bool:
    ticket = getattr(session, "pending_repair_ticket", None)
    selected_id = str(getattr(session, "_repair_ticket_selected_id", "") or "").strip()
    if ticket is None or not selected_id:
        return False
    if str(getattr(ticket, "ticket_id", "") or "") != selected_id:
        return False
    metadata = getattr(ticket, "metadata", None)
    if not isinstance(metadata, dict):
        metadata = {}
        ticket.metadata = metadata
    attempt_no = int(getattr(ticket, "attempts_used", 0) or 0) + 1
    injected_for = int(metadata.get("prompt_injected_for_attempt", 0) or 0)
    if injected_for >= attempt_no:
        return False
    conv.append_user(
        _format_repair_ticket_prompt(ticket),
        repair_semantics=repair_semantics,
    )
    metadata["prompt_injected_for_attempt"] = attempt_no
    recorder = getattr(session, "_record_event", None)
    if callable(recorder):
        recorder({
            "phase": "session_repair_ticket",
            "iteration": getattr(session, "iteration", 0),
            "ticket_id": ticket.ticket_id,
            "target_id": ticket.target_id,
            "route_id": str(getattr(ticket, "route_id", "") or ""),
            "obligation_id": str(getattr(ticket, "obligation_id", "") or ""),
            "work_type": str(getattr(ticket, "work_type", "") or ""),
            "proof_attempt_id": str(getattr(ticket, "proof_attempt_id", "") or ""),
            "attempt_number": attempt_no,
            "attempts_used": int(getattr(ticket, "attempts_used", 0) or 0),
            "repair_depth": int(getattr(ticket, "repair_depth", 0) or 0),
            "verdict": "repair_prompt_injected",
        })
    return True


def _format_turn_giveup_feedback(
    *,
    conv: Any,
    session: Any,
    giveup: Dict[str, str],
    turn: int,
    max_turns: int,
) -> str:
    from ensemble_prover.mini_prover import _giveup_decomposition_nudge
    from ensemble_prover.proof_state_executor import _with_turn_budget_footer

    raw_depth_cap = getattr(session, "max_recursion_depth", 3)
    depth_cap = int(raw_depth_cap if raw_depth_cap is not None else 3)
    nudge = _giveup_decomposition_nudge(
        str(giveup.get("cluster") or ""),
        opaque_mode=bool(getattr(conv, "opaque_mode", False)),
        allow_official_answer_visibility=bool(
            getattr(conv, "allow_official_answer_visibility", False)
        ),
        official_answer_payload_present=getattr(
            conv,
            "official_answer_payload_present",
            None,
        ),
        allow_helper_decomposition=bool(
            getattr(conv, "allow_helper_decomposition", True)
        ),
        matched_phrase=str(giveup.get("match") or ""),
        recursion_depth=int(getattr(session, "recursion_depth", 0) or 0),
        max_recursion_depth=depth_cap,
        role=str(getattr(conv, "role", "") or "prove"),
    )
    return _with_turn_budget_footer(
        nudge,
        role=str(getattr(conv, "role", "") or "prove"),
        turn=turn,
        max_turns=max_turns,
    )


_REPAIR_SELF_CHECK_METADATA_KEYS: tuple[str, ...] = (
    "temperature_requested",
    "effective_temperature",
    "temperature_phase_key",
    "temperature_phase",
    "temperature_source",
    "temperature_reason",
    "sample_temperature",
    "temperature_sent",
    "temperature_provider_dropped",
    "temperature_provider_drop_reason",
    "reasoning_control_requested",
    "reasoning_control_decision",
    "reasoning_control_sent",
    "reasoning_control_required",
    "reasoning_capability_record",
    "llm_response_recorded",
    "repair_self_check_required",
    "repair_self_check_attempted",
    "repair_self_check_accepted",
    "repair_self_check_status",
    "repair_self_check_missing_kind",
    "repair_self_check_compliant",
    "repair_self_check_evidence_source",
    "repair_self_check_budget_exhausted",
    "repair_self_check_helper_only_allowed",
    "repair_self_check_mismatch_observed",
    "repair_self_check_terminal_continuation",
    "repair_self_check_advisory",
    "repair_discovery_tool_calls_used",
    "repair_verification_tool_calls_used",
    "repair_submission_has_executable_lean",
    "unknown_identifier_api_search_bypassed_by_exact_self_check",
    "unknown_identifier_api_search_advisory",
)


_TURN_BUDGET_METADATA_KEYS: tuple[str, ...] = (
    "max_tokens_override",
    "max_tokens_override_reason",
    "formalization_llm_request_timeout_s",
    "formalization_llm_turn_elapsed_s",
    "llm_turn_elapsed_s",
    "tool_repeat_detected",
    "tool_repeat_action",
    "tool_repeat_signature",
    "llm_failure_tool_history_compacted",
    "llm_failure_tool_history_compacted_messages",
    "llm_failure_tool_history_compacted_tool_rounds",
    "llm_failure_tool_history_compacted_chars",
    "compute_examples_protocol_attempts",
    "compute_examples_tool_calls",
    "compute_examples_successes",
    "compute_examples_malformed_calls",
    "paid_tool_infrastructure_disposition",
    "paid_tool_continuation_identity",
    "paid_tool_continuation_granted",
    "durable_progress_tool_continuation_identity",
    "durable_progress_tool_continuation_granted",
    "provider_calls_completed",
    "provider_dispatches_started",
    "semantic_no_progress_detected",
    "semantic_no_progress_reason",
    "semantic_no_progress_signature",
    "semantic_diagnostic_progress_count",
    "semantic_diagnostic_best_phase",
    "semantic_diagnostic_best_error_kind",
    "semantic_diagnostic_best_goal_count",
    "semantic_diagnostic_last_reason",
    "semantic_diagnostic_best_signature",
    "final_no_tools_event",
    "final_no_tools_finish_reason",
    "final_no_tools_reasoning_content_chars",
    "final_no_tools_used_accepted_proof",
    "provider_defer_fingerprint",
    "provider_defer_ready_at",
    "provider_defer_retry_after_s",
    "provider_call_cumulative_elapsed_s",
    "provider_call_cumulative_wall_cap_s",
    "provider_call_cumulative_wall_exhausted",
    "provider_turn_lane_retired",
    "provider_turn_lane_identity",
    "recovered_finalizer_error",
    "recovered_finalizer_failure_kind",
    "recovered_finalizer_retryable",
    "recovered_finalizer_provider_call_quantum_exhausted",
    "recovered_finalizer_terminal",
    "recovered_finalizer_failure_reason",
    "recovered_finalizer_retry_deadline",
    "recovered_finalizer_provider_attempts",
    "recovered_finalizer_provider_defer",
    "recovered_finalizer_candidate_lean_accepted",
    "recovered_finalizer_candidate_adjudication_pending",
)


_SKELETON_ROUTE_METADATA_KEYS: tuple[str, ...] = (
    "try_skeleton_tool_calls",
    "try_skeleton_routes_banked",
    "unverified_decomposition_created",
    "assembly_contracts_added",
)


def _repair_self_check_metadata(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Return repair self-check fields that must survive into outcomes."""

    return {
        key: payload[key]
        for key in _REPAIR_SELF_CHECK_METADATA_KEYS
        if key in payload
    }


_REPAIR_PROTOCOL_ADVISORY_ERRORS = frozenset(
    {
        "repair_self_check_missing",
        "repair_self_check_no_try_lean_call",
        "repair_self_check_no_accepted_try_lean",
        "repair_self_check_tool_budget_exhausted",
    }
)

# Policy quarantine is a bounded verifier side lane, not another open-ended
# proof search. These caps apply to the whole rejected response regardless of
# how many declarations it contains or what per-check timeout was requested.
_POLICY_QUARANTINE_MAX_CANDIDATES = 8
_POLICY_QUARANTINE_TOTAL_WALL_S = 30.0


def _repair_protocol_error_is_advisory(error: Any) -> bool:
    """Return whether an error is protocol telemetry, not proof authority.

    The outer Lean verification pipeline is the authoritative mathematical
    judge. A missing, rejected, malformed, or budget-starved scratch check may
    reduce diagnostic quality, but it must not discard an executable final
    artifact before that independent checker sees it.
    """

    return str(error or "").strip() in _REPAIR_PROTOCOL_ADVISORY_ERRORS


async def _run_policy_helper_quarantine(
    *,
    lean: Any,
    dossier: Any,
    proof_state: Any,
    helper_candidates: Sequence[str],
    preamble: str,
    root_statement: str,
    phase: str,
    turn_index: int,
    timeout_s: Optional[float],
    deadline_monotonic: float,
    lease_disposition: Dict[str, str],
    answer_safe_preamble: str = "",
    session: Any = None,
) -> Any:
    """Stage and atomically publish one bounded quarantine journal."""

    from ensemble_prover.helper_salvage import HelperSalvageResult, HelperSalvager
    from ensemble_prover.proof_dossier import ProofDossier
    from ensemble_prover.runtime_context import mark_runtime_owned_callback

    candidate_limit = max(0, int(_POLICY_QUARANTINE_MAX_CANDIDATES))
    candidates_to_check: list[str] = []
    seen_candidates: set[str] = set()
    candidate_stream = helper_candidates if helper_candidates is not None else ()
    truncated = False
    for index, raw_candidate in enumerate(
        islice(iter(candidate_stream), candidate_limit + 1)
    ):
        if index >= candidate_limit:
            truncated = True
            break
        candidate = str(raw_candidate or "").strip()
        if not candidate or candidate in seen_candidates:
            continue
        seen_candidates.add(candidate)
        candidates_to_check.append(candidate)
    if not candidates_to_check:
        result = HelperSalvageResult()
        if truncated:
            result.skipped.append("quarantine_candidate_limit")
        return result

    salvager = HelperSalvager(
        lean,
        preamble=str(preamble or ""),
        answer_safe_preamble=str(answer_safe_preamble or ""),
        timeout_s=timeout_s,
        relevance_gate_root_statement="",
        relevance_gate_open_targets=(),
    )

    async def stage_candidates() -> tuple[Any, list[Any]]:
        staged_result = HelperSalvageResult()
        journal: list[Any] = []
        reserved_names: set[str] = set()
        proposed_helpers = getattr(dossier, "proposed_helpers", {}) or {}
        proof_graph = getattr(dossier, "proof_graph", None)
        graph_helper_names = (
            getattr(proof_graph, "helper_name_to_node_id", {}) or {}
            if proof_graph is not None
            else {}
        )
        for candidate in candidates_to_check:
            name = str(helper_decl_name(candidate) or "").strip()
            if not name:
                staged_result.skipped.append(
                    str(candidate.splitlines()[0] if candidate else "unnamed")[:120]
                )
                continue
            if (
                name in reserved_names
                or dossier.has_helper(name)
                or dossier.has_proposed_helper(name)
                or name in proposed_helpers
                or name in graph_helper_names
            ):
                staged_result.skipped.append(f"{name}:live_name_collision")
                continue
            stage = ProofDossier(
                theorem_name=str(getattr(dossier, "theorem_name", "") or ""),
                root_statement=str(root_statement or ""),
                problem_text="",
                cache_owner_theorem_name=str(
                    getattr(dossier, "cache_owner_theorem_name", "") or ""
                ),
                proof_cache_publish_enabled=False,
                suppress_solution_placeholders=bool(
                    getattr(dossier, "suppress_solution_placeholders", True)
                ),
                current_lean_environment_hash=str(
                    getattr(dossier, "current_lean_environment_hash", "") or ""
                ),
            )
            candidate_result = await salvager.salvage(
                [candidate],
                dossier=stage,
                phase=str(phase or "policy_rejected_helper_quarantine"),
                turn_index=int(turn_index or 0),
            )
            staged_result.rejected.extend(candidate_result.rejected)
            staged_result.skipped.extend(candidate_result.skipped)
            for accepted_name in candidate_result.accepted:
                record = stage.verified_helpers.get(accepted_name)
                if record is None:
                    staged_result.rejected.append(
                        f"{accepted_name}:missing_staged_certificate"
                    )
                    continue
                reserved_names.add(accepted_name)
                journal.append(record)
        return staged_result, journal

    salvage_task = asyncio.ensure_future(stage_candidates())

    def consume_late_salvage_result(task: asyncio.Future[Any]) -> None:
        try:
            task.result()
        except asyncio.CancelledError:
            pass
        except Exception:
            pass

    consume_late_salvage_result = mark_runtime_owned_callback(
        consume_late_salvage_result
    )
    try:
        done, _pending = await asyncio.wait(
            {salvage_task},
            timeout=max(0.0, deadline_monotonic - time.monotonic()),
        )
    except BaseException:
        salvage_task.cancel()
        lease_disposition.update(
            kind="abandon",
            reason="policy_quarantine_external_failure",
        )
        salvage_task.add_done_callback(consume_late_salvage_result)
        raise
    if salvage_task not in done:
        salvage_task.cancel()
        settled, _pending = await asyncio.wait({salvage_task}, timeout=0.2)
        if salvage_task in settled:
            lease_disposition["kind"] = "settle_timeout"
            consume_late_salvage_result(salvage_task)
        else:
            lease_disposition.update(
                kind="abandon",
                reason="policy_quarantine_task_unsettled",
            )
            salvage_task.add_done_callback(consume_late_salvage_result)
        result = HelperSalvageResult()
        result.skipped.append("quarantine_total_wall_budget_exhausted")
        if truncated:
            result.skipped.append("quarantine_candidate_limit")
        return result

    result, journal = salvage_task.result()
    if truncated:
        result.skipped.append("quarantine_candidate_limit")

    reconcile = getattr(proof_state, "reconcile_with_dossier", None)
    if callable(reconcile):
        reconcile(dossier)
    if time.monotonic() >= deadline_monotonic:
        result.skipped.append("quarantine_total_wall_budget_exhausted")
        lease_disposition["kind"] = "settle_timeout"
        return result

    preflight = getattr(dossier, "preflight_imported_verified_helper", None)
    for record in journal:
        if callable(preflight) and preflight(record) is None:
            result.rejected.append(
                f"{str(getattr(record, 'name', '') or 'unnamed')}:"
                "commit_preflight_rejected"
            )
            return result

    imported_names: list[str] = []
    try:
        for record in journal:
            imported = dossier.record_imported_verified_helper(
                record,
                phase=str(phase or "policy_rejected_helper_quarantine"),
                turn_index=int(turn_index or 0),
            )
            if imported is None:
                raise RuntimeError(
                    "policy quarantine helper commit rejected after preflight"
                )
            imported_names.append(str(getattr(imported, "name", "") or ""))
    except BaseException:
        remove_helper = getattr(dossier, "remove_verified_helper", None)
        if callable(remove_helper):
            for imported_name in reversed(imported_names):
                remove_helper(imported_name)
        raise
    result.accepted.extend(imported_names)
    if session is not None:
        for imported_name in imported_names:
            imported = getattr(dossier, "verified_helpers", {}).get(imported_name)
            if imported is not None:
                _stage_verified_helper_receipt(session, imported, dossier)
    return result


async def _salvage_policy_rejected_helpers(
    *,
    verdict_kind: Any,
    lean: Any,
    dossier: Any,
    proof_state: Any,
    helper_candidates: Sequence[str],
    preamble: str,
    root_statement: str,
    phase: str,
    turn_index: int,
    timeout_s: Optional[float],
    answer_safe_preamble: str = "",
    session: Any = None,
) -> Any:
    """Lean-certify safe helper declarations outside a forbidden root.

    The original response remains rejected as one compilation unit. Only the
    extractor's declaration-sized candidates enter ``HelperSalvager``, whose
    own command/source policy and incremental Lean replay form a quarantine
    boundary. Thus a root containing ``set_option`` or another forbidden
    command cannot be smuggled into the validation environment, while an
    independent, policy-safe theorem declaration is not thrown away with it.
    """

    from ensemble_prover.helper_salvage import HelperSalvageResult
    from ensemble_prover.mini_session.turn.policy import PolicyVerdictKind

    empty = HelperSalvageResult()
    if verdict_kind is not PolicyVerdictKind.REJECT_FORBIDDEN_CMD:
        return empty
    if lean is None or dossier is None:
        return empty

    # Acquire the process lease before even walking provider-owned candidate
    # input.  Consume at most one sentinel beyond the hard candidate cap;
    # neither a huge sequence nor a duplicate stream may turn quarantine
    # staging into unmetered synchronous work.
    quarantine_wall_s = max(0.001, float(_POLICY_QUARANTINE_TOTAL_WALL_S))
    quarantine_deadline_monotonic = time.monotonic() + quarantine_wall_s
    quarantine_lease = begin_process_deadline(
        deadline_monotonic=quarantine_deadline_monotonic,
        label="mini_policy_helper_quarantine",
    )
    # Exactly one lifecycle edge owns the process watchdog from acquisition
    # through staging, reconciliation, preflight, commit, and rollback.  The
    # inner operation may select timeout abandonment/settlement, but it never
    # touches the lease directly.
    lease_disposition = {"kind": "close", "reason": ""}
    try:
        return await _run_policy_helper_quarantine(
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            helper_candidates=helper_candidates,
            preamble=preamble,
            answer_safe_preamble=answer_safe_preamble,
            root_statement=root_statement,
            phase=phase,
            turn_index=turn_index,
            timeout_s=timeout_s,
            deadline_monotonic=quarantine_deadline_monotonic,
            lease_disposition=lease_disposition,
            session=session,
        )
    finally:
        disposition = str(lease_disposition.get("kind") or "close")
        if disposition == "abandon":
            quarantine_lease.abandon(
                str(lease_disposition.get("reason") or "policy_quarantine_unsettled")
            )
        elif disposition == "settle_timeout":
            quarantine_lease.settle_timeout()
        else:
            quarantine_lease.close()


def _turn_budget_metadata(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Return LLM budget/cap fields that must survive into outcomes."""

    return {key: payload[key] for key in _TURN_BUDGET_METADATA_KEYS if key in payload}


def _activated_recovered_finalizer_failure_metadata(
    payload: Mapping[str, Any],
) -> Dict[str, Any]:
    """Activate a banked provider receipt after its proof fails adjudication."""

    kind = str(payload.get("recovered_finalizer_failure_kind") or "").strip()
    if not kind:
        return {}
    retryable = bool(payload.get("recovered_finalizer_retryable"))
    terminal = bool(payload.get("recovered_finalizer_terminal"))
    failure_reason = str(
        payload.get("recovered_finalizer_failure_reason") or ""
    ).strip()
    terminal_reason = failure_reason if terminal else ""
    scoped_reason = ""
    failure_scope = llm_failure_scope(terminal_reason)

    provider_blocked_reason = _PROVIDER_BLOCKED_REASON_BY_KIND.get(kind, "")
    provider_lane_run_closed = kind == "provider_lane_run_closed"
    provider_lane_retired = kind == "llm_provider_cumulative_wall_exhausted"
    authenticated_quantum_yield = bool(
        payload.get("recovered_finalizer_provider_call_quantum_exhausted")
    )
    cooperative_provider_yield = bool(
        kind == "llm_provider_quantum_exhausted"
        or (
            kind == "provider_dispatch_attempt_limit_exhausted"
            and authenticated_quantum_yield
        )
    )
    if cooperative_provider_yield:
        # A settled-call scheduler boundary can coexist with a banked
        # candidate that is adjudicated later in the same action.  If that
        # candidate is rejected, activating the saved receipt must retain the
        # exact continuation; treating it as a global provider failure would
        # overwrite policy-repair/frontier ownership and consume live work.
        terminal = False
        terminal_reason = ""
        retryable = True
        scoped_reason = ""
        failure_scope = ""
    elif provider_lane_run_closed:
        # This exact serving fingerprint is unusable for the rest of the run,
        # but a different role/provider fingerprint remains valid work.  Do
        # not retry this lane and do not terminate the whole MiniSession.
        terminal = False
        terminal_reason = ""
        retryable = False
        scoped_reason = "provider_lane_run_closed"
        failure_scope = "scoped"
    elif provider_blocked_reason:
        terminal = False
        terminal_reason = ""
        retryable = True
        scoped_reason = provider_blocked_reason
        failure_scope = "scoped"
    elif provider_lane_retired:
        terminal = False
        terminal_reason = ""
        retryable = True
        scoped_reason = "llm_provider_cumulative_wall_exhausted"
        failure_scope = "scoped"
    elif not terminal and (
        kind in {"transient", "transport"}
        or (kind == "rate_limit" and retryable)
        or (kind.startswith("http_") and retryable)
    ):
        scoped_reason = failure_reason or "llm_network_error"
        failure_scope = "scoped"
    elif (
        not terminal
        and retryable
        and llm_failure_scope(failure_reason) == "scoped"
    ):
        scoped_reason = failure_reason
        failure_scope = "scoped"

    if failure_scope == "scoped":
        scoped_reason = scoped_reason or terminal_reason or failure_reason
        terminal = False
        terminal_reason = ""

    provider_defer = dict(
        payload.get("recovered_finalizer_provider_defer") or {}
    )
    retry_deadline = dict(
        payload.get("recovered_finalizer_retry_deadline") or {}
    )
    provider_attempts = list(
        payload.get("recovered_finalizer_provider_attempts") or []
    )
    should_defer = bool(not terminal and retryable and failure_scope == "scoped")
    preserve_ready_continuation = bool(cooperative_provider_yield)
    return {
        # Telemetry is intentionally merged before the authoritative routing
        # decision.  A malformed provider/checkpoint payload must never be
        # able to overwrite the computed terminal or scheduling fields.
        **retry_deadline,
        **provider_defer,
        "llm_error": str(payload.get("recovered_finalizer_error") or ""),
        "llm_failure_kind": kind,
        "llm_retryable": retryable,
        "terminal_failure": terminal,
        "terminal_failure_reason": terminal_reason,
        "llm_failure_scope": failure_scope,
        "scoped_failure_reason": scoped_reason,
        "provider_attempts": provider_attempts,
        "provider_turn_lane_retired": provider_lane_retired,
        "preserve_frontier_work": bool(
            should_defer or preserve_ready_continuation
        ),
        "defer_selected_frontier_action": should_defer,
        "recovered_finalizer_provider_receipt_activated": True,
    }


def _skeleton_route_metadata(
    payload: Dict[str, Any],
    *,
    soft_only: bool = False,
) -> tuple[bool, Dict[str, Any]]:
    """Return skeleton route fields that must survive every downstream outcome."""

    try:
        routes_banked = int(payload.get("try_skeleton_routes_banked") or 0)
    except (TypeError, ValueError):
        routes_banked = 0
    banked = routes_banked > 0
    metadata = {
        key: payload[key]
        for key in _SKELETON_ROUTE_METADATA_KEYS
        if key in payload
    }
    if banked:
        metadata["unverified_decomposition_created"] = True
        metadata["assembly_contracts_added"] = True
        if soft_only:
            metadata["strong_progress"] = False
    return banked, metadata


# `_strong_progress_for_accepted_helpers` was moved to
# ``ensemble_prover.proof_dossier`` so every Action that emits
# ``strong_progress`` metadata uses the same classifier. Re-exported here
# as a module-level name for backwards-compatible imports.
from ensemble_prover.proof_dossier import (  # noqa: E402
    strong_progress_for_accepted_helpers as _strong_progress_for_accepted_helpers,
    theory_progress_for_accepted_helpers as _theory_progress_for_accepted_helpers,
)


def _bank_turn_sources_as_proposed(
    dossier: Any,
    conv: Any,
    helpers: Sequence[str],
    *,
    phase: str,
    turn_index: int,
    fallback_helpers: Sequence[str] = (),
) -> List[str]:
    if dossier is None or not _can_bank_rejected_proposed_helpers(conv):
        return []
    try:
        from ensemble_prover.mini_prover import _bank_helpers_as_proposed

        return list(
            _bank_helpers_as_proposed(
                dossier,
                list(helpers or ()),
                phase=phase,
                turn_index=turn_index,
                fallback_helpers=list(fallback_helpers or ()),
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=bool(
                    getattr(conv, "allow_helper_decomposition", True)
                ),
            )
        )
    except Exception:
        return []


def _effective_official_answer_visibility(session: Any) -> bool:
    """Return the capability-backed answer policy for this exact prompt."""

    session_policy = getattr(
        session,
        "_effective_official_answer_visibility",
        None,
    )
    if callable(session_policy):
        try:
            return session_policy() is True
        except Exception:
            return False

    # Fail-closed compatibility path for narrow test and legacy stubs that do
    # not expose MiniSession's canonical policy helper.
    conv = getattr(session, "conv", None)
    dossier = getattr(session, "dossier", None)
    return _conversation_official_answer_visible(conv, dossier)


def _format_graph_native_selected_work_prompt(
    session: Any,
    *,
    execution_target: Optional[Mapping[str, Any]] = None,
) -> str:
    """Render the selected graph-native DAG work as an explicit LLM target."""

    record = getattr(session, "selected_work_item_record", None)
    if not isinstance(record, dict):
        return ""
    item_record = dict(
        getattr(getattr(session, "selected_work_item", None), "graph_record", None)
        or {}
    )
    graph_record = dict(record.get("graph_record") or {})
    merged_record = {**graph_record, **item_record, **record}
    if _selected_work_terminal_graph_target_suppressed(
        session,
        merged_record,
        context="graph_native_selected_work_prompt",
    ):
        return ""
    work_type = str(merged_record.get("work_type") or "").strip()
    if work_type not in {
        "formalize_claim",
        "formalize_missing_obligation",
        "prove_claim_variant",
        "mine_missing_obligation",
        "route_replan",
        "target_integrity_adjudication",
        "materialize_replay_source",
        "assemble_route",
    }:
        return ""
    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    official_answer_visible = _effective_official_answer_visibility(session)
    redact_solution_refs = not official_answer_visible

    def prompt_safe(
        value: Any,
        *,
        limit: int,
        truncate: bool = True,
        preserve_layout: bool = False,
    ) -> str:
        return _prompt_safe_inline_text(
            str(value or ""),
            limit=limit,
            redact_solution_refs=redact_solution_refs,
            truncate=truncate,
            preserve_layout=preserve_layout,
        )

    def answer_hidden_statement(value: Any) -> bool:
        return bool(
            redact_solution_refs
            and is_answer_unsafe_statement_text(
                str(value or ""),
                suppress_solution_placeholders=True,
            )
        )

    def node_summary(label: str, node_id: str) -> str:
        node_key = str(node_id or "").strip()
        if not node_key:
            return ""
        node = nodes.get(node_key) if isinstance(nodes, dict) else None
        if node is None:
            safe_key = prompt_safe(node_key, limit=120)
            return f"- {label}: `{safe_key}`"
        name = prompt_safe(
            str(getattr(node, "name", "") or node_key),
            limit=160,
        )
        status = prompt_safe(
            str(getattr(node, "status", "") or ""),
            limit=80,
        )
        node_metadata = dict(getattr(node, "metadata", {}) or {})
        raw_statement = str(getattr(node, "statement", "") or "").strip()
        suppress_nonexecutable_formalization_statement = bool(
            formalization_contract
            and raw_statement
            and (
                node_key == primary_node_id
                or bool(node_metadata.get("formalization_required"))
            )
            and not graph_statement_is_executable(raw_statement)
        )
        statement = prompt_safe(
            (
                ""
                if suppress_nonexecutable_formalization_statement
                or answer_hidden_statement(raw_statement)
                else raw_statement
            ),
            limit=700,
        )
        suffix = f" [{status}; graph label, not a Lean declaration]" if status else " [graph label, not a Lean declaration]"
        if statement:
            return f"- {label}: {name}{suffix}: {statement}"
        return f"- {label}: {name}{suffix}"

    ids = {
        "route": str(merged_record.get("route_id") or "").strip(),
        "claim": str(merged_record.get("claim_id") or "").strip(),
        "variant": str(merged_record.get("variant_id") or "").strip(),
        "obligation": str(merged_record.get("obligation_id") or "").strip(),
        "replan": str(merged_record.get("replan_id") or "").strip(),
    }
    primary_node_id = (
        ids.get("obligation")
        or ids.get("variant")
        or ids.get("claim")
        or ids.get("replan")
        or str(merged_record.get("graph_node_id") or merged_record.get("node_id") or "").strip()
    )
    primary_node = nodes.get(primary_node_id) if isinstance(nodes, dict) else None
    if primary_node is not None:
        node_metadata = dict(getattr(primary_node, "metadata", {}) or {})
        if node_metadata:
            merged_record = {**node_metadata, **merged_record}
    formalization_contract = _selected_formalization_helper_contract(session)
    if formalization_contract:
        record = getattr(session, "selected_work_item_record", None)
        if not isinstance(record, dict):
            record = {}
        selected_work_item = getattr(session, "selected_work_item", None)
        item_record = dict(getattr(selected_work_item, "graph_record", None) or {})
        graph_record = dict(record.get("graph_record") or {})
        merged_record = {**graph_record, **item_record, **record}
        if primary_node is not None:
            node_metadata = dict(getattr(primary_node, "metadata", {}) or {})
            if node_metadata:
                merged_record = {**node_metadata, **merged_record}
    lines = [
        "Graph-selected proof task:",
        f"- work type: `{work_type}`",
        "- invariant: this selected graph work is the active target for this turn; do not drift back to the root unless the work type is `assemble_route`.",
    ]
    selected_lifecycle_context = _selected_proof_idea_context_for_prompt(
        session,
        merged_record,
        audience="conversation",
    )
    if selected_lifecycle_context:
        lines.append(selected_lifecycle_context)
    for label, node_id in ids.items():
        rendered = node_summary(label, node_id)
        if rendered:
            lines.append(rendered)
    bound_execution_statement = str(
        (execution_target or {}).get("statement") or ""
    ).strip()
    raw_record_target = str(
        bound_execution_statement
        or merged_record.get("target_statement")
        or ""
    )
    if official_answer_visible and not bound_execution_statement:
        raw_record_target = str(
            item_record.get("target_statement")
            or graph_record.get("target_statement")
            or raw_record_target
            or getattr(primary_node, "statement", "")
            or ""
        )
    record_target = prompt_safe(
        (
            ""
            if (
                (
                    bool(merged_record.get("target_statement_answer_redacted"))
                    and not official_answer_visible
                )
                or answer_hidden_statement(raw_record_target)
            )
            else raw_record_target
        ),
        limit=700,
        truncate=False,
        preserve_layout=True,
    )
    if record_target:
        lines.append(f"- selected target statement: {record_target}")
    record_reason = prompt_safe(
        str(merged_record.get("obligation_reason") or ""),
        limit=300,
    )
    if record_reason:
        lines.append(f"- obligation reason: {record_reason}")
    parent_statement = prompt_safe(
        _formalization_parent_statement(session, merged_record),
        limit=700,
    )
    if parent_statement and work_type in {
        "formalize_missing_obligation",
        "mine_missing_obligation",
        "route_replan",
    }:
        lines.append(f"- parent target this work must support: `{parent_statement}`")
    forbidden_fragments = [
        prompt_safe(str(item or ""), limit=160)
        for item in list(merged_record.get("forbidden_materialization_fragments") or ())
        if str(item or "").strip()
    ]
    if forbidden_fragments and work_type == "formalize_missing_obligation":
        lines.append(
            "- stale rejected fragment(s), not standalone targets: "
            + ", ".join(f"`{item}`" for item in forbidden_fragments[:5])
        )
    rejected_candidates = [
        item
        for item in list(merged_record.get("rejected_formalization_candidates") or ())
        if isinstance(item, dict)
    ][-3:]
    if rejected_candidates and work_type == "formalize_missing_obligation":
        lines.append("- rejected formalization candidates to avoid repeating:")
        for item in rejected_candidates:
            statement = prompt_safe(
                str(item.get("statement") or ""),
                limit=360,
            )
            reason = prompt_safe(
                str(item.get("reason") or "rejected"),
                limit=160,
            )
            if statement:
                lines.append(f"  - `{statement}`; reason: {reason}")
    formalization_declaration_required = bool(formalization_contract)
    if merged_record.get("formalization_required"):
        lines.append(
            "- formalization required / materialization required: this is a graph-owned local-theory task, not a benchmark/root-closure shortcut. Submit the smallest executable Lean theorem or lemma statement under the route hypotheses, together with a proof attempt or Lean diagnostic from that attempted proof."
        )
        if formalization_declaration_required:
            required_name = prompt_safe(
                str(
                    formalization_contract.get("required_declaration_name")
                    or formalization_contract.get("name")
                    or ""
                ),
                limit=120,
            )
            if required_name:
                lines.append(
                    "- required final declaration name: "
                    f"`{required_name}`"
                )
            lines.append(
                "- declaration contract: because no executable Lean target is available yet, submit complete `theorem` or `lemma` declarations. If an auxiliary helper is needed, place it first; the final declaration must be the selected formalized obligation or parent-anchored bridge that uses those helpers. A bare `by ...` proof will not be checked against the root."
            )

    if work_type == "target_integrity_adjudication":
        instruction = (
            "Adjudicate this Lean-rejected target from clean state. Do not "
            "repeat unverified prose refutations as a reason to abandon it. "
            "Either prove the selected target, replace the bad bridge with a "
            "verified smaller lemma, or provide a Lean-checked counterexample "
            "or negation before retiring the target."
        )
    elif work_type == "formalize_claim":
        if formalization_declaration_required:
            instruction = (
                "Formalize this manufactured obligation as complete Lean "
                "theorem or lemma declaration(s), with all route hypotheses "
                "explicit in the final statement and a complete proof body. If an "
                "auxiliary helper is necessary, include it before the final "
                "declaration; do not stop after an auxiliary-only helper. Do not "
                "submit only the proposition, a bare proof body, a root proof, "
                "or the reason text. Also do not submit the reason as the "
                "Lean target; the checker will verify the declaration itself."
            )
        elif merged_record.get("formalization_required"):
            instruction = (
                "Formalize this manufactured obligation into the smallest "
                "executable Lean proposition with all route hypotheses explicit, "
                "then submit a Lean proof attempt for it in this turn. Use the "
                "reason text only as a pointer to the local calculation; do "
                "not submit the reason as the Lean target or stop at a bare "
                "proposition."
            )
        else:
            instruction = (
                "Formalize this proposed claim into the smallest executable Lean "
                "helper statement with all hypotheses explicit, then submit a "
                "Lean proof attempt for that statement in this turn."
            )
    elif work_type == "formalize_missing_obligation":
        if formalization_declaration_required:
            instruction = (
                "Formalize this missing obligation as complete Lean theorem "
                "or lemma declaration(s), with all route hypotheses explicit in "
                "the final statement and a complete proof body. If an auxiliary helper "
                "is necessary, include it before the final declaration; do not "
                "stop after an auxiliary-only helper. The final statement must "
                "share concrete mathematical objects with the parent target "
                "and be useful route support for later parent assembly; do "
                "not submit a generic library-name repair or a theorem that "
                "only fixes a stale rejected fragment. Do not submit only the "
                "proposition, a bare proof body, a root proof, or the reason "
                "text. Also do not submit the reason as the Lean target; the "
                "checker will verify the declaration itself."
            )
        else:
            instruction = (
                "Formalize this manufactured obligation into the smallest "
                "executable Lean proposition with all route hypotheses explicit, "
                "then submit a Lean proof attempt for it in this turn. Use the "
                "reason text only as a pointer to the local calculation; do not "
                "submit the reason as the Lean target or stop at a bare proposition."
            )
    elif work_type == "prove_claim_variant":
        instruction = (
            "Prove the selected formal variant as a Lean helper. If it blocks, "
            "submit the concrete failed local `have`/`suffices` attempt with "
            "Lean diagnostics or a Lean-tested counterexample rather than "
            "broad prose."
        )
    elif work_type == "mine_missing_obligation":
        instruction = (
            "Manufacture the selected missing obligation for this route: prove "
            "it directly, or replace it with a smaller true bridge that makes "
            "the route executable. Do not treat unavailable context as a final "
            "answer."
        )
    elif work_type == "route_replan":
        instruction = (
            "Repair the selected route by addressing its obligation first. "
            "Do not restart from the whole problem; submit a Lean proof "
            "attempt for the next executable route step, or a concrete "
            "failed local `have`/`suffices` attempt with Lean diagnostics. "
            "Do not stop at a bare proposition."
        )
    elif work_type == "assemble_route":
        lines.extend(_selected_assemble_route_active_root_lines(session))
        _, _, route_helper_blocks = _selected_assemble_route_contract_context(session)
        helper_lines = _helper_signature_lines_from_blocks(
            route_helper_blocks,
            limit=16,
        )
        if helper_lines:
            lines.append("- contract-scoped helper declarations available in Lean:")
            lines.extend(helper_lines)
        instruction = (
            "The deterministic tactic stitcher already failed on this route. "
            "Author the final Lean proof of the active root target directly, "
            "using only the contract-scoped helpers plus local reasoning. Do "
            "not search for a ready-made theorem, do not re-prove the answer "
            "shell, and do not submit helper stubs instead of the root proof. "
            "Use the route contract as a local theory; if composition exposes "
            "a local bridge gap, prove it locally in the root proof or submit "
            "the concrete failed local `have`/`suffices` attempt with Lean "
            "diagnostics."
        )
    else:
        instruction = (
            "Assemble the selected route using already proved graph claims/helpers. "
            "Submit the concrete Lean proof step that closes the route or root."
        )
    lines.append(f"- instruction: {instruction}")
    rendered = "\n".join(lines)
    if redact_solution_refs:
        # Prompt sanitization deliberately uses stable hashed aliases in most
        # surfaces, but those aliases resemble valid Lean identifiers.  This
        # graph-selected task surface must not invite the model to prove a
        # synthetic executable target after an answer reference was hidden.
        rendered = _GENERATED_SOLUTION_REF_ALIAS_RE.sub(
            "[official-answer reference hidden]",
            rendered,
        )
    return rendered


_GRAPH_REVISION_DERIVED_SCOPE_KEYS = frozenset(
    {
        "graph_revision",
        "proof_idea_graph_revision",
        "execution_currentness_digest",
        "cognition_currentness_digest",
        "cognition_graph_revision_unavailable",
        "cognition_graph_revision_failure_reason",
    }
)


def _graph_selected_work_scope_key(
    session: Any,
    selected_work: Optional[Mapping[str, Any]] = None,
) -> str:
    """Stable identity for both execution and cognition shown to the model.

    Exact formal work may be shared by several proof-idea consumers.  Reusing
    the same Lean target therefore does *not* imply that the conversation may
    retain the previous route/claim/branch strategy context.  Bind the anchor
    to both scopes so a primary-consumer switch clears target-local history.
    Graph revisions and their derived digests are freshness receipts, not
    owner coordinates; the exact prompt-dispatch validator checks them after
    the current anchor has been rendered.
    """

    record = dict(
        selected_work
        if selected_work is not None
        else (getattr(session, "selected_work_item_record", {}) or {})
    )
    statement = str(
        record.get("exact_target_statement")
        or record.get("target_statement")
        or ""
    ).strip()
    execution_scope = record.get("execution_scope")
    primary_cognition = (
        record.get("primary_cognition_scope")
        or record.get("primary_consumer_binding")
        or {}
    )
    consumer_bindings = record.get("consumer_bindings") or []

    def stable_record(value: Any) -> str:
        if not value:
            return ""

        def without_revision_derived(item: Any) -> Any:
            if isinstance(item, Mapping):
                return {
                    str(key): without_revision_derived(nested)
                    for key, nested in item.items()
                    if str(key) not in _GRAPH_REVISION_DERIVED_SCOPE_KEYS
                }
            if isinstance(item, list):
                return [without_revision_derived(nested) for nested in item]
            if isinstance(item, tuple):
                return [without_revision_derived(nested) for nested in item]
            return item

        normalized = without_revision_derived(value)
        try:
            return json.dumps(
                normalized,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
        except (TypeError, ValueError):
            return str(normalized)

    parts = (
        str(record.get("node_id") or record.get("graph_node_id") or "").strip(),
        str(record.get("work_type") or "").strip(),
        str(record.get("target_hash") or "").strip(),
        str(record.get("execution_scope_id") or "").strip(),
        str(record.get("execution_target_sha256") or "").strip(),
        str(record.get("execution_environment_hash") or "").strip(),
        str(record.get("execution_contract_identity") or "").strip(),
        stable_record(execution_scope),
        stable_record(primary_cognition),
        stable_record(consumer_bindings),
        statement,
    )
    if not any(parts):
        return ""
    return hashlib.sha256(
        "\n".join(parts).encode("utf-8", errors="replace")
    ).hexdigest()[:24]


def _is_graph_selected_work_prompt_message(msg: Any) -> bool:
    marker = (
        msg.get("_required_prompt_context")
        if isinstance(msg, dict)
        else None
    )
    return bool(
        isinstance(msg, dict)
        and msg.get("role") == "user"
        and (
            str(msg.get("content", "") or "").startswith(
                "Graph-selected proof task:"
            )
            or (
                isinstance(marker, Mapping)
                and str(marker.get("kind") or "") == "selected_work"
            )
        )
    )


def _purge_stored_graph_selected_work_prompts(
    conv: Any,
    *,
    new_scope_key: str = "",
) -> int:
    """Retire scheduler prompts, including target-local history on a switch.

    A same-target repair keeps its failed attempts and Lean diagnostics.  A
    different target starts a fresh target-local segment; otherwise retrieval
    and diagnostics for target A remain active while the scheduler asks for B.
    """

    history = getattr(conv, "history", None)
    if not isinstance(history, list):
        return 0
    setattr(conv, "_graph_selected_work_scope_anchor_message", None)
    prompt_indices = [
        index
        for index, msg in enumerate(history)
        if _is_graph_selected_work_prompt_message(msg)
    ]
    previous_scope_key = ""
    current_segment_start = prompt_indices[-1] if prompt_indices else -1
    if prompt_indices:
        previous = history[prompt_indices[-1]]
        previous_scope_key = str(
            previous.get(_GRAPH_SELECTED_WORK_SCOPE_KEY) or ""
        ).strip()
        if previous_scope_key:
            for index in reversed(prompt_indices[:-1]):
                candidate_scope = str(
                    history[index].get(_GRAPH_SELECTED_WORK_SCOPE_KEY) or ""
                ).strip()
                if candidate_scope != previous_scope_key:
                    break
                current_segment_start = index
    else:
        previous_scope_key = str(
            getattr(conv, "_graph_selected_work_last_scope_key", "") or ""
        ).strip()
    if not str(new_scope_key or "").strip():
        # Leaving the graph-selected lane retires the whole anchored,
        # target-local segment.  Removing only the pinned prompt leaves its
        # assistant attempts behind while retaining ``last_scope_key``.  A
        # later A -> root -> B interleave then mistakes the first root
        # assistant for unanchored A-local history and truncates the entire
        # transcript.  The prompt anchor is the authoritative root -> graph
        # boundary, so preserve everything before it and clear the fallback
        # scope identity with the packet.
        removed = 0
        if prompt_indices:
            cut = prompt_indices[0]
            removed = len(history) - cut
            conv.history = history[:cut]
        setattr(conv, "_graph_selected_work_last_scope_key", "")
        setattr(conv, "_graph_selected_work_scope_changed", False)
        return removed
    unanchored_target_local_start = -1
    for index, msg in enumerate(history):
        if not isinstance(msg, dict):
            continue
        role = str(msg.get("role") or "")
        content = str(msg.get("content") or "")
        if (
            role == "assistant"
            and (content.strip() or bool(msg.get("tool_calls")))
        ) or (
            role == "user"
            and (
                _message_repair_semantics(msg) == _REPAIR_FEEDBACK
                or "Lean rejected" in content
                or "Primary error family:" in content
                or (
                    _is_history_compaction_summary(msg)
                    and not _is_stable_handoff_message(msg)
                )
            )
        ):
            unanchored_target_local_start = index
            break
    scope_changed = bool(
        new_scope_key
        and (
            (
                prompt_indices
                and previous_scope_key != str(new_scope_key or "").strip()
            )
            or (
                not prompt_indices
                and previous_scope_key
                and previous_scope_key != str(new_scope_key or "").strip()
            )
        )
    )
    setattr(conv, "_graph_selected_work_scope_changed", scope_changed)
    if scope_changed:
        scoped_transition_start = -1
        if prompt_indices:
            first_prompt = history[prompt_indices[0]]
            if str(
                first_prompt.get(_GRAPH_SELECTED_WORK_SCOPE_KEY) or ""
            ).strip():
                # This is the authoritative root→graph transition. Earlier
                # proof attempts and Lean feedback are root-scoped, even when
                # their surface shape resembles target-local repair history.
                scoped_transition_start = prompt_indices[0]
        cut_candidates = [
            index
            for index in (
                scoped_transition_start,
                (
                    prompt_indices[0]
                    if prompt_indices and scoped_transition_start < 0
                    else -1
                ),
                (
                    unanchored_target_local_start
                    if scoped_transition_start < 0
                    else -1
                ),
            )
            if index >= 0
        ]
        if cut_candidates:
            cut = min(cut_candidates)
            removed = len(history) - cut
            conv.history = history[:cut]
        else:
            removed = 0
        return removed

    if prompt_indices and new_scope_key and previous_scope_key:
        anchor = history[current_segment_start]
        migration_prefix_cut = current_segment_start
        migration_removed = 0
        if (
            unanchored_target_local_start >= 0
            and unanchored_target_local_start < current_segment_start
        ):
            migration_prefix_cut = min(
                prompt_indices[0],
                unanchored_target_local_start,
            )
            migration_removed = current_segment_start - migration_prefix_cut
            history = [
                *history[:migration_prefix_cut],
                *history[current_segment_start:],
            ]
            current_segment_start = migration_prefix_cut
        kept: List[Dict[str, Any]] = []
        removed = max(0, migration_removed)
        for msg in history:
            if (
                _is_graph_selected_work_prompt_message(msg)
                and msg is not anchor
            ):
                removed += 1
                continue
            kept.append(msg)
        conv.history = kept
        setattr(conv, "_graph_selected_work_scope_anchor_message", anchor)
        return removed

    return 0


_GRAPH_NATIVE_PROOF_WORK_TYPES = frozenset(
    {
        "formalize_claim",
        "formalize_missing_obligation",
        "prove_claim_variant",
        "mine_missing_obligation",
        "route_replan",
        "target_integrity_adjudication",
        "materialize_replay_source",
    }
)
_GRAPH_NATIVE_CONVERSATION_WORK_TYPES = _GRAPH_NATIVE_PROOF_WORK_TYPES


def _selected_assemble_route_record(session: Any) -> Dict[str, Any]:
    record = getattr(session, "selected_work_item_record", None)
    if not isinstance(record, dict):
        return {}
    if str(record.get("work_type") or "").strip() != "assemble_route":
        return {}
    item_record = dict(
        getattr(getattr(session, "selected_work_item", None), "graph_record", None)
        or {}
    )
    graph_record = dict(record.get("graph_record") or {})
    return {**graph_record, **item_record, **record}


def _selected_assemble_route_authoring_ready(session: Any) -> bool:
    merged = _selected_assemble_route_record(session)
    if not merged:
        return False
    if str(merged.get("mapped_action_id") or "").strip() not in {
        "",
        "conversation_turn_prove",
        "conversation_turn_refine",
        "conversation_turn",
    }:
        return False
    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    if graph is None or not isinstance(nodes, dict):
        return False
    route_id = str(
        merged.get("route_id")
        or merged.get("graph_node_id")
        or merged.get("node_id")
        or ""
    ).strip()
    route = nodes.get(route_id)
    if route is None or str(getattr(route, "kind", "") or "") != "strategy_route":
        return False
    metadata = getattr(route, "metadata", None)
    if not isinstance(metadata, dict):
        return False
    contract_status_getter = getattr(graph, "route_assembly_contract_status", None)
    if not callable(contract_status_getter):
        return False
    problem = getattr(session, "problem", None)
    active_target = active_root_target_statement(
        dossier,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    target_statement = str(
        active_target
        or getattr(dossier, "root_statement", "")
        or getattr(problem, "statement_type", "")
        or ""
    ).strip()
    try:
        contract_status = dict(
            contract_status_getter(
                route_id,
                target_statement=target_statement,
            )
            or {}
        )
    except Exception:
        return False
    if not bool(contract_status.get("ready")):
        return False
    try:
        from ensemble_prover.mini_session.actions.graph_route_assembly import (
            GraphRouteAssemblyAction,
        )

        has_replayable_bridge = GraphRouteAssemblyAction._route_has_replayable_bridge(
            contract_status
        )
    except Exception:
        has_replayable_bridge = bool(
            contract_status.get("deterministic_ready")
            or contract_status.get("assembly_bridge_node_ids")
            or contract_status.get("selected_branch_frame_ids")
        )
    if not has_replayable_bridge:
        return False
    signature_getter = getattr(graph, "route_dependency_signature_hash", None)
    if not callable(signature_getter):
        return False
    try:
        current_signature_hash = str(signature_getter(route_id) or "").strip()
    except Exception:
        return False
    if not current_signature_hash:
        return False
    if (
        str(metadata.get("route_root_assembly_author_failed_signature_hash") or "")
        == current_signature_hash
    ):
        return False
    return bool(
        str(metadata.get("route_root_tactic_authoring_ready_hash") or "").strip()
        and str(metadata.get("route_root_tactic_authoring_ready_signature_hash") or "")
        == current_signature_hash
    )


def _selected_assemble_route_contract_context(
    session: Any,
) -> Tuple[Dict[str, Any], List[str], List[str]]:
    merged = _selected_assemble_route_record(session)
    if not merged:
        return {}, [], []
    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    if graph is None:
        return {}, [], []
    route_id = str(
        merged.get("route_id")
        or merged.get("graph_node_id")
        or merged.get("node_id")
        or ""
    ).strip()
    if not route_id:
        return {}, [], []
    active_target = active_root_target_statement(
        dossier,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    target_statement = str(
        active_target
        or getattr(dossier, "root_statement", "")
        or getattr(getattr(session, "problem", None), "statement_type", "")
        or ""
    ).strip()
    status_getter = getattr(graph, "route_assembly_contract_status", None)
    if not callable(status_getter):
        return {}, [], []
    try:
        status = dict(
            status_getter(route_id, target_statement=target_statement) or {}
        )
    except Exception:
        return {}, [], []
    deps = [
        str(dep or "").strip()
        for dep in list(status.get("dependency_node_ids") or [])
        if str(dep or "").strip()
    ]
    try:
        from ensemble_prover.mini_session.actions.graph_route_assembly import (
            GraphRouteAssemblyAction,
        )

        helper_names = GraphRouteAssemblyAction._route_helper_names(
            graph,
            deps,
            dossier,
        )
        helper_blocks = GraphRouteAssemblyAction._route_helper_blocks(
            dossier,
            helper_names,
            allow_hidden_helper_names=helper_names,
        )
    except Exception:
        helper_names = []
        helper_blocks = []
    return status, helper_names, helper_blocks


def _selected_assemble_route_goal_statement(session: Any) -> str:
    if not _selected_assemble_route_record(session):
        return ""
    dossier = getattr(session, "dossier", None)
    active_target = active_root_target_statement(
        dossier,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    if active_target:
        return active_target
    conv = getattr(session, "conv", None)
    goal = str(getattr(conv, "goal_statement", "") or "").strip()
    if goal:
        return goal
    problem = getattr(session, "problem", None)
    return str(
        getattr(problem, "statement_type", "")
        or getattr(dossier, "root_statement", "")
        or ""
    ).strip()


def _framed_active_root_targets_for_turn(
    *,
    dossier: Any,
    conv: Any,
    helper_blocks: Optional[Sequence[str]] = None,
) -> Tuple[Dict[str, Any], ...]:
    if dossier is None or conv is None:
        return ()
    if helper_blocks is None:
        try:
            helper_blocks = dossier.verified_helper_blocks()
        except Exception:
            helper_blocks = []
    else:
        helper_blocks = list(helper_blocks)
    root_statement = str(
        getattr(conv, "goal_statement", "")
        or getattr(dossier, "root_statement", "")
        or ""
    )
    # Active-root targets are recorded/hashed against the LLM (classification)
    # preamble, which is ``conv.preamble`` — the same set the tool loop frames
    # with.  Preferring ``lean_preamble`` here diverges when answer-visible /
    # theory context makes the two differ, silently dropping the targets on the
    # main turn while tools still see the reduced goal.
    preamble = str(
        getattr(conv, "preamble", "")
        or getattr(conv, "lean_preamble", "")
        or ""
    )
    return tuple(
        active_root_targets_for_frame(
            dossier,
            root_statement=root_statement,
            preamble=preamble,
            helper_blocks=helper_blocks,
            require_helper_context_hash_match=True,
        )
    )


def _helper_signature_lines_from_blocks(
    blocks: Sequence[str],
    *,
    limit: int = 16,
) -> List[str]:
    helper_blocks = list(blocks or [])
    lines: List[str] = []
    for block in helper_blocks[: max(0, int(limit or 0))]:
        name = helper_decl_name(block) or "<anonymous>"
        statement = helper_decl_statement(block)
        rendered = str(name or "").strip()
        if statement:
            rendered = f"{rendered} : {' '.join(statement.split())}"
        lines.append(f"  - {_prompt_safe_inline_text(rendered, limit=700)}")
    omitted = len(helper_blocks) - len(lines)
    if omitted > 0:
        lines.append(f"  - ... {omitted} more verified helper(s)")
    return lines


def _selected_assemble_route_active_root_lines(session: Any) -> List[str]:
    if not _selected_assemble_route_record(session):
        return []
    dossier = getattr(session, "dossier", None)
    current_frame = getattr(dossier, "active_root_targets_for_current_frame", None)
    targets = list(current_frame() if callable(current_frame) else ())
    if len(targets) != 1:
        return []
    item = targets[0]
    target = " ".join(
        str(item.get("working_target") or item.get("target") or "").split()
    ).strip()
    hypotheses = [
        " ".join(str(hyp or "").split()).strip()
        for hyp in list(item.get("hypotheses") or ())
        if str(hyp or "").strip()
    ]
    if not target:
        return []
    if not hypotheses:
        return [
            "- active root target: "
            f"{_prompt_safe_inline_text(target, limit=900)}"
        ]
    lines = [
        (
            "- active root target has local hypotheses; author a complete "
            "root proof that introduces them before closing the target:"
        )
    ]
    for hyp in hypotheses[:8]:
        lines.append(f"  - hypothesis: {_prompt_safe_inline_text(hyp, limit=240)}")
    if len(hypotheses) > 8:
        lines.append(f"  - ... {len(hypotheses) - 8} more local hypotheses")
    lines.append(f"  - target: {_prompt_safe_inline_text(target, limit=900)}")
    return lines


def _verified_helper_signature_lines(session: Any, *, limit: int = 16) -> List[str]:
    dossier = getattr(session, "dossier", None)
    if dossier is None:
        return []
    helpers = list(getattr(dossier, "verified_helpers", {}) or {})
    if not helpers:
        return []
    verified = getattr(dossier, "verified_helpers", {}) or {}
    lines: List[str] = []
    for name in helpers[: max(0, int(limit or 0))]:
        helper = verified.get(name) if isinstance(verified, dict) else None
        source = str(getattr(helper, "source", "") or "").strip()
        lines.extend(_helper_signature_lines_from_blocks([source], limit=1))
    omitted = len(helpers) - len(lines)
    if omitted > 0:
        lines.append(f"  - ... {omitted} more verified helper(s)")
    return lines


def _selected_work_terminal_graph_target_suppressed(
    session: Any,
    record: Dict[str, Any],
    *,
    context: str,
    metric_key: str = "",
) -> bool:
    session_suppressor = getattr(
        session,
        "_selected_work_targets_terminal_graph_work",
        None,
    )
    if callable(session_suppressor):
        try:
            return bool(
                session_suppressor(
                    record,
                    context=context,
                    metric_key=metric_key,
                )
            )
        except Exception:
            pass
    status_getter = getattr(session, "selected_work_graph_liveness_status", None)
    if not callable(status_getter):
        return False
    try:
        status = dict(status_getter(record) or {})
    except Exception:
        return False
    if bool(status.get("live", True)):
        return False
    increment = getattr(session, "_increment_dossier_metric", None)
    if callable(increment):
        if metric_key:
            increment(metric_key, 1)
        increment("mini_session_retired_graph_target_restore_suppressed", 1)
    recorder = getattr(session, "_record_event", None)
    if callable(recorder):
        recorder({
            "phase": "session_selected_work_liveness",
            "iteration": int(getattr(session, "iteration", 0) or 0),
            "context": str(context or ""),
            "selected_work_item": dict(record or {}),
            "liveness_status": dict(status),
            "verdict": "terminal_graph_target_suppressed",
        })
    return True


def _selected_graph_native_proof_target(session: Any) -> Dict[str, str]:
    """Return the selected graph-native proof node target, if any.

    Conversation turns can be scheduled as a fallback for graph-native work.
    In that mode the LLM is proving a selected claim/variant/obligation, not
    the root theorem.  The scheduler record is the durable source of truth.
    """

    record = getattr(session, "selected_work_item_record", None)
    if not isinstance(record, dict):
        return {}
    work_type = str(record.get("work_type") or "").strip()
    if work_type not in _GRAPH_NATIVE_PROOF_WORK_TYPES:
        return {}
    if str(record.get("mapped_action_id") or "").strip() not in {
        "",
        "conversation_turn_prove",
        "conversation_turn_refine",
        "conversation_turn",
    }:
        return {}
    item_record = dict(getattr(getattr(session, "selected_work_item", None), "graph_record", None) or {})
    graph_record = dict(record.get("graph_record") or {})
    merged = {**graph_record, **item_record, **record}
    official_answer_visible = _effective_official_answer_visibility(session)

    def statement_allowed_for_execution(statement: str) -> bool:
        return bool(
            not _GENERATED_SOLUTION_REF_ALIAS_RE.search(statement)
            and (
                official_answer_visible
                or not is_answer_unsafe_statement_text(
                    statement,
                    suppress_solution_placeholders=True,
                )
            )
        )

    if _selected_work_terminal_graph_target_suppressed(
        session,
        merged,
        context="graph_native_proof_target",
    ):
        return {}
    dossier = getattr(session, "dossier", None)
    active_target_statements = []
    current_frame = getattr(
        dossier,
        "active_root_equivalence_statements_for_current_frame",
        None,
    )
    if callable(current_frame):
        try:
            active_target_statements = list(dict.fromkeys(current_frame()))
        except Exception:
            active_target_statements = []
    if not active_target_statements:
        graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
        active_target_statements = list(
            dict.fromkeys(
                str(item or "").strip()
                for item in list(
                    getattr(graph, "active_root_target_statements", []) or []
                )
                if str(item or "").strip()
            )
        )

    def root_equivalent(statement: str) -> bool:
        return bool(
            dossier is not None
            and graph_statement_root_equivalent(
                statement,
                str(getattr(dossier, "root_statement", "") or ""),
                active_target_statements=tuple(active_target_statements),
            )
        )

    def graph_node_is_quarantined(node: Any) -> bool:
        return graph_node_frontier_quarantined(node)

    def target_integrity_root_equivalent_allowed(
        record: Dict[str, Any],
        node: Any = None,
    ) -> bool:
        node_metadata = dict(getattr(node, "metadata", {}) or {}) if node else {}
        return bool(
            (
                record.get("target_integrity_adjudication")
                or node_metadata.get("target_integrity_adjudication")
            )
            and (
                record.get("allow_root_equivalent_target_integrity_adjudication")
                or node_metadata.get(
                    "allow_root_equivalent_target_integrity_adjudication"
                )
            )
        )

    def materialization_root_equivalent_allowed(node: Any = None) -> bool:
        node_metadata = dict(getattr(node, "metadata", {}) or {}) if node else {}
        return bool(
            work_type == "materialize_replay_source"
            and node_metadata.get("needs_replay_materialization")
        )

    field_order_by_work_type = {
        "formalize_claim": ("claim_id", "graph_node_id", "node_id"),
        "formalize_missing_obligation": ("obligation_id", "graph_node_id", "node_id"),
        "prove_claim_variant": ("variant_id", "graph_node_id", "node_id"),
        "mine_missing_obligation": ("obligation_id", "graph_node_id", "node_id"),
        "route_replan": ("obligation_id", "replan_id", "graph_node_id", "node_id"),
        "target_integrity_adjudication": (
            "obligation_id",
            "graph_node_id",
            "node_id",
        ),
        "materialize_replay_source": ("graph_node_id", "node_id"),
    }
    if bool(merged.get("formalization_required")) and work_type != "route_replan":
        graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
        nodes = getattr(graph, "nodes", {}) if graph is not None else {}
        node_id = str(
            merged.get("graph_node_id")
            or merged.get("node_id")
            or merged.get("claim_id")
            or merged.get("obligation_id")
            or ""
        ).strip()
        node = nodes.get(node_id) if isinstance(nodes, dict) and node_id else None
        statement = str(
            merged.get("target_statement") or getattr(node, "statement", "") or ""
        ).strip()
        if (
            not statement
            or not statement_allowed_for_execution(statement)
            or not graph_statement_is_executable(statement)
        ):
            return {}
        if root_equivalent(statement) and not target_integrity_root_equivalent_allowed(
            merged,
            node,
        ):
            return {}
        if isinstance(nodes, dict) and node_id:
            if node is not None and graph_node_is_quarantined(node):
                return {}
        return {
            "work_type": work_type,
            "node_id": node_id,
            "statement": statement,
            "name": str(merged.get("name") or "").strip(),
        }
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    if not isinstance(nodes, dict):
        return {}
    if work_type == "route_replan":
        obligation_id = str(merged.get("obligation_id") or "").strip()
        if not obligation_id:
            replan_id = str(
                merged.get("replan_id")
                or merged.get("graph_node_id")
                or merged.get("node_id")
                or ""
            ).strip()
            replan_node = nodes.get(replan_id) if replan_id else None
            replan_metadata = (
                dict(getattr(replan_node, "metadata", {}) or {})
                if replan_node is not None
                else {}
            )
            obligation_id = str(
                replan_metadata.get("obligation_id")
                or replan_metadata.get("resolved_by_obligation_id")
                or ""
            ).strip()
        obligation = nodes.get(obligation_id) if obligation_id else None
        if obligation is None:
            return {}
        if graph_node_is_quarantined(obligation):
            return {}
        obligation_metadata = dict(getattr(obligation, "metadata", {}) or {})
        if obligation_metadata.get("formalization_required"):
            return {}
        statement = str(getattr(obligation, "statement", "") or "").strip()
        if (
            not statement
            or not statement_allowed_for_execution(statement)
            or not graph_statement_is_executable(statement)
        ):
            return {}
        if (
            root_equivalent(statement)
            and not target_integrity_root_equivalent_allowed(merged, obligation)
            and not materialization_root_equivalent_allowed(obligation)
        ):
            return {}
        return {
            "work_type": work_type,
            "node_id": obligation.node_id,
            "statement": statement,
            "name": str(getattr(obligation, "name", "") or "").strip(),
        }
    for field in field_order_by_work_type.get(work_type, ()):
        node_id = str(merged.get(field) or "").strip()
        if not node_id:
            continue
        node = nodes.get(node_id)
        if node is None:
            continue
        if graph_node_is_quarantined(node):
            continue
        statement = str(getattr(node, "statement", "") or "").strip()
        if not statement:
            continue
        if not statement_allowed_for_execution(statement):
            continue
        if not graph_statement_is_executable(statement):
            continue
        if (
            root_equivalent(statement)
            and not target_integrity_root_equivalent_allowed(merged, node)
            and not materialization_root_equivalent_allowed(node)
        ):
            continue
        return {
            "work_type": work_type,
            "node_id": node_id,
            "statement": statement,
            "name": str(getattr(node, "name", "") or "").strip(),
        }
    return {}


def _lean_safe_generated_name(prefix: str, seed: str) -> str:
    """Return a deterministic theorem/lemma name for graph formalization."""

    base = re.sub(r"[^A-Za-z0-9_']", "_", str(prefix or "obligation"))
    base = re.sub(r"_+", "_", base).strip("_") or "obligation"
    if not re.match(r"^[A-Za-z_]", base):
        base = f"obligation_{base}"
    digest = hashlib.sha256(str(seed or base).encode("utf-8")).hexdigest()[:16]
    return f"{base}_{digest}"


def _lean_decl_name_is_usable(name: str) -> bool:
    text = str(name or "").strip()
    return bool(re.match(r"^[A-Za-z_][A-Za-z0-9_'.]*$", text))


def _required_formalization_decl_name(
    merged: Dict[str, Any],
    *,
    node_id: str = "",
    node: Any = None,
) -> str:
    for raw_name in (
        merged.get("required_declaration_name"),
        merged.get("formalization_required_declaration_name"),
        merged.get("name"),
        getattr(node, "name", "") if node is not None else "",
    ):
        candidate = str(raw_name or "").strip()
        if _lean_decl_name_is_usable(candidate):
            return candidate
    work_type = str(merged.get("work_type") or "").strip()
    if work_type == "formalize_claim":
        prefix = "claim"
    elif work_type == "mine_missing_obligation":
        prefix = "mined_obligation"
    else:
        prefix = "obligation"
    seed = "|".join(
        item
        for item in (
            str(node_id or ""),
            str(merged.get("identity_key") or ""),
            str(merged.get("formalization_obligation_key") or ""),
            str(merged.get("materialization_seed") or ""),
            str(merged.get("target_statement") or ""),
        )
        if item
    )
    return _lean_safe_generated_name(prefix, seed or node_id or work_type)


def _formalization_parent_statement(
    session: Any,
    merged: Dict[str, Any],
) -> str:
    """Recover the parent/root target that a formalization bridge must support."""

    for key in (
        "materialization_parent_statement",
        "formalization_bridge_parent_statement",
        "parent_repair_target_statement",
        "original_root_statement",
    ):
        value = str(merged.get(key) or "").strip()
        if value:
            return value
    conv = getattr(session, "conv", None)
    dossier = getattr(session, "dossier", None)
    active_root = (
        active_root_target_statement(
            dossier,
            require_single=True,
            require_no_hypotheses=False,
            include_hypotheses=True,
        )
        if dossier is not None
        else ""
    )
    return str(
        active_root
        or getattr(conv, "goal_statement", "")
        or getattr(dossier, "root_statement", "")
        or ""
    ).strip()


def _selected_formalization_helper_contract(
    session: Any,
    *,
    graph_native_goal_statement: str = "",
) -> Dict[str, Any]:
    """Return selected graph work that needs a declaration, not a proof body."""

    if str(graph_native_goal_statement or "").strip():
        return {}
    record = getattr(session, "selected_work_item_record", None)
    if not isinstance(record, dict):
        return {}
    selected_work_item = getattr(session, "selected_work_item", None)
    selected_item_graph_record = getattr(selected_work_item, "graph_record", None)
    item_record = dict(selected_item_graph_record or {})
    record_graph_record = record.get("graph_record")
    graph_record = dict(record_graph_record or {})
    merged = {**graph_record, **item_record, **record}
    if _selected_work_terminal_graph_target_suppressed(
        session,
        merged,
        context="formalization_helper_contract",
        metric_key="mini_session_retired_graph_target_formalization_suppressed",
    ):
        return {}
    work_type = str(merged.get("work_type") or "").strip()
    if work_type not in {
        "formalize_claim",
        "formalize_missing_obligation",
        "mine_missing_obligation",
    }:
        return {}
    if str(merged.get("mapped_action_id") or "").strip() not in {
        "",
        "conversation_turn_prove",
        "conversation_turn_refine",
        "conversation_turn",
    }:
        return {}
    node_id = str(
        merged.get("graph_node_id")
        or merged.get("node_id")
        or merged.get("claim_id")
        or merged.get("obligation_id")
        or ""
    ).strip()
    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    node = nodes.get(node_id) if isinstance(nodes, dict) and node_id else None
    node_metadata = dict(getattr(node, "metadata", {}) or {}) if node is not None else {}
    if node is not None and graph_node_frontier_quarantined(node):
        return {}
    selected_graph_work = {**node_metadata, **merged}

    def persist_selected_work_field(key: str, value: Any) -> None:
        selected_graph_work[key] = value
        try:
            record[key] = value
        except Exception:
            pass
        if isinstance(record_graph_record, dict):
            try:
                record_graph_record[key] = value
            except Exception:
                pass
        if isinstance(selected_item_graph_record, dict):
            try:
                selected_item_graph_record[key] = value
            except Exception:
                pass
        if node is not None:
            try:
                node.metadata[key] = value
            except Exception:
                pass

    formalization_required = bool(
        merged.get("formalization_required") or node_metadata.get("formalization_required")
    )
    if not formalization_required:
        return {}
    raw_target_statement = str(
        merged.get("target_statement") or getattr(node, "statement", "") or ""
    ).strip()
    if raw_target_statement and graph_statement_is_executable(raw_target_statement):
        return {}
    target_statement = ""
    if raw_target_statement:
        seed = str(selected_graph_work.get("materialization_seed") or "").strip()
        persist_selected_work_field("materialization_seed", seed or raw_target_statement)
        persist_selected_work_field(
            "nonexecutable_target_statement",
            raw_target_statement,
        )
        persist_selected_work_field("target_statement", "")
    parent_statement = _formalization_parent_statement(
        session,
        {**node_metadata, **merged},
    )
    required_name = _required_formalization_decl_name(
        {**node_metadata, **merged},
        node_id=node_id,
        node=node,
    )
    if parent_statement:
        for key in (
            "materialization_parent_statement",
            "formalization_bridge_parent_statement",
            "parent_repair_target_statement",
        ):
            persist_selected_work_field(key, parent_statement)
    for key in ("required_declaration_name", "formalization_required_declaration_name"):
        persist_selected_work_field(key, required_name)
    return {
        "work_type": work_type,
        "node_id": node_id,
        "target_statement": target_statement,
        "parent_statement": parent_statement,
        "node_kind": str(getattr(node, "kind", "") or ""),
        "name": required_name,
        "required_declaration_name": required_name,
        "selected_graph_work": selected_graph_work,
    }


def _recovered_formalization_helper_contracts(
    session: Any,
    helpers: Sequence[str],
    lemma_dag_candidates: Sequence[str],
    *,
    graph_native_goal_statement: str = "",
) -> List[Dict[str, Any]]:
    """Recover open graph formalization contracts from helper declarations.

    Cost-governed static continuation intentionally clears selected graph work
    before dispatching a proof-only conversation lane.  If that conversation
    still emits a complete declaration whose Lean name identifies an open graph
    formalization obligation, route it through the same verifier as selected
    work instead of dropping it as helper-decomposition-disabled.
    """

    if str(graph_native_goal_statement or "").strip():
        return []
    candidates = _formalization_helper_candidates(helpers, lemma_dag_candidates)
    if not candidates:
        return []
    candidate_names = [
        name
        for name in (helper_decl_name(candidate) for candidate in candidates)
        if name
    ]
    if not candidate_names:
        return []
    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    if graph is None or not isinstance(nodes, dict):
        return []
    tombstone = getattr(graph, "is_superseded_tombstone", None)
    route_poisoned = getattr(graph, "_route_is_terminally_poisoned", None)
    allowed_work_types = {
        "formalize_claim",
        "formalize_missing_obligation",
        "mine_missing_obligation",
    }
    contracts: List[Dict[str, Any]] = []
    seen_node_ids: set[str] = set()
    for helper_name in candidate_names:
        for node in nodes.values():
            node_id = str(getattr(node, "node_id", "") or "").strip()
            if not node_id or node_id in seen_node_ids:
                continue
            node_metadata = dict(getattr(node, "metadata", {}) or {})
            node_name = str(getattr(node, "name", "") or "").strip()
            required_name = _required_formalization_decl_name(
                {**node_metadata, "name": node_name},
                node_id=node_id,
                node=node,
            )
            recoverable_names = {
                str(name or "").strip()
                for name in (
                    node_name,
                    required_name,
                    node_metadata.get("required_declaration_name"),
                    node_metadata.get("formalization_required_declaration_name"),
                )
                if str(name or "").strip()
            }
            if helper_name not in recoverable_names:
                continue
            if not bool(node_metadata.get("formalization_required")):
                continue
            node_status = str(getattr(node, "status", "") or "").strip()
            if node_status in {"failed", "rejected", "obsolete", "superseded"}:
                continue
            if graph_node_frontier_quarantined(node):
                continue
            if callable(tombstone) and bool(tombstone(node)):
                continue
            if bool(
                node_metadata.get("route_retired")
                or node_metadata.get("route_dependency_contradicted")
                or node_metadata.get("proposal_invalidated")
            ):
                continue
            route_id = str(node_metadata.get("route_id") or "").strip()
            if route_id:
                route_node = nodes.get(route_id)
                route_metadata = dict(
                    getattr(route_node, "metadata", {}) or {}
                ) if route_node is not None else {}
                route_status = str(getattr(route_node, "status", "") or "").strip()
                if (
                    route_node is None
                    or route_status in {"failed", "obsolete", "superseded"}
                    or bool(
                        route_metadata.get("route_retired")
                        or route_metadata.get("route_dependency_contradicted")
                        or route_metadata.get("proposal_invalidated")
                    )
                    or (callable(tombstone) and bool(tombstone(route_node)))
                    or (
                        callable(route_poisoned)
                        and bool(route_poisoned(route_id))
                    )
                ):
                    continue
            source_id = str(node_metadata.get("source_node_id") or "").strip()
            if source_id:
                source_node = nodes.get(source_id)
                source_metadata = dict(
                    getattr(source_node, "metadata", {}) or {}
                ) if source_node is not None else {}
                source_status = str(
                    getattr(source_node, "status", "") or ""
                ).strip()
                if (
                    source_node is None
                    or source_status in {"failed", "obsolete", "superseded"}
                    or bool(
                        source_metadata.get("route_retired")
                        or source_metadata.get("route_dependency_contradicted")
                        or source_metadata.get("proposal_invalidated")
                    )
                    or (callable(tombstone) and bool(tombstone(source_node)))
                ):
                    continue
            work_type = str(
                node_metadata.get("work_type")
                or node_metadata.get("source_work_type")
                or ""
            ).strip()
            if not work_type:
                if str(getattr(node, "kind", "") or "") == "missing_obligation":
                    work_type = "formalize_missing_obligation"
                else:
                    work_type = "formalize_claim"
            if work_type not in allowed_work_types:
                work_type = "formalize_missing_obligation"
            target_statement = str(getattr(node, "statement", "") or "").strip()
            if target_statement and graph_statement_is_executable(target_statement):
                continue
            parent_statement = _formalization_parent_statement(
                session,
                node_metadata,
            )
            selected_graph_work = {
                **node_metadata,
                "work_type": work_type,
                "node_id": node_id,
                "graph_node_id": node_id,
                "formalization_required": True,
                "node_kind": str(getattr(node, "kind", "") or ""),
                "node_status": node_status,
                "name": required_name,
                "required_declaration_name": required_name,
                "formalization_required_declaration_name": required_name,
                "target_statement": target_statement,
                "recovered_from_helper_name": helper_name,
                "recovered_formalization_contract": True,
            }
            if parent_statement:
                selected_graph_work["materialization_parent_statement"] = parent_statement
                selected_graph_work["formalization_bridge_parent_statement"] = parent_statement
                selected_graph_work["parent_repair_target_statement"] = parent_statement
            if str(getattr(node, "kind", "") or "") == "missing_obligation":
                selected_graph_work.setdefault("obligation_id", node_id)
            contract = {
                "work_type": work_type,
                "node_id": node_id,
                "target_statement": target_statement,
                "parent_statement": parent_statement,
                "node_kind": str(getattr(node, "kind", "") or ""),
                "name": required_name,
                "required_declaration_name": required_name,
                "selected_graph_work": selected_graph_work,
                "recovered_from_helper_name": helper_name,
                "recovered_formalization_contract": True,
            }
            for key in (
                "formalization_bridge_contract",
                "formalization_bridge_parent_statement",
                "parent_repair_target_statement",
                "auxiliary_bridge_parent_assembly_required",
                "auxiliary_bridge_allow_non_root_parent_assembly",
            ):
                if key in node_metadata:
                    contract[key] = node_metadata[key]
            contracts.append(contract)
            seen_node_ids.add(node_id)
    return contracts


def _formalization_helper_candidates(
    helpers: Sequence[str],
    lemma_dag_candidates: Sequence[str],
    *,
    require_executable_statement: bool = True,
) -> List[str]:
    out: List[str] = []
    seen: set[str] = set()
    try:
        from ensemble_prover.proof_state_cache import (
            _proof_state_helper_policy_rejection,
        )
    except Exception:
        _proof_state_helper_policy_rejection = None
    for helper in [*list(helpers or ()), *list(lemma_dag_candidates or ())]:
        text = str(helper or "").strip()
        if not text or text in seen:
            continue
        seen.add(text)
        if callable(_proof_state_helper_policy_rejection):
            try:
                if _proof_state_helper_policy_rejection(text):
                    continue
            except Exception:
                pass
        if helper_decl_kind(text) not in {"theorem", "lemma"}:
            continue
        if not helper_decl_name(text):
            continue
        statement = helper_decl_statement(text)
        if not statement:
            continue
        if require_executable_statement and not graph_statement_is_executable(statement):
            continue
        body = helper_decl_body(text)
        if not body or has_sorry_or_admit(body):
            continue
        out.append(text)
    return out


def _formalization_prefix_blocks_from_chunks(
    source_prefix_blocks: Sequence[str],
) -> List[str]:
    prefix_blocks: List[str] = []
    for block in source_prefix_blocks:
        text = str(block or "").strip()
        if not text:
            continue
        kind = helper_decl_kind(text)
        if kind not in {
            "theorem",
            "lemma",
            "def",
            "abbrev",
            "instance",
        }:
            continue
        if kind != "instance" and not helper_decl_name(text):
            continue
        if not helper_decl_body(text) or has_sorry_or_admit(helper_decl_body(text)):
            continue
        prefix_blocks.append(text)
    return prefix_blocks


def _same_target_decl_graph_formalization_candidate(
    extraction: Any,
    *,
    theorem_name: str = "",
    goal_statement: str = "",
) -> tuple[str, List[str]]:
    """Return a complete declaration candidate and replay prefixes.

    Proof telemetry is stricter: it only records same-target declaration
    metadata when the declaration body became the extracted proof body. Graph
    formalization still needs the complete theorem/lemma declaration even when
    the legacy extractor chose an earlier same-statement lemma body as the
    active proof, so this selector works from preserved chunks directly.
    """

    expected_name = str(theorem_name or "").strip()
    expected_statement_key = graph_statement_key(goal_statement)
    selected_index = -1
    candidates: List[tuple[tuple[int, int, int], int, str]] = []
    for index, chunk in enumerate(list(getattr(extraction, "chunks", []) or [])):
        candidate = str(chunk or "").strip()
        if helper_decl_kind(candidate) not in {"theorem", "lemma"}:
            continue
        name = helper_decl_name(candidate)
        if not name:
            continue
        statement = helper_decl_statement(candidate)
        if not statement:
            continue
        body = helper_decl_body(candidate)
        if not body or has_sorry_or_admit(body):
            continue
        name_match = bool(expected_name and name == expected_name)
        statement_match = bool(
            expected_statement_key
            and graph_statement_key(statement) == expected_statement_key
        )
        if expected_name and not name_match and not statement_match:
            continue
        if not expected_name and expected_statement_key and not statement_match:
            continue
        if not expected_name and not expected_statement_key:
            if not bool(getattr(extraction, "same_target_decl_proof_normalized", False)):
                continue
        candidates.append((
            (
                0 if name_match else 1,
                0 if statement_match else 1,
                index,
            ),
            index,
            candidate,
        ))
    if candidates:
        _score, selected_index, candidate = min(candidates, key=lambda item: item[0])
    elif bool(getattr(extraction, "same_target_decl_proof_normalized", False)):
        candidate = str(
            getattr(extraction, "same_target_decl_proof_block", "") or ""
        ).strip()
        selected_index = int(
            getattr(extraction, "same_target_decl_proof_chunk_index", -1)
        )
    else:
        return "", []
    if not candidate:
        return "", []
    if helper_decl_kind(candidate) not in {"theorem", "lemma"}:
        return "", []
    if not helper_decl_name(candidate):
        return "", []
    statement = helper_decl_statement(candidate)
    if not statement:
        return "", []
    body = helper_decl_body(candidate)
    if not body or has_sorry_or_admit(body):
        return "", []
    source_prefix_blocks: Sequence[str]
    if selected_index >= 0:
        source_prefix_blocks = list(getattr(extraction, "chunks", []) or [])[
            :selected_index
        ]
    else:
        source_prefix_blocks = list(
            getattr(extraction, "same_target_decl_proof_prefix_declarations", [])
            or []
        )
    prefix_blocks = _formalization_prefix_blocks_from_chunks(source_prefix_blocks)
    return candidate, prefix_blocks


def _proof_turn_decl_graph_formalization_candidate(
    extraction: Any,
    *,
    contract: Dict[str, Any],
    proof_text: str = "",
) -> tuple[str, List[str]]:
    """Recover complete declarations from proof-turn formalization replies.

    Declaration-required graph tasks often get a useful theorem/lemma plus a
    trailing ``example`` proof body.  The legacy proof lane extracts the proof
    body, but the graph formalization lane must preserve the declaration.
    """

    candidates: List[tuple[tuple[int, int, int, int], int, str]] = []
    chunks = list(getattr(extraction, "chunks", []) or [])
    proof_scan_text = str(proof_text or "")
    for index, chunk in enumerate(chunks):
        candidate = str(chunk or "").strip()
        if helper_decl_kind(candidate) not in {"theorem", "lemma"}:
            continue
        name = helper_decl_name(candidate)
        if not name:
            continue
        statement = helper_decl_statement(candidate)
        if not statement or not graph_statement_is_executable(statement):
            continue
        body = helper_decl_body(candidate)
        if not body or has_sorry_or_admit(body):
            continue
        bridge_status = _formalization_bridge_status(
            contract,
            statement,
            helper_name=name,
        )
        referenced_by_proof = _lean_identifier_referenced(proof_scan_text, name)
        referenced_later = any(
            _lean_identifier_referenced(str(later or ""), name)
            for later in chunks[index + 1 :]
        )
        candidates.append((
            (
                0 if referenced_by_proof else (1 if referenced_later else 2),
                0 if bool(bridge_status.get("accepted")) else 1,
                0 if bool(bridge_status.get("closes_target", True)) else 1,
                index,
            ),
            index,
            candidate,
        ))
    if not candidates:
        return "", []
    _score, selected_index, selected = min(candidates, key=lambda item: item[0])
    prefix_blocks = _formalization_prefix_blocks_from_chunks(chunks[:selected_index])
    return selected, prefix_blocks


def _lean_identifier_referenced(text: str, name: str) -> bool:
    clean_name = str(name or "").strip()
    if not clean_name:
        return False
    scan_text = _lean_dependency_scan_text(text)
    start = 0
    while True:
        index = scan_text.find(clean_name, start)
        if index < 0:
            return False
        end = index + len(clean_name)
        before = scan_text[index - 1] if index > 0 else ""
        after = scan_text[end] if end < len(scan_text) else ""
        if not _is_lean_identifier_continue_char(
            before
        ) and not _is_lean_identifier_continue_char(after):
            return True
        start = index + 1


def _lean_dependency_scan_text(text: str) -> str:
    """Strip comments and literal payloads before identifier scans."""

    return strip_lean_comments_and_string_literals(str(text or ""))


def _same_turn_helper_dependency_blocks(
    candidate: str,
    prefix_blocks: Sequence[str],
) -> List[str]:
    """Return same-response helpers referenced by ``candidate``, with closure."""

    dependency_blocks, _ = _same_turn_helper_dependency_analysis(
        candidate,
        prefix_blocks,
    )
    return dependency_blocks


def _same_turn_replay_dependency_blocks(
    candidate: str,
    prefix_blocks: Sequence[str],
) -> List[str]:
    """Return every referenced valid predecessor needed for Lean replay.

    Unlike helper banking, exact-declaration replay must retain referenced
    ``def``/``abbrev``/``instance`` prefixes as well as theorem/lemma facts.
    The underlying dependency analysis computes the transitive closure; this
    projection restores both classes in their original declaration order.
    """

    bankable_blocks, replay_only_names = _same_turn_helper_dependency_analysis(
        candidate,
        prefix_blocks,
    )
    required_names = {
        helper_decl_name(block)
        for block in bankable_blocks
        if helper_decl_name(block)
    }
    required_names.update(str(name or "") for name in replay_only_names if name)
    return [
        block
        for block in prefix_blocks
        if (helper_decl_name(block) or "") in required_names
    ]


def _same_turn_helper_dependency_analysis(
    candidate: str,
    prefix_blocks: Sequence[str],
) -> tuple[List[str], List[str]]:
    """Return bankable dependency blocks and replay-only prefix references."""

    blocks_by_name: Dict[str, str] = {}
    bankable_names: set[str] = set()
    replay_only_names: set[str] = set()
    for block in prefix_blocks:
        name = helper_decl_name(block)
        if not name:
            continue
        kind = helper_decl_kind(block)
        if kind in {"theorem", "lemma"}:
            bankable_names.add(name)
        elif kind in {"def", "abbrev", "instance"}:
            replay_only_names.add(name)
        else:
            continue
        blocks_by_name[name] = block
    needed: set[str] = set()
    queue: List[str] = [
        name
        for name in blocks_by_name
        if _lean_identifier_referenced(candidate, name)
    ]
    while queue:
        name = queue.pop(0)
        if name in needed:
            continue
        needed.add(name)
        block = blocks_by_name.get(name, "")
        for dep_name in blocks_by_name:
            if dep_name not in needed and _lean_identifier_referenced(block, dep_name):
                queue.append(dep_name)
    replay_only_dependencies = [
        name for name in replay_only_names if name in needed
    ]
    dependency_blocks = [
        block
        for block in prefix_blocks
        if (helper_decl_name(block) or "") in needed
        and (helper_decl_name(block) or "") in bankable_names
    ]
    return dependency_blocks, replay_only_dependencies


def _replay_only_prefix_names(prefix_blocks: Sequence[str]) -> List[str]:
    names: List[str] = []
    for block in prefix_blocks:
        if helper_decl_kind(block) not in {"def", "abbrev", "instance"}:
            continue
        label = _replay_only_prefix_label(block)
        if label and label not in names:
            names.append(label)
    return names


def _replay_only_prefix_label(block: str) -> str:
    name = helper_decl_name(block)
    if name:
        return name
    if helper_decl_kind(block) == "instance":
        digest = hashlib.sha256(
            str(block or "").encode("utf-8", errors="replace")
        ).hexdigest()[:12]
        return f"anonymous_instance:{digest}"
    return ""


async def _check_graph_native_formalization_replay(
    *,
    lean: Any,
    conv: Any,
    replay_helpers: Sequence[str],
) -> Any:
    try:
        return await lean.check(
            "True",
            "by\n  trivial",
            list(replay_helpers),
            preamble_override=str(getattr(conv, "preamble", "") or ""),
            check_kind="graph_native_formalization_helper",
        )
    except TypeError:
        return await lean.check(
            "True",
            "by\n  trivial",
            list(replay_helpers),
            preamble_override=str(getattr(conv, "preamble", "") or ""),
        )


def _formalization_parent_target_statement(contract: Dict[str, Any]) -> str:
    """Return the exact parent proposition used for Lean closure replay."""

    selected = dict(contract.get("selected_graph_work") or {})
    return str(
        contract.get("parent_statement")
        or selected.get("materialization_parent_statement")
        or selected.get("formalization_bridge_parent_statement")
        or selected.get("parent_repair_target_statement")
        or contract.get("formalization_bridge_parent_statement")
        or ""
    ).strip()


def _formalization_parent_target_binding(
    *,
    contract: Dict[str, Any],
    selected_node: Any,
    graph: Any,
    checked_parent_statement: str,
    dossier: Any,
) -> Tuple[str, Any, bool, str]:
    """Resolve and validate the graph node covered by a Lean parent replay.

    Statement replay and graph mutation used to resolve their targets through
    independent fallback chains.  A stale parent-obligation id could therefore
    promote and retire a proposition that Lean had never checked.  Keep the
    mutation fail-closed unless the selected record, live node, statement
    identity, and (when stamped) Lean environment all agree.
    """

    selected = dict(contract.get("selected_graph_work") or {})
    node_metadata = dict(getattr(selected_node, "metadata", {}) or {})
    record_parent_id = str(
        selected.get("formalization_bridge_parent_obligation_id")
        or contract.get("formalization_bridge_parent_obligation_id")
        or ""
    ).strip()
    live_parent_id = str(
        node_metadata.get("formalization_bridge_parent_obligation_id") or ""
    ).strip()
    if record_parent_id and live_parent_id and record_parent_id != live_parent_id:
        return "", None, False, "parent_obligation_id_changed"
    parent_obligation_id = str(
        record_parent_id
        or live_parent_id
        or getattr(selected_node, "node_id", "")
        or ""
    ).strip()
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    parent_obligation = (
        nodes.get(parent_obligation_id)
        if isinstance(nodes, dict) and parent_obligation_id
        else None
    )
    if parent_obligation is None:
        return parent_obligation_id, None, False, "parent_obligation_missing"

    checked_key = graph_statement_key(checked_parent_statement)
    parent_metadata = dict(getattr(parent_obligation, "metadata", {}) or {})
    live_parent_statement = str(
        getattr(parent_obligation, "statement", "") or ""
    ).strip()
    live_statement_is_authoritative = bool(
        live_parent_statement
        and (
            graph_statement_is_executable(live_parent_statement)
            or re.fullmatch(
                r"(?:_root_\.)?[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*",
                live_parent_statement,
            )
        )
    )
    if live_statement_is_authoritative:
        if (
            not checked_key
            or graph_statement_key(live_parent_statement) != checked_key
        ):
            return (
                parent_obligation_id,
                parent_obligation,
                False,
                "parent_statement_identity_mismatch",
            )
        bound_statements = [live_parent_statement]
    elif (
        str(getattr(parent_obligation, "kind", "") or "")
        == "missing_obligation"
        and bool(parent_metadata.get("formalization_required"))
    ):
        # A deliberately non-executable placeholder can only be bound through
        # aliases stored on the live node itself.  Contract/checkpoint aliases
        # are not proof authority and cannot override an executable live goal.
        bound_statements = [
            str(
                parent_metadata.get("materialization_parent_statement") or ""
            ).strip(),
            str(
                parent_metadata.get("formalization_bridge_parent_statement")
                or ""
            ).strip(),
            str(
                parent_metadata.get("parent_repair_target_statement") or ""
            ).strip(),
        ]
    else:
        bound_statements = []
    bound_keys = {
        graph_statement_key(statement)
        for statement in bound_statements
        if statement and graph_statement_key(statement)
    }
    if not checked_key or not bound_keys or bound_keys != {checked_key}:
        return (
            parent_obligation_id,
            parent_obligation,
            False,
            "parent_statement_identity_mismatch",
        )

    target_environment = str(
        parent_metadata.get("statement_environment_hash") or ""
    ).strip()
    checked_environment = str(
        getattr(dossier, "current_lean_environment_hash", "") or ""
    ).strip()
    compatible = getattr(dossier, "lean_environment_is_compatible", None)
    if bool(target_environment) != bool(checked_environment):
        return (
            parent_obligation_id,
            parent_obligation,
            False,
            "parent_statement_environment_unbound",
        )
    if target_environment and (
        not callable(compatible)
        or not bool(
            compatible(
                target_environment,
                checked_environment,
            )
        )
    ):
        return (
            parent_obligation_id,
            parent_obligation,
            False,
            "parent_statement_environment_mismatch",
        )
    return parent_obligation_id, parent_obligation, True, ""


async def _checked_formalization_closes_parent_target(
    *,
    lean: Any,
    conv: Any,
    candidate: str,
    replay_helpers: Sequence[str],
    contract: Dict[str, Any],
) -> bool:
    """Ask Lean whether a checked declaration proves the selected parent.

    A strict-decomposition response can contain the complete parent theorem,
    not merely an auxiliary bridge.  Surface statement keys intentionally do
    not erase inferred-vs-explicit binder types, so only a fresh Lean replay is
    allowed to promote that declaration from route support to parent closure.
    """

    helper_name = str(helper_decl_name(candidate) or "").strip()
    parent_statement = _formalization_parent_target_statement(contract)
    if not helper_name or not parent_statement:
        return False
    kwargs = {
        "preamble_override": str(getattr(conv, "preamble", "") or ""),
        "check_kind": "graph_native_formalization_parent_closure",
    }
    try:
        result = await lean.check(
            parent_statement,
            f"by\n  exact {helper_name}",
            list(replay_helpers),
            **kwargs,
        )
    except TypeError:
        kwargs.pop("check_kind", None)
        try:
            result = await lean.check(
                parent_statement,
                f"by\n  exact {helper_name}",
                list(replay_helpers),
                **kwargs,
            )
        except Exception:
            return False
    except Exception:
        return False
    return bool(getattr(result, "ok", False))


def _formalization_helper_feedback(
    reason: str = "",
    *,
    contract: Optional[Dict[str, Any]] = None,
    bridge_status: Optional[Dict[str, Any]] = None,
    rejected_statement: str = "",
) -> str:
    detail = str(reason or "").strip()
    suffix = f"\n\nLast failure: {detail}" if detail else ""
    extra_lines: List[str] = []
    parent_statement = ""
    if isinstance(bridge_status, dict):
        parent_statement = str(bridge_status.get("parent_statement") or "").strip()
    if not parent_statement and isinstance(contract, dict):
        selected = dict(contract.get("selected_graph_work") or {})
        parent_statement = str(
            selected.get("materialization_parent_statement")
            or selected.get("formalization_bridge_parent_statement")
            or selected.get("parent_repair_target_statement")
            or contract.get("formalization_bridge_parent_statement")
            or ""
        ).strip()
    safe_parent = _prompt_safe_inline_text(parent_statement, limit=700)
    if safe_parent:
        extra_lines.append(f"Parent target this declaration must support: `{safe_parent}`")
    safe_rejected = _prompt_safe_inline_text(
        str(rejected_statement or ""),
        limit=500,
    )
    if safe_rejected:
        extra_lines.append(f"Rejected declaration statement: `{safe_rejected}`")
    forbidden_fragments: List[str] = []
    if isinstance(contract, dict):
        selected = dict(contract.get("selected_graph_work") or {})
        for item in list(
            selected.get("forbidden_materialization_fragments")
            or contract.get("forbidden_materialization_fragments")
            or ()
        ):
            text = _prompt_safe_inline_text(str(item or ""), limit=160)
            if text and text not in forbidden_fragments:
                forbidden_fragments.append(text)
    if forbidden_fragments:
        extra_lines.append(
            "Stale rejected fragment(s), not standalone targets: "
            + ", ".join(f"`{item}`" for item in forbidden_fragments[:5])
        )
    if isinstance(bridge_status, dict):
        parent_features = [
            _prompt_safe_inline_text(str(item or ""), limit=80)
            for item in list(bridge_status.get("parent_features") or ())[:8]
            if str(item or "").strip()
        ]
        statement_features = [
            _prompt_safe_inline_text(str(item or ""), limit=80)
            for item in list(bridge_status.get("statement_features") or ())[:8]
            if str(item or "").strip()
        ]
        if parent_features:
            extra_lines.append(
                "Parent-specific symbols/features to connect to: "
                + ", ".join(f"`{item}`" for item in parent_features)
            )
        if statement_features:
            extra_lines.append(
                "Rejected statement only exposed: "
                + ", ".join(f"`{item}`" for item in statement_features)
            )
    extra = "\n" + "\n".join(extra_lines) if extra_lines else ""
    return (
        "This graph task does not yet have an executable Lean target, so a "
        "bare `by ...` proof cannot be checked against it. Submit complete "
        "Lean theorem or lemma declaration(s) whose final statement is the "
        "formalized obligation and whose body proves it. Do not submit only "
        "the proposition, a root proof, or a `sorry`/`admit` stub. Each "
        "declaration must be parent-anchored route support, not a generic "
        "library fact or standalone repair of a stale rejected identifier. If "
        "your last declaration was only an auxiliary helper, keep it as a "
        "prefix dependency and add a final theorem/lemma whose statement "
        "connects that helper to the selected graph obligation."
        f"{extra}"
        f"{suffix}"
    )


_FORMALIZATION_REJECTED_HELPER_BANK_SKIP_REASONS = frozenset(
    {
        "tautology_not_formalization_bridge",
        "bridge_restates_retired_target",
        "bridge_root_equivalent_to_retired_target",
        "bridge_restates_parent_target",
        "bridge_root_equivalent_to_parent_target",
        "bridge_negates_retired_target",
        "bridge_refutes_negative_retired_target",
        "bridge_negates_parent_target",
        "bridge_refutes_negative_parent_target",
        "formalization_statement_mismatches_executable_target",
    }
)


def _annotate_banked_rejected_formalization_helpers(
    *,
    dossier: Any,
    helper_names: Sequence[str],
    contract: Dict[str, Any],
    bridge_status: Dict[str, Any],
    phase: str,
    turn_index: int,
) -> None:
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", None) if graph is not None else None
    if not isinstance(nodes, dict):
        return
    wanted = {str(name or "").strip() for name in helper_names if str(name or "").strip()}
    if not wanted:
        return
    selected = dict(contract.get("selected_graph_work") or {})
    bridge_reason = str(bridge_status.get("reason") or "").strip()
    parent_statement = str(
        bridge_status.get("parent_statement")
        or selected.get("formalization_bridge_parent_statement")
        or selected.get("parent_repair_target_statement")
        or contract.get("formalization_bridge_parent_statement")
        or ""
    ).strip()
    for node in list(nodes.values()):
        metadata = getattr(node, "metadata", None)
        if not isinstance(metadata, dict):
            continue
        helper_name = str(metadata.get("proposed_helper_name") or "").strip()
        if helper_name not in wanted:
            continue
        metadata["formalization_rejected_bridge_candidate"] = True
        metadata["formalization_rejected_bridge_reason"] = bridge_reason
        metadata["formalization_rejected_bridge_phase"] = str(phase or "")
        metadata["formalization_rejected_bridge_turn_index"] = int(turn_index or 0)
        if parent_statement:
            metadata["formalization_rejected_bridge_parent_statement"] = parent_statement
        node_id = str(contract.get("node_id") or selected.get("node_id") or "").strip()
        if node_id:
            metadata["formalization_rejected_bridge_selected_node_id"] = node_id
        route_id = str(selected.get("route_id") or contract.get("route_id") or "").strip()
        if route_id:
            metadata["formalization_rejected_bridge_route_id"] = route_id


def _bank_rejected_formalization_helper_candidate(
    *,
    session: Any,
    conv: Any,
    dossier: Any,
    candidate: str,
    same_turn_prefix_blocks: Sequence[str],
    contract: Dict[str, Any],
    bridge_status: Dict[str, Any],
    phase_turn: int,
) -> List[str]:
    reason = str(bridge_status.get("reason") or "").strip()
    formal_statement = helper_decl_statement(candidate)
    if (
        reason in _FORMALIZATION_REJECTED_HELPER_BANK_SKIP_REASONS
        or _formalization_statement_is_trivial_tautology(formal_statement)
    ):
        return []
    dependency_blocks, _dependency_names = _same_turn_helper_dependency_analysis(
        candidate,
        same_turn_prefix_blocks,
    )
    sources = [
        *list(dependency_blocks or ()),
        str(candidate or "").strip(),
    ]
    phase = f"{getattr(conv, 'role', 'prove')}_graph_native_formalization_rejected"
    banked = _bank_turn_sources_as_proposed(
        dossier,
        conv,
        sources,
        phase=phase,
        turn_index=phase_turn,
    )
    if banked:
        _annotate_banked_rejected_formalization_helpers(
            dossier=dossier,
            helper_names=banked,
            contract=contract,
            bridge_status=bridge_status,
            phase=phase,
            turn_index=phase_turn,
        )
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment(
                "mini_session_graph_formalization_rejected_helpers_banked_proposed",
                len(banked),
            )
    return banked


def _no_proof_target_integrity_metadata(
    *,
    session: Any,
    conv: Any,
    dossier: Any,
    llm_output: str,
    selected_work_record: Dict[str, Any],
    target_statement: str,
    role: str,
    turn: int,
    common_payload: Dict[str, Any],
) -> Dict[str, Any]:
    selected_work = dict(selected_work_record or {})
    selected_work_type = str(selected_work.get("work_type") or "").strip()
    explicit_target = str(
        target_statement or selected_work.get("target_statement") or ""
    ).strip()
    suppress_root_target_fallback = bool(
        selected_work_type in _GRAPH_NATIVE_PROOF_WORK_TYPES
        or selected_work.get("formalization_required")
        or selected_work.get("materialization_required")
        or selected_work.get("formalization_statement_pending")
    )
    target = explicit_target or (
        ""
        if suppress_root_target_fallback
        else str(
            getattr(conv, "goal_statement", "")
            or getattr(dossier, "root_statement", "")
            or ""
        ).strip()
    )
    if suppress_root_target_fallback and not target:
        return {}
    signals = classify_target_integrity_signals(
        llm_output=str(llm_output or ""),
        proof="",
        failure_analysis={},
        target_statement=target,
        selected_work_type=selected_work_type,
    )
    if not signals:
        return {}
    increment = getattr(session, "_increment_dossier_metric", None)
    if callable(increment):
        increment("mini_session_target_integrity_signals", len(signals))
        increment("mini_session_target_integrity_no_proof_signals", len(signals))
    for signal in signals:
        metric = str(signal.get("metric") or "").strip()
        if metric and callable(increment):
            increment(metric, 1)
        _emit_record(session, {
            **common_payload,
            "phase": "target_integrity_signal",
            "turn_in_phase": turn,
            "role": role,
            "kind": str(signal.get("kind") or ""),
            "target_integrity_signal_kind": str(signal.get("kind") or ""),
            "target_integrity_signal_kinds": [
                str(item.get("kind") or "") for item in signals
            ],
            "target_integrity_signals": list(signals),
            "match": str(signal.get("match") or ""),
            "selected_work_type": selected_work_type,
            "target_statement": target,
            "source": "no_proof_extracted",
            "verdict": "detected",
        })
    try:
        from ensemble_prover.mini_session.turn.post_failure import (
            _record_target_integrity_adjudication,
        )

        obligation_ids, replan_ids, materialized = _record_target_integrity_adjudication(
            dossier=dossier,
            target_statement=target,
            signals=signals,
            phase=role,
            turn_index=turn,
            selected_work_type=selected_work_type,
            selected_work_record=selected_work,
        )
    except Exception:
        obligation_ids, replan_ids, materialized = [], [], False
    if obligation_ids or replan_ids:
        _emit_record(session, {
            **common_payload,
            "phase": "target_integrity_adjudication",
            "turn_in_phase": turn,
            "role": role,
            "selected_work_type": selected_work_type,
            "target_statement": target,
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
            "obligation_node_ids": list(obligation_ids),
            "replan_node_ids": list(replan_ids),
            "signal_kinds": [str(signal.get("kind") or "") for signal in signals],
            "source": "no_proof_extracted",
            "verdict": "materialized" if materialized else "already_materialized",
        })
        if materialized and callable(increment):
            increment(
                "mini_session_target_integrity_no_proof_adjudication_materialized",
                1,
            )
    feedback = target_integrity_feedback(list(signals))
    if feedback:
        conv.append_user(feedback)
    return {
        "target_integrity_signals": list(signals),
        "target_integrity_bypass_local_repair": True,
        "target_integrity_disable_proof_state_repair": True,
        "target_integrity_obligation_node_ids": list(obligation_ids),
        "target_integrity_replan_node_ids": list(replan_ids),
        "target_integrity_adjudication_materialized": bool(materialized),
        "target_integrity_adjudication_available": bool(obligation_ids or replan_ids),
        "target_integrity_adjudication_created": bool(materialized),
    }


def _strip_balanced_outer_parens(text: str) -> str:
    stripped = str(text or "").strip()
    while stripped.startswith("(") and stripped.endswith(")"):
        depth = 0
        balanced_outer = True
        for index, char in enumerate(stripped):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(stripped) - 1:
                    balanced_outer = False
                    break
            if depth < 0:
                balanced_outer = False
                break
        if not balanced_outer or depth != 0:
            break
        stripped = stripped[1:-1].strip()
    return stripped


def _top_level_symbol_parts(text: str, symbol: str) -> List[str]:
    raw = str(text or "")
    parts: List[str] = []
    start = 0
    depth = 0
    for index, char in enumerate(raw):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and char == symbol:
            parts.append(raw[start:index].strip())
            start = index + 1
    if parts:
        parts.append(raw[start:].strip())
    return [part for part in parts if part]


def _strip_leading_forall_body(text: str) -> str:
    current = _strip_balanced_outer_parens(" ".join(str(text or "").split()))
    while current.startswith("∀") or current.startswith("forall "):
        depth = 0
        comma_index = -1
        for index, char in enumerate(current):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth = max(0, depth - 1)
            elif depth == 0 and char == ",":
                comma_index = index
                break
        if comma_index < 0:
            break
        current = _strip_balanced_outer_parens(current[comma_index + 1 :].strip())
    return current


def _formalization_statement_is_trivial_tautology(statement: str) -> bool:
    """Recognize cheap theorem-shaped ``True`` wrappers used for laundering."""

    text = _strip_leading_forall_body(statement)
    if text in {"True", "False"}:
        return True
    for symbol in ("=", "≤", "≥", "↔"):
        relation_parts = _top_level_symbol_parts(text, symbol)
        if len(relation_parts) == 2:
            left = _strip_balanced_outer_parens(relation_parts[0])
            right = _strip_balanced_outer_parens(relation_parts[1])
            left_key = graph_statement_key(left)
            right_key = graph_statement_key(right)
            if left_key and right_key and left_key == right_key:
                return True
    conjunction_parts = _top_level_symbol_parts(text, "∧")
    if conjunction_parts and all(
        _formalization_statement_is_trivial_tautology(part)
        for part in conjunction_parts
    ):
        return True
    disjunction_parts = _top_level_symbol_parts(text, "∨")
    if disjunction_parts and any(
        _formalization_statement_is_trivial_tautology(part)
        for part in disjunction_parts
    ):
        return True
    for arrow in ("→", "->"):
        pieces = text.split(arrow, 1)
        if len(pieces) != 2:
            continue
        left = _strip_balanced_outer_parens(pieces[0])
        right = _strip_balanced_outer_parens(pieces[1])
        if graph_statement_key(left) == graph_statement_key(right):
            return True
        if left == "False":
            return True
        # ``A → False`` is negation, not a trivial wrapper. Only recurse into
        # a non-False consequent.
        if right != "False" and _formalization_statement_is_trivial_tautology(
            right
        ):
            return True
    return False


def _formalization_neutral_expression_key(expression: str) -> str:
    """Canonicalize only syntactically obvious neutral arithmetic identities."""

    text = _strip_balanced_outer_parens(expression)
    for symbol, neutral, symmetric in (("+", "0", True), ("*", "1", True)):
        parts = _top_level_symbol_parts(text, symbol)
        if len(parts) == 2:
            left, right = parts
            if _strip_balanced_outer_parens(right) == neutral:
                return _formalization_neutral_expression_key(left)
            if symmetric and _strip_balanced_outer_parens(left) == neutral:
                return _formalization_neutral_expression_key(right)
    minus_parts = _top_level_symbol_parts(text, "-")
    if len(minus_parts) == 2:
        left_key = _formalization_neutral_expression_key(minus_parts[0])
        right_key = _formalization_neutral_expression_key(minus_parts[1])
        if right_key == graph_statement_key("0"):
            return left_key
        if left_key and left_key == right_key:
            return graph_statement_key("0")
    return graph_statement_key(text)


def _formalization_statement_is_algebraically_trivial(statement: str) -> bool:
    """Recognize neutral arithmetic identities for auxiliary relevance only."""

    text = _strip_leading_forall_body(statement)
    for arrow in ("→", "->"):
        while True:
            pieces = text.split(arrow, 1)
            if len(pieces) != 2:
                break
            text = _strip_balanced_outer_parens(pieces[1])
    equality = _top_level_symbol_parts(text, "=")
    if len(equality) != 2:
        return False
    return _formalization_neutral_expression_key(
        equality[0]
    ) == _formalization_neutral_expression_key(equality[1])


_AUXILIARY_BRIDGE_GENERIC_FEATURES: FrozenSet[str] = frozenset({
    "by",
    "exact",
    "fun",
    "have",
    "intro",
    "lemma",
    "theorem",
    "Prop",
    "Sort",
    "Type",
    "Nat",
    "Int",
    "Rat",
    "Real",
    "Fin",
    "True",
    "False",
})


_AUXILIARY_BRIDGE_STRONG_FEATURES: FrozenSet[str] = frozenset({
    "Int.floor",
    "Int.fract",
    "Int.ceil",
    "MvPolynomial.eval",
    "MvPolynomial.X",
    "Nat.Prime",
    "floor",
    "fract",
    "ceil",
    "eval",
    "Prime",
})


_AUXILIARY_BRIDGE_CONTENT_OPERATORS: FrozenSet[str] = frozenset({
    "¬",
    "∣",
    "^",
    "+",
    "-",
    "*",
    "/",
    "%",
    "=",
    "<",
    ">",
    "≤",
    "≥",
})


_AUXILIARY_BRIDGE_LOCAL_NAME_RE = re.compile(r"h[a-zA-Z0-9_']*")


def _auxiliary_bridge_is_local_name(token: str) -> bool:
    """Filter proof-local names out of coarse semantic relevance features."""

    text = str(token or "").strip()
    if not text or "." in text:
        return False
    if text in _AUXILIARY_BRIDGE_STRONG_FEATURES:
        return False
    return bool(_AUXILIARY_BRIDGE_LOCAL_NAME_RE.fullmatch(text))


def _auxiliary_bridge_feature_sets(statement: str) -> Tuple[set[str], set[str]]:
    """Return all and non-generic features for parent/support relevance checks."""

    tokens = re.findall(
        r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*|\d+|[¬∣^+\-*/%=<>≤≥]",
        str(statement or ""),
    )
    all_features: set[str] = set()
    content_features: set[str] = set()
    for raw in tokens:
        token = str(raw or "").strip()
        if not token or token in _AUXILIARY_BRIDGE_GENERIC_FEATURES:
            continue
        if _auxiliary_bridge_is_local_name(token):
            continue
        if token in _AUXILIARY_BRIDGE_CONTENT_OPERATORS:
            all_features.add(token)
            content_features.add(token)
            continue
        if token.isdigit():
            if token not in {"0", "1"}:
                all_features.add(token)
                content_features.add(token)
            continue
        if len(token) > 1:
            all_features.add(token)
            content_features.add(token)
    return all_features, content_features


def _auxiliary_bridge_strong_features(features: set[str]) -> set[str]:
    return {
        feature
        for feature in features
        if feature in _AUXILIARY_BRIDGE_STRONG_FEATURES
        or ("." in feature and not feature.startswith(("inst.", "this.")))
    }


def _auxiliary_bridge_identifier_key(value: Any) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", str(value or "")).strip("_")


def _auxiliary_bridge_contract_identifier_keys(contract: Dict[str, Any]) -> set[str]:
    selected = dict(contract.get("selected_graph_work") or {})
    keys: set[str] = set()
    identifier_fields = (
        "node_id",
        "graph_node_id",
        "obligation_id",
        "formalization_obligation_id",
        "helper_obligation_id",
        "selected_node_id",
    )
    for source in (contract, selected):
        for field in identifier_fields:
            key = _auxiliary_bridge_identifier_key(source.get(field))
            if key:
                keys.add(key)
    return keys


def _auxiliary_bridge_helper_name_matches_contract(
    *,
    helper_name: str,
    contract: Dict[str, Any],
) -> bool:
    helper_key = _auxiliary_bridge_identifier_key(helper_name)
    if not helper_key:
        return False
    for key in _auxiliary_bridge_contract_identifier_keys(contract):
        if key and (
            helper_key == key
            or helper_key.startswith(f"{key}_")
            or helper_key.endswith(f"_{key}")
        ):
            return True
    return False


def _auxiliary_bridge_statement_has_relation(statement_features: set[str]) -> bool:
    return bool(statement_features & _AUXILIARY_BRIDGE_CONTENT_OPERATORS)


def _auxiliary_split_leading_quantifiers(statement: str) -> Tuple[List[str], str]:
    """Split Unicode/ASCII universal and existential Lean binders."""

    binders: List[str] = []
    rest = str(statement or "").strip()
    while True:
        match = re.match(r"^(?:∀|∃|forall\b|exists\b)\s*", rest)
        if match is None or rest.startswith("∀ᶠ"):
            break
        tail = rest[match.end() :]
        depth = 0
        comma_index = -1
        for index, char in enumerate(tail):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth = max(0, depth - 1)
            elif depth == 0 and char == ",":
                comma_index = index
                break
        if comma_index < 0:
            break
        binder = tail[:comma_index].strip()
        if binder:
            binders.extend(_split_binder_segments((binder,)))
        rest = tail[comma_index + 1 :].strip()
    return binders, rest


def _auxiliary_bridge_conclusion_profile(statement: str) -> Dict[str, Any]:
    """Return alpha-normalized semantic features of a theorem conclusion."""

    outer_binders, implication_body = _auxiliary_split_leading_quantifiers(statement)
    implication_parts = split_lean_top_level_implications(implication_body)
    conclusion = implication_parts[-1] if implication_parts else implication_body
    # Lean's ``¬ A`` and ``A → False`` are the same proposition.  Preserve the
    # antecedent when the terminal is ``False`` so a genuine negated bridge is
    # not reduced to the content-free token ``False``.
    if len(implication_parts) >= 2 and str(conclusion or "").strip() == "False":
        conclusion = f"¬ ({implication_parts[-2]})"
    inner_binders, conclusion_body = _auxiliary_split_leading_quantifiers(conclusion)
    all_binders = (*outer_binders, *inner_binders)
    bound_function_names = {
        name
        for binder in all_binders
        if "→" in str(binder) or "->" in str(binder)
        for name in _binder_segment_declared_names(binder)
    }
    bound_names = {
        name for binder in all_binders for name in _binder_segment_declared_names(binder)
    }
    normalized = str(conclusion_body or conclusion or statement)
    for name in sorted(bound_names, key=len, reverse=True):
        replacement = "__bound_fn__" if name in bound_function_names else "__bound__"
        normalized = re.sub(
            rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])",
            replacement,
            normalized,
        )
    _all_features, content = _auxiliary_bridge_feature_sets(normalized)
    semantic = {
        feature
        for feature in content
        if feature not in _AUXILIARY_BRIDGE_CONTENT_OPERATORS
        and not feature.isdigit()
        and feature not in {"__bound__", "__bound_fn__"}
    }
    # Member projections tokenize differently across equivalent surfaces such
    # as ``x.re`` and ``(f x).re``. Retain the projection suffix as a semantic
    # feature so those conclusions can still be related after alpha-renaming.
    semantic.update(
        feature.rsplit(".", 1)[-1]
        for feature in tuple(semantic)
        if "." in feature and feature.rsplit(".", 1)[-1]
    )
    return {
        "normalized": normalized,
        "semantic": semantic,
        "operators": content & _AUXILIARY_BRIDGE_CONTENT_OPERATORS,
        "uses_bound_value": "__bound__" in normalized,
        "uses_bound_function": "__bound_fn__" in normalized,
    }


def _auxiliary_bridge_typed_surface_key(statement: str) -> str:
    """Normalize only explicit ascriptions on compound parenthesized terms.

    This is deliberately not a general type-erasure pass. Binder annotations
    and single-name ascriptions can change elaboration and stay in the key.
    The caller additionally requires a current Lean contract identity before
    using this key as auxiliary-support evidence.
    """

    raw = str(statement or "")

    def normalize_segment(segment: str) -> str:
        out: List[str] = []
        index = 0
        while index < len(segment):
            if segment[index] != "(":
                out.append(segment[index])
                index += 1
                continue
            depth = 1
            close_index = index + 1
            while close_index < len(segment) and depth > 0:
                if segment[close_index] == "(":
                    depth += 1
                elif segment[close_index] == ")":
                    depth -= 1
                close_index += 1
            if depth != 0:
                out.append(segment[index:])
                break
            inner = segment[index + 1 : close_index - 1]
            nested_depth = 0
            colon_index = -1
            for inner_index, char in enumerate(inner):
                if char in "([{":
                    nested_depth += 1
                elif char in ")]}":
                    nested_depth = max(0, nested_depth - 1)
                elif char == ":" and nested_depth == 0:
                    colon_index = inner_index
                    break
            left = inner[:colon_index].strip() if colon_index >= 0 else ""
            # A compound expression is distinguishable from a binder or
            # single overloaded name token without interpreting Lean types.
            compound_left = bool(
                left
                and any(
                    operator in left
                    for operator in ("*", "/", "^", "+", "-")
                )
            )
            if colon_index >= 0 and compound_left and inner[colon_index + 1 :].strip():
                out.append(f"({normalize_segment(left)})")
            else:
                out.append(f"({normalize_segment(inner)})")
            index = close_index
        return "".join(out)

    return graph_statement_key(normalize_segment(raw))


def _auxiliary_bridge_relevance_status(
    *,
    statement: str,
    parent_statement: str,
    contract_identity: str = "",
) -> Dict[str, Any]:
    """Reject theorem-shaped helper support with no visible parent connection."""

    if _formalization_statement_is_trivial_tautology(
        statement
    ) or _formalization_statement_is_algebraically_trivial(statement):
        return {
            "accepted": False,
            "reason": "auxiliary_bridge_statement_trivial",
            "relevance_failure_kind": "trivial_conclusion",
        }
    if has_lean_contract_identity(contract_identity):
        statement_typed_key = _auxiliary_bridge_typed_surface_key(statement)
        parent_typed_key = _auxiliary_bridge_typed_surface_key(parent_statement)
        if (
            statement_typed_key
            and parent_typed_key
            and statement_typed_key == parent_typed_key
        ):
            return {
                "accepted": True,
                "exact_typed_surface_identity": True,
                "shared_features": sorted(
                    _auxiliary_bridge_feature_sets(statement)[1]
                ),
            }
    parent_all, parent_content = _auxiliary_bridge_feature_sets(parent_statement)
    statement_all, statement_content = _auxiliary_bridge_feature_sets(statement)
    shared_all = parent_all & statement_all
    shared_content = parent_content & statement_content
    parent_conclusion = _auxiliary_bridge_conclusion_profile(parent_statement)
    statement_conclusion = _auxiliary_bridge_conclusion_profile(statement)
    shared_conclusion_semantic = set(parent_conclusion["semantic"]) & set(
        statement_conclusion["semantic"]
    )
    shared_conclusion_operators = set(parent_conclusion["operators"]) & set(
        statement_conclusion["operators"]
    )
    alpha_structural_overlap = bool(
        parent_conclusion["uses_bound_value"]
        and statement_conclusion["uses_bound_value"]
        and len(shared_conclusion_operators) >= 2
    )
    function_structural_overlap = bool(
        parent_conclusion["uses_bound_function"]
        and statement_conclusion["uses_bound_function"]
        and "=" in shared_conclusion_operators
    )
    # Repeating the parent's antecedent and proving an unrelated generic
    # conclusion is not bridge support.  Require the conclusion itself to
    # retain parent-conclusion semantics, not merely a repeated antecedent.
    # Alpha-renamed arithmetic conclusions may instead share a bound-value
    # structure plus at least two operators; one generic relation is too weak.
    if (
        shared_conclusion_semantic
        or alpha_structural_overlap
        or function_structural_overlap
    ) and len(
        shared_content
    ) >= 2:
        return {
            "accepted": True,
            "shared_features": sorted(shared_content),
            "shared_conclusion_features": sorted(shared_conclusion_semantic),
            "shared_conclusion_operators": sorted(shared_conclusion_operators),
            "alpha_structural_overlap": alpha_structural_overlap,
            "function_structural_overlap": function_structural_overlap,
        }
    if (
        (
            shared_conclusion_semantic
            or alpha_structural_overlap
            or function_structural_overlap
        )
        and shared_content
        and len(shared_all) >= 2
    ):
        return {
            "accepted": True,
            "shared_features": sorted(shared_all),
            "shared_conclusion_features": sorted(shared_conclusion_semantic),
            "shared_conclusion_operators": sorted(shared_conclusion_operators),
            "alpha_structural_overlap": alpha_structural_overlap,
            "function_structural_overlap": function_structural_overlap,
        }
    return {
        "accepted": False,
        "reason": "auxiliary_bridge_statement_unrelated_to_parent",
        "relevance_failure_kind": (
            "conclusion_unrelated_to_parent"
            if shared_content
            else "statement_unrelated_to_parent"
        ),
        "parent_features": sorted(parent_content)[:12],
        "statement_features": sorted(statement_content)[:12],
        "shared_features": sorted(shared_all),
        "shared_conclusion_features": sorted(shared_conclusion_semantic),
        "shared_conclusion_operators": sorted(shared_conclusion_operators),
        "alpha_structural_overlap": alpha_structural_overlap,
        "function_structural_overlap": function_structural_overlap,
    }


def _auxiliary_bridge_local_support_status(
    *,
    contract: Dict[str, Any],
    statement: str,
    parent_statement: str,
    helper_name: str,
    relevance: Dict[str, Any],
) -> Dict[str, Any]:
    """Allow named local micro-lemmas to support, not replace, parent assembly."""

    parent_all, parent_content = _auxiliary_bridge_feature_sets(parent_statement)
    statement_all, statement_content = _auxiliary_bridge_feature_sets(statement)
    shared_content = parent_content & statement_content
    strong_shared = _auxiliary_bridge_strong_features(shared_content)
    if not strong_shared:
        strong_shared = _auxiliary_bridge_strong_features(parent_all & statement_all)
    if not strong_shared:
        return {
            "accepted": False,
            "reason": str(
                relevance.get("reason")
                or "auxiliary_bridge_statement_unrelated_to_parent"
            ),
            "relevance": dict(relevance),
        }
    if not _auxiliary_bridge_statement_has_relation(statement_content):
        return {
            "accepted": False,
            "reason": "auxiliary_bridge_support_lacks_mathematical_relation",
            "relevance": dict(relevance),
        }
    if not _auxiliary_bridge_helper_name_matches_contract(
        helper_name=helper_name,
        contract=contract,
    ):
        return {
            "accepted": False,
            "reason": str(
                relevance.get("reason")
                or "auxiliary_bridge_statement_unrelated_to_parent"
            ),
            "relevance": dict(relevance),
            "strong_shared_features": sorted(strong_shared),
            "helper_name": str(helper_name or ""),
        }
    return {
        "accepted": True,
        "reason": "auxiliary_bridge_local_support_candidate",
        "closes_target": False,
        "requires_parent_assembly": True,
        "shared_features": sorted(strong_shared),
        "relevance": dict(relevance),
    }


def _formalization_bridge_status(
    contract: Dict[str, Any],
    formal_statement: str,
    *,
    helper_name: str = "",
    contract_identity: str = "",
) -> Dict[str, Any]:
    """Check whether a declaration may close a non-executable graph target.

    Lean-checking a theorem only proves that theorem.  For informal graph work,
    the prover also needs a separate semantic bridge saying that the theorem is
    the intended formalization of the selected graph node.
    """

    statement = " ".join(str(formal_statement or "").split()).strip()
    if graph_statement_has_circular_premise(statement):
        premise_keys, conclusion_key = graph_statement_contract_profile(statement)
        return {
            "accepted": False,
            "reason": "bridge_assumes_own_conclusion",
            "circular_premise_key": conclusion_key,
            "premise_keys": list(premise_keys),
        }
    ambiguous_binder_types = (
        ()
        if has_lean_contract_identity(contract_identity)
        else graph_statement_contract_ambiguities(statement)
    )
    if ambiguous_binder_types:
        return {
            "accepted": False,
            "reason": "bridge_contract_ambiguous_proof_binder",
            "ambiguous_binder_types": list(ambiguous_binder_types),
        }
    selected = dict(contract.get("selected_graph_work") or {})
    target_statement = str(contract.get("target_statement") or "").strip()
    bridge_contract = str(
        selected.get("formalization_bridge_contract")
        or contract.get("formalization_bridge_contract")
        or ""
    ).strip()
    parent_statement = str(
        contract.get("parent_statement")
        or selected.get("formalization_bridge_parent_statement")
        or selected.get("parent_repair_target_statement")
        or contract.get("formalization_bridge_parent_statement")
        or ""
    ).strip()
    if parent_statement:
        existential_payload_premise = (
            graph_statement_parent_existential_payload_premise(
                statement,
                parent_statement,
            )
        )
        if existential_payload_premise:
            return {
                "accepted": False,
                "reason": "bridge_assumes_parent_existential_payload",
                "parent_statement": parent_statement,
                "circular_parent_premise": existential_payload_premise,
            }
        for premise_statement in graph_statement_closed_premises(statement):
            if graph_statement_root_equivalent(
                premise_statement,
                parent_statement,
                active_target_statements=(parent_statement,),
            ):
                return {
                    "accepted": False,
                    "reason": "bridge_assumes_parent_target",
                    "parent_statement": parent_statement,
                    "circular_parent_premise": premise_statement,
                }
        # Both circularity checks above clear the bridge by finding NOTHING in
        # the candidate's closed premises.  The premise walker only sees a
        # universal outer telescope, so an existential-headed candidate has no
        # analyzable premise projection.  Having found no reason to reject,
        # refuse rather than admit on an analysis we know to be incomplete.
        # Checked last so a premise the walker DID reach still yields its
        # specific, more useful rejection reason.
        if not graph_statement_leading_telescope_is_universal(statement):
            return {
                "accepted": False,
                "reason": "bridge_premises_not_analyzable",
                "parent_statement": parent_statement,
            }
    if _formalization_statement_is_trivial_tautology(statement):
        return {
            "accepted": False,
            "reason": "tautology_not_formalization_bridge",
        }

    def parent_rejection_status(
        *,
        restates_reason: str,
        root_equivalent_reason: str,
        negates_reason: str,
        refutes_negative_reason: str,
    ) -> Optional[Dict[str, Any]]:
        if not parent_statement:
            return None
        parent_key = graph_statement_key(parent_statement)
        statement_key = graph_statement_key(statement)
        if parent_key and statement_key and parent_key == statement_key:
            return {
                "accepted": False,
                "reason": restates_reason,
                "parent_statement": parent_statement,
            }
        if graph_statement_root_equivalent(
            statement,
            parent_statement,
            active_target_statements=(parent_statement,),
        ):
            return {
                "accepted": False,
                "reason": root_equivalent_reason,
                "parent_statement": parent_statement,
            }
        negated_key = graph_negated_statement_key(statement)
        if parent_key and negated_key and parent_key == negated_key:
            return {
                "accepted": False,
                "reason": negates_reason,
                "parent_statement": parent_statement,
            }
        parent_negated_key = graph_negated_statement_key(parent_statement)
        if parent_negated_key and statement_key and parent_negated_key == statement_key:
            return {
                "accepted": False,
                "reason": refutes_negative_reason,
                "parent_statement": parent_statement,
            }
        return None

    if bridge_contract == "strict_decomposition_bridge":
        if not parent_statement:
            return {
                "accepted": False,
                "reason": "strict_decomposition_bridge_missing_parent",
            }
        rejection = parent_rejection_status(
            restates_reason="bridge_restates_retired_target",
            root_equivalent_reason="bridge_root_equivalent_to_retired_target",
            negates_reason="bridge_negates_retired_target",
            refutes_negative_reason="bridge_refutes_negative_retired_target",
        )
        if rejection is not None:
            return rejection
        return {
            "accepted": True,
            "reason": "strict_decomposition_bridge_candidate",
            "closes_target": False,
            "requires_parent_assembly": True,
        }
    if bridge_contract == "auxiliary_bridge_support":
        if not parent_statement:
            return {
                "accepted": False,
                "reason": "auxiliary_bridge_missing_parent",
                "requires_parent_assembly": True,
            }
        rejection = parent_rejection_status(
            restates_reason="bridge_restates_parent_target",
            root_equivalent_reason="bridge_root_equivalent_to_parent_target",
            negates_reason="bridge_negates_parent_target",
            refutes_negative_reason="bridge_refutes_negative_parent_target",
        )
        if rejection is not None:
            return rejection
        if parent_statement:
            relevance = _auxiliary_bridge_relevance_status(
                statement=statement,
                parent_statement=parent_statement,
                contract_identity=contract_identity,
            )
            if not bool(relevance.get("accepted")):
                local_support = _auxiliary_bridge_local_support_status(
                    contract=contract,
                    statement=statement,
                    parent_statement=parent_statement,
                    helper_name=helper_name,
                    relevance=relevance,
                )
                if bool(local_support.get("accepted")):
                    return local_support
                return local_support
        return {
            "accepted": True,
            "reason": "auxiliary_bridge_support_candidate",
            "closes_target": False,
            "requires_parent_assembly": True,
            "relevance": dict(relevance),
            "shared_features": list(relevance.get("shared_features") or []),
            "shared_conclusion_features": list(
                relevance.get("shared_conclusion_features") or []
            ),
        }
    if parent_statement and not (
        target_statement and graph_statement_is_executable(target_statement)
    ):
        rejection = parent_rejection_status(
            restates_reason="bridge_restates_parent_target",
            root_equivalent_reason="bridge_root_equivalent_to_parent_target",
            negates_reason="bridge_negates_parent_target",
            refutes_negative_reason="bridge_refutes_negative_parent_target",
        )
        if rejection is not None:
            return rejection
    if target_statement and graph_statement_is_executable(target_statement):
        if " ".join(target_statement.split()).strip() == statement:
            return {
                "accepted": True,
                "reason": "exact_executable_target",
                "closes_target": True,
            }
        return {
            "accepted": False,
            "reason": "formalization_statement_mismatches_executable_target",
        }
    bridge_keys = {
        "formalization_bridge_verified",
        "semantic_bridge_verified",
        "formalization_semantic_bridge_verified",
    }
    if any(bool(selected.get(key) or contract.get(key)) for key in bridge_keys):
        return {
            "accepted": True,
            "reason": "semantic_bridge_verified",
            "closes_target": True,
        }
    return {
        "accepted": False,
        "reason": "formalization_bridge_required",
    }


def _formalization_helper_exactly_negates_bridge_parent(
    *,
    formal_statement: str,
    contract: Dict[str, Any],
    bridge_status: Dict[str, Any],
) -> bool:
    selected = dict(contract.get("selected_graph_work") or {})
    parent_statement = str(
        bridge_status.get("parent_statement")
        or selected.get("formalization_bridge_parent_statement")
        or selected.get("parent_repair_target_statement")
        or contract.get("formalization_bridge_parent_statement")
        or contract.get("target_statement")
        or ""
    ).strip()
    parent_key = graph_statement_key(parent_statement)
    negated_key = graph_negated_statement_key(formal_statement)
    return bool(parent_key and negated_key and parent_key == negated_key)


async def _typecheck_graph_native_goal_statement(
    *,
    session: Any,
    statement: str,
) -> Dict[str, Any]:
    if not str(statement or "").strip():
        return {"ok": True, "inconclusive": False, "output": ""}
    lean = getattr(session, "lean", None)
    if lean is None:
        return {
            "ok": False,
            "inconclusive": True,
            "output": "Lean checker missing",
        }
    if not (
        callable(getattr(lean, "check_with_sorry_raw", None))
        or callable(getattr(lean, "check", None))
    ):
        return {
            "ok": False,
            "inconclusive": True,
            "output": "Lean checker missing statement typecheck API",
        }
    dossier = getattr(session, "dossier", None)
    conv = getattr(session, "conv", None)
    try:
        from ensemble_prover.mini_recursive import _typecheck_claim_statement

        helpers = (
            list(dossier.verified_helper_blocks())
            if dossier is not None and hasattr(dossier, "verified_helper_blocks")
            else []
        )
        configured_timeout_s = max(
            float(getattr(getattr(lean, "cfg", None), "timeout_s", 0.0) or 0.0),
            float(getattr(lean, "timeout_s", 0.0) or 0.0),
        )
        return_ok, return_inconclusive, output = await _typecheck_claim_statement(
            lean=lean,
            statement=str(statement or ""),
            preamble=str(
                getattr(conv, "lean_preamble", "")
                or getattr(conv, "preamble", "")
                or ""
            ),
            helpers=helpers,
            # Elaborating a generated proposition is an authoritative safety
            # boundary. Eight seconds made ordinary queueing look like a
            # mathematical rejection and then let the provider see the
            # unchecked statement. Use the same generous verifier floor as
            # answer-safe replay; infrastructure remains a recoverable defer.
            timeout_s=max(300.0, configured_timeout_s),
        )
        return {
            "ok": bool(return_ok),
            "inconclusive": bool(return_inconclusive),
            "output": str(output or ""),
        }
    except Exception as exc:
        return {
            "ok": False,
            "inconclusive": True,
            "output": f"{type(exc).__name__}: {exc}",
        }


def _graph_native_residual_attestation_status(
    *,
    session: Any,
    graph_native_target: Mapping[str, Any],
) -> str:
    """Read the exact proof-state receipt status for a selected graph target."""

    proof_state = getattr(session, "proof_state", None)
    nodes = getattr(proof_state, "nodes", {}) or {}
    node_id = str(graph_native_target.get("node_id") or "").strip()
    node = nodes.get(node_id) if node_id else None
    if node is None or str(getattr(node, "kind", "") or "") != "child_goal":
        return "not_required"
    status_getter = getattr(
        proof_state,
        "residual_goal_attestation_status",
        None,
    )
    if callable(status_getter):
        try:
            persisted_status = str(status_getter(node) or "").strip()
            from ensemble_prover.proof_state_executor import (
                proof_state_node_current_residual_attestation_status,
            )
            status = proof_state_node_current_residual_attestation_status(
                conv=getattr(session, "conv", None),
                dossier=getattr(session, "dossier", None),
                lean=getattr(session, "lean", None),
                proof_state=proof_state,
                node_or_id=node,
            )
            if (
                persisted_status == "attested"
                and status == "residual_elaboration_attestation_required"
            ):
                return "residual_elaboration_reattestation_required"
        except TypeError:
            status = str(status_getter(node) or "").strip()
        except Exception:
            status = ""
        if status:
            return status
    source = str(
        getattr(getattr(node, "goal", None), "source_failure", "") or ""
    ).strip()
    try:
        from ensemble_prover.proof_state import (
            proof_state_source_requires_residual_goal_attestation,
        )

        if proof_state_source_requires_residual_goal_attestation(source):
            return "residual_elaboration_attestation_required"
    except Exception:
        if source:
            return "residual_elaboration_attestation_required"
    return "not_required"


def _mark_graph_native_goal_statement_type_rejected(
    *,
    session: Any,
    graph_native_target: Dict[str, str],
    output: str,
    phase_turn: int,
) -> None:
    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    node_id = str(graph_native_target.get("node_id") or "").strip()
    node = nodes.get(node_id) if isinstance(nodes, dict) and node_id else None
    if node is not None:
        metadata = getattr(node, "metadata", None)
        if not isinstance(metadata, dict):
            metadata = {}
            node.metadata = metadata
        rejected_statement = str(
            graph_native_target.get("statement") or getattr(node, "statement", "") or ""
        ).strip()
        metadata["graph_native_statement_type_rejected"] = True
        metadata["graph_native_statement_type_rejection_output"] = str(output or "")[:1200]
        metadata["graph_native_statement_type_rejected_statement"] = rejected_statement
        metadata["formalization_required"] = True
        metadata["graph_native_statement_type_rejected_status"] = str(
            getattr(node, "status", "") or ""
        )
        node_kind = str(getattr(node, "kind", "") or "")
        if node_kind == "formal_variant":
            node.status = "rejected"
            claim_id = str(metadata.get("claim_node_id") or "").strip()
            parent = nodes.get(claim_id) if isinstance(nodes, dict) and claim_id else None
            if parent is not None:
                parent_metadata = getattr(parent, "metadata", None)
                if not isinstance(parent_metadata, dict):
                    parent_metadata = {}
                    parent.metadata = parent_metadata
                parent_metadata["formalization_required"] = True
                parent_metadata["last_formal_variant_type_rejected"] = node_id
                parent_metadata.setdefault(
                    "formalization_bridge_contract",
                    "strict_decomposition_bridge",
                )
                if rejected_statement:
                    parent_metadata.setdefault(
                        "formalization_bridge_parent_statement",
                        rejected_statement,
                    )
                    parent_metadata.setdefault(
                        "parent_repair_target_statement",
                        rejected_statement,
                    )
                if str(getattr(parent, "status", "") or "") in {"blocked", "failed"}:
                    parent.status = "open"
        else:
            if rejected_statement:
                rejected_hash = hashlib.sha256(
                    rejected_statement.encode("utf-8", errors="replace")
                ).hexdigest()[:16]
                metadata.setdefault(
                    "formalization_bridge_contract",
                    "strict_decomposition_bridge",
                )
                metadata["formalization_bridge_parent_statement"] = rejected_statement
                metadata["parent_repair_target_statement"] = rejected_statement
                metadata["requires_strict_smaller_bridge"] = True
                metadata["type_rejected_statement_hash"] = rejected_hash
                node.statement = (
                    "Repair Lean-invalid graph target "
                    f"{rejected_hash} into a corrected, strictly smaller "
                    "Lean-checkable bridge proposition."
                )
            node.status = "open"
    increment = getattr(session, "_increment_dossier_metric", None)
    if callable(increment):
        increment("mini_session_graph_native_statement_type_rejected", 1)
    if graph is not None and node_id:
        try:
            graph.record_attempt(
                node_id,
                phase="graph_native_statement_typecheck",
                turn_index=int(phase_turn or 0),
                proof="",
                verdict="graph_native_statement_type_rejected",
                error_type="graph_native_statement_type_rejected",
                metadata={
                    "graph_native_goal_statement": str(
                        graph_native_target.get("statement") or ""
                    ),
                    "lean_output": str(output or "")[:1200],
                    "selected_graph_work": dict(
                        getattr(session, "selected_work_item_record", {}) or {}
                    ),
                },
            )
        except Exception:
            pass


async def _run_graph_native_formalization_helper_contract(
    *,
    session: Any,
    action_id: str,
    conv: Any,
    lean: Any,
    dossier: Any,
    contract: Dict[str, Any],
    helpers: Sequence[str],
    lemma_dag_candidates: Sequence[str],
    context_helpers: Sequence[str],
    common_payload: Dict[str, Any],
    phase_turn: int,
    conv_turn_offset: int,
    absolute_turn: int,
    started: float,
    seed_same_turn_prefix_blocks: Sequence[str] = (),
    allow_prefix_scoped_candidate_statements: bool = False,
    publication_guard: Optional[Callable[[], None]] = None,
) -> MiniOutcome:
    """Verify a formalization-required graph task as a helper declaration."""

    if publication_guard is None:
        dispatch_id = str(
            getattr(session, "_inflight_action_dispatch_id", "") or ""
        ).strip()

        def publication_guard() -> None:
            require_current_action_dispatch(session, dispatch_id)

    skeleton_route_banked, skeleton_route_metadata = _skeleton_route_metadata(
        common_payload,
        soft_only=True,
    )
    _, skeleton_route_counter_metadata = _skeleton_route_metadata(common_payload)
    if dossier is None:
        _emit_record(session, {
            **common_payload,
            "rejection_reason": "formalization_helper_missing_dossier",
            "lean_error_type": "formalization_helper_missing_dossier",
            "verdict": "proof_policy_rejected",
        })
        return MiniOutcome(
            action_id=action_id,
            solved=False,
            proof=None,
            helpers_added=(),
            progress=bool(skeleton_route_banked),
            cost_seconds=time.monotonic() - started,
            metadata={
                "role": str(getattr(conv, "role", "") or "prove"),
                "conv_turn_index_offset": conv_turn_offset,
                "conv_turn_index_absolute": absolute_turn,
                "conv_turn_index_phase": phase_turn,
                **_turn_budget_metadata(common_payload),
                "rejection_reason": "formalization_helper_missing_dossier",
                **skeleton_route_metadata,
            },
        )
    graph = getattr(dossier, "proof_graph", None)
    node_id = str(contract.get("node_id") or "").strip()
    node = getattr(graph, "nodes", {}).get(node_id) if graph is not None else None
    candidates = _formalization_helper_candidates(
        helpers,
        lemma_dag_candidates,
        require_executable_statement=not bool(
            allow_prefix_scoped_candidate_statements
        ),
    )
    if not candidates:
        feedback = _formalization_helper_feedback(contract=contract)
        try:
            conv.append_user(feedback)
        except Exception:
            pass
        _emit_record(session, {
            **common_payload,
            "rejection_reason": "formalization_helper_declaration_missing",
            "lean_error_type": "formalization_helper_declaration_missing",
            "graph_native_formalization_contract": dict(contract),
            "verdict": "no_proof_extracted",
        })
        return MiniOutcome(
            action_id=action_id,
            solved=False,
            proof=None,
            helpers_added=(),
            progress=bool(skeleton_route_banked),
            cost_seconds=time.monotonic() - started,
            metadata={
                "role": str(getattr(conv, "role", "") or "prove"),
                "conv_turn_index_offset": conv_turn_offset,
                "conv_turn_index_absolute": absolute_turn,
                "conv_turn_index_phase": phase_turn,
                **_turn_budget_metadata(common_payload),
                "no_proof": True,
                "rejection_reason": "formalization_helper_declaration_missing",
                "graph_native_formalization_contract": dict(contract),
                "llm_response": common_payload.get("llm_response"),
                **skeleton_route_metadata,
            },
        )

    context_replay_names = [
        helper_decl_name(block) or ""
        for block in context_helpers
        if helper_decl_name(block)
    ]
    raw_same_turn_prefix_blocks: List[str] = [
        str(block or "").strip()
        for block in list(seed_same_turn_prefix_blocks or ())
        if str(block or "").strip()
    ]
    same_turn_prefix_blocks: List[str] = _formalization_helper_candidates(
        raw_same_turn_prefix_blocks,
        (),
        require_executable_statement=False,
    )
    replay_only_prefix_blocks: List[str] = [
        block
        for block in raw_same_turn_prefix_blocks
        if helper_decl_kind(block) in {"def", "abbrev", "instance"}
        and (helper_decl_name(block) or helper_decl_kind(block) == "instance")
        and helper_decl_body(block)
        and not has_sorry_or_admit(helper_decl_body(block))
    ]
    last_failure = ""
    last_bridge_status: Dict[str, Any] = {}
    last_rejected_statement = ""
    banked_rejected_candidate_names: List[str] = []

    async def authoritative_exact_negation_outcome(
        *,
        candidate: str,
        formal_statement: str,
        bridge_status: Dict[str, Any],
        replay_helpers: Sequence[str],
    ) -> Optional[MiniOutcome]:
        """Preserve an exact negative artifact without accepting target drift.

        The declaration still fails the positive formalization contract.  Its
        proof body is useful only when it directly negates that exact target,
        and even then it crosses into durable state solely after an independent
        Lean replay plus axiom audit by the falsification service.
        """

        if not _formalization_helper_exactly_negates_bridge_parent(
            formal_statement=formal_statement,
            contract=contract,
            bridge_status=bridge_status,
        ):
            return None
        selected = dict(contract.get("selected_graph_work") or {})
        target_statement = str(
            bridge_status.get("parent_statement")
            or selected.get("formalization_bridge_parent_statement")
            or selected.get("parent_repair_target_statement")
            or contract.get("formalization_bridge_parent_statement")
            or contract.get("target_statement")
            or ""
        ).strip()
        if not target_statement:
            return None
        from ensemble_prover.mini_session.child_goal_falsification import (
            record_authoritative_negation_artifact,
        )

        authority_helpers = tuple(list(replay_helpers or ())[:-1])
        feedback_preamble, feedback_helpers = (
            _accepted_negation_feedback_context(conv, authority_helpers)
        )
        try:
            authoritative, certificate_hash, terminalized_aliases = (
                await record_authoritative_negation_artifact(
                    parent_session=session,
                    dossier=dossier,
                    target_statement=target_statement,
                    negation_declarations=(candidate,),
                    preamble=_accepted_negation_preamble(conv),
                    # The candidate is last and must not be available as a premise
                    # while certifying its own proof body.
                    helper_blocks=authority_helpers,
                    feedback_preamble=feedback_preamble,
                    feedback_helper_blocks=feedback_helpers,
                    engine="graph_native_exact_negation_declaration",
                    reason="graph_native_exact_negation_artifact",
                    publication_guard=publication_guard,
                )
            )
        except Exception:
            publication_guard()
            # The declaration remains a normal target mismatch if the
            # optional certification backend is unavailable.
            return None
        if _negation_certification_conflicted(dossier, certificate_hash):
            conflict_metadata = _proof_disproof_conflict_metadata(dossier)
            _emit_record(session, {
                **common_payload,
                **conflict_metadata,
                "falsification_certificate_hash": certificate_hash,
                "verdict": "graph_native_proof_disproof_conflict",
            })
            return MiniOutcome(
                action_id=action_id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "role": str(getattr(conv, "role", "") or "prove"),
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    **conflict_metadata,
                    "falsification_certificate_hash": certificate_hash,
                    "lean_verdict": "proof_disproof_conflict",
                    "verdict": "graph_native_proof_disproof_conflict",
                },
            )
        if not authoritative:
            return None
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment("mini_session_graph_formalization_bridge_rejected", 1)
            increment(
                "mini_session_graph_formalization_negative_bridge_support_rejected",
                1,
            )
        _emit_record(session, {
            **common_payload,
            "lean_ok": True,
            "helper_statement": formal_statement,
            "graph_native_formalization_contract": dict(contract),
            "formalization_bridge_status": dict(bridge_status),
            "negative_evidence_helper": True,
            "authoritative_falsification": True,
            "falsified_statement": target_statement,
            "falsification_certificate_hash": certificate_hash,
            "terminalized_proof_state_aliases": list(terminalized_aliases),
            "rejection_reason": "declaration target mismatch; exact negation certified",
            "lean_error_type": "authoritative_exact_negation",
            "verdict": "graph_native_target_authoritatively_falsified",
        })
        return MiniOutcome(
            action_id=action_id,
            solved=False,
            proof=None,
            helpers_added=(),
            progress=True,
            cost_seconds=time.monotonic() - started,
            metadata={
                "role": str(getattr(conv, "role", "") or "prove"),
                "conv_turn_index_offset": conv_turn_offset,
                "conv_turn_index_absolute": absolute_turn,
                "conv_turn_index_phase": phase_turn,
                **_turn_budget_metadata(common_payload),
                **skeleton_route_counter_metadata,
                "lean_verdict": "authoritative_target_falsified",
                "authoritative_falsification": True,
                "falsified_statement": target_statement,
                **_root_falsification_terminal_metadata(
                    session,
                    target_statement,
                ),
                "falsification_certificate_hash": certificate_hash,
                "terminalized_proof_state_aliases": list(terminalized_aliases),
                "graph_native_target_node_id": node_id,
                "graph_native_work_type": contract.get("work_type"),
                "graph_native_formalization_contract": dict(contract),
                "selected_graph_work": selected,
                "rejection_reason": "declaration target mismatch; exact negation certified",
                "verdict": "graph_native_target_authoritatively_falsified",
            },
        )

    def increment_dependency_rejected_metric() -> None:
        increment = getattr(session, "_increment_dossier_metric", None)
        if not callable(increment):
            return
        if bool(common_payload.get("same_target_decl_proof_graph_formalization_routed")):
            increment(
                "mini_session_same_target_decl_proofs_graph_formalization_dependency_rejected",
                1,
            )
        if bool(common_payload.get("proof_turn_decl_graph_formalization_routed")):
            increment(
                "mini_session_proof_turn_decl_graph_formalization_dependency_rejected",
                1,
            )

    async def implicit_instance_prefix_dependencies(candidate: str) -> List[str]:
        implicit_candidates: List[Tuple[str, str]] = []
        seen_labels: set[str] = set()
        for block in replay_only_prefix_blocks:
            if helper_decl_kind(block) != "instance":
                continue
            label = _replay_only_prefix_label(block)
            if not label or label in seen_labels:
                continue
            seen_labels.add(label)
            implicit_candidates.append((label, block))
        if not implicit_candidates:
            return []

        async def replay_with_instances(instance_blocks: Sequence[str]) -> bool:
            implicit_replay_helpers = [
                *list(context_helpers or ()),
                *pre_replay_dependency_blocks,
                *list(instance_blocks or ()),
                candidate,
            ]
            implicit_result = await _check_graph_native_formalization_replay(
                lean=lean,
                conv=conv,
                replay_helpers=implicit_replay_helpers,
            )
            return bool(getattr(implicit_result, "ok", False))

        async def prune_serviceable_subset(
            subset: Sequence[Tuple[str, str]],
        ) -> List[Tuple[str, str]]:
            necessary = list(subset or ())
            index = 0
            while index < len(necessary):
                trial = [
                    block
                    for item_index, (_label, block) in enumerate(necessary)
                    if item_index != index
                ]
                if not trial:
                    index += 1
                    continue
                if await replay_with_instances(trial):
                    necessary.pop(index)
                    continue
                index += 1
            return necessary

        for item in implicit_candidates:
            if await replay_with_instances([item[1]]):
                return [item[0]]

        if len(implicit_candidates) == 1:
            return []

        implicit_blocks = [block for _label, block in implicit_candidates]
        if await replay_with_instances(implicit_blocks):
            necessary = await prune_serviceable_subset(implicit_candidates)
            return [label for label, _block in necessary]

        max_subset_replays = 64
        subset_replays = 0
        if len(implicit_candidates) <= 8:
            for subset_size in range(2, len(implicit_candidates)):
                for subset in combinations(implicit_candidates, subset_size):
                    subset_replays += 1
                    if subset_replays > max_subset_replays:
                        return []
                    blocks = [block for _label, block in subset]
                    if await replay_with_instances(blocks):
                        necessary = await prune_serviceable_subset(subset)
                        return [label for label, _block in necessary]
        return []

    async def analyze_verified_statement_contract(
        statement: str,
        replay_helpers: Sequence[str],
    ) -> Any:
        analyzer = getattr(lean, "analyze_statement_contracts", None)
        if not callable(analyzer) or not str(statement or "").strip():
            return None
        try:
            analyses, _output, _returncode = await analyzer(
                [statement],
                preamble_override="\n\n".join(
                    part
                    for part in (
                        str(getattr(conv, "preamble", "") or "").strip(),
                        *(
                            str(block or "").strip()
                            for block in replay_helpers
                        ),
                    )
                    if part
                ),
            )
        except Exception:
            return None
        analysis = next(iter(analyses or ()), None)
        if not str(
            getattr(analysis, "structural_identity", "") or ""
        ).strip():
            return None
        return analysis

    for candidate in candidates:
        formal_statement = helper_decl_statement(candidate)
        same_turn_dependency_analysis_prefix_blocks: List[str] = [
            *same_turn_prefix_blocks,
            *replay_only_prefix_blocks,
        ]
        (
            pre_replay_dependency_blocks,
            pre_replay_only_dependency_names,
        ) = _same_turn_helper_dependency_analysis(
            candidate,
            same_turn_dependency_analysis_prefix_blocks,
        )
        if pre_replay_only_dependency_names:
            last_failure = "same-turn helper dependency requires replay-only prefix"
            increment_dependency_rejected_metric()
            _emit_record(session, {
                **common_payload,
                "helper_statement": formal_statement,
                "graph_native_formalization_contract": dict(contract),
                "replay_only_prefix_names": list(
                    _replay_only_prefix_names(
                        same_turn_dependency_analysis_prefix_blocks
                    )
                ),
                "replay_only_dependency_names": list(
                    pre_replay_only_dependency_names
                ),
                "rejection_reason": last_failure,
                "lean_error_type": "formalization_helper_non_standalone_dependency",
                "verdict": "graph_native_formalization_dependency_rejected",
            })
            continue
        candidate_replay_helpers = [
            *list(context_helpers or ()),
            *pre_replay_dependency_blocks,
            candidate,
        ]
        result = await _check_graph_native_formalization_replay(
            lean=lean,
            conv=conv,
            replay_helpers=candidate_replay_helpers,
        )
        if not bool(getattr(result, "ok", False)):
            replay_only_prefix_names = _replay_only_prefix_names(
                same_turn_dependency_analysis_prefix_blocks
            )
            replay_only_failure_names = list(
                dict.fromkeys([
                    *pre_replay_only_dependency_names,
                ])
            )
            if not replay_only_failure_names:
                replay_only_failure_names = (
                    await implicit_instance_prefix_dependencies(candidate)
                )
            if replay_only_failure_names:
                last_failure = (
                    "same-turn helper dependency requires replay-only prefix"
                )
                increment_dependency_rejected_metric()
                _emit_record(session, {
                    **common_payload,
                    "helper_statement": formal_statement,
                    "graph_native_formalization_contract": dict(contract),
                    "replay_only_prefix_names": list(replay_only_prefix_names),
                    "replay_only_dependency_names": list(
                        replay_only_failure_names
                    ),
                    "rejection_reason": last_failure,
                    "lean_error_type": "formalization_helper_non_standalone_dependency",
                    "verdict": "graph_native_formalization_dependency_rejected",
                })
                continue
            last_failure = str(getattr(result, "output", "") or "Lean rejected")
            replay_bridge_status = _formalization_bridge_status(
                contract,
                formal_statement,
                helper_name=helper_decl_name(candidate) or "",
            )
            if bool(replay_bridge_status.get("accepted")):
                replay_bridge_status = {
                    **dict(replay_bridge_status),
                    "reason": "formalization_helper_replay_failed",
                }
            banked = _bank_rejected_formalization_helper_candidate(
                session=session,
                conv=conv,
                dossier=dossier,
                candidate=candidate,
                same_turn_prefix_blocks=same_turn_prefix_blocks,
                contract=contract,
                bridge_status=replay_bridge_status,
                phase_turn=phase_turn,
            )
            for name in banked:
                if name not in banked_rejected_candidate_names:
                    banked_rejected_candidate_names.append(name)
            continue
        contract_analysis = await analyze_verified_statement_contract(
            formal_statement,
            candidate_replay_helpers,
        )
        bridge_status = _formalization_bridge_status(
            contract,
            formal_statement,
            helper_name=helper_decl_name(candidate) or "",
            contract_identity=str(
                getattr(contract_analysis, "structural_identity", "") or ""
            ),
        )
        parent_closure_checked = False
        checked_parent_statement = ""
        parent_obligation_id = ""
        parent_obligation = None
        parent_target_binding_admitted = False
        parent_target_binding_reason = ""
        if not bool(bridge_status.get("closes_target", False)):
            parent_closure_checked = (
                await _checked_formalization_closes_parent_target(
                    lean=lean,
                    conv=conv,
                    candidate=candidate,
                    replay_helpers=candidate_replay_helpers,
                    contract=contract,
                )
            )
        if parent_closure_checked:
            checked_parent_statement = _formalization_parent_target_statement(
                contract
            )
            (
                parent_obligation_id,
                parent_obligation,
                parent_target_binding_admitted,
                parent_target_binding_reason,
            ) = _formalization_parent_target_binding(
                contract=contract,
                selected_node=node,
                graph=graph,
                checked_parent_statement=checked_parent_statement,
                dossier=dossier,
            )
            bridge_status = {
                **dict(bridge_status),
                "accepted": bool(parent_target_binding_admitted),
                "reason": (
                    "lean_verified_parent_target_closure"
                    if parent_target_binding_admitted
                    else "parent_target_graph_binding_rejected"
                ),
                "closes_target": bool(parent_target_binding_admitted),
                "requires_parent_assembly": not parent_target_binding_admitted,
                "parent_target_closure_replay_verified": True,
                "parent_target_closure_checked_statement_key": (
                    graph_statement_key(checked_parent_statement)
                ),
                "parent_target_closure_checked_environment_hash": str(
                    getattr(dossier, "current_lean_environment_hash", "") or ""
                ).strip(),
                "parent_target_closure_bound_obligation_id": (
                    parent_obligation_id
                ),
                "parent_target_closure_graph_binding_admitted": (
                    parent_target_binding_admitted
                ),
                "parent_target_closure_graph_binding_reason": (
                    parent_target_binding_reason
                ),
            }
        if not bool(bridge_status.get("accepted")):
            last_failure = str(
                bridge_status.get("reason")
                or "formalization_bridge_required"
            )
            last_bridge_status = dict(bridge_status)
            last_rejected_statement = formal_statement
            negative_outcome = await authoritative_exact_negation_outcome(
                candidate=candidate,
                formal_statement=formal_statement,
                bridge_status=bridge_status,
                replay_helpers=candidate_replay_helpers,
            )
            if negative_outcome is not None:
                return negative_outcome
            banked = _bank_rejected_formalization_helper_candidate(
                session=session,
                conv=conv,
                dossier=dossier,
                candidate=candidate,
                same_turn_prefix_blocks=same_turn_prefix_blocks,
                contract=contract,
                bridge_status=bridge_status,
                phase_turn=phase_turn,
            )
            for name in banked:
                if name not in banked_rejected_candidate_names:
                    banked_rejected_candidate_names.append(name)
            if node is not None:
                node_metadata = getattr(node, "metadata", None)
                if not isinstance(node_metadata, dict):
                    node_metadata = {}
                    node.metadata = node_metadata
                rejected = list(
                    node_metadata.get("rejected_formalization_candidates") or []
                )
                rejected.append(
                    {
                        "statement": formal_statement,
                        "reason": last_failure,
                        "phase": f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
                        "turn_index": phase_turn,
                    }
                )
                node_metadata["rejected_formalization_candidates"] = rejected[-5:]
                node_metadata["formalization_bridge_required"] = True
                same_rejections = [
                    item
                    for item in rejected
                    if str(item.get("statement") or "") == formal_statement
                    and str(item.get("reason") or "") == last_failure
                ]
                same_reason_rejections = [
                    item
                    for item in rejected
                    if str(item.get("reason") or "") == last_failure
                ]
                nonprogress_bridge_rejection_reasons = {
                    "auxiliary_bridge_statement_unrelated_to_parent",
                    "auxiliary_bridge_support_lacks_mathematical_relation",
                    "formalization_bridge_required",
                    "bridge_assumes_own_conclusion",
                    "bridge_assumes_parent_target",
                    "bridge_contract_ambiguous_proof_binder",
                }
                repeated_relevance_count = sum(
                    1
                    for item in rejected
                    if str(item.get("reason") or "")
                    in nonprogress_bridge_rejection_reasons
                )
                repeated_bridge_count = max(
                    len(same_rejections),
                    repeated_relevance_count,
                )
                suppress_repeated_bridge = (
                    repeated_bridge_count >= 3
                    and not bool(
                        node_metadata.get(
                            "formalization_repeated_unrelated_bridge_suppressed"
                        )
                    )
                )
                if suppress_repeated_bridge:
                    node_metadata["schedulable"] = False
                    node_metadata[
                        "formalization_repeated_unrelated_bridge_suppressed"
                    ] = True
                    node_metadata[
                        "formalization_repeated_unrelated_bridge_reason"
                    ] = last_failure
                    node_metadata[
                        "formalization_repeated_unrelated_bridge_count"
                    ] = repeated_bridge_count
            increment = getattr(session, "_increment_dossier_metric", None)
            if callable(increment):
                increment("mini_session_graph_formalization_bridge_rejected", 1)
                if last_failure in {
                    "bridge_negates_parent_target",
                    "bridge_negates_retired_target",
                    "bridge_refutes_negative_parent_target",
                    "bridge_refutes_negative_retired_target",
                }:
                    increment(
                        "mini_session_graph_formalization_negative_bridge_support_rejected",
                        1,
                    )
                if node is not None and suppress_repeated_bridge:
                    increment(
                        "mini_session_graph_formalization_repeated_bridge_suppressed",
                        1,
                    )
            _emit_record(session, {
                **common_payload,
                "lean_ok": True,
                "helper_statement": formal_statement,
                "graph_native_formalization_contract": dict(contract),
                "formalization_bridge_status": dict(bridge_status),
                "rejection_reason": last_failure,
                "lean_error_type": "formalization_bridge_required",
                "formalization_rejected_candidate_banked_proposed_helpers": list(
                    banked
                ),
                "verdict": "graph_native_formalization_bridge_rejected",
            })
            if node is not None and suppress_repeated_bridge:
                _emit_record(session, {
                    **common_payload,
                    "helper_statement": formal_statement,
                    "graph_native_formalization_contract": dict(contract),
                    "rejection_reason": last_failure,
                    "repeat_count": repeated_bridge_count,
                    "same_statement_repeat_count": len(same_rejections),
                    "same_reason_repeat_count": len(same_reason_rejections),
                    "verdict": "graph_native_formalization_repeated_bridge_suppressed",
                })
            if helper_decl_name(candidate):
                same_turn_prefix_blocks.append(candidate)
            continue
        route_support_only = not bool(bridge_status.get("closes_target", True))
        if parent_closure_checked:
            route_support_provenance = [
                "root_authoritative_helper",
                "lean_verified_parent_target_closure",
            ]
            route_support_visibility = "root_authoritative"
        else:
            route_support_provenance = (
                ["route_support_only_helper"] if route_support_only else []
            )
            route_support_visibility = (
                "advisory_route_support_only" if route_support_only else ""
            )
        if (
            route_support_only
            and _formalization_helper_exactly_negates_bridge_parent(
                formal_statement=formal_statement,
                contract=contract,
                bridge_status=bridge_status,
            )
        ):
            last_failure = "negative evidence refutes bridge parent"
            increment = getattr(session, "_increment_dossier_metric", None)
            if callable(increment):
                increment(
                    "mini_session_graph_formalization_negative_bridge_support_rejected",
                    1,
                )
                increment("mini_session_graph_formalization_bridge_rejected", 1)
            _emit_record(session, {
                **common_payload,
                "lean_ok": True,
                "helper_statement": formal_statement,
                "graph_native_formalization_contract": dict(contract),
                "formalization_bridge_status": dict(bridge_status),
                "negative_evidence_helper": True,
                "rejection_reason": last_failure,
                "lean_error_type": "negative_evidence_bridge_support",
                "verdict": "graph_native_formalization_bridge_rejected",
            })
            continue
        (
            dependency_blocks,
            replay_only_dependency_names,
        ) = _same_turn_helper_dependency_analysis(
            candidate,
            same_turn_dependency_analysis_prefix_blocks,
        )
        replay_only_prefix_names = _replay_only_prefix_names(
            same_turn_dependency_analysis_prefix_blocks
        )
        replay_only_failure_names = list(
            dict.fromkeys([
                *replay_only_dependency_names,
            ])
        )
        candidate_support_names: List[str] = []
        banked_same_turn_dependency_names: List[str] = []
        durable_same_turn_dependency_blocks: List[str] = []
        dependency_banking_failed = False
        for dependency_block in dependency_blocks:
            if replay_only_failure_names:
                dependency_replay_helpers = [
                    *list(context_helpers or ()),
                    *durable_same_turn_dependency_blocks,
                    dependency_block,
                ]
                dependency_replay = await _check_graph_native_formalization_replay(
                    lean=lean,
                    conv=conv,
                    replay_helpers=dependency_replay_helpers,
                )
                if not bool(getattr(dependency_replay, "ok", False)):
                    dependency_banking_failed = True
                    last_failure = (
                        "same-turn helper dependency requires replay-only prefix"
                    )
                    break
            dependency_record = dossier.record_verified_helper(
                dependency_block,
                phase=f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
                turn_index=phase_turn,
                support_names=candidate_support_names,
                replay_context_names=[
                    *context_replay_names,
                    *banked_same_turn_dependency_names,
                ],
                provenance_tags=(
                    ["route_support_only_dependency"] if route_support_only else []
                ),
                visibility_policy=route_support_visibility,
            )
            if dependency_record is None:
                dependency_banking_failed = True
                last_failure = "same-turn helper dependency policy rejected"
                break
            _stage_verified_helper_receipt(session, dependency_record, dossier)
            if dependency_record.name not in candidate_support_names:
                candidate_support_names.append(dependency_record.name)
            banked_same_turn_dependency_names.append(dependency_record.name)
            durable_same_turn_dependency_blocks.append(dependency_block)
        if dependency_banking_failed:
            increment_dependency_rejected_metric()
            _emit_record(session, {
                **common_payload,
                "lean_ok": True,
                "helper_statement": formal_statement,
                "graph_native_formalization_contract": dict(contract),
                "formalization_bridge_status": dict(bridge_status),
                "replay_only_prefix_names": list(replay_only_prefix_names),
                "replay_only_dependency_names": list(
                    replay_only_failure_names
                ),
                "rejection_reason": last_failure,
                "lean_error_type": "formalization_helper_non_standalone_dependency",
                "verdict": "graph_native_formalization_dependency_rejected",
            })
            continue
        if replay_only_failure_names:
            candidate_standalone_replay_helpers = [
                *list(context_helpers or ()),
                *durable_same_turn_dependency_blocks,
                candidate,
            ]
            candidate_standalone = await _check_graph_native_formalization_replay(
                lean=lean,
                conv=conv,
                replay_helpers=candidate_standalone_replay_helpers,
            )
            if not bool(getattr(candidate_standalone, "ok", False)):
                last_failure = (
                    "same-turn helper dependency requires replay-only prefix"
                )
                increment_dependency_rejected_metric()
                _emit_record(session, {
                    **common_payload,
                    "lean_ok": True,
                    "helper_statement": formal_statement,
                    "graph_native_formalization_contract": dict(contract),
                    "formalization_bridge_status": dict(bridge_status),
                    "replay_only_prefix_names": list(replay_only_prefix_names),
                    "replay_only_dependency_names": list(
                        replay_only_failure_names
                    ),
                    "rejection_reason": last_failure,
                    "lean_error_type": "formalization_helper_non_standalone_dependency",
                    "verdict": "graph_native_formalization_dependency_rejected",
                })
                continue
        helper_record = dossier.record_verified_helper(
            candidate,
            phase=f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
            turn_index=phase_turn,
            support_names=candidate_support_names,
            replay_context_names=[
                *context_replay_names,
                *banked_same_turn_dependency_names,
            ],
            provenance_tags=route_support_provenance,
            visibility_policy=route_support_visibility,
            contract_identity=str(
                getattr(contract_analysis, "structural_identity", "") or ""
            ),
            contract_display_statement=str(
                getattr(contract_analysis, "display_type", "") or ""
            ),
            contract_binder_sorts=tuple(
                getattr(contract_analysis, "binder_sorts", ()) or ()
            ),
            contract_proof_binder_types=tuple(
                getattr(contract_analysis, "proof_binder_types", ()) or ()
            ),
            _contract_identity_statement=formal_statement,
        )
        if helper_record is None:
            last_failure = "verified helper policy rejected the declaration"
            continue
        _stage_verified_helper_receipt(session, helper_record, dossier)
        helper_name = helper_record.name
        helper_is_negative_evidence = (
            str(getattr(helper_record, "render_policy", "") or "").strip()
            == "advisory_negative_evidence"
            or "negative_evidence_helper"
            in list(getattr(helper_record, "quality_tags", []) or [])
        )
        if (
            helper_is_negative_evidence
            and not bool(bridge_status.get("closes_target", True))
            and _formalization_helper_exactly_negates_bridge_parent(
                formal_statement=formal_statement,
                contract=contract,
                bridge_status=bridge_status,
            )
        ):
            last_failure = "negative evidence refutes bridge parent"
            increment = getattr(session, "_increment_dossier_metric", None)
            if callable(increment):
                increment(
                    "mini_session_graph_formalization_negative_bridge_support_rejected",
                    1,
                )
                increment("mini_session_graph_formalization_bridge_rejected", 1)
            _emit_record(session, {
                **common_payload,
                "lean_ok": True,
                "helper_statement": formal_statement,
                "graph_native_formalization_contract": dict(contract),
                "formalization_bridge_status": dict(bridge_status),
                "negative_evidence_helper": True,
                "rejection_reason": last_failure,
                "lean_error_type": "negative_evidence_bridge_support",
                "verdict": "graph_native_formalization_bridge_rejected",
            })
            continue
        if bool(contract.get("proof_only_helper_support_deferred_materialization")):
            materialized_contract = _materialize_proof_only_auxiliary_bridge_contract(
                session,
                contract,
                formal_statement=formal_statement,
                phase_turn=phase_turn,
            )
            if not materialized_contract:
                last_failure = "proof_only_helper_support_materialization_failed"
                increment = getattr(session, "_increment_dossier_metric", None)
                if callable(increment):
                    increment("mini_session_proof_only_helper_support_rejected", 1)
                _emit_record(session, {
                    **common_payload,
                    "lean_ok": True,
                    "helper_statement": formal_statement,
                    "graph_native_formalization_contract": dict(contract),
                    "formalization_bridge_status": dict(bridge_status),
                    "rejection_reason": last_failure,
                    "lean_error_type": "formalization_bridge_materialization_failed",
                    "verdict": "graph_native_formalization_bridge_rejected",
                })
                continue
            contract = materialized_contract
            node_id = str(contract.get("node_id") or "").strip()
            node = (
                getattr(graph, "nodes", {}).get(node_id)
                if graph is not None and node_id
                else None
            )
            bridge_status = _formalization_bridge_status(
                contract,
                formal_statement,
                helper_name=helper_decl_name(candidate) or "",
            )
            if not bool(bridge_status.get("accepted")):
                last_failure = str(
                    bridge_status.get("reason")
                    or "formalization_bridge_required"
                )
                increment = getattr(session, "_increment_dossier_metric", None)
                if callable(increment):
                    increment("mini_session_graph_formalization_bridge_rejected", 1)
                    increment("mini_session_proof_only_helper_support_rejected", 1)
                _emit_record(session, {
                    **common_payload,
                    "lean_ok": True,
                    "helper_statement": formal_statement,
                    "graph_native_formalization_contract": dict(contract),
                    "formalization_bridge_status": dict(bridge_status),
                    "rejection_reason": last_failure,
                    "lean_error_type": "formalization_bridge_required",
                    "verdict": "graph_native_formalization_bridge_rejected",
                })
                continue
        closes_target = not route_support_only
        if not closes_target:
            target_node_id = node_id
            helper_node_id = (
                graph.helper_name_to_node_id.get(helper_name, "")
                if graph is not None
                else ""
            )
            support_recorded = False
            if graph is not None and node is not None:
                node_kind = str(getattr(node, "kind", "") or "")
                if node_kind == "missing_obligation":
                    recorder = getattr(graph, "record_obligation_bridge_support", None)
                    if callable(recorder):
                        bridge_parent_statement = str(
                            bridge_status.get("parent_statement")
                            or (
                                contract.get("selected_graph_work")
                                or {}
                            ).get("formalization_bridge_parent_statement")
                            or (
                                contract.get("selected_graph_work")
                                or {}
                            ).get("parent_repair_target_statement")
                            or contract.get(
                                "formalization_bridge_parent_statement"
                            )
                            or ""
                        )
                        parent_contract_analysis = (
                            await analyze_verified_statement_contract(
                                bridge_parent_statement,
                                candidate_replay_helpers,
                            )
                            if bridge_parent_statement
                            else None
                        )
                        support_recorded = bool(
                            recorder(
                                node.node_id,
                                helper_node_id,
                                formal_statement=formal_statement,
                                bridge_reason=str(bridge_status.get("reason") or ""),
                                parent_statement=bridge_parent_statement,
                                phase=f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
                                turn_index=phase_turn,
                                source_hash=helper_record.source_hash,
                                support_names=candidate_support_names,
                                parent_proof_binder_structural_hashes=tuple(
                                    getattr(
                                        parent_contract_analysis,
                                        "proof_binder_structural_hashes",
                                        (),
                                    )
                                    or ()
                                ),
                                helper_proof_binder_structural_hashes=tuple(
                                    getattr(
                                        contract_analysis,
                                        "proof_binder_structural_hashes",
                                        (),
                                    )
                                    or ()
                                ),
                            )
                        )
                else:
                    node_metadata = getattr(node, "metadata", None)
                    if not isinstance(node_metadata, dict):
                        node_metadata = {}
                        node.metadata = node_metadata
                    prior_support_helper_node_id = str(
                        node_metadata.get(
                            "formalization_bridge_support_helper_node_id"
                        )
                        or ""
                    )
                    prior_support_helper_name = str(
                        node_metadata.get("formalization_bridge_support_helper_name")
                        or ""
                    )
                    prior_support_source_hash = str(
                        node_metadata.get("formalization_bridge_support_source_hash")
                        or ""
                    )
                    prior_support_statement = str(
                        node_metadata.get("formalization_bridge_support_statement")
                        or ""
                    )
                    node_metadata["formalization_bridge_support_recorded"] = True
                    node_metadata["formalization_bridge_parent_assembly_required"] = True
                    node_metadata[
                        "formalization_bridge_support_helper_name"
                    ] = helper_name
                    if helper_node_id:
                        node_metadata[
                            "formalization_bridge_support_helper_node_id"
                        ] = helper_node_id
                    node_metadata["formalization_bridge_support_source_hash"] = (
                        helper_record.source_hash
                    )
                    node_metadata["formalization_bridge_support_statement"] = (
                        formal_statement
                    )
                    support_recorded = bool(
                        (
                            helper_node_id,
                            helper_name,
                            helper_record.source_hash,
                            formal_statement,
                        )
                        != (
                            prior_support_helper_node_id,
                            prior_support_helper_name,
                            prior_support_source_hash,
                            prior_support_statement,
                        )
                    )
                    if helper_node_id:
                        try:
                            graph.add_edge(
                                helper_node_id,
                                node.node_id,
                                "supports",
                            )
                            graph.add_edge(
                                node.node_id,
                                helper_node_id,
                                "formalization_bridge_support",
                            )
                        except Exception:
                            pass
            bridge_metadata = (
                dict(getattr(node, "metadata", {}) or {}) if node is not None else {}
            )
            if graph is not None and node is not None and helper_node_id:
                node_metadata = getattr(node, "metadata", None)
                if isinstance(node_metadata, dict):
                    node_metadata[
                        "formalization_bridge_support_helper_name"
                    ] = helper_name
                    node_metadata[
                        "formalization_bridge_support_helper_node_id"
                    ] = helper_node_id
            parent_work_materialized = bool(
                bridge_metadata.get("formalization_bridge_parent_work_materialized")
            )
            parent_work_missing = bool(
                bridge_metadata.get("formalization_bridge_parent_work_missing")
            )
            parent_assembly_scheduled = bool(
                bridge_metadata.get("formalization_bridge_parent_work_type")
                == "assemble_route"
            )
            bridge_support_verdict = (
                "graph_native_formalization_bridge_support_recorded"
                if support_recorded
                else "graph_native_formalization_duplicate_bridge_support_suppressed"
            )
            increment = getattr(session, "_increment_dossier_metric", None)
            if callable(increment):
                increment(
                    (
                        "mini_session_graph_formalization_bridge_support_recorded"
                        if support_recorded
                        else "mini_session_graph_formalization_duplicate_bridge_support_suppressed"
                    ),
                    1,
                )
                increment(
                    "mini_session_graph_formalization_route_support_helpers_hidden",
                    1,
                )
                if bool(bridge_status.get("requires_parent_assembly")):
                    increment(
                        "mini_session_graph_formalization_bridge_parent_assembly_required",
                        1,
                    )
                if parent_work_materialized:
                    increment(
                        "mini_session_graph_formalization_bridge_parent_work_materialized",
                        1,
                    )
                    if parent_assembly_scheduled:
                        increment(
                            "mini_session_graph_formalization_bridge_parent_assembly_scheduled",
                            1,
                        )
                elif parent_work_missing:
                    increment(
                        "mini_session_graph_formalization_bridge_parent_work_missing",
                        1,
                    )
            if graph is not None and node is not None:
                try:
                    graph.record_attempt(
                        node.node_id,
                        phase=f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
                        turn_index=phase_turn,
                        proof=candidate,
                        verdict=bridge_support_verdict,
                        error_type="formalization_bridge_parent_assembly_required",
                        metadata={
                            "selected_graph_work": dict(
                                contract.get("selected_graph_work") or {}
                            ),
                            "graph_native_goal_statement": formal_statement,
                            "graph_native_helper_name": helper_name,
                            "helper_source_hash": helper_record.source_hash,
                            "formalization_bridge_status": dict(bridge_status),
                            "support_recorded": bool(support_recorded),
                            "same_turn_dependency_helper_names": list(
                                banked_same_turn_dependency_names
                            ),
                            "formalization_bridge_parent_work_materialized": (
                                parent_work_materialized
                            ),
                            "formalization_bridge_parent_work_missing": (
                                parent_work_missing
                            ),
                            "formalization_bridge_parent_assembly_scheduled": (
                                parent_assembly_scheduled
                            ),
                        },
                    )
                except Exception:
                    pass
            dossier.record_attempt(
                phase=f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
                turn_index=phase_turn,
                proof=candidate,
                helper_names=[helper_name],
                verdict=(
                    "bridge_support_recorded"
                    if support_recorded
                    else "duplicate_bridge_support_suppressed"
                ),
                node_id=target_node_id or node_id or None,
                metadata={
                    "selected_graph_work": dict(
                        contract.get("selected_graph_work") or {}
                    ),
                    "graph_native_goal_statement": formal_statement,
                    "graph_native_helper_name": helper_name,
                    "formalization_bridge_status": dict(bridge_status),
                    "same_turn_dependency_helper_names": list(
                        banked_same_turn_dependency_names
                    ),
                    "formalization_bridge_parent_assembly_required": True,
                    "formalization_bridge_parent_work_materialized": (
                        parent_work_materialized
                    ),
                    "formalization_bridge_parent_work_missing": parent_work_missing,
                    "formalization_bridge_parent_assembly_scheduled": (
                        parent_assembly_scheduled
                    ),
                    "support_recorded": bool(support_recorded),
                },
            )
            visible_helpers_added = (
                dossier.visible_accepted_helper_names([helper_name])
                if hasattr(dossier, "visible_accepted_helper_names")
                else [helper_name]
            )
            support_progress_earned = bool(
                node is not None
                and isinstance(getattr(node, "metadata", None), dict)
                and node.metadata.get(
                    "formalization_bridge_support_progress_earned"
                )
            )
            bridge_progress = bool(support_progress_earned or visible_helpers_added)
            _emit_record(session, {
                **common_payload,
                "dossier_context_helpers": list(context_helpers),
                "replay_helpers": list(candidate_replay_helpers),
                "lean_ok": True,
                "lean_output": str(getattr(result, "output", "") or ""),
                "helper_name": helper_name,
                "helpers_added": list(visible_helpers_added),
                "hidden_route_support_helper_names": (
                    [] if visible_helpers_added else [helper_name]
                ),
                "same_turn_dependency_helper_names": list(
                    banked_same_turn_dependency_names
                ),
                "graph_native_goal_statement": formal_statement,
                "graph_native_target_node_id": target_node_id or node_id,
                "graph_native_work_type": contract.get("work_type"),
                "graph_native_formalization_contract": dict(contract),
                "formalization_bridge_status": dict(bridge_status),
                "formalization_bridge_parent_assembly_required": True,
                "formalization_bridge_parent_work_materialized": (
                    parent_work_materialized
                ),
                "formalization_bridge_parent_work_missing": parent_work_missing,
                "formalization_bridge_parent_assembly_scheduled": (
                    parent_assembly_scheduled
                ),
                "support_recorded": bool(support_recorded),
                "support_progress_earned": support_progress_earned,
                "route_support_only_helper": True,
                "proof_only_helper_support_materialized": bool(
                    contract.get("proof_only_helper_support_materialized")
                ),
                "verdict": bridge_support_verdict,
            })
            return MiniOutcome(
                action_id=action_id,
                solved=False,
                proof=None,
                helpers_added=tuple(visible_helpers_added),
                progress=bridge_progress,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "role": str(getattr(conv, "role", "") or "prove"),
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    **skeleton_route_counter_metadata,
                    "lean_verdict": bridge_support_verdict,
                    "graph_native_goal_statement": formal_statement,
                    "graph_native_target_node_id": target_node_id or node_id,
                    "graph_native_work_type": contract.get("work_type"),
                    "graph_native_formalization_contract": dict(contract),
                    "selected_graph_work": dict(
                        contract.get("selected_graph_work") or {}
                    ),
                    "graph_native_helper_name": helper_name,
                    "route_support_only_helper": True,
                    "hidden_route_support_helper_names": (
                        [] if visible_helpers_added else [helper_name]
                    ),
                    "same_turn_dependency_helper_names": list(
                        banked_same_turn_dependency_names
                    ),
                    "visible_helpers_added": list(visible_helpers_added),
                    "bridge_support_progress": bridge_progress,
                    "support_progress_earned": support_progress_earned,
                    "formalization_bridge_parent_assembly_required": True,
                    "formalization_bridge_parent_work_materialized": (
                        parent_work_materialized
                    ),
                    "formalization_bridge_parent_work_missing": parent_work_missing,
                    "formalization_bridge_parent_assembly_scheduled": (
                        parent_assembly_scheduled
                    ),
                },
            )
        target_node_id = node_id
        variant_node_id = ""
        if graph is not None and node is not None:
            node_kind = str(getattr(node, "kind", "") or "")
            if node_kind == "missing_obligation":
                old_statement = str(getattr(node, "statement", "") or "").strip()
                if old_statement and old_statement != formal_statement:
                    node.metadata.setdefault(
                        "pre_formalization_statement",
                        old_statement,
                    )
                node.statement = formal_statement
                node.metadata["formalization_required"] = False
                node.metadata["formalized_by_helper_name"] = helper_name
                node.metadata["formalized_statement"] = formal_statement
                # The placeholder may predate the current Lean environment or
                # carry no environment stamp at all.  This exact declaration
                # was just replay-checked in the dossier's current context;
                # bind the now-executable node to that same context before the
                # helper-certification gate compares their receipts.
                node.metadata.update(dossier.statement_environment_metadata())
                helper_node_id = graph.helper_name_to_node_id.get(helper_name, "")
                graph.mark_obligation_proved_by_helper(
                    node.node_id,
                    helper_node_id,
                    source_hash=helper_record.source_hash,
                    proof_hash=helper_record.source_hash,
                    support_names=candidate_support_names,
                )
                if parent_closure_checked:
                    if (
                        parent_target_binding_admitted
                        and parent_obligation is not None
                        and parent_obligation is not node
                        and parent_obligation.kind == "missing_obligation"
                    ):
                        prior_parent_statement = str(
                            parent_obligation.statement or ""
                        ).strip()
                        if (
                            prior_parent_statement
                            and prior_parent_statement != formal_statement
                        ):
                            parent_obligation.metadata.setdefault(
                                "pre_formalization_statement",
                                prior_parent_statement,
                            )
                        parent_obligation.statement = formal_statement
                        parent_obligation.metadata.update(
                            dossier.statement_environment_metadata()
                        )
                        parent_obligation.metadata[
                            "formalization_required"
                        ] = False
                        parent_obligation.metadata[
                            "formalized_by_helper_name"
                        ] = helper_name
                        parent_obligation.metadata[
                            "formalized_statement"
                        ] = formal_statement
                        graph.mark_obligation_proved_by_helper(
                            parent_obligation.node_id,
                            helper_node_id,
                            source_hash=helper_record.source_hash,
                            proof_hash=helper_record.source_hash,
                            support_names=candidate_support_names,
                        )
                    closure_nodes_proved = bool(
                        parent_target_binding_admitted
                        and node.status == "proved"
                        and (
                            parent_obligation is None
                            or parent_obligation.status == "proved"
                        )
                    )
                    retire_open_premises = getattr(
                        graph,
                        "retire_formalization_bridge_open_premises",
                        None,
                    )
                    retired_open_premise_ids = (
                        list(
                            retire_open_premises(
                                parent_obligation_id,
                                reason=(
                                    "lean_verified_parent_target_closure"
                                ),
                            )
                            or []
                        )
                        if closure_nodes_proved
                        and callable(retire_open_premises)
                        else []
                    )
                    bridge_status = {
                        **dict(bridge_status),
                        "parent_target_closure_graph_admitted": (
                            closure_nodes_proved
                        ),
                        "retired_bridge_open_premise_node_ids": (
                            retired_open_premise_ids
                        ),
                    }
            elif node_kind == "proposed_claim":
                variant = graph.record_formal_variant(
                    claim_node_id=node.node_id,
                    claim_name=str(getattr(node, "name", "") or ""),
                    statement=formal_statement,
                    variant_name=helper_name,
                    source="graph_native_formalization_helper",
                    phase=f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
                    turn_index=phase_turn,
                    variant_key=f"{node.node_id}:{formal_statement}",
                    metadata={
                        "formalized_by_helper_name": helper_name,
                        **dossier.statement_environment_metadata(),
                        "selected_graph_work": dict(
                            contract.get("selected_graph_work") or {}
                        ),
                    },
                )
                variant_node_id = variant.node_id
                target_node_id = variant.node_id
                helper_node_id = graph.helper_name_to_node_id.get(helper_name, "")
                graph.mark_variant_proved_by_helper(
                    variant.node_id,
                    helper_node_id,
                    source_hash=helper_record.source_hash,
                    proof_hash=helper_record.source_hash,
                    support_names=candidate_support_names,
                )
            elif node_kind == "formal_variant":
                helper_node_id = graph.helper_name_to_node_id.get(helper_name, "")
                graph.mark_variant_proved_by_helper(
                    node.node_id,
                    helper_node_id,
                    source_hash=helper_record.source_hash,
                    proof_hash=helper_record.source_hash,
                    support_names=candidate_support_names,
                )
            dossier.record_attempt(
                phase=f"{getattr(conv, 'role', 'prove')}_graph_native_formalization",
                turn_index=phase_turn,
                proof=candidate,
                helper_names=[helper_name],
                verdict="proved",
                node_id=target_node_id or node_id or None,
                metadata={
                    "selected_graph_work": dict(
                        contract.get("selected_graph_work") or {}
                    ),
                    "graph_native_goal_statement": formal_statement,
                    "graph_native_helper_name": helper_name,
                    "formalization_bridge_status": dict(bridge_status),
                    "same_turn_dependency_helper_names": list(
                        banked_same_turn_dependency_names
                    ),
                    "formalized_variant_node_id": variant_node_id,
                },
            )
        visible_helpers_added = (
            dossier.visible_accepted_helper_names([helper_name])
            if hasattr(dossier, "visible_accepted_helper_names")
            else [helper_name]
        )
        _emit_record(session, {
            **common_payload,
            "dossier_context_helpers": list(context_helpers),
            "replay_helpers": list(candidate_replay_helpers),
            "lean_ok": True,
            "lean_output": str(getattr(result, "output", "") or ""),
            "helper_name": helper_name,
            "helpers_added": list(visible_helpers_added),
            "same_turn_dependency_helper_names": list(
                banked_same_turn_dependency_names
            ),
            "graph_native_goal_statement": formal_statement,
            "graph_native_target_node_id": target_node_id or node_id,
            "graph_native_work_type": contract.get("work_type"),
            "graph_native_formalization_contract": dict(contract),
            "formalization_bridge_status": dict(bridge_status),
            "verdict": "graph_native_formalization_proved",
        })
        return MiniOutcome(
            action_id=action_id,
            solved=False,
            proof=None,
            helpers_added=tuple(visible_helpers_added),
            progress=True,
            cost_seconds=time.monotonic() - started,
            metadata={
                "role": str(getattr(conv, "role", "") or "prove"),
                "conv_turn_index_offset": conv_turn_offset,
                "conv_turn_index_absolute": absolute_turn,
                "conv_turn_index_phase": phase_turn,
                **_turn_budget_metadata(common_payload),
                **skeleton_route_counter_metadata,
                "lean_verdict": "graph_native_formalization_accepted",
                "graph_native_goal_statement": formal_statement,
                "graph_native_target_node_id": target_node_id or node_id,
                "graph_native_work_type": contract.get("work_type"),
                "graph_native_formalization_contract": dict(contract),
                "selected_graph_work": dict(
                    contract.get("selected_graph_work") or {}
                ),
                "graph_native_helper_name": helper_name,
                "formalization_bridge_status": dict(bridge_status),
                "same_turn_dependency_helper_names": list(
                    banked_same_turn_dependency_names
                ),
                "visible_helpers_added": list(visible_helpers_added),
            },
        )

    feedback = _formalization_helper_feedback(
        last_failure,
        contract=contract,
        bridge_status=last_bridge_status,
        rejected_statement=last_rejected_statement,
    )
    try:
        conv.append_user(feedback)
    except Exception:
        pass
    _emit_record(session, {
        **common_payload,
        "rejection_reason": "formalization_helper_declaration_rejected",
        "lean_error_type": "formalization_helper_declaration_rejected",
        "graph_native_formalization_contract": dict(contract),
        "formalization_bridge_status": dict(last_bridge_status),
        "lean_output": last_failure,
        "banked_proposed_helpers": list(banked_rejected_candidate_names),
        "formalization_rejected_helpers_banked_proposed": list(
            banked_rejected_candidate_names
        ),
        "verdict": "lean_rejected",
    })
    return MiniOutcome(
        action_id=action_id,
        solved=False,
        proof=None,
        helpers_added=(),
        progress=bool(skeleton_route_banked),
        cost_seconds=time.monotonic() - started,
        metadata={
            "role": str(getattr(conv, "role", "") or "prove"),
            "conv_turn_index_offset": conv_turn_offset,
            "conv_turn_index_absolute": absolute_turn,
            "conv_turn_index_phase": phase_turn,
            **_turn_budget_metadata(common_payload),
            "lean_verdict": "formalization_helper_declaration_rejected",
            "lean_error": last_failure,
            "graph_native_formalization_contract": dict(contract),
            "formalization_bridge_status": dict(last_bridge_status),
            "banked_proposed_helpers": list(banked_rejected_candidate_names),
            "formalization_rejected_helpers_banked_proposed": list(
                banked_rejected_candidate_names
            ),
            **skeleton_route_metadata,
        },
    )


def _proof_only_auxiliary_bridge_contract(session: Any) -> Dict[str, Any]:
    """Plan scoped auxiliary bridge work for proof-only helper replies."""

    record = getattr(session, "selected_work_item_record", None)
    if not isinstance(record, dict):
        return {}
    item_record = dict(
        getattr(getattr(session, "selected_work_item", None), "graph_record", None)
        or {}
    )
    graph_record = dict(record.get("graph_record") or {})
    merged = {**graph_record, **item_record, **record}
    if _selected_work_terminal_graph_target_suppressed(
        session,
        merged,
        context="proof_only_helper_support_materialization",
        metric_key="mini_session_retired_graph_target_formalization_suppressed",
    ):
        return {}
    work_type = str(merged.get("work_type") or "").strip()
    allowed_work_types = {
        "root_repair",
        "formalize_missing_obligation",
        "mine_missing_obligation",
    }
    if work_type not in allowed_work_types:
        return {}
    if str(merged.get("mapped_action_id") or "").strip() not in {
        "",
        "conversation_turn_prove",
        "conversation_turn_refine",
        "conversation_turn",
    }:
        return {}
    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    if graph is None or not isinstance(nodes, dict):
        return {}
    raw_source_node_id = str(
        merged.get("graph_node_id") or merged.get("node_id") or ""
    ).strip()
    source_node = nodes.get(raw_source_node_id)
    if source_node is None:
        if work_type != "root_repair":
            return {}
        raw_source_node_id = str(getattr(graph, "root_node_id", "") or "").strip()
        source_node = nodes.get(raw_source_node_id)
    source_metadata = (
        dict(getattr(source_node, "metadata", {}) or {})
        if source_node is not None
        else {}
    )
    parent_statement = str(
        merged.get("formalization_bridge_parent_statement")
        or merged.get("parent_repair_target_statement")
        or source_metadata.get("formalization_bridge_parent_statement")
        or source_metadata.get("parent_repair_target_statement")
        or (
            merged.get("target_statement")
            if work_type == "root_repair"
            else ""
        )
        or getattr(getattr(session, "conv", None), "goal_statement", "")
        or getattr(getattr(session, "dossier", None), "root_statement", "")
        or ""
    ).strip()
    if not parent_statement:
        return {}
    if source_node is not None:
        source_status = str(getattr(source_node, "status", "") or "").strip()
        is_tombstone = getattr(graph, "is_superseded_tombstone", None)
        if (
            source_status in {"failed", "rejected", "obsolete", "superseded"}
            or bool(
                source_metadata.get("route_retired")
                or source_metadata.get("route_dependency_contradicted")
                or source_metadata.get("proposal_invalidated")
            )
            or (callable(is_tombstone) and bool(is_tombstone(source_node)))
            ):
            return {}
        route_id = str(
            merged.get("route_id") or source_metadata.get("route_id") or ""
        ).strip()
        route_poisoned = getattr(graph, "_route_is_terminally_poisoned", None)
        if route_id:
            route_node = nodes.get(route_id)
            route_metadata = (
                dict(getattr(route_node, "metadata", {}) or {})
                if route_node is not None
                else {}
            )
            route_status = str(getattr(route_node, "status", "") or "").strip()
            if (
                route_node is None
                or route_status in {"failed", "obsolete", "superseded"}
                or bool(
                    route_metadata.get("route_retired")
                    or route_metadata.get("route_dependency_contradicted")
                    or route_metadata.get("proposal_invalidated")
                )
                or (callable(is_tombstone) and bool(is_tombstone(route_node)))
                or (callable(route_poisoned) and bool(route_poisoned(route_id)))
            ):
                return {}
    signature = hashlib.sha256(
        parent_statement.encode("utf-8", errors="replace")
    ).hexdigest()[:16]
    source_node_id = str(raw_source_node_id or getattr(graph, "root_node_id", "") or "")
    selected_graph_work = {
        **dict(merged),
        "proof_only_helper_support_selected_work_type": work_type,
        "work_type": "formalize_missing_obligation",
        "formalization_required": True,
        "materialization_required": True,
        "formalization_statement_pending": True,
        "formalization_bridge_contract": "auxiliary_bridge_support",
        "formalization_bridge_parent_statement": parent_statement,
        "parent_repair_target_statement": parent_statement,
        "auxiliary_bridge_parent_assembly_required": True,
        "auxiliary_bridge_allow_non_root_parent_assembly": True,
        "proof_only_helper_support_deferred_materialization": True,
        "proof_only_helper_support_parent_signature": signature,
        "source_node_id": source_node_id,
    }
    return {
        "work_type": "formalize_missing_obligation",
        "node_id": "",
        "target_statement": "",
        "node_kind": "missing_obligation",
        "name": "",
        "selected_graph_work": selected_graph_work,
        "formalization_bridge_contract": "auxiliary_bridge_support",
        "formalization_bridge_parent_statement": parent_statement,
        "proof_only_helper_support_deferred_materialization": True,
        "proof_only_helper_support_parent_signature": signature,
        "proof_only_helper_support_source_node_id": source_node_id,
        "proof_only_helper_support_selected_work_type": work_type,
    }


def _materialize_proof_only_auxiliary_bridge_contract(
    session: Any,
    contract: Dict[str, Any],
    *,
    formal_statement: str,
    phase_turn: int,
) -> Dict[str, Any]:
    """Create graph work for accepted proof-only auxiliary support."""

    dossier = getattr(session, "dossier", None)
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    if graph is None:
        return {}
    parent_statement = str(
        contract.get("formalization_bridge_parent_statement") or ""
    ).strip()
    if not parent_statement:
        return {}
    parent_signature = str(
        contract.get("proof_only_helper_support_parent_signature") or ""
    ).strip()
    if not parent_signature:
        parent_signature = hashlib.sha256(
            parent_statement.encode("utf-8", errors="replace")
        ).hexdigest()[:16]
    source_node_id = str(
        contract.get("proof_only_helper_support_source_node_id")
        or getattr(graph, "root_node_id", "")
        or ""
    ).strip()
    if source_node_id not in getattr(graph, "nodes", {}):
        source_node_id = str(getattr(graph, "root_node_id", "") or "").strip()
    statement_signature = hashlib.sha256(
        str(formal_statement or "").encode("utf-8", errors="replace")
    ).hexdigest()[:16]
    route = graph.record_strategy_route(
        name=f"proof_only_helper_support_{parent_signature}",
        description=(
            "Assemble accepted proof-only auxiliary helper support back into "
            "the active parent repair target."
        ),
        route_key=(
            "proof_only_helper_support:"
            + source_node_id
            + ":"
            + parent_signature
        ),
        score=0.4,
        phase=f"{getattr(getattr(session, 'conv', None), 'role', 'prove')}_proof_only_helper_support",
        turn_index=phase_turn,
        metadata={
            "route_scope": "partial_route",
            "source": "proof_only_helper_support",
            "proof_only_helper_support_parent_signature": parent_signature,
            "proof_only_helper_support_statement_signature": statement_signature,
            "formalization_bridge_contract": "auxiliary_bridge_support",
            "formalization_bridge_parent_statement": parent_statement,
            "parent_repair_target_statement": parent_statement,
            "auxiliary_bridge_allow_non_root_parent_assembly": True,
        },
    )
    obligation_reason = (
        "Use the accepted Lean-checked auxiliary helper as support, then "
        "assemble it back into the active parent repair target."
    )
    obligation_statement = (
        "Accepted proof-only auxiliary bridge support "
        f"{statement_signature} for parent repair target {parent_signature}; "
        "assemble the helper support back to the parent target."
    )
    identity_key = ":".join(
        item
        for item in [
            "proof_only_helper_support",
            source_node_id,
            parent_signature,
        ]
        if item
    )
    obligation = graph.record_missing_obligation(
        statement=obligation_statement,
        reason=obligation_reason,
        source_node_id=source_node_id,
        route_id=route.node_id,
        phase=f"{getattr(getattr(session, 'conv', None), 'role', 'prove')}_proof_only_helper_support",
        turn_index=phase_turn,
        error_type="proof_only_helper_support_requires_parent_assembly",
        metadata={
            "source": "proof_only_helper_support",
            "identity_key": identity_key,
            "formalization_required": True,
            "materialization_required": True,
            "formalization_statement_pending": True,
            "formalization_bridge_contract": "auxiliary_bridge_support",
            "formalization_bridge_parent_statement": parent_statement,
            "parent_repair_target_statement": parent_statement,
            "auxiliary_bridge_parent_assembly_required": True,
            "auxiliary_bridge_allow_non_root_parent_assembly": True,
            "proof_only_helper_support_materialized": True,
            "proof_only_helper_support_parent_signature": parent_signature,
            "proof_only_helper_support_statement_signature": statement_signature,
            **session.dossier.statement_environment_metadata(),
        },
    )
    replan = graph.record_replan_item(
        source_node_id=source_node_id,
        route_id=route.node_id,
        obligation_id=obligation.node_id,
        reason=obligation_reason,
        phase=f"{getattr(getattr(session, 'conv', None), 'role', 'prove')}_proof_only_helper_support",
        turn_index=phase_turn,
        priority=0.75,
        metadata={
            "source": "proof_only_helper_support",
            "target_statement": parent_statement,
            "materialization_seed": obligation_statement,
            "formalization_required": True,
            "materialization_required": True,
            "formalization_statement_pending": True,
            "formalization_bridge_contract": "auxiliary_bridge_support",
            "formalization_bridge_parent_statement": parent_statement,
            "parent_repair_target_statement": parent_statement,
            "auxiliary_bridge_parent_assembly_required": True,
            "auxiliary_bridge_allow_non_root_parent_assembly": True,
            "route_replan_requires_obligation": True,
            "proof_only_helper_support_materialized": True,
            "proof_only_helper_support_parent_signature": parent_signature,
        },
    )
    replan.metadata["schedulable"] = False
    selected_graph_work = {
        **dict(contract.get("selected_graph_work") or {}),
        "work_type": "formalize_missing_obligation",
        "node_id": obligation.node_id,
        "graph_node_id": obligation.node_id,
        "obligation_id": obligation.node_id,
        "route_id": route.node_id,
        "replan_id": replan.node_id,
        "formalization_required": True,
        "materialization_required": True,
        "formalization_statement_pending": True,
        "materialization_seed": obligation_statement,
        "formalization_bridge_contract": "auxiliary_bridge_support",
        "formalization_bridge_parent_statement": parent_statement,
        "parent_repair_target_statement": parent_statement,
        "auxiliary_bridge_parent_assembly_required": True,
        "auxiliary_bridge_allow_non_root_parent_assembly": True,
        "proof_only_helper_support_materialized": True,
    }
    recorder = getattr(session, "_record_event", None)
    if callable(recorder):
        recorder({
            "phase": f"{getattr(getattr(session, 'conv', None), 'role', 'prove')}_proof_only_helper_support",
            "iteration": int(getattr(session, "iteration", 0) or 0),
            "route_id": route.node_id,
            "obligation_id": obligation.node_id,
            "replan_id": replan.node_id,
            "parent_statement": parent_statement,
            "helper_statement": str(formal_statement or ""),
            "verdict": "proof_only_helper_support_work_materialized",
        })
    return {
        **dict(contract),
        "node_id": obligation.node_id,
        "target_statement": obligation.statement,
        "name": obligation.name,
        "selected_graph_work": selected_graph_work,
        "proof_only_helper_support_materialized": True,
    }


async def _try_materialize_proof_only_helper_support(
    *,
    session: Any,
    action_id: str,
    conv: Any,
    lean: Any,
    dossier: Any,
    helpers: Sequence[str],
    lemma_dag_candidates: Sequence[str],
    context_helpers: Sequence[str],
    common_payload: Dict[str, Any],
    phase_turn: int,
    conv_turn_offset: int,
    absolute_turn: int,
    started: float,
    publication_guard: Optional[Callable[[], None]] = None,
) -> Optional[MiniOutcome]:
    candidates = _formalization_helper_candidates(helpers, lemma_dag_candidates)
    if not candidates:
        return None
    contract = _proof_only_auxiliary_bridge_contract(session)
    if not contract:
        return None
    _emit_record(session, {
        **common_payload,
        "candidate_count": len(candidates),
        "graph_native_formalization_contract": dict(contract),
        "verdict": "proof_only_helper_support_materialization_attempt",
    })
    outcome = await _run_graph_native_formalization_helper_contract(
        session=session,
        action_id=action_id,
        conv=conv,
        lean=lean,
        dossier=dossier,
        contract=contract,
        helpers=candidates,
        lemma_dag_candidates=(),
        context_helpers=context_helpers,
        common_payload={
            **common_payload,
            "proof_only_helper_support_attempted": True,
        },
        phase_turn=phase_turn,
        conv_turn_offset=conv_turn_offset,
        absolute_turn=absolute_turn,
        started=started,
        publication_guard=publication_guard,
    )
    outcome_metadata = dict(outcome.metadata or {})
    support_admitted = bool(
        outcome_metadata.get("route_support_only_helper")
        and str(outcome_metadata.get("lean_verdict") or "")
        in {
            "graph_native_formalization_bridge_support_recorded",
            "graph_native_formalization_duplicate_bridge_support_suppressed",
        }
    )
    if support_admitted:
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment("mini_session_proof_only_helper_support_materialized", 1)
        return replace(
            outcome,
            metadata={
                **outcome_metadata,
                "proof_only_helper_support_materialized": True,
                "proof_only_helper_support_rejected": False,
            },
        )
    increment = getattr(session, "_increment_dossier_metric", None)
    if callable(increment):
        increment("mini_session_proof_only_helper_support_rejected", 1)
    return replace(
        outcome,
        metadata={
            **dict(outcome.metadata or {}),
            "proof_only_helper_support_attempted": True,
            "proof_only_helper_support_rejected": True,
        },
    )


def _graph_native_helper_name(
    *,
    theorem_name: str,
    node_id: str,
    node_name: str,
    work_type: str,
) -> str:
    base = re.sub(r"[^A-Za-z0-9_]+", "_", str(node_name or "").strip()).strip("_")
    if not base:
        base = re.sub(r"[^A-Za-z0-9_]+", "_", str(work_type or "graph").strip()).strip("_")
    if not base:
        base = "graph_claim"
    if base and base[0].isdigit():
        base = f"h_{base}"
    root_name = re.sub(r"[^A-Za-z0-9_]+", "_", str(theorem_name or "t").strip()).strip("_")
    digest = hashlib.sha256(str(node_id or base).encode("utf-8", errors="replace")).hexdigest()[:12]
    prefix = f"{root_name}_graph" if root_name else "graph"
    return f"{prefix}_{base}_{digest}"


def _graph_native_helper_source(
    *,
    helper_name: str,
    statement: str,
    proof: str,
) -> str:
    body = str(proof or "").strip()
    indented = "\n".join(
        f"  {line}" if line.strip() else ""
        for line in body.splitlines()
    )
    return f"lemma {helper_name} : {str(statement or '').strip()} :=\n{indented}"


def _should_defer_post_failure_search(
    *,
    proof: str,
    helpers: Sequence[str],
    lemma_dag_candidate_helpers: Sequence[str],
    proof_state: Any,
    proof_state_child_tactics_enabled: bool,
    proof_state_child_tactic_timeout_s: float,
    proof_state_child_tactic_max_candidates: int,
    proof_state_decl_application_limit: int,
    phase_turn: int,
    max_turns: int,
    graph_native_failure_context: bool = False,
    repair_self_check_status: str = "",
    giveup_cluster: str = "",
) -> bool:
    """Return whether the next LLM repair turn should precede graph search."""

    if proof_state is None or graph_native_failure_context:
        return False
    if not proof or helpers or lemma_dag_candidate_helpers:
        return False
    if not bool(proof_state_child_tactics_enabled):
        return False
    if int(max_turns or 0) > 0 and int(phase_turn or 0) >= int(max_turns or 0):
        return False
    if str(giveup_cluster or "").strip():
        return False
    repair_status = str(repair_self_check_status or "").strip()
    if repair_status in {
        "helper_only_decomposition",
        "no_accepted_try_lean",
        "tool_budget_exhausted",
    }:
        return False
    expensive_budget_enabled = (
        float(proof_state_child_tactic_timeout_s or 0.0) > 0.0
        and (
            int(proof_state_child_tactic_max_candidates or 0) > 0
            or int(proof_state_decl_application_limit or 0) > 0
        )
    )
    return bool(expensive_budget_enabled)


def _lean_failure_wall_signature(failure_analysis: Dict[str, Any]) -> str:
    """Stable fingerprint for repeated Lean walls, insensitive to proof prose."""

    error_type = str((failure_analysis or {}).get("error_type") or "").strip()
    if not error_type:
        return ""
    details = dict((failure_analysis or {}).get("details") or {})
    remaining_goals = [
        item
        for item in list((failure_analysis or {}).get("remaining_goals") or [])
        if isinstance(item, dict)
    ]
    target = ""
    if remaining_goals:
        first = remaining_goals[0]
        target = " ".join(str(first.get("target") or "").split())[:500]
    if not target:
        for key in ("target", "expected", "term", "message", "first_line"):
            value = " ".join(str(details.get(key) or "").split())
            if value:
                target = value[:500]
                break
    if not target:
        for diag in list((failure_analysis or {}).get("diagnostics") or []):
            if not isinstance(diag, dict):
                continue
            value = " ".join(
                str(diag.get("summary") or diag.get("message") or "").split()
            )
            if value:
                target = value[:500]
                break
    if not target:
        target = " ".join(
            str((failure_analysis or {}).get("diagnostic_search_text") or "").split()
        )[:500]
    payload = f"{error_type}|{target}"
    return hashlib.sha256(payload.encode("utf-8", errors="replace")).hexdigest()[:16]


class ConversationTurnAction:
    id: str = "conversation_turn"
    priority: int = 50
    cost_estimate_s: float = 30.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state", "conv"})
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "_answer_safe_recheck_pending",
            "_answer_safe_recheck_parked",
            "_answer_safe_recheck_held_terminal_provider_failure",
        }
    )
    _ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION: ClassVar[int] = 6
    _ANSWER_SAFE_RECHECK_MAX_PARKED: ClassVar[int] = 8
    _ANSWER_SAFE_RECHECK_MAX_CONTENT_CHARS: ClassVar[int] = 250_000
    _ANSWER_SAFE_RECHECK_MAX_STATE_CHARS: ClassVar[int] = 2_000_000
    _PROVIDER_QUANTUM_CHECKPOINT_MAX_STATE_CHARS: ClassVar[int] = 500_000
    _PROVIDER_QUANTUM_CHECKPOINT_MAX_HISTORY_CHARS: ClassVar[int] = 1_500_000
    _PROVIDER_QUANTUM_CHECKPOINT_MAX_HISTORY_MESSAGES: ClassVar[int] = 128
    _PROVIDER_QUANTUM_CHECKPOINT_MAX_BINDING_CHARS: ClassVar[int] = 300_000
    _PROVIDER_QUANTUM_CHECKPOINT_MAX_TARGET_CHARS: ClassVar[int] = 1_000_000
    _PROVIDER_QUANTUM_CHECKPOINT_MAX_LEGACY_BINDING_CHARS: ClassVar[int] = (
        4_000_000
    )
    _PROVIDER_QUANTUM_TARGET_ALIASES_KEY: ClassVar[str] = (
        "_provider_quantum_target_aliases"
    )
    _PROVIDER_QUANTUM_SELECTED_WORK_WRAPPER_KEYS: ClassVar[Tuple[str, ...]] = (
        "graph_record",
        "metadata",
        "selected_work",
        "selected_work_item",
    )
    _PROVIDER_QUANTUM_SELECTED_WORK_MAX_LAYERS: ClassVar[int] = 32
    _PROVIDER_QUANTUM_STATE_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "schema_version",
            "provider_turn_lane_identity",
            "provider_chain_resume_target_id",
            "invalid_prompt_neutralization_pending",
            "tool_calls_used",
            "seen_tool_call_signatures",
            "max_tool_calls_per_turn",
            "repair_discovery_tool_calls_used",
            "repair_verification_tool_calls_used",
            "repair_discovery_quota_exhausted",
            "repair_self_check_required",
            "repair_self_check_seen",
            "repair_self_check_attempted",
            "repair_self_check_status",
            "repair_self_check_codes",
            "repair_self_check_reminder_sent",
            "repair_self_check_final_slot_recovery_reminder_sent",
            "pending_tool_replay",
            "pending_tool_replay_is_paid_retry",
            "pending_tool_replay_disposition",
            "durable_progress_tool_continuation_identity",
            "durable_progress_tool_continuation_role",
            "durable_progress_tool_continuation_target",
            "durable_progress_tool_continuation_helper_receipts",
            "tool_infrastructure_receipt_id",
            "tool_infrastructure_disposition",
            "deepseek_dsml_reprompted_after_budget",
            "final_no_tools_policy_reprompted",
            "force_finalize_without_tools",
            "final_no_tools_recovery_attempted",
            "final_no_tools_visibility_recovery_pending",
            "repeat_guidance_used",
            "repeat_recovery_pending",
            "tool_repeat_detected",
            "tool_repeat_action",
            "tool_repeat_signature",
            "proof_tool_attempts",
            "consecutive_no_formal_progress",
            "consecutive_search_tool_calls",
            "semantic_result_counts",
            "semantic_no_progress_detected",
            "semantic_no_progress_reason",
            "semantic_no_progress_signature",
            "semantic_diagnostic_progress_count",
            "semantic_diagnostic_best_phase",
            "semantic_diagnostic_best_error_kind",
            "semantic_diagnostic_best_goal_count",
            "semantic_diagnostic_last_reason",
            "semantic_diagnostic_best_signature",
            "semantic_diagnostic_best_by_tool",
            "partial_try_lean_promotions",
            "banked_mixed_final_content",
            "banked_mixed_finalizer_pending",
            "banked_mixed_finalizer_lane_identity",
            "provider_call_cumulative_elapsed_s",
            "provider_call_cumulative_wall_cap_s",
            "provider_call_cumulative_deadline_monotonic",
            "provider_call_cumulative_wall_exhausted",
        }
    )
    _PROVIDER_QUANTUM_BOOL_STATE_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "repair_discovery_quota_exhausted",
            "repair_self_check_required",
            "repair_self_check_seen",
            "repair_self_check_attempted",
            "repair_self_check_reminder_sent",
            "repair_self_check_final_slot_recovery_reminder_sent",
            "pending_tool_replay_is_paid_retry",
            "deepseek_dsml_reprompted_after_budget",
            "final_no_tools_policy_reprompted",
            "force_finalize_without_tools",
            "final_no_tools_recovery_attempted",
            "final_no_tools_visibility_recovery_pending",
            "repeat_guidance_used",
            "repeat_recovery_pending",
            "tool_repeat_detected",
            "semantic_no_progress_detected",
            "banked_mixed_finalizer_pending",
            "provider_call_cumulative_wall_exhausted",
            "invalid_prompt_neutralization_pending",
        }
    )
    _PROVIDER_QUANTUM_INT_STATE_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "schema_version",
            "tool_calls_used",
            "max_tool_calls_per_turn",
            "repair_discovery_tool_calls_used",
            "repair_verification_tool_calls_used",
            "proof_tool_attempts",
            "consecutive_no_formal_progress",
            "consecutive_search_tool_calls",
            "semantic_diagnostic_progress_count",
            "semantic_diagnostic_best_phase",
            "semantic_diagnostic_best_goal_count",
            "partial_try_lean_promotions",
        }
    )
    _PROVIDER_QUANTUM_FLOAT_STATE_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "provider_call_cumulative_elapsed_s",
            "provider_call_cumulative_wall_cap_s",
            "provider_call_cumulative_deadline_monotonic",
        }
    )
    _PROVIDER_QUANTUM_STRING_STATE_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "provider_turn_lane_identity",
            "provider_chain_resume_target_id",
            "repair_self_check_status",
            "pending_tool_replay_disposition",
            "durable_progress_tool_continuation_identity",
            "durable_progress_tool_continuation_role",
            "durable_progress_tool_continuation_target",
            "tool_infrastructure_receipt_id",
            "tool_infrastructure_disposition",
            "tool_repeat_action",
            "tool_repeat_signature",
            "semantic_no_progress_reason",
            "semantic_no_progress_signature",
            "semantic_diagnostic_best_error_kind",
            "semantic_diagnostic_last_reason",
            "semantic_diagnostic_best_signature",
            "banked_mixed_final_content",
            "banked_mixed_finalizer_lane_identity",
        }
    )
    _ANSWER_SAFE_RECHECK_PENDING_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "active",
            "role",
            "content",
            "sent_messages",
            "proof",
            "goal_statement_override",
            "primary_accepted",
            "execution_binding",
            "conv_turn_offset",
            "phase_turn",
            "turn_entry",
            "recovery_attempts",
            "recovered_finalizer_receipt",
            "selected_work_record",
            "verification_check_lemmas",
            "verification_context_helpers",
            "verification_helpers",
            "fallback_verification_check_lemmas",
            "fallback_verification_context_helpers",
            "fallback_verification_helpers",
        }
    )
    _ANSWER_SAFE_RECHECK_BINDING_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "graph_node_id",
            "graph_work_type",
            "graph_statement",
            "graph_scope_key",
            "selected_node_id",
            "selected_variant_id",
            "selected_work_type",
            "selected_mapped_action",
            "selected_context_digest",
            "root_statement",
            "conversation_goal_statement",
            "lean_preamble",
            "prompt_preamble",
            "active_root_targets",
        }
    )
    _ANSWER_SAFE_RECHECK_EXACT_VERIFICATION_KEYS: ClassVar[FrozenSet[str]] = (
        frozenset(
            {
                "verification_check_lemmas",
                "verification_context_helpers",
                "verification_helpers",
                "fallback_verification_check_lemmas",
                "fallback_verification_context_helpers",
                "fallback_verification_helpers",
            }
        )
    )
    _ANSWER_SAFE_RECHECK_TURN_ENTRY_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "history",
            "role",
            "graph_last_scope_key",
            "last_premise_block",
            "last_premise_names",
            "last_premise_block_injected",
        }
    )
    _ANSWER_SAFE_RECHECK_RECEIPT_KEYS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "final_no_tools_event",
            "final_no_tools_finish_reason",
            "final_no_tools_reasoning_content_chars",
            "final_no_tools_used_accepted_proof",
            "provider_calls_completed",
            "provider_dispatches_started",
            "provider_call_cumulative_elapsed_s",
            "provider_call_cumulative_wall_cap_s",
            "provider_call_cumulative_wall_exhausted",
            "recovered_finalizer_error",
            "recovered_finalizer_failure_kind",
            "recovered_finalizer_retryable",
            "recovered_finalizer_provider_call_quantum_exhausted",
            "recovered_finalizer_terminal",
            "recovered_finalizer_failure_reason",
            "recovered_finalizer_retry_deadline",
            "recovered_finalizer_provider_attempts",
            "recovered_finalizer_provider_defer",
        }
    )
    _ANSWER_SAFE_RECHECK_HELD_TERMINAL_KEYS: ClassVar[FrozenSet[str]] = (
        frozenset(
            {
                "llm_error",
                "llm_failure_kind",
                "terminal_failure_reason",
                "provider_turn_lane_identity",
            }
        )
    )
    _ANSWER_SAFE_RECHECK_PROVIDER_DEFER_KEYS: ClassVar[FrozenSet[str]] = (
        frozenset(
            {
                "provider_defer_fingerprint",
                "provider_defer_ready_at",
                "provider_defer_retry_after_s",
            }
        )
    )
    _ANSWER_SAFE_RECHECK_RETRY_DEADLINE_BOOL_KEYS: ClassVar[
        FrozenSet[str]
    ] = frozenset({"llm_retry_deadline_exhausted"})
    _ANSWER_SAFE_RECHECK_RETRY_DEADLINE_INT_KEYS: ClassVar[
        FrozenSet[str]
    ] = frozenset(
        {
            "llm_retry_deadline_attempt",
            "llm_retry_deadline_status_code",
        }
    )
    _ANSWER_SAFE_RECHECK_RETRY_DEADLINE_STRING_KEYS: ClassVar[
        FrozenSet[str]
    ] = frozenset(
        {
            "llm_retry_deadline_reason",
            "llm_retry_deadline_model",
            "llm_retry_deadline_base_url",
            "llm_retry_deadline_policy",
            "llm_retry_deadline_original_exception_type",
            "llm_retry_deadline_original_exception_family",
            "llm_retry_deadline_original_error",
        }
    )
    _ANSWER_SAFE_RECHECK_RETRY_DEADLINE_FLOAT_KEYS: ClassVar[
        FrozenSet[str]
    ] = frozenset(
        {
            "llm_retry_deadline_retry_after_s",
            "llm_retry_deadline_retry_delay_s",
            "llm_retry_deadline_remaining_s",
            "llm_retry_deadline_request_timeout_s",
            "llm_retry_deadline_request_elapsed_s",
            "llm_retry_deadline_operation_elapsed_s",
            "llm_retry_deadline_configured_timeout_s",
            "llm_retry_deadline_operation_timeout_s",
        }
    )

    def __init__(
        self,
        *,
        role: str = "prove",
        client: Any = None,
        sample_temperature: Optional[float] = None,
        searcher_override: Optional[Any] = None,
        lean_check_tool_enabled: bool = True,
        try_lean_tool_enabled: bool = False,
        compute_examples_tool_enabled: bool = False,
        apply_decl_to_goal_tool_enabled: bool = False,
        max_tool_calls_per_turn: int = 10,
        raw_feedback: bool = False,
        repair_retrieval_enabled: bool = True,
        repair_retrieval_top_k: int = 6,
        proof_state_child_tactics_enabled: bool = True,
        proof_state_child_tactic_timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        proof_state_child_tactic_max_candidates: int = 32,
        proof_state_child_goal_limit: int = 3,
        proof_state_decl_application_limit: int = 6,
        proof_state_batch_parallelism: int = 1,
        max_turns_for_budget: int = 1,
        mini_phase_temperatures: Optional[MiniPhaseTemperatures] = None,
        llm_turn_elapsed_s: float = 0.0,
        formalization_llm_request_timeout_s: float = 0.0,
        formalization_llm_turn_elapsed_s: float = 0.0,
        provider_dispatch_limit: int = 0,
    ) -> None:
        self.role = str(role or "prove")
        self.id = f"conversation_turn_{self.role}"
        self.client = client
        self.sample_temperature = sample_temperature
        self.searcher_override = searcher_override
        self.lean_check_tool_enabled = bool(lean_check_tool_enabled)
        self.try_lean_tool_enabled = bool(try_lean_tool_enabled)
        self.compute_examples_tool_enabled = bool(compute_examples_tool_enabled)
        self.apply_decl_to_goal_tool_enabled = bool(apply_decl_to_goal_tool_enabled)
        self.max_tool_calls_per_turn = int(max_tool_calls_per_turn or 0)
        self.raw_feedback = bool(raw_feedback)
        self.repair_retrieval_enabled = bool(repair_retrieval_enabled)
        self.repair_retrieval_top_k = int(repair_retrieval_top_k or 0)
        self.proof_state_child_tactics_enabled = bool(proof_state_child_tactics_enabled)
        self.proof_state_child_tactic_timeout_s = float(proof_state_child_tactic_timeout_s or 0.0)
        self.proof_state_child_tactic_max_candidates = int(proof_state_child_tactic_max_candidates or 0)
        self.proof_state_child_goal_limit = int(proof_state_child_goal_limit or 0)
        self.proof_state_decl_application_limit = int(proof_state_decl_application_limit or 0)
        self.proof_state_batch_parallelism = int(proof_state_batch_parallelism or 1)
        self.mini_phase_temperatures = mini_phase_temperatures
        self.llm_turn_elapsed_s = float(llm_turn_elapsed_s or 0.0)
        self.formalization_llm_request_timeout_s = float(
            formalization_llm_request_timeout_s or 0.0
        )
        self.formalization_llm_turn_elapsed_s = float(
            formalization_llm_turn_elapsed_s or 0.0
        )
        self.provider_dispatch_limit = max(0, int(provider_dispatch_limit or 0))
        self._answer_safe_recheck_pending: Dict[str, Any] = {}
        self._answer_safe_recheck_parked: Dict[str, Dict[str, Any]] = {}
        self._answer_safe_recheck_held_terminal_provider_failure: Dict[
            str,
            str,
        ] = {}
        # A completed provider call may deliberately end the current action
        # at a tool boundary. Remember only the scheduler iteration that
        # earned that boundary so the next selection can try one independent
        # competitor while retaining this action as a guaranteed fallback.
        # This is ordering state, not a provider failure/cooldown.
        self._provider_quantum_yield_generation: int = 0
        self._provider_quantum_yield_consumed_generation: int = 0
        self._provider_quantum_checkpoint: Dict[str, Any] = {}
        self._provider_quantum_runtime_loaded: bool = False
        # MED-4 (2026-05-08): max_turns_for_budget represents the OUTER-
        # loop iteration count for the budget footer, NOT the always-1
        # inner-turn count. Callers (factory.py) should pass the role's
        # outer turn budget so the LLM sees "turn N of MAX". When unset,
        # fall back to ``session.max_iterations`` at run-time.
        self.max_turns_for_budget = int(max_turns_for_budget or 0)

    def _validated_answer_safe_recheck_pending_state(
        self,
        pending: Any,
        *,
        require_exact_verification_state: bool = False,
    ) -> Dict[str, Any]:
        """Return one bounded JSON-safe verifier continuation or fail closed."""

        if pending in (None, {}):
            return {}
        if not isinstance(pending, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation is malformed"
            )
        unknown_keys = set(pending) - self._ANSWER_SAFE_RECHECK_PENDING_KEYS
        if unknown_keys:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation has unsupported fields"
            )
        required_keys = self._ANSWER_SAFE_RECHECK_PENDING_KEYS - {
            "recovered_finalizer_receipt",
            "selected_work_record",
            "verification_check_lemmas",
            "verification_context_helpers",
            "verification_helpers",
            "fallback_verification_check_lemmas",
            "fallback_verification_context_helpers",
            "fallback_verification_helpers",
        }
        if not required_keys.issubset(pending):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation is incomplete"
            )
        if pending.get("active") is not True:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation is inactive"
            )
        if str(pending.get("role") or "") != self.role:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation role changed"
            )
        content = pending.get("content")
        proof = pending.get("proof")
        if not isinstance(content, str) or not content.strip():
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation content is missing"
            )
        if len(content) > self._ANSWER_SAFE_RECHECK_MAX_CONTENT_CHARS:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation content is oversized"
            )
        if not isinstance(proof, str) or not proof.strip():
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation proof is missing"
            )
        if len(proof) > self._ANSWER_SAFE_RECHECK_MAX_CONTENT_CHARS:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation proof is oversized"
            )
        exact_check_lemmas = pending.get("verification_check_lemmas")
        exact_context_helpers = pending.get("verification_context_helpers")
        exact_verification_helpers = pending.get("verification_helpers")
        exact_replay_parts = (
            exact_check_lemmas,
            exact_context_helpers,
            exact_verification_helpers,
        )
        if any(part is None for part in exact_replay_parts) and any(
            part is not None for part in exact_replay_parts
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation replay context is incomplete"
            )
        fallback_check_lemmas = pending.get(
            "fallback_verification_check_lemmas"
        )
        fallback_context_helpers = pending.get(
            "fallback_verification_context_helpers"
        )
        fallback_verification_helpers = pending.get(
            "fallback_verification_helpers"
        )
        fallback_replay_parts = (
            fallback_check_lemmas,
            fallback_context_helpers,
            fallback_verification_helpers,
        )
        if any(part is None for part in fallback_replay_parts) and any(
            part is not None for part in fallback_replay_parts
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier fallback context is incomplete"
            )
        if require_exact_verification_state and (
            any(part is None for part in exact_replay_parts)
            or any(part is None for part in fallback_replay_parts)
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier exact replay state is missing"
            )
        for label, blocks in (
            ("check lemmas", exact_check_lemmas),
            ("context helpers", exact_context_helpers),
            ("verification helpers", exact_verification_helpers),
            ("fallback check lemmas", fallback_check_lemmas),
            ("fallback context helpers", fallback_context_helpers),
            ("fallback verification helpers", fallback_verification_helpers),
        ):
            if blocks is None:
                continue
            if (
                not isinstance(blocks, list)
                or len(blocks) > 512
                or any(not isinstance(block, str) for block in blocks)
                or any(
                    len(block) > self._ANSWER_SAFE_RECHECK_MAX_CONTENT_CHARS
                    for block in blocks
                )
            ):
                raise StateSnapshotCompatibilityError(
                    f"conversation verifier continuation {label} are malformed"
                )
        if (
            isinstance(fallback_check_lemmas, list)
            and not fallback_check_lemmas
            and (
                bool(fallback_context_helpers)
                or bool(fallback_verification_helpers)
            )
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier fallback state is inconsistent"
            )
        sent_messages = pending.get("sent_messages")
        if not isinstance(sent_messages, list):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation messages are malformed"
            )
        if len(sent_messages) > 128 or any(
            not isinstance(message, Mapping) for message in sent_messages
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation has too many messages"
            )
        execution_binding = pending.get("execution_binding")
        if not isinstance(execution_binding, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation binding is malformed"
            )
        if set(execution_binding) != self._ANSWER_SAFE_RECHECK_BINDING_KEYS:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation binding is incomplete"
            )
        for key in self._ANSWER_SAFE_RECHECK_BINDING_KEYS - {
            "active_root_targets"
        }:
            if not isinstance(execution_binding.get(key), str):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier continuation binding is malformed"
                )
        active_root_targets = execution_binding.get("active_root_targets")
        if (
            not isinstance(active_root_targets, list)
            or len(active_root_targets) > 32
            or any(
                not isinstance(target, Mapping)
                for target in active_root_targets
            )
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier active-root binding is malformed"
            )
        selected_work_record = pending.get("selected_work_record", {})
        if not isinstance(selected_work_record, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation verifier selected work is malformed"
            )
        if selected_work_record:
            selected_node_id = str(
                selected_work_record.get("node_id")
                or selected_work_record.get("graph_node_id")
                or ""
            ).strip()
            selected_work_type = str(
                selected_work_record.get("work_type") or ""
            ).strip()
            selected_variant_id = str(
                selected_work_record.get("variant_id") or ""
            ).strip()
            selected_statement = str(
                selected_work_record.get("exact_target_statement")
                or selected_work_record.get("target_statement")
                or ""
            ).strip()
            if (
                selected_node_id
                != str(execution_binding.get("selected_node_id") or "").strip()
                or selected_work_type
                != str(execution_binding.get("selected_work_type") or "").strip()
                or selected_variant_id
                != str(
                    execution_binding.get("selected_variant_id") or ""
                ).strip()
                or (
                    selected_statement
                    and selected_statement
                    != str(execution_binding.get("graph_statement") or "").strip()
                )
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier selected work binding changed"
                )
        turn_entry = pending.get("turn_entry")
        if not isinstance(turn_entry, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation turn entry is malformed"
            )
        if set(turn_entry) != self._ANSWER_SAFE_RECHECK_TURN_ENTRY_KEYS:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation turn entry is incomplete"
            )
        history = turn_entry.get("history")
        if (
            not isinstance(history, list)
            or len(history) > 2_048
            or any(not isinstance(message, Mapping) for message in history)
            or not isinstance(turn_entry.get("role"), str)
            or not isinstance(turn_entry.get("graph_last_scope_key"), str)
            or not isinstance(turn_entry.get("last_premise_block"), str)
            or not isinstance(turn_entry.get("last_premise_names"), list)
            or len(turn_entry.get("last_premise_names", [])) > 512
            or any(
                not isinstance(name, str)
                for name in turn_entry.get("last_premise_names", [])
            )
            or not isinstance(
                turn_entry.get("last_premise_block_injected"),
                bool,
            )
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation turn entry is malformed"
            )
        if not isinstance(pending.get("primary_accepted"), bool):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation acceptance is malformed"
            )
        for key in ("conv_turn_offset", "phase_turn", "recovery_attempts"):
            value = pending.get(key)
            if type(value) is not int or value < 0 or value > 1_000_000:
                raise StateSnapshotCompatibilityError(
                    f"conversation verifier continuation {key} is malformed"
                )
        goal_override = pending.get("goal_statement_override")
        if goal_override is not None and (
            not isinstance(goal_override, str) or len(goal_override) > 250_000
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation goal is malformed"
            )
        recovered_receipt = pending.get("recovered_finalizer_receipt", {})
        if not isinstance(recovered_receipt, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation verifier provider receipt is malformed"
            )
        if set(recovered_receipt) - self._ANSWER_SAFE_RECHECK_RECEIPT_KEYS:
            raise StateSnapshotCompatibilityError(
                "conversation verifier provider receipt has unsupported fields"
            )
        for key in (
            "final_no_tools_event",
            "final_no_tools_finish_reason",
            "recovered_finalizer_error",
            "recovered_finalizer_failure_kind",
            "recovered_finalizer_failure_reason",
        ):
            if key in recovered_receipt and not isinstance(
                recovered_receipt.get(key),
                str,
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier provider receipt is malformed"
                )
        for key in (
            "final_no_tools_used_accepted_proof",
            "provider_call_cumulative_wall_exhausted",
            "recovered_finalizer_retryable",
            "recovered_finalizer_provider_call_quantum_exhausted",
            "recovered_finalizer_terminal",
        ):
            if key in recovered_receipt and not isinstance(
                recovered_receipt.get(key),
                bool,
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier provider receipt is malformed"
                )
        for key in (
            "final_no_tools_reasoning_content_chars",
            "provider_calls_completed",
            "provider_dispatches_started",
        ):
            value = recovered_receipt.get(key)
            if key in recovered_receipt and (
                type(value) is not int or value < 0 or value > 1_000_000
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier provider receipt is malformed"
                )
        for key in (
            "provider_call_cumulative_elapsed_s",
            "provider_call_cumulative_wall_cap_s",
        ):
            value = recovered_receipt.get(key)
            if key in recovered_receipt and (
                type(value) not in {int, float}
                or not math.isfinite(float(value))
                or float(value) < 0.0
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier provider receipt is malformed"
                )
        for key in (
            "recovered_finalizer_retry_deadline",
            "recovered_finalizer_provider_defer",
        ):
            if key in recovered_receipt and not isinstance(
                recovered_receipt.get(key),
                Mapping,
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier provider receipt is malformed"
                )
        provider_defer = dict(
            recovered_receipt.get("recovered_finalizer_provider_defer") or {}
        )
        if provider_defer:
            if set(provider_defer) != self._ANSWER_SAFE_RECHECK_PROVIDER_DEFER_KEYS:
                raise StateSnapshotCompatibilityError(
                    "conversation verifier provider defer is malformed"
                )
            fingerprint = provider_defer.get("provider_defer_fingerprint")
            ready_at = provider_defer.get("provider_defer_ready_at")
            retry_after_s = provider_defer.get("provider_defer_retry_after_s")
            if (
                not isinstance(fingerprint, str)
                or not fingerprint.strip()
                or len(fingerprint) > 2_000
                or type(ready_at) not in {int, float}
                or not math.isfinite(float(ready_at))
                or float(ready_at) <= 0.0
                or type(retry_after_s) not in {int, float}
                or not math.isfinite(float(retry_after_s))
                or float(retry_after_s) < 0.0
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation verifier provider defer is malformed"
                )
        retry_deadline = dict(
            recovered_receipt.get("recovered_finalizer_retry_deadline") or {}
        )
        retry_deadline_allowed = (
            self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_BOOL_KEYS
            | self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_INT_KEYS
            | self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_STRING_KEYS
            | self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_FLOAT_KEYS
        )
        if set(retry_deadline) - retry_deadline_allowed:
            raise StateSnapshotCompatibilityError(
                "conversation verifier retry deadline is malformed"
            )
        if any(
            not isinstance(retry_deadline.get(key), bool)
            for key in self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_BOOL_KEYS
            if key in retry_deadline
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier retry deadline is malformed"
            )
        if any(
            type(retry_deadline.get(key)) is not int
            or retry_deadline.get(key) < 0
            or retry_deadline.get(key) > 1_000_000
            for key in self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_INT_KEYS
            if key in retry_deadline
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier retry deadline is malformed"
            )
        if any(
            not isinstance(retry_deadline.get(key), str)
            or len(retry_deadline.get(key)) > 4_000
            for key in self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_STRING_KEYS
            if key in retry_deadline
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier retry deadline is malformed"
            )
        if any(
            type(retry_deadline.get(key)) not in {int, float}
            or not math.isfinite(float(retry_deadline.get(key)))
            or abs(float(retry_deadline.get(key))) > 1_000_000_000.0
            for key in self._ANSWER_SAFE_RECHECK_RETRY_DEADLINE_FLOAT_KEYS
            if key in retry_deadline
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier retry deadline is malformed"
            )
        provider_attempts = recovered_receipt.get(
            "recovered_finalizer_provider_attempts",
            [],
        )
        if (
            not isinstance(provider_attempts, list)
            or len(provider_attempts) > 128
            or any(
                not isinstance(attempt, Mapping)
                for attempt in provider_attempts
            )
        ):
            raise StateSnapshotCompatibilityError(
                "conversation verifier provider attempts are malformed"
            )
        try:
            encoded = json.dumps(
                dict(pending),
                allow_nan=False,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
        except (TypeError, ValueError, OverflowError) as exc:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation is not JSON-safe"
            ) from exc
        if len(encoded) > self._ANSWER_SAFE_RECHECK_MAX_STATE_CHARS:
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation is oversized"
            )
        decoded = json.loads(encoded)
        if not isinstance(decoded, dict):
            raise StateSnapshotCompatibilityError(
                "conversation verifier continuation is malformed"
            )
        return decoded

    @staticmethod
    def _answer_safe_recheck_binding_identity(binding: Mapping[str, Any]) -> str:
        try:
            encoded = json.dumps(
                dict(binding),
                allow_nan=False,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
        except (TypeError, ValueError, OverflowError) as exc:
            raise StateSnapshotCompatibilityError(
                "conversation verifier binding is not JSON-safe"
            ) from exc
        return hashlib.sha256(encoded.encode("utf-8")).hexdigest()

    def _answer_safe_recheck_has_exact_verification_state(
        self,
        pending: Mapping[str, Any],
    ) -> bool:
        return all(
            isinstance(pending.get(key), list)
            for key in self._ANSWER_SAFE_RECHECK_EXACT_VERIFICATION_KEYS
        )

    def _validated_answer_safe_recheck_parked_state(
        self,
        parked: Any,
        *,
        require_exact_verification_state: bool = False,
    ) -> Dict[str, Dict[str, Any]]:
        if parked in (None, {}):
            return {}
        if not isinstance(parked, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation parked verifier state is malformed"
            )
        if len(parked) > self._ANSWER_SAFE_RECHECK_MAX_PARKED:
            raise StateSnapshotCompatibilityError(
                "conversation parked verifier state is oversized"
            )
        validated: Dict[str, Dict[str, Any]] = {}
        for raw_identity, raw_pending in parked.items():
            identity = str(raw_identity or "").strip()
            pending = self._validated_answer_safe_recheck_pending_state(
                raw_pending,
                require_exact_verification_state=(
                    require_exact_verification_state
                ),
            )
            expected_identity = self._answer_safe_recheck_binding_identity(
                dict(pending.get("execution_binding") or {})
            )
            if identity != expected_identity:
                raise StateSnapshotCompatibilityError(
                    "conversation parked verifier binding identity changed"
                )
            validated[identity] = pending
        encoded_chars = self._answer_safe_recheck_parked_encoded_chars(
            validated
        )
        if encoded_chars > self._ANSWER_SAFE_RECHECK_MAX_STATE_CHARS * 2:
            raise StateSnapshotCompatibilityError(
                "conversation parked verifier state is oversized"
            )
        return validated

    @staticmethod
    def _answer_safe_recheck_parked_encoded_chars(
        parked: Mapping[str, Mapping[str, Any]],
    ) -> int:
        try:
            encoded = json.dumps(
                parked,
                allow_nan=False,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
        except (TypeError, ValueError, OverflowError) as exc:
            raise StateSnapshotCompatibilityError(
                "conversation parked verifier state is not JSON-safe"
            ) from exc
        return len(encoded)

    def _validated_answer_safe_recheck_held_terminal_state(
        self,
        state: Any,
    ) -> Dict[str, str]:
        if state in (None, {}):
            return {}
        if (
            not isinstance(state, Mapping)
            or set(state) != self._ANSWER_SAFE_RECHECK_HELD_TERMINAL_KEYS
        ):
            raise StateSnapshotCompatibilityError(
                "conversation held provider terminal state is malformed"
            )
        validated = {key: state.get(key) for key in state}
        if any(
            not isinstance(value, str) or len(value) > 4_000
            for value in validated.values()
        ) or not str(validated.get("llm_failure_kind") or "").strip() or not str(
            validated.get("terminal_failure_reason") or ""
        ).strip():
            raise StateSnapshotCompatibilityError(
                "conversation held provider terminal state is malformed"
            )
        return {key: str(value) for key, value in validated.items()}

    def _park_answer_safe_recheck(self, pending: Mapping[str, Any]) -> None:
        clean = self._validated_answer_safe_recheck_pending_state(pending)
        identity = self._answer_safe_recheck_binding_identity(
            dict(clean.get("execution_binding") or {})
        )
        self._answer_safe_recheck_parked.pop(identity, None)
        self._answer_safe_recheck_parked[identity] = clean
        max_parked_chars = self._ANSWER_SAFE_RECHECK_MAX_STATE_CHARS * 2
        while self._answer_safe_recheck_parked and (
            len(self._answer_safe_recheck_parked)
            > self._ANSWER_SAFE_RECHECK_MAX_PARKED
            or self._answer_safe_recheck_parked_encoded_chars(
                self._answer_safe_recheck_parked
            )
            > max_parked_chars
        ):
            oldest_identity = next(iter(self._answer_safe_recheck_parked))
            self._answer_safe_recheck_parked.pop(oldest_identity, None)

    @staticmethod
    def _bounded_json_copy(
        value: Any,
        *,
        max_chars: int,
        label: str,
    ) -> Any:
        """Return an immutable JSON-shaped copy or reject the checkpoint."""

        try:
            encoded = json.dumps(
                value,
                allow_nan=False,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
            if len(encoded) > max(1, int(max_chars or 0)):
                raise StateSnapshotCompatibilityError(f"{label} is oversized")
            return json.loads(encoded)
        except StateSnapshotCompatibilityError:
            raise
        except (TypeError, ValueError, OverflowError, RecursionError) as exc:
            raise StateSnapshotCompatibilityError(
                f"{label} is not bounded JSON"
            ) from exc

    @classmethod
    def _compact_provider_quantum_selected_work_record(
        cls,
        record: Any,
        *,
        target: str,
    ) -> Dict[str, Any]:
        """Deduplicate exact target aliases inside one checkpoint binding.

        Elaborated residuals can be hundreds of kilobytes.  The binding owns
        the exact target once, while selected-work records and their known
        wrapper layers can repeat it in three fields per layer.  Record the
        omitted paths explicitly so restore remains byte-exact and malformed
        snapshots fail closed.
        """

        if record in (None, {}):
            return {}
        if not isinstance(record, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum selected work is malformed"
            )
        marker_key = cls._PROVIDER_QUANTUM_TARGET_ALIASES_KEY
        source_payload = dict(record)
        existing_aliases = source_payload.get(marker_key)
        if marker_key in source_payload:
            payload = cls._bounded_json_copy(
                source_payload,
                max_chars=(
                    cls._PROVIDER_QUANTUM_CHECKPOINT_MAX_LEGACY_BINDING_CHARS
                ),
                label="conversation provider quantum selected work",
            )
            if (
                not target
                or not isinstance(existing_aliases, list)
                or not existing_aliases
                or any(not isinstance(path, str) for path in existing_aliases)
                or len(set(existing_aliases)) != len(existing_aliases)
                or len(existing_aliases)
                > cls._PROVIDER_QUANTUM_SELECTED_WORK_MAX_LAYERS * 3
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum target aliases are malformed"
                )
            for path in existing_aliases:
                wrapper_path, field_path = cls._provider_quantum_alias_path(path)
                layer = cls._provider_quantum_selected_work_layer_at(
                    payload,
                    wrapper_path,
                )
                if layer is None:
                    raise StateSnapshotCompatibilityError(
                        "conversation provider quantum target aliases are malformed"
                    )
                if field_path == ("execution_scope", "target_statement"):
                    scope = layer.get("execution_scope")
                    if not isinstance(scope, Mapping) or "target_statement" in scope:
                        raise StateSnapshotCompatibilityError(
                            "conversation provider quantum target aliases are "
                            "ambiguous"
                        )
                elif field_path[0] in layer:
                    raise StateSnapshotCompatibilityError(
                        "conversation provider quantum target aliases are ambiguous"
                    )
            for wrapper_path, layer in cls._provider_quantum_selected_work_layers(
                payload
            ):
                if wrapper_path and marker_key in layer:
                    raise StateSnapshotCompatibilityError(
                        "conversation provider quantum target aliases are malformed"
                    )
            return payload

        aliases: List[str] = []
        payload = dict(source_payload)
        pending: List[
            Tuple[
                Tuple[str, ...],
                Dict[str, Any],
                Dict[str, Any],
                FrozenSet[int],
            ]
        ] = [((), source_payload, payload, frozenset({id(record)}))]
        layer_count = 0
        while pending:
            wrapper_path, source_layer, layer, ancestor_ids = pending.pop(0)
            layer_count += 1
            if layer_count > cls._PROVIDER_QUANTUM_SELECTED_WORK_MAX_LAYERS:
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum selected work is too deeply nested"
                )
            if wrapper_path and marker_key in layer:
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum target aliases are malformed"
                )
            prefix = ".".join(wrapper_path)

            def alias_path(suffix: str) -> str:
                return f"{prefix}.{suffix}" if prefix else suffix

            if target:
                for field_name in (
                    "target_statement",
                    "exact_target_statement",
                ):
                    if layer.get(field_name) == target:
                        layer.pop(field_name)
                        aliases.append(alias_path(field_name))
                scope = layer.get("execution_scope")
                if isinstance(scope, Mapping):
                    compact_scope = dict(scope)
                    if compact_scope.get("target_statement") == target:
                        compact_scope.pop("target_statement")
                        aliases.append(
                            alias_path("execution_scope.target_statement")
                        )
                    layer["execution_scope"] = compact_scope

            for key in cls._PROVIDER_QUANTUM_SELECTED_WORK_WRAPPER_KEYS:
                source_child = source_layer.get(key)
                if not isinstance(source_child, dict):
                    continue
                if id(source_child) in ancestor_ids:
                    raise StateSnapshotCompatibilityError(
                        "conversation provider quantum selected work is not "
                        "bounded JSON"
                    )
                child = dict(source_child)
                layer[key] = child
                pending.append(
                    (
                        (*wrapper_path, key),
                        source_child,
                        child,
                        ancestor_ids | {id(source_child)},
                    )
                )
        if aliases:
            payload[marker_key] = aliases
        return cls._bounded_json_copy(
            payload,
            max_chars=cls._PROVIDER_QUANTUM_CHECKPOINT_MAX_LEGACY_BINDING_CHARS,
            label="conversation provider quantum selected work",
        )

    @classmethod
    def _provider_quantum_selected_work_layers(
        cls,
        payload: Dict[str, Any],
    ) -> List[Tuple[Tuple[str, ...], Dict[str, Any]]]:
        """Return bounded known wrapper layers together with exact paths."""

        pending: List[Tuple[Tuple[str, ...], Dict[str, Any]]] = [((), payload)]
        layers: List[Tuple[Tuple[str, ...], Dict[str, Any]]] = []
        seen: set[int] = set()
        while pending:
            wrapper_path, layer = pending.pop(0)
            if id(layer) in seen:
                continue
            seen.add(id(layer))
            layers.append((wrapper_path, layer))
            if len(layers) > cls._PROVIDER_QUANTUM_SELECTED_WORK_MAX_LAYERS:
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum selected work is too deeply nested"
                )
            for key in cls._PROVIDER_QUANTUM_SELECTED_WORK_WRAPPER_KEYS:
                child = layer.get(key)
                if isinstance(child, dict):
                    pending.append(((*wrapper_path, key), child))
        return layers

    @classmethod
    def _provider_quantum_alias_path(
        cls,
        path: str,
    ) -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
        """Parse one finite target-alias path or reject it."""

        parts = tuple(path.split("."))
        if parts[-2:] == ("execution_scope", "target_statement"):
            wrapper_path = parts[:-2]
            field_path = parts[-2:]
        elif parts[-1:] in {("target_statement",), ("exact_target_statement",)}:
            wrapper_path = parts[:-1]
            field_path = parts[-1:]
        else:
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum target aliases are malformed"
            )
        if (
            len(wrapper_path)
            >= cls._PROVIDER_QUANTUM_SELECTED_WORK_MAX_LAYERS
            or any(
                key not in cls._PROVIDER_QUANTUM_SELECTED_WORK_WRAPPER_KEYS
                for key in wrapper_path
            )
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum target aliases are malformed"
            )
        return wrapper_path, field_path

    @staticmethod
    def _provider_quantum_selected_work_layer_at(
        payload: Dict[str, Any],
        wrapper_path: Tuple[str, ...],
    ) -> Optional[Dict[str, Any]]:
        """Resolve a known wrapper path without creating missing layers."""

        layer: Any = payload
        for key in wrapper_path:
            if not isinstance(layer, dict):
                return None
            layer = layer.get(key)
        return layer if isinstance(layer, dict) else None

    @classmethod
    def _rehydrate_provider_quantum_selected_work_record(
        cls,
        record: Any,
        *,
        target: str,
    ) -> Dict[str, Any]:
        """Restore target aliases removed by checkpoint compaction."""

        payload = cls._compact_provider_quantum_selected_work_record(
            record,
            target=target,
        )
        aliases = payload.pop(cls._PROVIDER_QUANTUM_TARGET_ALIASES_KEY, [])
        for path in aliases:
            wrapper_path, field_path = cls._provider_quantum_alias_path(path)
            layer = cls._provider_quantum_selected_work_layer_at(
                payload,
                wrapper_path,
            )
            if layer is None:
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum target aliases are malformed"
                )
            if field_path == ("execution_scope", "target_statement"):
                scope = dict(layer.get("execution_scope") or {})
                scope["target_statement"] = target
                layer["execution_scope"] = scope
            else:
                layer[field_path[0]] = target
        return payload

    def _validated_provider_quantum_checkpoint(
        self,
        raw: Any,
        *,
        conv: Any = None,
        expected_target: Optional[str] = None,
        expected_repair_cycle: Optional[str] = None,
    ) -> Dict[str, Any]:
        """Validate one ordinary provider/tool continuation checkpoint."""

        if raw in (None, {}):
            return {}
        if not isinstance(raw, Mapping) or set(raw) != {
            "state",
            "history",
            "binding",
        }:
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum checkpoint is malformed"
            )
        raw_state = raw.get("state")
        # Schema-v4 checkpoints predate both search cadence governance and the
        # ModelChain continuation cursor. Missing optional governors represent
        # their neutral state; migrate before enforcing the serialized cap so
        # an accepted checkpoint is bounded and idempotent on its next restore.
        if (
            isinstance(raw_state, Mapping)
            and type(raw_state.get("schema_version")) is int
            and raw_state.get("schema_version") == 4
        ):
            raw_state = dict(raw_state)
            raw_state.setdefault("consecutive_search_tool_calls", 0)
            raw_state.setdefault("provider_chain_resume_target_id", "")
            raw_state.setdefault("invalid_prompt_neutralization_pending", False)
        state = self._bounded_json_copy(
            raw_state,
            max_chars=self._PROVIDER_QUANTUM_CHECKPOINT_MAX_STATE_CHARS,
            label="conversation provider quantum state",
        )
        history = self._bounded_json_copy(
            raw.get("history"),
            max_chars=self._PROVIDER_QUANTUM_CHECKPOINT_MAX_HISTORY_CHARS,
            label="conversation provider quantum history",
        )
        raw_binding = raw.get("binding")
        binding_keys = {
            "role",
            "target",
            "repair_cycle",
            "selected_work_record",
            "selected_context_digest",
        }
        if (
            not isinstance(raw_binding, Mapping)
            or len(raw_binding) != len(binding_keys)
            or set(raw_binding) != binding_keys
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum binding is malformed"
            )
        bounded_binding_target = self._bounded_json_copy(
            raw_binding.get("target"),
            max_chars=self._PROVIDER_QUANTUM_CHECKPOINT_MAX_TARGET_CHARS,
            label="conversation provider quantum target",
        )
        compact_binding_metadata = {
            "role": raw_binding.get("role"),
            "repair_cycle": raw_binding.get("repair_cycle"),
            "selected_context_digest": raw_binding.get(
                "selected_context_digest"
            ),
            "selected_work_record": (
                self._compact_provider_quantum_selected_work_record(
                    raw_binding.get("selected_work_record"),
                    target=(
                        bounded_binding_target
                        if isinstance(bounded_binding_target, str)
                        else ""
                    ),
                )
            ),
        }
        binding = self._bounded_json_copy(
            compact_binding_metadata,
            max_chars=self._PROVIDER_QUANTUM_CHECKPOINT_MAX_BINDING_CHARS,
            label="conversation provider quantum binding",
        )
        binding["target"] = bounded_binding_target
        if (
            not isinstance(state, dict)
            or set(state) != self._PROVIDER_QUANTUM_STATE_KEYS
            or type(state.get("schema_version")) is not int
            or state.get("schema_version") != 4
            or not isinstance(state.get("provider_turn_lane_identity"), str)
            or len(state.get("provider_turn_lane_identity") or "") != 64
            or type(state.get("max_tool_calls_per_turn")) is not int
            or int(state.get("max_tool_calls_per_turn") or 0)
            != max(0, int(self.max_tool_calls_per_turn or 0))
            or state.get("pending_tool_replay_disposition")
            == "durable_progress_cutpoint"
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum state is incompatible"
            )
        typed_state_keys = (
            self._PROVIDER_QUANTUM_BOOL_STATE_KEYS
            | self._PROVIDER_QUANTUM_INT_STATE_KEYS
            | self._PROVIDER_QUANTUM_FLOAT_STATE_KEYS
            | self._PROVIDER_QUANTUM_STRING_STATE_KEYS
            | frozenset(
                {
                    "seen_tool_call_signatures",
                    "repair_self_check_codes",
                    "pending_tool_replay",
                    "durable_progress_tool_continuation_helper_receipts",
                    "semantic_result_counts",
                    "semantic_diagnostic_best_by_tool",
                }
            )
        )
        if typed_state_keys != self._PROVIDER_QUANTUM_STATE_KEYS:
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum schema is incomplete"
            )
        if any(
            type(state.get(key)) is not bool
            for key in self._PROVIDER_QUANTUM_BOOL_STATE_KEYS
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum boolean state is malformed"
            )
        if any(
            type(state.get(key)) is not int
            for key in self._PROVIDER_QUANTUM_INT_STATE_KEYS
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum integer state is malformed"
            )
        for key in self._PROVIDER_QUANTUM_FLOAT_STATE_KEYS:
            value = state.get(key)
            if (
                isinstance(value, bool)
                or not isinstance(value, (int, float))
                or not math.isfinite(float(value))
                or float(value) < 0.0
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum numeric state is malformed"
                )
        if any(
            not isinstance(state.get(key), str)
            for key in self._PROVIDER_QUANTUM_STRING_STATE_KEYS
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum string state is malformed"
            )
        nonnegative_int_keys = (
            self._PROVIDER_QUANTUM_INT_STATE_KEYS
            - {
                "schema_version",
                "semantic_diagnostic_best_phase",
                "semantic_diagnostic_best_goal_count",
            }
        )
        if any(
            int(state.get(key)) < 0 or int(state.get(key)) > 1_000_000
            for key in nonnegative_int_keys
        ) or any(
            int(state.get(key)) < -1 or int(state.get(key)) > 1_000_000
            for key in {
                "semantic_diagnostic_best_phase",
                "semantic_diagnostic_best_goal_count",
            }
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum integer bounds are malformed"
            )
        if (
            int(state.get("tool_calls_used"))
            > int(state.get("max_tool_calls_per_turn"))
            or int(state.get("proof_tool_attempts"))
            > int(state.get("max_tool_calls_per_turn"))
            or int(state.get("consecutive_no_formal_progress"))
            > int(state.get("max_tool_calls_per_turn"))
            or int(state.get("consecutive_search_tool_calls"))
            > int(state.get("max_tool_calls_per_turn"))
            or int(state.get("semantic_diagnostic_progress_count"))
            > int(state.get("max_tool_calls_per_turn"))
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum tool counters are malformed"
            )
        # Repeat-detection signatures include selected calls that deliberately
        # do not charge the paid tool budget (for example cadence skips and
        # infrastructure deferrals before launch).  Their count therefore is
        # not bounded by max_tool_calls_per_turn.  The enclosing state already
        # has a strict serialized-size bound; retain the full set so a restart
        # cannot forget repeats merely because those calls were non-charging.
        seen_tool_call_signatures = state.get("seen_tool_call_signatures")
        if (
            not isinstance(seen_tool_call_signatures, list)
            or any(
                not isinstance(signature, str) or not signature
                for signature in seen_tool_call_signatures
            )
            or len(set(seen_tool_call_signatures))
            != len(seen_tool_call_signatures)
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum seen_tool_call_signatures "
                "is malformed"
            )
        bounded_lists = {
            "repair_self_check_codes": 4,
            "pending_tool_replay": 4,
            "durable_progress_tool_continuation_helper_receipts": 64,
        }
        for key, limit in bounded_lists.items():
            value = state.get(key)
            if not isinstance(value, list) or len(value) > limit:
                raise StateSnapshotCompatibilityError(
                    f"conversation provider quantum {key} is malformed"
                )
        if any(
            not isinstance(value, str)
            for key in {"seen_tool_call_signatures", "repair_self_check_codes"}
            for value in state.get(key)
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum list state is malformed"
            )
        def valid_tool_call(call: Any) -> bool:
            function = call.get("function") if isinstance(call, dict) else None
            return isinstance(call, dict) and not (
                not isinstance(function, dict)
                or not isinstance(function.get("name"), str)
                or not str(function.get("name") or "").strip()
                or len(str(function.get("name") or "")) > 200
                or (
                    "arguments" in function
                    and not isinstance(
                        function.get("arguments"),
                        (str, dict, list, int, float, bool, type(None)),
                    )
                )
                or (
                    "id" in call
                    and not isinstance(call.get("id"), str)
                )
                or (
                    "type" in call
                    and not isinstance(call.get("type"), str)
                )
            )

        for call in state.get("pending_tool_replay"):
            if not valid_tool_call(call):
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum pending tool is malformed"
                )
        helper_receipts = state.get(
            "durable_progress_tool_continuation_helper_receipts"
        )
        if any(
            not isinstance(receipt, dict)
            or set(receipt) != {"name", "source_hash"}
            or any(not isinstance(value, str) for value in receipt.values())
            for receipt in helper_receipts
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum helper receipts are malformed"
            )
        if not isinstance(state.get("semantic_result_counts"), dict) or len(
            state.get("semantic_result_counts") or {}
        ) > 32:
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum semantic counts are malformed"
            )
        if any(
            not isinstance(signature, str)
            or type(count) is not int
            or count < 0
            or count > 1_000_000
            for signature, count in state.get("semantic_result_counts").items()
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum semantic counts are malformed"
            )
        if not isinstance(
            state.get("semantic_diagnostic_best_by_tool"), dict
        ) or len(state.get("semantic_diagnostic_best_by_tool") or {}) > 8:
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum diagnostic state is malformed"
            )
        for tool_name, diagnostic in state.get(
            "semantic_diagnostic_best_by_tool"
        ).items():
            if (
                not isinstance(tool_name, str)
                or not isinstance(diagnostic, dict)
                or set(diagnostic)
                != {"phase", "error_kind", "goal_count", "signature"}
                or type(diagnostic.get("phase")) is not int
                or diagnostic.get("phase") < -1
                or diagnostic.get("phase") > 16
                or not isinstance(diagnostic.get("error_kind"), str)
                or (
                    diagnostic.get("goal_count") is not None
                    and (
                        type(diagnostic.get("goal_count")) is not int
                        or diagnostic.get("goal_count") < 0
                        or diagnostic.get("goal_count") > 1_000_000
                    )
                )
                or not isinstance(diagnostic.get("signature"), str)
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum diagnostic state is malformed"
                )
        if (
            not isinstance(history, list)
            or len(history) > self._PROVIDER_QUANTUM_CHECKPOINT_MAX_HISTORY_MESSAGES
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum history is malformed"
            )
        for message in history:
            if not isinstance(message, dict):
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum history is malformed"
                )
            role = message.get("role")
            content = message.get("content")
            if role in {"system", "user"}:
                valid_message = isinstance(content, str)
            elif role == "assistant":
                tool_calls = message.get("tool_calls", [])
                valid_message = bool(
                    (content is None or isinstance(content, str))
                    and isinstance(tool_calls, list)
                    and len(tool_calls) <= max(
                        1, int(self.max_tool_calls_per_turn or 0)
                    )
                    and all(valid_tool_call(call) for call in tool_calls)
                )
            elif role == "tool":
                valid_message = bool(
                    isinstance(content, str)
                    and isinstance(message.get("tool_call_id"), str)
                    and str(message.get("tool_call_id") or "").strip()
                )
            else:
                valid_message = False
            if not valid_message:
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum history is malformed"
                )
        if (
            not isinstance(binding, dict)
            or set(binding)
            != {
                "role",
                "target",
                "repair_cycle",
                "selected_work_record",
                "selected_context_digest",
            }
            or any(
                not isinstance(binding.get(key), str)
                for key in {
                    "role",
                    "target",
                    "repair_cycle",
                    "selected_context_digest",
                }
            )
            or not isinstance(binding.get("selected_work_record"), dict)
            or len(binding.get("role") or "") > 80
            or len(binding.get("target") or "")
            > self._PROVIDER_QUANTUM_CHECKPOINT_MAX_TARGET_CHARS
            or len(binding.get("repair_cycle") or "") > 4_000
            or len(binding.get("selected_context_digest") or "") > 256
            or binding.get("role") != self.role
            or (
                expected_target is not None
                and binding.get("target") != expected_target
            )
            or (
                expected_repair_cycle is not None
                and binding.get("repair_cycle") != expected_repair_cycle
            )
        ):
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum binding is malformed"
            )
        selected_work_record = binding.get("selected_work_record") or {}
        mapped_action_id = str(
            selected_work_record.get("mapped_action_id") or ""
        ).strip()
        if mapped_action_id and mapped_action_id not in {self.id, "conversation_turn"}:
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum selected work changed owner"
            )
        if conv is not None:
            from ensemble_prover.mini_session.turn.tool_loop import (
                _provider_turn_lane_identity,
            )

            expected_identity = _provider_turn_lane_identity(
                conv,
                binding["target"],
                repair_cycle_identity=binding["repair_cycle"],
            )
            if state.get("provider_turn_lane_identity") != expected_identity:
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum lane identity changed"
                )
        # A process-monotonic absolute deadline cannot cross a restart. The
        # cumulative elapsed receipt remains authoritative; the loop derives
        # a fresh remaining deadline from it on resume.
        state["provider_call_cumulative_deadline_monotonic"] = 0.0
        return {"state": state, "history": history, "binding": binding}

    @staticmethod
    def _provider_quantum_live_binding(session: Any) -> Tuple[str, str]:
        """Return the target and repair cycle currently owned by the scheduler."""

        conv = getattr(session, "conv", None)
        graph_target = _selected_graph_native_proof_target(session)
        target = str(graph_target.get("statement") or "").strip()
        if not target and _selected_assemble_route_authoring_ready(session):
            target = _selected_assemble_route_goal_statement(session)
        if not target:
            target = str(getattr(conv, "goal_statement", "") or "").strip()
        selected_record = getattr(session, "selected_work_item_record", {}) or {}
        if not isinstance(selected_record, Mapping):
            selected_record = {}
        repair_cycle = _provider_repair_cycle_identity(
            session,
            selected_record,
        )
        return target, repair_cycle

    _PROVIDER_LANE_LEASE_STATE_RESET: ClassVar[Dict[str, Any]] = {
        "provider_call_cumulative_elapsed_s": 0.0,
        "provider_call_cumulative_deadline_monotonic": 0.0,
        "provider_call_cumulative_wall_exhausted": False,
        "provider_turn_lane_retired": False,
    }

    def renew_provider_lane_lease(
        self,
        session: Any,
        retired_lane_identities: Optional[Iterable[str]] = None,
    ) -> bool:
        """Grant this action's retired conversation lane a fresh wall lease.

        Spent lease time lives in this action's provider quantum checkpoint
        and, while this action's role owns the shared conversation, in the
        conversation's quantum state. Only state stamped with one of the
        retired lane identities is reset (a state without any stamp is reset
        only when it is itself flagged exhausted or retired); the sibling
        role's live lease in the shared conversation is never touched. The
        cap, transcript, and lane identity are untouched. Returns whether any
        spent lease was reset.
        """

        retired = {
            str(identity or "").strip()
            for identity in (retired_lane_identities or ())
            if str(identity or "").strip()
        }
        states: List[Dict[str, Any]] = []
        checkpoint = getattr(self, "_provider_quantum_checkpoint", None)
        if isinstance(checkpoint, dict) and isinstance(
            checkpoint.get("state"), dict
        ):
            states.append(checkpoint["state"])
        conv = getattr(session, "conv", None)
        conv_state = getattr(conv, "_provider_call_quantum_state", None)
        if (
            isinstance(conv_state, dict)
            and str(getattr(conv, "role", "") or "").strip() == self.role
        ):
            # Prove/refine share one live Conversation; the inactive sibling's
            # parked lease belongs to the other action.
            states.append(conv_state)
        renewed = False
        for state in states:
            identity = str(state.get("provider_turn_lane_identity") or "").strip()
            flagged = bool(
                state.get("provider_call_cumulative_wall_exhausted")
            ) or bool(state.get("provider_turn_lane_retired"))
            if identity:
                if retired_lane_identities is not None and identity not in retired:
                    continue
            elif not flagged:
                continue
            try:
                spent_s = float(
                    state.get("provider_call_cumulative_elapsed_s", 0.0) or 0.0
                )
            except (TypeError, ValueError, OverflowError):
                spent_s = 0.0
            if spent_s <= 0.0 and not flagged:
                continue
            state.update(dict(self._PROVIDER_LANE_LEASE_STATE_RESET))
            renewed = True
        return renewed

    @classmethod
    def _provider_quantum_timing_only_state(
        cls,
        state: Mapping[str, Any],
    ) -> Dict[str, Any]:
        """Retain one lane's wall lease without transcript-bound protocol state."""

        sanitized: Dict[str, Any] = {
            key: False for key in cls._PROVIDER_QUANTUM_BOOL_STATE_KEYS
        }
        sanitized.update({
            key: 0 for key in cls._PROVIDER_QUANTUM_INT_STATE_KEYS
        })
        sanitized.update({
            key: 0.0 for key in cls._PROVIDER_QUANTUM_FLOAT_STATE_KEYS
        })
        sanitized.update({
            key: "" for key in cls._PROVIDER_QUANTUM_STRING_STATE_KEYS
        })
        for key in (
            "durable_progress_tool_continuation_helper_receipts",
            "pending_tool_replay",
            "repair_self_check_codes",
            "seen_tool_call_signatures",
        ):
            sanitized[key] = []
        sanitized["semantic_diagnostic_best_by_tool"] = {}
        sanitized["semantic_result_counts"] = {}
        sanitized["schema_version"] = int(state.get("schema_version", 0) or 0)
        sanitized["max_tool_calls_per_turn"] = int(
            state.get("max_tool_calls_per_turn", 0) or 0
        )
        sanitized["semantic_diagnostic_best_phase"] = -1
        sanitized["semantic_diagnostic_best_goal_count"] = -1
        sanitized["provider_turn_lane_identity"] = str(
            state.get("provider_turn_lane_identity") or ""
        )
        for key in (
            "provider_call_cumulative_elapsed_s",
            "provider_call_cumulative_wall_cap_s",
            "provider_call_cumulative_deadline_monotonic",
        ):
            sanitized[key] = float(state.get(key, 0.0) or 0.0)
        sanitized["provider_call_cumulative_wall_exhausted"] = bool(
            state.get("provider_call_cumulative_wall_exhausted", False)
        )
        return sanitized

    def prepare_scheduler_runtime_state(self, session: Any) -> None:
        """Capture the bounded live conversation continuation for checkpoint."""

        conv = getattr(session, "conv", None)
        raw_state = getattr(conv, "_provider_call_quantum_state", None)
        if str(getattr(conv, "role", "") or "").strip() != self.role:
            # Prove/refine share one live Conversation, but each action owns
            # its own authenticated provider lane.  Preparing the currently
            # inactive sibling for a scheduler snapshot must not delete its
            # parked wall/tool receipt; it will be validated against the live
            # target and repair cycle when that action is selected again.
            return
        if not isinstance(raw_state, Mapping) or not raw_state:
            self._provider_quantum_checkpoint = {}
            return
        if str(raw_state.get("pending_tool_replay_disposition") or "").strip() == (
            "durable_progress_cutpoint"
        ):
            # This narrower paid continuation has its own authenticated
            # session-level checkpoint owner.
            self._provider_quantum_checkpoint = {}
            return
        retained_binding: Dict[str, Any] = {}
        retained_state = self._provider_quantum_checkpoint.get("state")
        if (
            isinstance(retained_state, Mapping)
            and retained_state.get("provider_turn_lane_identity")
            == raw_state.get("provider_turn_lane_identity")
            and isinstance(
                self._provider_quantum_checkpoint.get("binding"),
                Mapping,
            )
        ):
            # Frontier fairness temporarily clears selected_work_item_record.
            # The binding captured at the authenticated yield boundary remains
            # the action-owned authority for this unchanged provider lane.
            retained_binding = copy.deepcopy(
                dict(self._provider_quantum_checkpoint["binding"])
            )
        if retained_binding:
            live_target = str(retained_binding.get("target") or "").strip()
            live_repair_cycle = str(
                retained_binding.get("repair_cycle") or ""
            ).strip()
            retained_selected_work = (
                self._rehydrate_provider_quantum_selected_work_record(
                    retained_binding.get("selected_work_record"),
                    target=live_target,
                )
            )
            current_repair_cycle = _provider_repair_cycle_identity(
                session,
                retained_selected_work,
            )
            if current_repair_cycle != live_repair_cycle:
                # A static/fairness lane verified new formal evidence while
                # this provider continuation was parked.  The old transcript
                # and wall lease are authenticated to the prior environment;
                # discard them rather than serializing a snapshot that cannot
                # replay or rebinding paid state to the new environment.
                self._provider_quantum_checkpoint = {}
                if hasattr(conv, "_provider_call_quantum_state"):
                    delattr(conv, "_provider_call_quantum_state")
                self._provider_quantum_yield_consumed_generation = int(
                    self._provider_quantum_yield_generation
                )
                return
            binding = retained_binding
        else:
            live_target, live_repair_cycle = self._provider_quantum_live_binding(
                session
            )
            binding = {
                "role": str(getattr(conv, "role", "") or "").strip(),
                "target": live_target,
                "repair_cycle": live_repair_cycle,
                "selected_context_digest": str(
                    getattr(
                        session,
                        "_selected_proof_idea_context_digest",
                        "",
                    )
                    or ""
                ).strip(),
                "selected_work_record": dict(
                    getattr(
                        session,
                        "selected_work_item_record",
                        {},
                    )
                    or {}
                ),
            }
        self._provider_quantum_checkpoint = (
            self._validated_provider_quantum_checkpoint(
                {
                    "state": copy.deepcopy(dict(raw_state)),
                    "history": copy.deepcopy(
                        list(getattr(conv, "history", []) or [])
                    ),
                    "binding": binding,
                },
                conv=conv,
                expected_target=live_target,
                expected_repair_cycle=live_repair_cycle,
            )
        )

    def _activate_provider_quantum_checkpoint(self, session: Any) -> bool:
        """Reactivate this role's exact in-memory provider continuation.

        The shared conversation can currently expose a sibling role's state.
        Rehydrate the action-owned provider receipt only when its target and
        repair-cycle identity still match.  Preserve the live transcript when
        it contains newer sibling evidence; a protocol-bound continuation is
        restored only when its saved transcript is still an exact prefix.
        """

        if not self._provider_quantum_checkpoint:
            return False
        conv = getattr(session, "conv", None)
        if conv is None:
            return False
        previous_role = str(getattr(conv, "role", "") or "")
        conv.role = self.role
        previous_context_digest = str(
            getattr(session, "_selected_proof_idea_context_digest", "") or ""
        )
        selection_restore_attempted = False
        activated = False
        try:
            try:
                parked_checkpoint = self._validated_provider_quantum_checkpoint(
                    self._provider_quantum_checkpoint,
                    conv=conv,
                )
            except StateSnapshotCompatibilityError:
                self._provider_quantum_checkpoint = {}
                return False
            parked_lane_identity = str(
                parked_checkpoint["state"].get("provider_turn_lane_identity")
                or ""
            ).strip()
            retired_lane_identities = set(
                getattr(
                    session,
                    "provider_turn_retired_lane_identities",
                    set(),
                )
                or set()
            )
            if (
                parked_lane_identity
                and parked_lane_identity in retired_lane_identities
            ):
                # Cumulative-wall retirement is non-refundable. A parked
                # action checkpoint is subordinate to the session's durable
                # spent-lane ledger and cannot restore either selection or
                # provider state after frontier fairness clears them.
                self._provider_quantum_checkpoint = {}
                return False
            current_selected_record = getattr(
                session,
                "selected_work_item_record",
                {},
            ) or {}
            current_selected_item = getattr(session, "selected_work_item", None)
            parked_selected_record = (
                self._rehydrate_provider_quantum_selected_work_record(
                    parked_checkpoint["binding"].get("selected_work_record"),
                    target=str(
                        parked_checkpoint["binding"].get("target") or ""
                    ),
                )
            )
            if (
                not current_selected_record
                and current_selected_item is None
                and parked_selected_record
            ):
                selection_restore_attempted = True
                sanitize_selected_work = getattr(
                    session,
                    "_sanitize_selected_work_record_answer_aliases",
                    None,
                )
                if callable(sanitize_selected_work):
                    parked_selected_record = dict(
                        sanitize_selected_work(parked_selected_record) or {}
                    )
                restore_selected_work = getattr(
                    session,
                    "_restore_selected_work_record",
                    None,
                )
                session._selected_proof_idea_context_digest = (
                    str(
                        parked_checkpoint["binding"].get(
                            "selected_context_digest"
                        )
                        or ""
                    ).strip()
                )
                if not callable(
                    restore_selected_work
                ) or not restore_selected_work(
                    parked_selected_record,
                    self.id,
                    context="provider_quantum_checkpoint_reactivate",
                    metric_key=(
                        "mini_session_retired_graph_target_provider_quantum_suppressed"
                    ),
                ):
                    self._provider_quantum_checkpoint = {}
                    return False
            live_target, live_repair_cycle = self._provider_quantum_live_binding(
                session
            )
            try:
                checkpoint = self._validated_provider_quantum_checkpoint(
                    self._provider_quantum_checkpoint,
                    conv=conv,
                    expected_target=live_target,
                    expected_repair_cycle=live_repair_cycle,
                )
            except StateSnapshotCompatibilityError:
                self._provider_quantum_checkpoint = {}
                return False

            state = dict(checkpoint["state"])
            checkpoint_history = copy.deepcopy(list(checkpoint["history"]))
            live_history = copy.deepcopy(list(getattr(conv, "history", []) or []))
            checkpoint_is_live_prefix = bool(
                len(checkpoint_history) <= len(live_history)
                and live_history[: len(checkpoint_history)] == checkpoint_history
            )
            live_is_checkpoint_prefix = bool(
                len(live_history) <= len(checkpoint_history)
                and checkpoint_history[: len(live_history)] == live_history
            )
            if checkpoint_is_live_prefix:
                merged_history = live_history
                transcript_disposition = "live_transcript_retained"
            elif live_is_checkpoint_prefix:
                merged_history = checkpoint_history
                transcript_disposition = "checkpoint_transcript_restored"
            else:
                # Sibling roles can append mutually divergent transcripts.
                # Preserve the live mathematical evidence and the exact
                # non-refundable wall lease, but reset every tool/finalizer
                # cursor whose meaning depends on the parked transcript.
                state = self._provider_quantum_timing_only_state(state)
                merged_history = live_history
                transcript_disposition = "live_transcript_timing_only"
                checkpoint = self._validated_provider_quantum_checkpoint(
                    {
                        "state": copy.deepcopy(state),
                        "history": copy.deepcopy(merged_history),
                        "binding": copy.deepcopy(checkpoint["binding"]),
                    },
                    conv=conv,
                    expected_target=live_target,
                    expected_repair_cycle=live_repair_cycle,
                )

            conv._provider_turn_repair_cycle_identity = str(
                live_repair_cycle or ""
            )
            conv._provider_call_quantum_state = copy.deepcopy(state)
            conv.history = merged_history
            self._provider_quantum_checkpoint = copy.deepcopy(checkpoint)
            # The provider state, transcript, action checkpoint, and role now
            # form one coherent ownership transfer. Observational telemetry
            # must not make a late external stop roll back only the role.
            activated = True
            recorder = getattr(session, "_record_event", None)
            if callable(recorder):
                recorder(
                    {
                        "phase": "session_provider_quantum_checkpoint",
                        "action_id": self.id,
                        "provider_call_cumulative_elapsed_s": float(
                            state.get(
                                "provider_call_cumulative_elapsed_s",
                                0.0,
                            )
                            or 0.0
                        ),
                        "transcript_disposition": transcript_disposition,
                        "verdict": "provider_quantum_checkpoint_reactivated",
                    }
                )
            return True
        finally:
            if not activated:
                if selection_restore_attempted:
                    clear_selected_work = getattr(
                        session,
                        "_clear_selected_work_item",
                        None,
                    )
                    if callable(clear_selected_work):
                        clear_selected_work()
                    session._selected_proof_idea_context_digest = (
                        previous_context_digest
                    )
                conv.role = previous_role

    def scheduler_runtime_state(self) -> Dict[str, Any]:
        """Export bounded conversation continuations, never full proof state."""

        pending = self._validated_answer_safe_recheck_pending_state(
            self._answer_safe_recheck_pending
        )
        parked = self._validated_answer_safe_recheck_parked_state(
            self._answer_safe_recheck_parked
        )
        verifier_owners = [
            candidate
            for candidate in (pending, *parked.values())
            if candidate
        ]
        schema_version = (
            self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION
            if all(
                self._answer_safe_recheck_has_exact_verification_state(
                    candidate
                )
                for candidate in verifier_owners
            )
            else 5
        )
        if schema_version == self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION:
            pending = self._validated_answer_safe_recheck_pending_state(
                pending,
                require_exact_verification_state=True,
            )
            parked = self._validated_answer_safe_recheck_parked_state(
                parked,
                require_exact_verification_state=True,
            )
        return {
            "schema_version": schema_version,
            "answer_safe_recheck_pending": pending,
            "answer_safe_recheck_parked": parked,
            "answer_safe_recheck_parked_order": list(
                self._answer_safe_recheck_parked
            ),
            "answer_safe_recheck_held_terminal_provider_failure": (
                self._validated_answer_safe_recheck_held_terminal_state(
                    self._answer_safe_recheck_held_terminal_provider_failure
                )
            ),
            "provider_quantum_checkpoint": (
                self._validated_provider_quantum_checkpoint(
                    self._provider_quantum_checkpoint
                )
            ),
            "provider_quantum_yield_generation": int(
                self._provider_quantum_yield_generation
            ),
            "provider_quantum_yield_consumed_generation": int(
                self._provider_quantum_yield_consumed_generation
            ),
        }

    def apply_scheduler_runtime_state(self, state: Any) -> None:
        """Restore a schema-validated verifier-only continuation."""

        if not isinstance(state, Mapping):
            raise StateSnapshotCompatibilityError(
                "conversation runtime state is malformed"
            )
        schema_version = state.get("schema_version")
        if schema_version == 1:
            expected_keys = {"schema_version", "answer_safe_recheck_pending"}
        elif schema_version == 2:
            expected_keys = {
                "schema_version",
                "answer_safe_recheck_pending",
                "answer_safe_recheck_parked",
            }
        elif schema_version == 3:
            expected_keys = {
                "schema_version",
                "answer_safe_recheck_pending",
                "answer_safe_recheck_parked",
                "answer_safe_recheck_held_terminal_provider_failure",
            }
        elif schema_version == 4:
            expected_keys = {
                "schema_version",
                "answer_safe_recheck_pending",
                "answer_safe_recheck_parked",
                "answer_safe_recheck_parked_order",
                "answer_safe_recheck_held_terminal_provider_failure",
            }
        elif schema_version in {
            5,
            self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION,
        }:
            expected_keys = {
                "schema_version",
                "answer_safe_recheck_pending",
                "answer_safe_recheck_parked",
                "answer_safe_recheck_parked_order",
                "answer_safe_recheck_held_terminal_provider_failure",
                "provider_quantum_checkpoint",
                "provider_quantum_yield_generation",
                "provider_quantum_yield_consumed_generation",
            }
        else:
            raise StateSnapshotCompatibilityError(
                "conversation runtime-state schema is unsupported"
            )
        if set(state) != expected_keys:
            raise StateSnapshotCompatibilityError(
                "conversation runtime state has unsupported fields"
            )
        if (
            type(state.get("schema_version")) is not int
            or schema_version not in {
                1,
                2,
                3,
                4,
                5,
                self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION,
            }
        ):
            raise StateSnapshotCompatibilityError(
                "conversation runtime-state schema is unsupported"
            )
        raw_pending = copy.deepcopy(state.get("answer_safe_recheck_pending"))
        require_exact_verification_state = bool(
            schema_version == self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION
        )
        pending = self._validated_answer_safe_recheck_pending_state(
            raw_pending,
            require_exact_verification_state=(
                require_exact_verification_state
            ),
        )
        parked = self._validated_answer_safe_recheck_parked_state(
            state.get("answer_safe_recheck_parked", {}),
            require_exact_verification_state=(
                require_exact_verification_state
            ),
        )
        if schema_version in {
            4,
            5,
            self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION,
        }:
            parked_order = state.get("answer_safe_recheck_parked_order")
            if (
                not isinstance(parked_order, list)
                or len(parked_order) != len(parked)
                or any(not isinstance(identity, str) for identity in parked_order)
                or len(set(parked_order)) != len(parked_order)
                or set(parked_order) != set(parked)
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation parked verifier order is malformed"
                )
            parked = {
                identity: parked[identity]
                for identity in parked_order
            }
        held_terminal = self._validated_answer_safe_recheck_held_terminal_state(
            state.get(
                "answer_safe_recheck_held_terminal_provider_failure",
                {},
            )
        )
        provider_quantum_checkpoint = (
            self._validated_provider_quantum_checkpoint(
                state.get("provider_quantum_checkpoint", {})
            )
            if schema_version
            in {5, self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION}
            else {}
        )
        provider_quantum_yield_generation = 0
        provider_quantum_yield_consumed_generation = 0
        if schema_version in {
            5,
            self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION,
        }:
            provider_quantum_yield_generation = state.get(
                "provider_quantum_yield_generation"
            )
            provider_quantum_yield_consumed_generation = state.get(
                "provider_quantum_yield_consumed_generation"
            )
            if (
                type(provider_quantum_yield_generation) is not int
                or type(provider_quantum_yield_consumed_generation) is not int
                or provider_quantum_yield_generation < 0
                or provider_quantum_yield_generation > 1_000_000
                or provider_quantum_yield_consumed_generation < 0
                or provider_quantum_yield_consumed_generation
                > provider_quantum_yield_generation
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum fairness state is malformed"
                )
        if pending:
            pending_identity = self._answer_safe_recheck_binding_identity(
                dict(pending.get("execution_binding") or {})
            )
            if pending_identity in parked:
                raise StateSnapshotCompatibilityError(
                    "conversation verifier binding has duplicate ownership"
                )
        self._answer_safe_recheck_pending = pending
        self._answer_safe_recheck_parked = parked
        self._answer_safe_recheck_held_terminal_provider_failure = held_terminal
        self._provider_quantum_checkpoint = provider_quantum_checkpoint
        self._provider_quantum_runtime_loaded = bool(
            schema_version
            in {5, self._ANSWER_SAFE_RECHECK_RUNTIME_SCHEMA_VERSION}
        )
        self._provider_quantum_yield_generation = int(
            provider_quantum_yield_generation
        )
        self._provider_quantum_yield_consumed_generation = int(
            provider_quantum_yield_consumed_generation
        )

    def synchronize_scheduler_runtime_state(self, session: Any) -> None:
        """Publish the restored action-owned cursor to the session mirror."""

        if self._answer_safe_recheck_pending and not getattr(
            session,
            "answer_safe_recheck_pending",
            None,
        ):
            setattr(
                session,
                "answer_safe_recheck_pending",
                copy.deepcopy(self._answer_safe_recheck_pending),
            )
        if not self._provider_quantum_runtime_loaded:
            return
        parked_lane_identity = str(
            self._provider_quantum_checkpoint.get("state", {}).get(
                "provider_turn_lane_identity"
            )
            or ""
        ).strip()
        if parked_lane_identity and parked_lane_identity in set(
            getattr(
                session,
                "provider_turn_retired_lane_identities",
                set(),
            )
            or set()
        ):
            self._provider_quantum_checkpoint = {}
            return
        conv = getattr(session, "conv", None)
        if conv is None:
            if not self._provider_quantum_checkpoint:
                return
            raise StateSnapshotCompatibilityError(
                "conversation provider quantum has no live conversation"
            )
        if str(getattr(conv, "role", "") or "").strip() != self.role:
            # Multiple role-owned checkpoints can coexist in one scheduler
            # snapshot even though only one role is mirrored on the shared
            # Conversation. Leave inactive checkpoints parked on their
            # actions; selection reactivates and revalidates the exact owner.
            return
        if not self._provider_quantum_checkpoint:
            if hasattr(conv, "_provider_call_quantum_state"):
                delattr(conv, "_provider_call_quantum_state")
            return
        selected_work_record = (
            self._rehydrate_provider_quantum_selected_work_record(
                self._provider_quantum_checkpoint["binding"].get(
                    "selected_work_record"
                ),
                target=str(
                    self._provider_quantum_checkpoint["binding"].get("target")
                    or ""
                ),
            )
        )
        sanitize_selected_work = getattr(
            session,
            "_sanitize_selected_work_record_answer_aliases",
            None,
        )
        if callable(sanitize_selected_work):
            selected_work_record = dict(
                sanitize_selected_work(selected_work_record) or {}
            )
        session._selected_proof_idea_context_digest = str(
            self._provider_quantum_checkpoint["binding"].get(
                "selected_context_digest"
            )
            or ""
        ).strip()
        if selected_work_record:
            restore_selected_work = getattr(
                session,
                "_restore_selected_work_record",
                None,
            )
            if not callable(restore_selected_work) or not restore_selected_work(
                selected_work_record,
                self.id,
                context="provider_quantum_checkpoint_restore",
                metric_key=(
                    "mini_session_retired_graph_target_provider_quantum_suppressed"
                ),
            ):
                raise StateSnapshotCompatibilityError(
                    "conversation provider quantum selected work is not live"
                )
        else:
            clear_selected_work = getattr(
                session,
                "_clear_selected_work_item",
                None,
            )
            if callable(clear_selected_work):
                clear_selected_work()
            else:
                session.selected_work_item = None
                session.selected_work_item_action_id = ""
                session.selected_work_item_record = {}
        live_target, live_repair_cycle = self._provider_quantum_live_binding(
            session
        )
        checkpoint = self._validated_provider_quantum_checkpoint(
            self._provider_quantum_checkpoint,
            conv=conv,
            expected_target=live_target,
            expected_repair_cycle=live_repair_cycle,
        )
        conv._provider_turn_repair_cycle_identity = str(
            checkpoint["binding"].get("repair_cycle") or ""
        )
        conv._provider_call_quantum_state = copy.deepcopy(checkpoint["state"])
        conv.history = copy.deepcopy(checkpoint["history"])
        if selected_work_record:
            checkpoint["binding"]["selected_work_record"] = (
                self._compact_provider_quantum_selected_work_record(
                    getattr(session, "selected_work_item_record", {}) or {},
                    target=str(checkpoint["binding"].get("target") or ""),
                )
            )
            self._provider_quantum_checkpoint = copy.deepcopy(checkpoint)
            session._provider_quantum_selected_work_restored = True

    def has_answer_safe_recheck_work(
        self,
        *,
        exclude_active: bool = False,
    ) -> bool:
        """Whether authenticated provider-free verifier work remains owned."""

        pending = (
            {}
            if exclude_active
            else self._validated_answer_safe_recheck_pending_state(
                self._answer_safe_recheck_pending
            )
        )
        parked = self._validated_answer_safe_recheck_parked_state(
            self._answer_safe_recheck_parked
        )
        return bool(pending or parked)

    def answer_safe_recheck_work_records(self) -> List[Dict[str, Any]]:
        """Return exact graph selections owning provider-free verification."""

        candidates: List[Dict[str, Any]] = []
        pending = self._validated_answer_safe_recheck_pending_state(
            self._answer_safe_recheck_pending
        )
        if pending:
            candidates.append(pending)
        candidates.extend(
            self._validated_answer_safe_recheck_parked_state(
                self._answer_safe_recheck_parked
            ).values()
        )
        records: List[Dict[str, Any]] = []
        for candidate in candidates:
            binding = dict(candidate.get("execution_binding") or {})
            selected_work_record = dict(
                candidate.get("selected_work_record") or {}
            )
            node_id = str(
                binding.get("selected_node_id")
                or binding.get("graph_node_id")
                or ""
            ).strip()
            work_type = str(
                binding.get("selected_work_type")
                or binding.get("graph_work_type")
                or ""
            ).strip()
            if not node_id or not work_type:
                record = {
                    "_answer_safe_recheck_identity": (
                        self._answer_safe_recheck_binding_identity(binding)
                    ),
                    "_answer_safe_recheck_unscoped": True,
                }
                if not selected_work_record:
                    record["_answer_safe_recheck_legacy_binding"] = binding
                records.append(record)
                continue
            if not selected_work_record:
                # Schema-v1/v2 checkpoints did not preserve the authentic
                # scope packet.  Publish the immutable binding so the session
                # can locate one exact current live-frontier record.  Never
                # manufacture a reduced scheduler record here: that would
                # lose cognition and execution-scope authority.
                records.append(
                    {
                        "_answer_safe_recheck_identity": (
                            self._answer_safe_recheck_binding_identity(binding)
                        ),
                        "_answer_safe_recheck_legacy_binding": binding,
                    }
                )
                continue
            records.append(
                {
                    **selected_work_record,
                    "_answer_safe_recheck_identity": (
                        self._answer_safe_recheck_binding_identity(binding)
                    ),
                    "node_id": node_id,
                    "graph_node_id": str(
                        binding.get("graph_node_id") or node_id
                    ).strip(),
                    "variant_id": str(
                        binding.get("selected_variant_id") or ""
                    ).strip(),
                    "work_type": work_type,
                    "target_statement": str(
                        binding.get("graph_statement") or ""
                    ),
                    "mapped_action_id": self.id,
                }
            )
        return records

    def answer_safe_recheck_is_applicable(
        self,
        session: Any,
        *,
        identity: str,
    ) -> bool:
        """Applicability for authenticated verifier-only ownership.

        This path deliberately does not inspect provider/client availability,
        provider retirement, or semantic model-attempt limits: no provider
        call is made.  Conversation and Lean state remain mandatory, and the
        exact action-owned continuation must still exist.
        """

        if session.conv is None or session.lean is None:
            return False
        clean_identity = str(identity or "").strip()
        if not clean_identity:
            return False
        for candidate in (
            self._validated_answer_safe_recheck_pending_state(
                self._answer_safe_recheck_pending
            ),
            *self._validated_answer_safe_recheck_parked_state(
                self._answer_safe_recheck_parked
            ).values(),
        ):
            if candidate and self._answer_safe_recheck_binding_identity(
                dict(candidate.get("execution_binding") or {})
            ) == clean_identity:
                return True
        return False

    def rebind_legacy_answer_safe_recheck(
        self,
        session: Any,
        *,
        identity: str,
    ) -> str:
        """Migrate one pre-scope-packet continuation to exact live authority."""

        clean_identity = str(identity or "").strip()
        if not clean_identity:
            return ""
        pending = self._validated_answer_safe_recheck_pending_state(
            self._answer_safe_recheck_pending
        )
        parked = self._validated_answer_safe_recheck_parked_state(
            self._answer_safe_recheck_parked
        )
        owner = ""
        candidate: Dict[str, Any] = {}
        if pending and self._answer_safe_recheck_binding_identity(
            dict(pending.get("execution_binding") or {})
        ) == clean_identity:
            owner = "pending"
            candidate = pending
        elif clean_identity in parked:
            owner = "parked"
            candidate = dict(parked[clean_identity])
        if not candidate:
            return ""

        old_binding = dict(candidate.get("execution_binding") or {})
        old_selected_record = copy.deepcopy(
            dict(candidate.get("selected_work_record") or {})
        )
        selected_record = dict(
            getattr(session, "selected_work_item_record", {}) or {}
        )
        selected_work_type = str(
            selected_record.get("work_type") or ""
        ).strip()
        selected_mapped_action = str(
            selected_record.get("mapped_action_id") or ""
        ).strip()
        graph_target = (
            _selected_graph_native_proof_target(session)
            if selected_record
            else {}
        )
        graph_statement = str(graph_target.get("statement") or "").strip()
        if selected_record:
            if not graph_statement:
                return ""
            try:
                _format_graph_native_selected_work_prompt(
                    session,
                    execution_target=graph_target,
                )
            except (SelectedProofIdeaContextError, TypeError, ValueError):
                return ""
        else:
            if any(
                str(old_binding.get(key) or "").strip()
                for key in (
                    "graph_node_id",
                    "graph_work_type",
                    "graph_statement",
                    "selected_node_id",
                    "selected_variant_id",
                    "selected_work_type",
                )
            ):
                return ""
            setattr(session, "_selected_proof_idea_dispatch_packet", {})
            setattr(session, "_selected_proof_idea_context_digest", "")
        current_binding = {
            "graph_node_id": str(graph_target.get("node_id") or ""),
            "graph_work_type": str(graph_target.get("work_type") or ""),
            "graph_statement": graph_statement,
            "graph_scope_key": str(_graph_selected_work_scope_key(session) or ""),
            "selected_node_id": str(selected_record.get("node_id") or ""),
            "selected_variant_id": str(selected_record.get("variant_id") or ""),
            "selected_work_type": selected_work_type,
            "selected_mapped_action": selected_mapped_action,
            "selected_context_digest": str(
                getattr(session, "_selected_proof_idea_context_digest", "") or ""
            ),
            "root_statement": str(
                getattr(session.dossier, "root_statement", "") or ""
            ),
            "conversation_goal_statement": str(
                getattr(session.conv, "goal_statement", "") or ""
            ),
            "lean_preamble": str(getattr(session.conv, "lean_preamble", "") or ""),
            "prompt_preamble": str(getattr(session.conv, "preamble", "") or ""),
            "active_root_targets": copy.deepcopy(
                list(
                    _framed_active_root_targets_for_turn(
                        dossier=session.dossier,
                        conv=session.conv,
                    )
                    or []
                )
            ),
        }
        stable_keys = set(self._ANSWER_SAFE_RECHECK_BINDING_KEYS) - {
            "graph_scope_key",
            "selected_context_digest",
        }
        if any(old_binding.get(key) != current_binding.get(key) for key in stable_keys):
            return ""
        old_context_digest = str(
            old_binding.get("selected_context_digest") or ""
        ).strip()
        current_context_digest = str(
            current_binding.get("selected_context_digest") or ""
        ).strip()
        if old_selected_record:
            def without_revision_derived(value: Any) -> Any:
                if isinstance(value, Mapping):
                    return {
                        str(key): without_revision_derived(item)
                        for key, item in value.items()
                        if str(key) not in _GRAPH_REVISION_DERIVED_SCOPE_KEYS
                    }
                if isinstance(value, list):
                    return [without_revision_derived(item) for item in value]
                if isinstance(value, tuple):
                    return [without_revision_derived(item) for item in value]
                return value

            def normalized_selected_record(value: Mapping[str, Any]) -> Dict[str, Any]:
                normalized = dict(without_revision_derived(value))
                if str(normalized.get("graph_node_id") or "").strip() == str(
                    normalized.get("node_id") or ""
                ).strip():
                    normalized.pop("graph_node_id", None)
                if str(
                    normalized.get("exact_target_statement") or ""
                ).strip() == str(
                    normalized.get("target_statement") or ""
                ).strip():
                    normalized.pop("exact_target_statement", None)
                return normalized

            old_without_revision = normalized_selected_record(old_selected_record)
            current_without_revision = normalized_selected_record(selected_record)
            if old_without_revision != current_without_revision:
                return ""
        elif old_context_digest and old_context_digest != current_context_digest:
            return ""

        migrated = copy.deepcopy(candidate)
        migrated["execution_binding"] = current_binding
        migrated["selected_work_record"] = copy.deepcopy(selected_record)
        try:
            migrated = self._validated_answer_safe_recheck_pending_state(migrated)
        except StateSnapshotCompatibilityError:
            # Historical packets could legitimately consume the full old
            # envelope before selected-scope packets were persisted. Provider
            # transcripts and the replay conversation baseline are not Lean
            # authority; compact them before rejecting an otherwise exact
            # paid proof migration.
            compacted = copy.deepcopy(migrated)
            compacted["sent_messages"] = []
            compacted_turn_entry = dict(compacted.get("turn_entry") or {})
            compacted_turn_entry["history"] = []
            compacted["turn_entry"] = compacted_turn_entry
            migrated = self._validated_answer_safe_recheck_pending_state(
                compacted
            )
        migrated_identity = self._answer_safe_recheck_binding_identity(
            current_binding
        )
        collision_owned = bool(
            migrated_identity != clean_identity
            and (
                (
                    pending
                    and owner != "pending"
                    and self._answer_safe_recheck_binding_identity(
                        dict(pending.get("execution_binding") or {})
                    )
                    == migrated_identity
                )
                or migrated_identity in parked
            )
        )
        if collision_owned:
            # The current exact owner must run first.  Keep this older paid
            # candidate under its original identity; run() will park it when
            # consuming the exact owner, so neither proof is overwritten and
            # checkpoint ownership remains unique.
            return migrated_identity
        if owner == "pending":
            self._answer_safe_recheck_pending = migrated
        else:
            self._answer_safe_recheck_parked.pop(clean_identity, None)
            self._park_answer_safe_recheck(migrated)
        return migrated_identity

    def discard_answer_safe_recheck_work(self, identity: str) -> None:
        """Retire one exact continuation whose graph target is terminal."""

        clean_identity = str(identity or "").strip()
        if not clean_identity:
            return
        pending = self._validated_answer_safe_recheck_pending_state(
            self._answer_safe_recheck_pending
        )
        if pending and self._answer_safe_recheck_binding_identity(
            dict(pending.get("execution_binding") or {})
        ) == clean_identity:
            self._answer_safe_recheck_pending = {}
        self._answer_safe_recheck_parked.pop(clean_identity, None)

    def hold_answer_safe_terminal_provider_failure(
        self,
        metadata: Mapping[str, Any],
    ) -> None:
        """Retain provider terminal authority until paid verification drains."""

        record = {
            "llm_error": str(metadata.get("llm_error") or "")[:4_000],
            "llm_failure_kind": str(
                metadata.get("llm_failure_kind") or ""
            )[:4_000],
            "terminal_failure_reason": str(
                metadata.get("terminal_failure_reason")
                or metadata.get("llm_failure_kind")
                or ""
            )[:4_000],
            "provider_turn_lane_identity": str(
                metadata.get("provider_turn_lane_identity") or ""
            )[:4_000],
        }
        self._answer_safe_recheck_held_terminal_provider_failure = (
            self._validated_answer_safe_recheck_held_terminal_state(record)
        )

    def take_answer_safe_terminal_provider_failure(self) -> Dict[str, Any]:
        """Consume held terminal authority after the last verifier result."""

        record = self._validated_answer_safe_recheck_held_terminal_state(
            self._answer_safe_recheck_held_terminal_provider_failure
        )
        self._answer_safe_recheck_held_terminal_provider_failure = {}
        if not record:
            return {}
        return {
            **record,
            "terminal_failure": True,
            "llm_retryable": False,
            "llm_failure_scope": "global",
            "scoped_failure_reason": "",
            "recovered_finalizer_provider_receipt_activated": True,
            "provider_terminal_released_after_verifier_work": True,
        }

    def has_answer_safe_terminal_provider_failure(self) -> bool:
        """Whether terminal provider authority is waiting behind verification."""

        return bool(
            self._validated_answer_safe_recheck_held_terminal_state(
                self._answer_safe_recheck_held_terminal_provider_failure
            )
        )

    def _live_provider_quantum_owns_checkpoint(self, session: Any) -> bool:
        """Whether the live lane still owns this authenticated checkpoint."""

        conv = getattr(session, "conv", None)
        raw_state = getattr(conv, "_provider_call_quantum_state", None)
        if not isinstance(raw_state, Mapping) or not raw_state:
            return False
        try:
            checkpoint = self._validated_provider_quantum_checkpoint(
                self._provider_quantum_checkpoint,
                conv=conv,
            )
            binding = dict(checkpoint.get("binding") or {})
            live_checkpoint = self._validated_provider_quantum_checkpoint(
                {
                    "state": copy.deepcopy(dict(raw_state)),
                    "history": copy.deepcopy(
                        list(getattr(conv, "history", []) or [])
                    ),
                    "binding": binding,
                },
                conv=conv,
                expected_target=str(binding.get("target") or ""),
                expected_repair_cycle=str(binding.get("repair_cycle") or ""),
            )
        except StateSnapshotCompatibilityError:
            return False
        checkpoint_identity = str(
            (checkpoint.get("state") or {}).get("provider_turn_lane_identity")
            or ""
        ).strip()
        live_identity = str(
            (live_checkpoint.get("state") or {}).get(
                "provider_turn_lane_identity"
            )
            or ""
        ).strip()
        return bool(checkpoint_identity and live_identity == checkpoint_identity)

    def on_outcome_applied(self, _session: Any, _outcome: MiniOutcome) -> None:
        """Retire the in-memory answer-safety recheck after application."""
        metadata = dict(getattr(_outcome, "metadata", {}) or {})
        if bool(metadata.get("provider_call_quantum_exhausted")) and str(
            metadata.get("llm_failure_kind") or ""
        ).strip() in {
            "llm_provider_quantum_exhausted",
            "provider_dispatch_attempt_limit_exhausted",
        }:
            # Capture the exact graph/repair binding before scheduler fairness
            # parks the selected frontier cursor. Later pre-select snapshots
            # can refresh history/state without re-deriving this target from
            # an intentionally cleared session selection.
            try:
                self.prepare_scheduler_runtime_state(_session)
            except StateSnapshotCompatibilityError:
                # Checkpoint capture must not turn a valid in-memory proof
                # continuation into a failed action. Direct snapshot calls
                # remain fail-closed and expose the incompatible state.
                pass
            self._provider_quantum_yield_generation += 1
        else:
            if not self._live_provider_quantum_owns_checkpoint(_session):
                self._provider_quantum_checkpoint = {}
            self._provider_quantum_yield_consumed_generation = int(
                self._provider_quantum_yield_generation
            )
        if not bool(metadata.get("durable_progress_tool_replay_pending")):
            try:
                _session.durable_progress_tool_continuation = {}
            except Exception:
                pass
        if bool(metadata.get("answer_safe_recheck_pending")):
            return
        self._answer_safe_recheck_pending = {}

    def should_yield_static_dispatch(self, session: Any) -> bool:
        """Offer one scheduler quantum to a real independent competitor.

        The scheduler keeps this action as a fallback, so a lone conversation
        continues immediately. An available formal/static lane can run once
        before the next provider generation, preventing a multi-call turn
        from monopolizing the whole MiniSession without misclassifying the
        boundary as a provider failure.
        """

        del session
        if self._provider_quantum_yield_consumed_generation >= (
            self._provider_quantum_yield_generation
        ):
            return False
        self._provider_quantum_yield_consumed_generation = int(
            self._provider_quantum_yield_generation
        )
        return True

    def owns_durable_progress_tool_continuation(
        self,
        identity: str,
        session: Any,
    ) -> bool:
        """Authenticate a target-bound closing-call continuation."""

        return bool(
            self.durable_progress_tool_continuation_payload(
                identity,
                session,
            )
        )

    def durable_progress_tool_continuation_payload(
        self,
        identity: str,
        session: Any,
    ) -> Dict[str, Any]:
        """Return the bounded live replay payload after full validation."""

        clean_identity = str(identity or "").strip()
        conv = getattr(session, "conv", None)
        state = getattr(conv, "_provider_call_quantum_state", {}) or {}
        if not clean_identity or not isinstance(state, Mapping):
            return {}
        target = str(
            state.get("durable_progress_tool_continuation_target") or ""
        ).strip()
        from ensemble_prover.mini_session.turn.tool_loop import (
            _validated_durable_progress_tool_continuation_state,
        )

        validated = _validated_durable_progress_tool_continuation_state(
            state,
            conv=conv,
            dossier=getattr(session, "dossier", None),
            goal_statement_override=target,
            max_tool_calls_per_turn=self.max_tool_calls_per_turn,
        )
        if not (
            validated
            and str(
                validated.get("durable_progress_tool_continuation_identity")
                or ""
            ).strip()
            == clean_identity
        ):
            return {}
        return copy.deepcopy(validated)

    def restore_durable_progress_tool_continuation(
        self,
        identity: str,
        payload: Mapping[str, Any],
        session: Any,
    ) -> bool:
        """Rehydrate bounded closing work without provider timing state."""

        clean_identity = str(identity or "").strip()
        conv = getattr(session, "conv", None)
        if not clean_identity or conv is None or not isinstance(payload, Mapping):
            return False
        previous = getattr(conv, "_provider_call_quantum_state", None)
        had_previous = hasattr(conv, "_provider_call_quantum_state")
        restored = False
        try:
            setattr(
                conv,
                "_provider_call_quantum_state",
                copy.deepcopy(dict(payload)),
            )
            restored = bool(
                self.owns_durable_progress_tool_continuation(
                    clean_identity,
                    session,
                )
            )
            return restored
        finally:
            if not restored:
                if had_previous:
                    setattr(conv, "_provider_call_quantum_state", previous)
                elif hasattr(conv, "_provider_call_quantum_state"):
                    delattr(conv, "_provider_call_quantum_state")

    def owns_paid_tool_retry_continuation(
        self,
        identity: str,
        session: Any,
    ) -> bool:
        """Authenticate scheduler headroom against the live provider lane."""

        clean_identity = str(identity or "").strip()
        conv = getattr(session, "conv", None)
        state = getattr(conv, "_provider_call_quantum_state", {}) or {}
        if not clean_identity or not isinstance(state, Mapping):
            return False
        pending_replay = list(state.get("pending_tool_replay") or ())
        pending_call = (
            pending_replay[0]
            if len(pending_replay) == 1
            and isinstance(pending_replay[0], Mapping)
            else {}
        )
        pending_function = pending_call.get("function")
        pending_tool_name = str(
            pending_function.get("name")
            if isinstance(pending_function, Mapping)
            else ""
        ).strip()
        replay_provenance_authorized = bool(
            state.get("pending_tool_replay_is_paid_retry")
            or str(
                state.get("tool_infrastructure_disposition") or ""
            ).strip()
            == "infrastructure_deferred_before_launch"
        )
        return bool(
            pending_tool_name == "try_lean"
            and replay_provenance_authorized
            and str(state.get("tool_infrastructure_receipt_id") or "").strip()
            == clean_identity
            and str(state.get("provider_turn_lane_identity") or "").strip()
            == _provider_lane_identity_for_session(session, role=self.role)
        )

    def proof_work_portfolio_identity(
        self,
        session: Any,
        _work_item: Any,
    ) -> Dict[str, Any]:
        """Stable model/tool portfolio for semantic no-progress accounting."""

        client = self.client or getattr(session, "prover_client", None)

        def config_record(config: Any) -> Dict[str, Any]:
            if config is None:
                return {}
            record: Dict[str, Any] = {}
            for key in (
                "name",
                "base_url",
                "model",
                "model_revision",
                "revision",
                "deployment_revision",
                "weights_hash",
                "reasoning_effort",
                "thinking_enabled",
                "max_tokens",
                "context_window",
            ):
                try:
                    value = getattr(config, key)
                except (AttributeError, RuntimeError):
                    continue
                if value is None or isinstance(value, (str, int, float, bool)):
                    record[key] = value
                else:
                    record[key] = str(value)
            return record

        configs = getattr(client, "configs", None)
        if isinstance(configs, (list, tuple)) and configs:
            model_identity: Any = [config_record(item) for item in configs]
        else:
            model_identity = config_record(getattr(client, "cfg", None))
        formal_evidence_fn = getattr(
            session,
            "_durable_formal_progress_evidence",
            None,
        )
        formal_evidence = (
            tuple(formal_evidence_fn())
            if callable(formal_evidence_fn)
            else ()
        )
        return {
            "schema_version": 1,
            "role": self.role,
            "model_identity": model_identity,
            "tool_policy": {
                "lean_check": self.lean_check_tool_enabled,
                "try_lean": self.try_lean_tool_enabled,
                "compute_examples": self.compute_examples_tool_enabled,
                "apply_decl_to_goal": self.apply_decl_to_goal_tool_enabled,
                "max_tool_calls_per_turn": self.max_tool_calls_per_turn,
                "raw_feedback": self.raw_feedback,
                "repair_retrieval_enabled": self.repair_retrieval_enabled,
                "repair_retrieval_top_k": self.repair_retrieval_top_k,
            },
            "durable_formal_evidence_hash": hashlib.sha256(
                json.dumps(
                    list(formal_evidence),
                    separators=(",", ":"),
                    ensure_ascii=True,
                ).encode("utf-8")
            ).hexdigest(),
        }

    def is_applicable(self, session: Any) -> bool:
        if session.conv is None or session.lean is None:
            return False
        if (
            self.provider_dispatch_limit > 0
            and max(
                int(
                    getattr(
                        session,
                        "provider_dispatches_started_total",
                        0,
                    )
                    or 0
                ),
                # Plain/legacy clients have no transport authorization hook,
                # so a completed call is their only durable provider-exposure
                # receipt. Either counter must exhaust an operational probe.
                int(
                    getattr(
                        session,
                        "provider_calls_completed_total",
                        0,
                    )
                    or 0
                ),
            )
            >= self.provider_dispatch_limit
        ):
            return False
        if (
            self.has_answer_safe_terminal_provider_failure()
            and not self.has_answer_safe_recheck_work()
        ):
            return False
        durable_continuation = dict(
            getattr(session, "durable_progress_tool_continuation", {}) or {}
        )
        durable_continuation_current = bool(
            str(durable_continuation.get("action_id") or "").strip() == self.id
            and self.owns_durable_progress_tool_continuation(
                str(durable_continuation.get("identity") or ""),
                session,
            )
        )
        retired_provider_lanes = getattr(
            session,
            "provider_turn_retired_lane_identities",
            set(),
        )
        if (
            not durable_continuation_current
            and
            isinstance(retired_provider_lanes, (set, frozenset))
            and _provider_lane_identity_for_session(session, role=self.role)
            in retired_provider_lanes
        ):
            return False
        selected_record = getattr(session, "selected_work_item_record", None)
        if isinstance(selected_record, dict):
            work_type = str(selected_record.get("work_type") or "").strip()
            mapped_action = str(selected_record.get("mapped_action_id") or "").strip()
            if work_type == "assemble_route" and mapped_action in {
                self.id,
                "conversation_turn_prove",
                "conversation_turn_refine",
                "conversation_turn",
            }:
                if not _selected_assemble_route_authoring_ready(session):
                    dossier = getattr(session, "dossier", None)
                    increment = getattr(dossier, "increment_tool_metric", None)
                    if callable(increment):
                        increment(
                            "mini_session_assemble_route_conversation_rejected",
                            1,
                        )
                    return False
        client = self.client or session.prover_client
        if client is None:
            return False
        semantic_work_item_fn = getattr(
            session,
            "_conversation_semantic_work_item",
            None,
        )
        semantic_exhausted_fn = getattr(
            session,
            "proof_work_semantic_attempt_exhausted",
            None,
        )
        if callable(semantic_work_item_fn) and callable(semantic_exhausted_fn):
            semantic_work_item = semantic_work_item_fn(self.id)
            if semantic_work_item is not None and semantic_exhausted_fn(
                semantic_work_item,
                action_id=self.id,
                touch=False,
            ):
                return False
        return True

    async def run(self, session: Any) -> MiniOutcome:  # noqa: C901, PLR0912, PLR0915
        # M4 fix (2026-05-08): every return path must clear
        # ``session.last_turn_extraction`` and ``session.last_lean_verdict``
        # so a subsequent outer-loop dispatch (HelperOnlySalvageAction,
        # PostLeanFailureAction) does not act on stale data from a prior
        # turn. Wrapping the body in try/finally is the only way to
        # guarantee this across the many early returns in the pipeline.
        self._activate_provider_quantum_checkpoint(session)
        pending_residual_requests_at_start = _pending_residual_request_snapshot(
            getattr(session, "proof_state", None)
        )
        pending_helper_requests_at_start = _pending_helper_acceptance_snapshot(
            getattr(session, "proof_state", None)
        )
        conv_at_entry = getattr(session, "conv", None)
        live_history_at_entry = copy.deepcopy(
            list(getattr(conv_at_entry, "history", []) or [])
        )
        live_role_at_entry = str(
            getattr(conv_at_entry, "role", "") or self.role
        )
        live_scope_key_at_entry = str(
            getattr(
                conv_at_entry,
                "_graph_selected_work_last_scope_key",
                "",
            )
            or ""
        )
        live_scope_anchor_at_entry = copy.deepcopy(
            getattr(
                conv_at_entry,
                "_graph_selected_work_scope_anchor_message",
                None,
            )
        )
        live_last_premise_block_at_entry = str(
            getattr(session, "last_premise_block", "") or ""
        )
        live_last_premise_names_at_entry = list(
            getattr(session, "last_premise_names", []) or []
        )
        live_last_premise_injected_at_entry = bool(
            getattr(session, "_last_premise_block_injected", False)
        )
        live_conv_last_content_at_entry = str(
            getattr(conv_at_entry, "_last_llm_content", "") or ""
        )
        self._answer_safe_replay_executed = False
        self._answer_safe_replay_history_baseline = []
        self._answer_safe_replay_content = ""

        def merge_verifier_replay_into_live_history() -> None:
            if not bool(self._answer_safe_replay_executed):
                return
            replay_history = copy.deepcopy(
                list(getattr(conv_at_entry, "history", []) or [])
            )
            replay_baseline = list(
                self._answer_safe_replay_history_baseline or []
            )
            replay_tail = (
                replay_history[len(replay_baseline):]
                if replay_history[: len(replay_baseline)] == replay_baseline
                else []
            )
            conv_at_entry.history = copy.deepcopy(live_history_at_entry)
            conv_at_entry.role = live_role_at_entry
            setattr(
                conv_at_entry,
                "_graph_selected_work_last_scope_key",
                live_scope_key_at_entry,
            )
            setattr(
                conv_at_entry,
                "_graph_selected_work_scope_anchor_message",
                copy.deepcopy(live_scope_anchor_at_entry),
            )
            session.last_premise_block = live_last_premise_block_at_entry
            session.last_premise_names = list(
                live_last_premise_names_at_entry
            )
            session._last_premise_block_injected = (
                live_last_premise_injected_at_entry
            )
            setattr(
                conv_at_entry,
                "_last_llm_content",
                live_conv_last_content_at_entry,
            )
            pending_content = str(self._answer_safe_replay_content or "")
            live_has_pending_assistant = any(
                isinstance(message, Mapping)
                and str(message.get("role") or "") == "assistant"
                and str(message.get("content") or "") == pending_content
                for message in conv_at_entry.history
            )
            retained_tail: List[Dict[str, Any]] = []
            for message in replay_tail:
                if not isinstance(message, Mapping):
                    continue
                clean_message = copy.deepcopy(dict(message))
                if (
                    str(clean_message.get("role") or "") == "assistant"
                    and str(clean_message.get("content") or "")
                    == pending_content
                ):
                    if live_has_pending_assistant:
                        continue
                    live_has_pending_assistant = True
                retained_tail.append(clean_message)
            overlap = 0
            max_overlap = min(
                len(conv_at_entry.history),
                len(retained_tail),
            )
            for overlap_size in range(max_overlap, 0, -1):
                if (
                    conv_at_entry.history[-overlap_size:]
                    == retained_tail[:overlap_size]
                ):
                    overlap = overlap_size
                    break
            conv_at_entry.history.extend(retained_tail[overlap:])
            self._answer_safe_replay_executed = False
            self._answer_safe_replay_history_baseline = []
            self._answer_safe_replay_content = ""

        try:
            outcome = await self._run_impl(session)
            merge_verifier_replay_into_live_history()
            metadata = dict(getattr(outcome, "metadata", {}) or {})
            recovered_candidate_accepted = bool(
                metadata.get("recovered_finalizer_candidate_lean_accepted")
                or getattr(outcome, "solved", False)
                or getattr(outcome, "root_candidate", None) is not None
                or str(metadata.get("lean_verdict") or "").strip()
                in {
                    "graph_native_formalization_accepted",
                    "graph_native_lean_accepted",
                    "lean_accepted",
                }
            )
            recovered_candidate_adjudication_pending = bool(
                metadata.get("recovered_finalizer_candidate_adjudication_pending")
            )
            if (
                not recovered_candidate_accepted
                and not recovered_candidate_adjudication_pending
                and not str(metadata.get("llm_failure_kind") or "").strip()
                and not bool(metadata.get("terminal_failure"))
            ):
                recovered_failure_metadata = (
                    _activated_recovered_finalizer_failure_metadata(metadata)
                )
                if recovered_failure_metadata:
                    metadata.update(recovered_failure_metadata)
                    outcome = replace(outcome, metadata=metadata)
            pending_residual_requests_at_end = (
                _pending_residual_request_snapshot(
                    getattr(session, "proof_state", None)
                )
            )
            newly_pending_request_ids = sorted(
                set(pending_residual_requests_at_end)
                - set(pending_residual_requests_at_start)
            )
            pending_helper_requests_at_end = (
                _pending_helper_acceptance_snapshot(
                    getattr(session, "proof_state", None)
                )
            )
            newly_pending_helper_ids = sorted(
                set(pending_helper_requests_at_end)
                - set(pending_helper_requests_at_start)
            )
            pending_handoff_unsuperseded = bool(
                (newly_pending_request_ids or newly_pending_helper_ids)
                and not bool(getattr(outcome, "solved", False))
                and getattr(outcome, "root_candidate", None) is None
                and not bool(metadata.get("terminal_failure"))
            )
            pending_handoff_iteration_neutral = bool(
                pending_handoff_unsuperseded
                and not pending_residual_requests_at_start
                and not pending_helper_requests_at_start
            )
            if pending_handoff_unsuperseded:
                pending_residual_node_ids = sorted(
                    {
                        pending_residual_requests_at_end[request_id]
                        for request_id in newly_pending_request_ids
                    }
                )
                pending_helper_node_ids = sorted(
                    {
                        pending_helper_requests_at_end[request_id]
                        for request_id in newly_pending_helper_ids
                    }
                )
                metadata["pending_verifier_handoff_added"] = True
                metadata["pending_verifier_handoff_started_with_pending"] = bool(
                    pending_residual_requests_at_start
                    or pending_helper_requests_at_start
                )
                if newly_pending_request_ids:
                    metadata.update({
                        "pending_residual_goal_extraction_added": True,
                        "pending_residual_goal_extraction_preserved": True,
                        "pending_residual_goal_extraction_retry": True,
                        "pending_residual_goal_extraction_started_with_pending": bool(
                            pending_residual_requests_at_start
                            or pending_helper_requests_at_start
                        ),
                        "pending_residual_goal_extraction_request_ids": list(
                            newly_pending_request_ids
                        ),
                        "pending_residual_goal_extraction_node_ids": (
                            pending_residual_node_ids
                        ),
                    })
                if newly_pending_helper_ids:
                    metadata.update(
                        {
                            "pending_helper_acceptance_added": True,
                            "pending_helper_acceptance_preserved": True,
                            "pending_helper_acceptance_request_ids": list(
                                newly_pending_helper_ids
                            ),
                            "pending_helper_acceptance_node_ids": (
                                pending_helper_node_ids
                            ),
                        }
                    )
                if pending_handoff_iteration_neutral:
                    # The provider/tool call has already paid to create this
                    # exact residual frame. Reserve one nominal-final-iteration
                    # slot for deterministic verifier replay. A later turn
                    # that starts with any pending frame receives no refund,
                    # preventing repeated infrastructure deferrals from
                    # becoming a zero-cost loop.
                    metadata.update(
                        {
                            "iteration_neutral": True,
                            "scheduler_neutral": True,
                            "stagnation_neutral": True,
                            "hard_pivot_neutral": True,
                            "preserve_frontier_work": True,
                            "preserve_action_budget": True,
                            "defer_selected_frontier_action": False,
                            "non_consuming_repair_ticket_continuation": True,
                        }
                    )
                outcome = replace(
                    outcome,
                    progress=bool(
                        getattr(outcome, "progress", False)
                        or pending_handoff_iteration_neutral
                    ),
                    metadata=metadata,
                )
            response = str(metadata.get("llm_response") or "").strip()
            recorder = getattr(
                getattr(session, "conv", None),
                "record_suppressed_assistant_handoff_evidence",
                None,
            )
            if (
                response
                and not bool(getattr(outcome, "solved", False))
                and callable(recorder)
            ):
                recorder(
                    response,
                    reason=str(
                        metadata.get("rejection_reason")
                        or metadata.get("verdict")
                        or "non_replayed_response"
                    ),
                )
            return outcome
        finally:
            merge_verifier_replay_into_live_history()
            session.last_turn_extraction = None
            session.last_lean_verdict = None
            session.last_llm_content = ""

    async def _run_impl(self, session: Any) -> MiniOutcome:  # noqa: C901, PLR0912, PLR0915
        from ensemble_prover.helper_salvage import (
            merge_context_helpers,
            merge_helpers_for_correction_recheck,
            refresh_revalidated_dependent_support_hashes,
        )
        from ensemble_prover.mini_session.turn import (
            AnswerSafeRecheckInfrastructureError,
            ToolLoopResult,
            apply_policy_gates,
            apply_proof_patch_from_reply,
            call_llm_with_tools_one_round,
            extract_helpers_and_proof,
            format_proof_patch_failure_feedback,
            verify_with_lean,
        )
        from ensemble_prover.mini_temperature import (
            MiniTemperatureContext,
            refresh_temperature_metadata_from_client,
            resolve_mini_temperature,
        )
        from ensemble_prover.proof_dossier import helper_decl_name
        from ensemble_prover.mini_prover import (
            CHECK_LEAN_TOOL,
            SEARCH_MATHLIB_TOOL,
            SEARCH_THEOREMS_TOOL,
            _searcher_supports_static_mathlib,
            _REPAIR_FEEDBACK,
            _REPAIR_CONTINUATION,
            _repair_turn_requires_self_check,
        )
        from ensemble_prover.proof_tools import (
            APPLY_DECL_TO_ACTIVE_GOAL_TOOL as APPLY_DECL_TO_GOAL_TOOL,
        )
        from ensemble_prover.lean_compute_tool import COMPUTE_EXAMPLES_TOOL
        from ensemble_prover.skeleton_tool import TRY_SKELETON_TOOL
        from ensemble_prover.try_lean_tool import TRY_LEAN_TOOL
        from ensemble_prover.certify_counterexample_tool import (
            CERTIFY_COUNTEREXAMPLE_TOOL,
        )

        started = time.monotonic()
        dispatch_id = str(
            getattr(session, "_inflight_action_dispatch_id", "") or ""
        ).strip()

        def publication_guard() -> None:
            require_current_action_dispatch(session, dispatch_id)

        client = self.client or session.prover_client
        model_id = str(
            getattr(getattr(client, "cfg", None), "model", "")
            or getattr(client, "model", "")
            or ""
        )
        base_searcher = (
            self.searcher_override
            if self.searcher_override is not None
            else session.searcher
        )
        searcher = base_searcher
        conv = session.conv
        dossier = session.dossier
        proof_state = session.proof_state
        answer_safe_pending = dict(self._answer_safe_recheck_pending or {})
        answer_safe_pending_replay = bool(
            answer_safe_pending.get("active") is True
            and str(answer_safe_pending.get("role") or "") == self.role
            and str(answer_safe_pending.get("content") or "").strip()
            and isinstance(answer_safe_pending.get("turn_entry"), dict)
        )
        graph_native_target = _selected_graph_native_proof_target(session)
        graph_native_goal_statement = str(
            graph_native_target.get("statement") or ""
        ).strip()
        formalization_helper_contract = _selected_formalization_helper_contract(
            session,
            graph_native_goal_statement=graph_native_goal_statement,
        )
        initial_framed_active_root_targets = _framed_active_root_targets_for_turn(
            dossier=dossier,
            conv=conv,
        )
        selected_record = dict(
            getattr(session, "selected_work_item_record", {}) or {}
        )
        selected_work_type = str(
            selected_record.get("work_type") or ""
        ).strip()
        selected_mapped_action = str(
            selected_record.get("mapped_action_id") or ""
        ).strip()
        selected_graph_execution_required = bool(
            selected_work_type in _GRAPH_NATIVE_PROOF_WORK_TYPES
            and selected_mapped_action
            in {
                "",
                "conversation_turn_prove",
                "conversation_turn_refine",
                "conversation_turn",
            }
            and not formalization_helper_contract
        )
        if not selected_graph_execution_required:
            # A root/unscoped turn has no selected cognition packet.  Clear a
            # prior graph target before hashing the immutable verifier replay
            # binding; the graph-prompt formatter returns early for unscoped
            # work and therefore cannot own this reset.
            setattr(session, "_selected_proof_idea_dispatch_packet", {})
            setattr(session, "_selected_proof_idea_context_digest", "")
        # Resolve selected cognition before constructing the immutable replay
        # binding.  Prompt rendering owns that resolution and publishes its
        # exact digest; capturing the binding first would make the paid proof
        # stale as a side effect of its own initial dispatch.
        graph_native_prompt = ""
        if not selected_graph_execution_required or graph_native_goal_statement:
            try:
                graph_native_prompt = _format_graph_native_selected_work_prompt(
                    session,
                    execution_target=graph_native_target,
                )
            except SelectedProofIdeaContextError as exc:
                if conv is not None:
                    _purge_stored_graph_selected_work_prompts(conv)
                setattr(session, "_selected_proof_idea_dispatch_packet", {})
                setattr(session, "_selected_proof_idea_context_digest", "")
                _emit_record(session, {
                    "phase": self.role,
                    "selected_work_item": selected_record,
                    "error": str(exc),
                    "verdict": "selected_proof_idea_projection_invalidated",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "lean_verdict": "selected_graph_execution_binding_rejected",
                        "lean_error_type": "selected_proof_idea_context_stale",
                        "scoped_failure_reason": str(exc),
                        "selected_work_item": selected_record,
                        "selected_work_projection_invalidated": True,
                        "selected_work_projection_zero_provider": True,
                        "preserve_frontier_work": False,
                        "scheduler_neutral": True,
                        "stagnation_neutral": True,
                        "hard_pivot_neutral": True,
                        "strong_progress": False,
                    },
                )
        current_answer_safe_execution_binding = {
            "graph_node_id": str(graph_native_target.get("node_id") or ""),
            "graph_work_type": str(graph_native_target.get("work_type") or ""),
            "graph_statement": graph_native_goal_statement,
            "graph_scope_key": str(_graph_selected_work_scope_key(session) or ""),
            "selected_node_id": str(selected_record.get("node_id") or ""),
            "selected_variant_id": str(selected_record.get("variant_id") or ""),
            "selected_work_type": selected_work_type,
            "selected_mapped_action": selected_mapped_action,
            "selected_context_digest": str(
                getattr(session, "_selected_proof_idea_context_digest", "") or ""
            ),
            "root_statement": str(
                getattr(dossier, "root_statement", "") or ""
            ),
            "conversation_goal_statement": str(
                getattr(conv, "goal_statement", "") or ""
            ),
            "lean_preamble": str(getattr(conv, "lean_preamble", "") or ""),
            "prompt_preamble": str(getattr(conv, "preamble", "") or ""),
            "active_root_targets": copy.deepcopy(
                list(initial_framed_active_root_targets or [])
            ),
        }
        current_binding_identity = self._answer_safe_recheck_binding_identity(
            current_answer_safe_execution_binding
        )
        # Claim the exact current target before parking a mismatched active
        # continuation.  Otherwise a full bounded queue can evict the very
        # entry this invocation is about to consume.
        parked_for_current = self._answer_safe_recheck_parked.pop(
            current_binding_identity,
            None,
        )
        if answer_safe_pending_replay and dict(
            answer_safe_pending.get("execution_binding") or {}
        ) != current_answer_safe_execution_binding:
            self._park_answer_safe_recheck(answer_safe_pending)
            answer_safe_pending = {}
            answer_safe_pending_replay = False
            self._answer_safe_recheck_pending = {}
        if parked_for_current:
            answer_safe_pending = dict(parked_for_current)
            answer_safe_pending_replay = True
            self._answer_safe_recheck_pending = copy.deepcopy(
                answer_safe_pending
            )
        setattr(
            session,
            "answer_safe_recheck_pending",
            (
                copy.deepcopy(answer_safe_pending)
                if answer_safe_pending_replay
                else None
            ),
        )
        expected_answer_safe_execution_binding = dict(
            answer_safe_pending.get("execution_binding") or {}
        )
        live_turn_state_before_answer_safe_replay = {
            "history": copy.deepcopy(list(getattr(conv, "history", []) or [])),
            "role": str(getattr(conv, "role", "") or self.role),
            "graph_last_scope_key": str(
                getattr(conv, "_graph_selected_work_last_scope_key", "") or ""
            ),
            "graph_scope_anchor_message": copy.deepcopy(
                getattr(conv, "_graph_selected_work_scope_anchor_message", None)
            ),
            "last_premise_block": str(
                getattr(session, "last_premise_block", "") or ""
            ),
            "last_premise_names": list(
                getattr(session, "last_premise_names", []) or []
            ),
            "last_premise_block_injected": bool(
                getattr(session, "_last_premise_block_injected", False)
            ),
            "last_llm_content": str(
                getattr(session, "last_llm_content", "") or ""
            ),
            "conv_last_llm_content": str(
                getattr(conv, "_last_llm_content", "") or ""
            ),
        }

        def restore_live_turn_state() -> None:
            record = live_turn_state_before_answer_safe_replay
            conv.history = copy.deepcopy(list(record["history"]))
            conv.role = str(record["role"])
            setattr(
                conv,
                "_graph_selected_work_last_scope_key",
                str(record["graph_last_scope_key"]),
            )
            setattr(
                conv,
                "_graph_selected_work_scope_anchor_message",
                copy.deepcopy(record["graph_scope_anchor_message"]),
            )
            session.last_premise_block = str(record["last_premise_block"])
            session.last_premise_names = list(record["last_premise_names"])
            session._last_premise_block_injected = bool(
                record["last_premise_block_injected"]
            )
            session.last_llm_content = str(record["last_llm_content"])
            setattr(
                conv,
                "_last_llm_content",
                str(record["conv_last_llm_content"]),
            )

        if answer_safe_pending_replay:
            # Restore the prompt-side state from immediately before the paid
            # turn.  The provider response itself is retained below, so this
            # continuation can traverse the normal extraction/finalization
            # pipeline without duplicating the assistant message or its
            # infrastructure feedback in history.
            turn_entry = dict(answer_safe_pending["turn_entry"])
            conv.history = copy.deepcopy(list(turn_entry.get("history") or []))
            if "role" in turn_entry:
                conv.role = str(turn_entry.get("role") or self.role)
            setattr(
                conv,
                "_graph_selected_work_last_scope_key",
                str(turn_entry.get("graph_last_scope_key") or ""),
            )
            setattr(conv, "_graph_selected_work_scope_anchor_message", None)
            session.last_premise_block = str(
                turn_entry.get("last_premise_block") or ""
            )
            session.last_premise_names = list(
                turn_entry.get("last_premise_names") or []
            )
            session._last_premise_block_injected = bool(
                turn_entry.get("last_premise_block_injected")
            )
            self._answer_safe_replay_executed = True
            self._answer_safe_replay_content = str(
                answer_safe_pending.get("content") or ""
            )
            self._answer_safe_replay_history_baseline = copy.deepcopy(
                list(getattr(conv, "history", []) or [])
            )
        turn_entry_replay_snapshot = {
            "history": copy.deepcopy(list(getattr(conv, "history", []) or [])),
            "role": str(getattr(conv, "role", "") or self.role),
            "graph_last_scope_key": str(
                getattr(conv, "_graph_selected_work_last_scope_key", "") or ""
            ),
            "last_premise_block": str(
                getattr(session, "last_premise_block", "") or ""
            ),
            "last_premise_names": list(
                getattr(session, "last_premise_names", []) or []
            ),
            "last_premise_block_injected": bool(
                getattr(session, "_last_premise_block_injected", False)
            ),
        }
        local_micro_theory_metadata: Dict[str, Any] = {}
        local_micro_theory_suppresses_library = (
            _local_micro_theory_suppresses_library_tools(session)
        )
        if local_micro_theory_suppresses_library:
            prompt_text = ""
            prompt_getter = getattr(session, "local_micro_theory_prompt_text", None)
            if callable(prompt_getter):
                prompt_text = str(prompt_getter() or "").strip()
            if prompt_text and conv is not None:
                conv.append_user(
                    prompt_text,
                    repair_semantics=_REPAIR_CONTINUATION,
                )
            consume = getattr(
                session,
                "consume_local_micro_theory_suppressed_turn",
                None,
            )
            if callable(consume):
                local_micro_theory_metadata.update(dict(consume() or {}))
            local_micro_theory_metadata.setdefault(
                "local_micro_theory_search_suppressed",
                True,
            )
            searcher = None

        # Legacy refiner handoff is role-driven: when the refiner action
        # first takes over it switches the conversation role and appends the
        # explicit recovery instruction before the next LLM call.
        if conv is not None and str(getattr(conv, "role", "") or "") != self.role:
            try:
                conv.role = self.role
                conv.turn_budget = self.max_turns_for_budget or getattr(conv, "turn_budget", 0)
                if self.role == "refine":
                    summarize = getattr(
                        conv,
                        "append_suppressed_draft_handoff_summary",
                        None,
                    )
                    if callable(summarize):
                        summarize()
                    conv.append_user(
                        f"Refiner phase begins. You have {conv.turn_budget} refiner "
                        "turn(s). Recover the blocked local proof obligation from "
                        "the problem and transcript, manufacture needed bridge "
                        "facts as local `have`/`suffices` steps or exact helper "
                        "statements, then submit one Lean proof attempt for the "
                        "active goal. Any helper declarations must be fully proved; "
                        "do not replace the proof attempt with helper stubs."
                    )
            except Exception:
                pass

        if selected_graph_execution_required and not graph_native_goal_statement:
            # A selected graph prompt and its executable Lean target form one
            # dispatch authority.  Never expose target X and then fall back to
            # verifying the ambient root Y when the selected graph identity is
            # stale, missing, quarantined, or otherwise non-executable.
            if conv is not None:
                try:
                    _purge_stored_graph_selected_work_prompts(conv)
                except Exception:
                    pass
            setattr(session, "_selected_proof_idea_dispatch_packet", {})
            setattr(session, "_selected_proof_idea_context_digest", "")
            _emit_record(session, {
                "phase": self.role,
                "selected_work_item": selected_record,
                "lean_error_type": "selected_graph_execution_target_unavailable",
                "verdict": "selected_graph_execution_binding_rejected",
            })
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "role": self.role,
                    "lean_verdict": "selected_graph_execution_binding_rejected",
                    "lean_error_type": (
                        "selected_graph_execution_target_unavailable"
                    ),
                    "selected_work_item": selected_record,
                    "selected_work_projection_invalidated": True,
                    "preserve_frontier_work": False,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "strong_progress": False,
                },
            )

        if graph_native_prompt and conv is not None:
            try:
                graph_scope_key = _graph_selected_work_scope_key(session)
                _purge_stored_graph_selected_work_prompts(
                    conv,
                    new_scope_key=graph_scope_key,
                )
                if bool(
                    getattr(conv, "_graph_selected_work_scope_changed", False)
                ) and bool(
                    getattr(session, "_last_premise_block_injected", False)
                ):
                    # Premise retrieval is target-local too. A block injected
                    # for the retired target must be regenerated rather than
                    # silently carried into the new proof obligation.  A
                    # not-yet-injected block was retrieved for the new target,
                    # however, and must survive this purge so the paid result
                    # reaches the provider below.
                    session.last_premise_block = ""
                    session.last_premise_names = []
                    session._last_premise_block_injected = False
                    increment = getattr(session, "_increment_dossier_metric", None)
                    if callable(increment):
                        increment(
                            "mini_session_graph_target_context_resets",
                            1,
                        )
                appended_graph_prompt = getattr(
                    conv,
                    "_graph_selected_work_scope_anchor_message",
                    None,
                )
                if isinstance(appended_graph_prompt, dict):
                    appended_graph_prompt["content"] = graph_native_prompt
                    appended_graph_prompt["_repair_semantics"] = (
                        _REPAIR_CONTINUATION
                    )
                else:
                    appended_graph_prompt = conv.append_user(
                        graph_native_prompt,
                        repair_semantics=_REPAIR_CONTINUATION,
                    )
                # The graph-selected packet carries the exact executable
                # target and its primary proof-idea cognition.  Provider
                # budget handling must omit optional history before it and
                # must fail explicitly rather than prefix-trimming it.
                if isinstance(appended_graph_prompt, dict):
                    appended_graph_prompt["pinned"] = True
                    appended_graph_prompt["_required_prompt_context"] = {
                        "kind": "selected_work",
                        "units": [
                            "executable_target",
                            "selected_core",
                            "current_attempt",
                            "current_residual",
                        ],
                        "scope_key": graph_scope_key,
                        "context_digest": str(
                            getattr(
                                session,
                                "_selected_proof_idea_context_digest",
                                "",
                            )
                            or ""
                        ),
                    }
                    appended_graph_prompt["_selected_proof_idea_packet"] = (
                        copy.deepcopy(
                            getattr(
                                session,
                                "_selected_proof_idea_dispatch_packet",
                                {},
                            )
                            or {}
                        )
                    )
                if graph_scope_key:
                    if (
                        isinstance(appended_graph_prompt, dict)
                        and any(
                            message is appended_graph_prompt
                            for message in list(conv.history or ())
                        )
                    ):
                        appended_graph_prompt[_GRAPH_SELECTED_WORK_SCOPE_KEY] = (
                            graph_scope_key
                        )
                    else:
                        for message in reversed(list(conv.history or ())):
                            if (
                                isinstance(message, dict)
                                and message.get("role") == "user"
                                and str(message.get("content") or "")
                                == graph_native_prompt
                            ):
                                message["pinned"] = True
                                message["_required_prompt_context"] = {
                                    "kind": "selected_work",
                                    "units": [
                                        "executable_target",
                                        "selected_core",
                                        "current_attempt",
                                        "current_residual",
                                    ],
                                    "scope_key": graph_scope_key,
                                    "context_digest": str(
                                        getattr(
                                            session,
                                            "_selected_proof_idea_context_digest",
                                            "",
                                        )
                                        or ""
                                    ),
                                }
                                message["_selected_proof_idea_packet"] = (
                                    copy.deepcopy(
                                        getattr(
                                            session,
                                            "_selected_proof_idea_dispatch_packet",
                                            {},
                                        )
                                        or {}
                                    )
                                )
                                message[_GRAPH_SELECTED_WORK_SCOPE_KEY] = (
                                    graph_scope_key
                                )
                                break
                    setattr(
                        conv,
                        "_graph_selected_work_last_scope_key",
                        graph_scope_key,
                    )
            except Exception:
                graph_native_prompt = ""
        elif conv is not None:
            # A pinned selected-work packet is dispatch authority only for the
            # graph-native target rendered on this turn.  Root repair (and any
            # other unselected lane) must not inherit a historical packet: its
            # graph revision may be genuinely stale even though the current
            # turn no longer has graph-selected work to refresh it against.
            try:
                _purge_stored_graph_selected_work_prompts(conv)
            except Exception:
                pass
            if bool(getattr(session, "_last_premise_block_injected", False)):
                session.last_premise_block = ""
                session.last_premise_names = []
                session._last_premise_block_injected = False
            setattr(session, "_selected_proof_idea_dispatch_packet", {})
            setattr(session, "_selected_proof_idea_context_digest", "")

        # Premise blocks are target-local provider input.  Inject only after
        # the selected-work purge has settled so a freshly retrieved B block
        # cannot be appended behind A and immediately deleted unseen.
        pending_premise_block = str(
            getattr(session, "last_premise_block", "") or ""
        ).strip()
        if pending_premise_block and not bool(
            getattr(session, "_last_premise_block_injected", False)
        ):
            conv.append_user(
                pending_premise_block,
                repair_semantics=_REPAIR_CONTINUATION,
            )
            known_names = list(getattr(conv, "known_premise_names", []) or [])
            seen_names = set(known_names)
            for name in list(getattr(session, "last_premise_names", []) or []):
                name_str = str(name or "").strip()
                if name_str and name_str not in seen_names:
                    known_names.append(name_str)
                    seen_names.add(name_str)
            conv.known_premise_names = known_names
            session._last_premise_block_injected = True
        if conv is not None:
            try:
                conv.declaration_required_submission = bool(
                    formalization_helper_contract
                )
            except Exception:
                pass
        assemble_route_goal_statement = (
            _selected_assemble_route_goal_statement(session)
            if _selected_assemble_route_authoring_ready(session)
            else ""
        )
        assemble_route_contract_status: Dict[str, Any] = {}
        assemble_route_helper_names: List[str] = []
        assemble_route_helper_blocks: List[str] = []
        if assemble_route_goal_statement:
            (
                assemble_route_contract_status,
                assemble_route_helper_names,
                assemble_route_helper_blocks,
            ) = _selected_assemble_route_contract_context(session)
        llm_dossier = dossier
        if assemble_route_goal_statement and dossier is not None:
            try:
                llm_dossier = copy.copy(dossier)
                setattr(llm_dossier, "_mini_skip_proof_state_reconcile", True)
                verified_helpers = getattr(dossier, "verified_helpers", {}) or {}
                if isinstance(verified_helpers, dict):
                    llm_dossier.verified_helpers = {
                        name: verified_helpers[name]
                        for name in assemble_route_helper_names
                        if name in verified_helpers
                    }
                if hasattr(llm_dossier, "proposed_helpers"):
                    llm_dossier.proposed_helpers = {}
            except Exception:
                llm_dossier = dossier
        selected_goal_statement_override = graph_native_goal_statement or None
        llm_goal_statement_override = selected_goal_statement_override
        if assemble_route_goal_statement and not llm_goal_statement_override:
            llm_goal_statement_override = assemble_route_goal_statement
        graph_native_attempt_node_id = (
            str(graph_native_target.get("node_id") or "").strip()
            if graph_native_goal_statement and graph_native_target
            else ""
        )
        graph_native_attempt_metadata = (
            {
                "selected_graph_work": dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                ),
                "graph_native_goal_statement": graph_native_goal_statement,
                "graph_native_work_type": graph_native_target.get("work_type"),
            }
            if graph_native_attempt_node_id
            else None
        )

        # Absolute turn index — see R12.5.
        role_key = str(getattr(conv, "role", "") or self.role or "prove")
        if answer_safe_pending_replay:
            conv_turn_offset = max(
                0,
                int(
                    answer_safe_pending.get("conv_turn_offset", 0)
                    or 0
                ),
            )
            absolute_turn = conv_turn_offset + 1
            phase_turn = max(
                1,
                int(
                    answer_safe_pending.get("phase_turn", 1)
                    or 1
                ),
            )
            # The answer-safe recheck belongs to the current live turn, so it
            # does not consume another turn from the session budget.
            session._conversation_turn_count = max(
                int(getattr(session, "_conversation_turn_count", 0) or 0),
                absolute_turn,
            )
            role_counts = getattr(
                session,
                "_conversation_role_turn_counts",
                None,
            )
            if not isinstance(role_counts, dict):
                role_counts = {}
            role_counts[role_key] = max(
                int(role_counts.get(role_key, 0) or 0),
                phase_turn,
            )
            session._conversation_role_turn_counts = role_counts
        else:
            conv_turn_offset = int(
                getattr(session, "_conversation_turn_count", 0)
            )
            session._conversation_turn_count = conv_turn_offset + 1
            absolute_turn = conv_turn_offset + 1
            role_counts = getattr(
                session,
                "_conversation_role_turn_counts",
                None,
            )
            if not isinstance(role_counts, dict):
                role_counts = {}
            phase_turn = int(role_counts.get(role_key, 0) or 0) + 1
            role_counts[role_key] = phase_turn
            session._conversation_role_turn_counts = role_counts
            exposure_counts = getattr(
                session,
                "_conversation_role_turn_exposure_counts",
                None,
            )
            if not isinstance(exposure_counts, dict):
                exposure_counts = {}
            exposure_counts[role_key] = max(
                0,
                int(exposure_counts.get(role_key, 0) or 0),
            ) + 1
            session._conversation_role_turn_exposure_counts = exposure_counts

        # M5: reset per-turn fired flags. The session lives across many
        # turns; observability dedup is scoped to the current turn only.
        _reset_per_turn_fired_flags(session, absolute_turn)

        # MED-4: the budget footer max_turns is the outer-loop iteration
        # count, not the inner always-1 turn. Use the action's configured
        # value when set, else fall back to the session's max_iterations.
        max_turns_footer = self.max_turns_for_budget or int(
            getattr(session, "max_iterations", 0) or 0
        )

        if graph_native_goal_statement and not answer_safe_pending_replay:
            try:
                from ensemble_prover.proof_state_executor import (
                    ensure_current_typed_residual_attestation_retries,
                )

                ensure_current_typed_residual_attestation_retries(
                    conv=getattr(session, "conv", None),
                    dossier=getattr(session, "dossier", None),
                    lean=getattr(session, "lean", None),
                    proof_state=getattr(session, "proof_state", None),
                )
            except Exception:
                pass
            residual_attestation_status = (
                _graph_native_residual_attestation_status(
                    session=session,
                    graph_native_target=graph_native_target,
                )
            )
            if residual_attestation_status in {
                "residual_elaboration_attestation_required",
                "residual_elaboration_reattestation_required",
            }:
                reattestation_pending = residual_attestation_status == (
                    "residual_elaboration_reattestation_required"
                )
                proof_state_node = (
                    getattr(getattr(session, "proof_state", None), "nodes", {})
                    or {}
                ).get(str(graph_native_target.get("node_id") or ""))
                if proof_state_node is not None and not reattestation_pending:
                    proof_state_node.status = "blocked"
                    proof_state_node.action = residual_attestation_status
                    proof_state_node.blocker = residual_attestation_status
                    proof_state_node.priority = 0.0
                _emit_record(session, {
                    "phase": self.role,
                    "turn_in_phase": phase_turn,
                    "model": model_id,
                    "graph_native_goal_statement": graph_native_goal_statement,
                    "graph_native_target_node_id": graph_native_target.get(
                        "node_id"
                    ),
                    "graph_native_work_type": graph_native_target.get("work_type"),
                    "residual_goal_attestation_status": (
                        residual_attestation_status
                    ),
                    "provider_attempts": [],
                    "verdict": (
                        "residual_goal_reattestation_deferred"
                        if reattestation_pending
                        else "residual_goal_dispatch_quarantined"
                    ),
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        "graph_native_goal_statement": (
                            graph_native_goal_statement
                        ),
                        "graph_native_target_node_id": graph_native_target.get(
                            "node_id"
                        ),
                        "residual_goal_attestation_status": (
                            residual_attestation_status
                        ),
                        "residual_goal_dispatch_quarantined": bool(
                            not reattestation_pending
                        ),
                        "residual_goal_reattestation_pending": bool(
                            reattestation_pending
                        ),
                        "provider_attempts": [],
                        "preserve_action_budget": True,
                        "preserve_frontier_work": bool(reattestation_pending),
                        "refund_conversation_phase_turn": True,
                        "refund_conversation_absolute_turn": True,
                        "non_consuming_repair_ticket_continuation": True,
                        "scheduler_neutral": True,
                        "stagnation_neutral": True,
                        "hard_pivot_neutral": True,
                        "graph_work_consumed_verdict": (
                            "residual_goal_reattestation_deferred"
                            if reattestation_pending
                            else "residual_goal_dispatch_quarantined"
                        ),
                        "graph_work_consumed_error_type": (
                            residual_attestation_status
                        ),
                    },
                )
            # Exact verifier-only replay already passed this target precheck
            # before the paid provider turn, and its immutable binding pins
            # the statement plus both preambles.  Repeating the precheck can
            # only introduce an unrelated infrastructure pause before the
            # owned candidate reaches its conclusive Lean adjudication.
            type_status = (
                {"ok": True, "inconclusive": False, "output": ""}
                if answer_safe_pending_replay
                else await _typecheck_graph_native_goal_statement(
                    session=session,
                    statement=graph_native_goal_statement,
                )
            )
            if not bool(type_status.get("ok")) and not bool(
                type_status.get("inconclusive")
            ):
                type_output = str(type_status.get("output") or "")
                _mark_graph_native_goal_statement_type_rejected(
                    session=session,
                    graph_native_target=graph_native_target,
                    output=type_output,
                    phase_turn=phase_turn,
                )
                _emit_record(session, {
                    "phase": self.role,
                    "turn_in_phase": phase_turn,
                    "model": model_id,
                    "graph_native_goal_statement": graph_native_goal_statement,
                    "graph_native_target_node_id": graph_native_target.get("node_id"),
                    "graph_native_work_type": graph_native_target.get("work_type"),
                    "lean_output": type_output[:1200],
                    "lean_error_type": "graph_native_statement_type_rejected",
                    "verdict": "graph_native_statement_type_rejected",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        "lean_verdict": "graph_native_statement_type_rejected",
                        "lean_error": type_output,
                        "lean_error_type": "graph_native_statement_type_rejected",
                        "graph_native_goal_statement": graph_native_goal_statement,
                        "graph_native_target_node_id": graph_native_target.get(
                            "node_id"
                        ),
                        "graph_work_consumed_verdict": (
                            "graph_native_statement_type_rejected"
                        ),
                        "graph_work_consumed_error_type": (
                            "graph_native_statement_type_rejected"
                        ),
                    },
                )
            if not bool(type_status.get("ok")) and bool(
                type_status.get("inconclusive")
            ):
                # Never treat queueing, timeout, or checker infrastructure as
                # evidence against a proposition, and never fall through to a
                # provider with an unvalidated generated target. Preserve all
                # mathematical budgets, defer this exact action, and let the
                # scheduler explore another ready step before a bounded retry.
                type_output = str(type_status.get("output") or "")
                _emit_record(session, {
                    "phase": self.role,
                    "turn_in_phase": phase_turn,
                    "model": model_id,
                    "graph_native_goal_statement": graph_native_goal_statement,
                    "graph_native_target_node_id": graph_native_target.get(
                        "node_id"
                    ),
                    "graph_native_work_type": graph_native_target.get("work_type"),
                    "lean_output": type_output[:1200],
                    "lean_error_type": (
                        "graph_native_statement_typecheck_inconclusive"
                    ),
                    "provider_attempts": [],
                    "verdict": "graph_native_statement_typecheck_deferred",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        "lean_verdict": (
                            "graph_native_statement_typecheck_deferred"
                        ),
                        "lean_error": type_output,
                        "lean_error_type": (
                            "graph_native_statement_typecheck_inconclusive"
                        ),
                        "graph_native_goal_statement": (
                            graph_native_goal_statement
                        ),
                        "graph_native_target_node_id": graph_native_target.get(
                            "node_id"
                        ),
                        "graph_native_statement_typecheck_pending": True,
                        "provider_attempts": [],
                        "preserve_action_budget": True,
                        "preserve_frontier_work": True,
                        "defer_selected_frontier_action": True,
                        "refund_conversation_phase_turn": True,
                        "refund_conversation_absolute_turn": True,
                        "non_consuming_repair_ticket_continuation": True,
                        "llm_failure_kind": (
                            "graph_statement_typecheck_inconclusive"
                        ),
                        "llm_retryable": True,
                        "llm_failure_scope": "scoped",
                        "scoped_failure_reason": (
                            "graph_statement_typecheck_inconclusive"
                        ),
                    },
                )

        _inject_selected_repair_ticket_prompt(
            session=session,
            conv=conv,
            repair_semantics=_REPAIR_FEEDBACK,
        )

        # Build the tools_list mirroring legacy run_conversation:3252-3260.
        repair_turn_active = _repair_turn_requires_self_check(conv)
        effective_try_lean_tool_enabled = bool(
            self.try_lean_tool_enabled or repair_turn_active
        )
        use_tools = (
            searcher is not None
            or self.lean_check_tool_enabled
            or effective_try_lean_tool_enabled
            or self.compute_examples_tool_enabled
            or (proof_state is not None and self.proof_state_child_goal_limit > 0)
            or (
                self.apply_decl_to_goal_tool_enabled
                and not local_micro_theory_suppresses_library
            )
        )
        tools_list: List[dict] = []
        if searcher is not None:
            if _searcher_supports_static_mathlib(searcher):
                tools_list.append(SEARCH_MATHLIB_TOOL)
            if hasattr(searcher, "static_mathlib_searcher"):
                tools_list.append(SEARCH_THEOREMS_TOOL)
        if self.lean_check_tool_enabled:
            tools_list.append(CHECK_LEAN_TOOL)
        if effective_try_lean_tool_enabled:
            tools_list.append(TRY_LEAN_TOOL)
            tools_list.append(CERTIFY_COUNTEREXAMPLE_TOOL)
        if self.compute_examples_tool_enabled:
            tools_list.append(COMPUTE_EXAMPLES_TOOL)
        try_skeleton_tool_enabled = bool(
            proof_state is not None and self.proof_state_child_goal_limit > 0
        )
        if try_skeleton_tool_enabled:
            tools_list.append(TRY_SKELETON_TOOL)
        if (
            self.apply_decl_to_goal_tool_enabled
            and not local_micro_theory_suppresses_library
        ):
            tools_list.append(APPLY_DECL_TO_GOAL_TOOL)

        # ---- Step 1: LLM tool-use loop -------------------------------
        selected_record_for_temperature = (
            getattr(session, "selected_work_item_record", {}) or {}
        )
        if not isinstance(selected_record_for_temperature, dict):
            selected_record_for_temperature = {}
        pending_repair_ticket = getattr(session, "pending_repair_ticket", None)
        selected_repair_ticket_id = str(
            getattr(session, "_repair_ticket_selected_id", "") or ""
        ).strip()
        repair_ticket_active = bool(
            pending_repair_ticket is not None
            and selected_repair_ticket_id
            and str(getattr(pending_repair_ticket, "ticket_id", "") or "")
            == selected_repair_ticket_id
        )
        # Provider continuation accounting is a lease on this exact selected
        # work / repair-ticket cycle. The tool loop combines this marker with
        # the exact Lean target and role, so a scheduler pivot cannot inherit a
        # retired lane's wall budget.
        setattr(
            conv,
            "_provider_turn_repair_cycle_identity",
            _provider_repair_cycle_identity(
                session,
                selected_record_for_temperature,
            ),
        )
        from ensemble_prover.mini_session.turn.tool_loop import (
            _provider_turn_lane_identity,
        )

        provider_turn_lane_identity = _provider_turn_lane_identity(
            conv,
            llm_goal_statement_override,
        )
        temperature_decision = resolve_mini_temperature(
            self.mini_phase_temperatures,
            MiniTemperatureContext(
                role=self.role,
                action_id=self.id,
                sample_temperature=self.sample_temperature,
                selected_work_item_record=dict(selected_record_for_temperature),
                selected_work_type=str(
                    selected_record_for_temperature.get("work_type") or ""
                ),
                selected_node_id=str(
                    selected_record_for_temperature.get("node_id") or ""
                ),
                repair_turn_active=bool(repair_turn_active),
                repair_ticket_active=repair_ticket_active,
                pending_repair_ticket=pending_repair_ticket is not None,
                formalization_helper_contract=bool(formalization_helper_contract),
                stagnation_counter=int(getattr(session, "stagnation_counter", 0) or 0),
                max_stagnation=int(getattr(session, "max_stagnation", 0) or 0),
            ),
        )
        temperature_metadata = temperature_decision.metadata(client=client)
        max_tokens_override = _selected_work_request_envelope_policy(session)
        token_cap_metadata: Dict[str, Any] = {}
        token_cap_metadata["request_envelope_policy"] = (
            max_tokens_override.identity_record()
        )
        token_cap_metadata["max_tokens_override_reason"] = (
            "work_aware_conversation_cap"
        )
        formalization_request_timeout_s = (
            float(self.formalization_llm_request_timeout_s or 0.0)
            if formalization_helper_contract
            else 0.0
        )
        formalization_turn_elapsed_s = (
            float(self.formalization_llm_turn_elapsed_s or 0.0)
            if formalization_helper_contract
            else 0.0
        )
        turn_elapsed_s = (
            formalization_turn_elapsed_s
            if formalization_helper_contract
            else float(self.llm_turn_elapsed_s or 0.0)
        )
        if formalization_request_timeout_s > 0.0:
            token_cap_metadata["formalization_llm_request_timeout_s"] = (
                formalization_request_timeout_s
            )
        if formalization_turn_elapsed_s > 0.0:
            token_cap_metadata["formalization_llm_turn_elapsed_s"] = (
                formalization_turn_elapsed_s
            )
        elif turn_elapsed_s > 0.0:
            token_cap_metadata["llm_turn_elapsed_s"] = turn_elapsed_s
        # Route-local tool execution receives a shallow dossier copy but the
        # real proof state. Keep a rollback transaction around the tool loop,
        # then make its *reported* elapsed result part of the same deadline
        # predicate.  Without this outer boundary, a tool can finalize the
        # shared proof state just before the loop reports expiry; suppressing
        # the later dossier handoff alone leaves root state/dossier divergent.
        from ensemble_prover.mini_deadline_transaction import DeadlineMutationTransaction
        from ensemble_prover.mini_session.process_watchdog import begin_process_deadline

        loop_started = time.monotonic()
        turn_process_lease = begin_process_deadline(
            deadline_monotonic=(
                loop_started + turn_elapsed_s if turn_elapsed_s > 0.0 else 0.0
            ),
            label="mini_conversation_turn_workspace",
        )
        reported_elapsed_budget_exhaustion = False

        def tool_loop_deadline_exhausted() -> bool:
            if reported_elapsed_budget_exhaustion:
                return True
            return bool(
                turn_elapsed_s > 0.0
                and time.monotonic() - loop_started >= turn_elapsed_s
            )

        # Hard-deadline tool work never receives live mutable proof objects.
        # Joint deepcopy preserves the shallow route-dossier/proof-graph and
        # graph aliases that independent copies would break. Runtime
        # capabilities remain shared.  Cache reads remain available; cache
        # writes already use DeadlineMutationTransaction receipts, which join
        # the outer transaction and are compensated if this owner loses.
        workspace_enabled = bool(
            turn_elapsed_s > 0.0 and not answer_safe_pending_replay
        )
        workspace_dossier = dossier
        workspace_proof_state = proof_state
        workspace_llm_dossier = llm_dossier
        workspace_conv = conv
        workspace_clone_error = ""
        if workspace_enabled:
            try:
                (
                    workspace_dossier,
                    workspace_proof_state,
                    workspace_llm_dossier,
                    workspace_conv,
                ) = copy.deepcopy((dossier, proof_state, llm_dossier, conv))
            except Exception as exc:
                def clone_failure_path_hint() -> str:
                    """Hint at a likely bad leaf without invoking copy hooks again."""

                    stack: List[Tuple[str, Any, int]] = [
                        ("conv", conv, 0),
                        ("llm_dossier", llm_dossier, 0),
                        ("proof_state", proof_state, 0),
                        ("dossier", dossier, 0),
                    ]
                    seen: set[int] = set()
                    inspected = 0
                    while stack and inspected < 4096:
                        current_label, current_value, depth = stack.pop()
                        value_id = id(current_value)
                        if value_id in seen:
                            continue
                        seen.add(value_id)
                        inspected += 1
                        value_type = type(current_value)
                        if value_type.__dict__.get("__deepcopy__") is not None:
                            continue
                        if value_type.__module__ == "_thread":
                            return current_label[:500]
                        if depth >= 12:
                            continue
                        if isinstance(current_value, dict):
                            children = []
                            for index, (key, child) in enumerate(
                                current_value.items()
                            ):
                                if index >= 64:
                                    break
                                if isinstance(key, (str, int)):
                                    key_label = repr(key)[:80]
                                else:
                                    key_label = f"<{type(key).__name__}>"
                                children.append((f"[{key_label}]", child))
                        elif isinstance(current_value, (list, tuple)):
                            children = [
                                (f"[{index}]", child)
                                for index, child in enumerate(current_value[:64])
                            ]
                        else:
                            try:
                                children = []
                                for index, (key, child) in enumerate(
                                    vars(current_value).items()
                                ):
                                    if index >= 64:
                                        break
                                    children.append((f".{str(key)[:80]}", child))
                            except (TypeError, AttributeError):
                                children = []
                        for suffix, child in reversed(children):
                            stack.append((current_label + suffix, child, depth + 1))
                    return "workspace"

                try:
                    workspace_clone_error_path_hint = clone_failure_path_hint()
                except Exception:
                    workspace_clone_error_path_hint = "workspace"
                workspace_clone_error = (
                    f"{type(exc).__name__}: {str(exc or '')[:500]} "
                    f"[workspace_path_hint={workspace_clone_error_path_hint}]"
                )

        def prepare_workspace_commit() -> Dict[str, Any]:
            """Build a detached publication payload without touching live state."""

            memo = {
                id(workspace_dossier): dossier,
                id(workspace_conv): conv,
            }
            if workspace_proof_state is not None and proof_state is not None:
                memo[id(workspace_proof_state)] = proof_state
            workspace_graph = getattr(workspace_dossier, "proof_graph", None)
            live_graph = getattr(dossier, "proof_graph", None)
            if workspace_graph is not None and live_graph is not None:
                memo[id(workspace_graph)] = live_graph

            def preserve_node_identities(
                workspace_owner: Any,
                live_owner: Any,
            ) -> List[Tuple[Any, Any]]:
                workspace_nodes = getattr(workspace_owner, "nodes", None)
                live_nodes = getattr(live_owner, "nodes", None)
                preserved: List[Tuple[Any, Any]] = []
                if not isinstance(workspace_nodes, dict) or not isinstance(
                    live_nodes,
                    dict,
                ):
                    return preserved
                for node_id, workspace_node in workspace_nodes.items():
                    live_node = live_nodes.get(node_id)
                    if live_node is None:
                        continue
                    memo[id(workspace_node)] = live_node
                    preserved.append((workspace_node, live_node))
                return preserved

            graph_nodes = preserve_node_identities(workspace_graph, live_graph)
            proof_nodes = preserve_node_identities(
                workspace_proof_state,
                proof_state,
            )
            return {
                "graph_nodes": [
                    (live_node, copy.deepcopy(vars(workspace_node), memo))
                    for workspace_node, live_node in graph_nodes
                ],
                "proof_nodes": [
                    (live_node, copy.deepcopy(vars(workspace_node), memo))
                    for workspace_node, live_node in proof_nodes
                ],
                "live_graph": live_graph,
                "graph_state": (
                    copy.deepcopy(vars(workspace_graph), memo)
                    if workspace_graph is not None and live_graph is not None
                    else None
                ),
                "dossier_state": copy.deepcopy(vars(workspace_dossier), memo),
                "proof_state_state": (
                    copy.deepcopy(vars(workspace_proof_state), memo)
                    if workspace_proof_state is not None and proof_state is not None
                    else None
                ),
                "conv_state": copy.deepcopy(vars(workspace_conv), memo),
                "llm_dossier": (
                    dossier
                    if workspace_llm_dossier is workspace_dossier
                    else copy.deepcopy(workspace_llm_dossier, memo)
                ),
            }

        prepared_workspace_commit: Optional[Dict[str, Any]] = None

        tool_loop_transaction = DeadlineMutationTransaction(
            deadline_exhausted=(
                tool_loop_deadline_exhausted if turn_elapsed_s > 0.0 else None
            ),
            # Workspace state itself is disposable and needs no second full
            # snapshot.  Inner tool transactions still join this outer owner
            # so reversible cache receipts share its final decision.
            dossier=None,
            proof_state=None,
            label="conversation_turn_tool_loop",
        )

        class TurnLeaseParticipant:
            def commit(self) -> bool:
                return True

            def finalize(self) -> bool:
                return True

            def linearize(self) -> bool:
                return turn_process_lease.close_at_transaction_commit()

            def release(self) -> bool:
                return True

            def rollback(self) -> None:
                turn_process_lease.settle_timeout()

        tool_loop_transaction.add_participant(TurnLeaseParticipant())

        class WorkspacePublicationParticipant:
            def __init__(self) -> None:
                self.prepared: Optional[Dict[str, Any]] = None
                self.originals: List[Tuple[Any, Dict[str, Any]]] = []
                self.applied = False

            def commit(self) -> bool:
                prepared = self.prepared
                if prepared is None:
                    return False
                targets: List[Tuple[Any, Dict[str, Any]]] = [
                    *prepared["graph_nodes"],
                    *prepared["proof_nodes"],
                ]
                live_graph = prepared["live_graph"]
                if prepared["graph_state"] is not None and live_graph is not None:
                    targets.append((live_graph, prepared["graph_state"]))
                targets.append((dossier, prepared["dossier_state"]))
                if prepared["proof_state_state"] is not None and proof_state is not None:
                    targets.append((proof_state, prepared["proof_state_state"]))
                targets.append((conv, prepared["conv_state"]))
                # Shallow snapshots cannot execute user code and preserve the
                # exact pre-publication aliases for compensation.
                self.originals = [(target, dict(vars(target))) for target, _ in targets]
                for target, state in targets:
                    vars(target).clear()
                    vars(target).update(state)
                self.applied = True
                return True

            def finalize(self) -> bool:
                return True

            def release(self) -> bool:
                self.originals = []
                return True

            def rollback(self) -> None:
                if not self.applied:
                    return
                for target, state in reversed(self.originals):
                    vars(target).clear()
                    vars(target).update(state)
                self.applied = False
                self.originals = []

        workspace_publication = WorkspacePublicationParticipant()
        if workspace_enabled:
            tool_loop_transaction.add_participant(workspace_publication)

        class DeferredCachePublication:
            def __init__(self, raw_cache: Any, store_kwargs: Dict[str, Any]) -> None:
                self.raw_cache = raw_cache
                self.store_kwargs = store_kwargs
                self.inner: Any = None

            def commit(self) -> bool:
                begin = getattr(self.raw_cache, "begin_deadline_aware_store", None)
                if not callable(begin):
                    return True
                self.inner = begin(
                    deadline_exhausted=tool_loop_deadline_exhausted,
                    **self.store_kwargs,
                )
                if self.inner is None:
                    return True
                commit = getattr(self.inner, "commit", None)
                return not callable(commit) or bool(commit())

            def finalize(self) -> bool:
                finalize = getattr(self.inner, "finalize", None)
                return not callable(finalize) or bool(finalize())

            def release(self) -> bool:
                release = getattr(self.inner, "release", None)
                return not callable(release) or release() is not False

            def rollback(self) -> None:
                rollback = getattr(self.inner, "rollback", None)
                if callable(rollback):
                    rollback()

        class DeadlineCacheFacade:
            def __init__(self, raw_cache: Any) -> None:
                self.raw_cache = raw_cache

            def begin_deadline_aware_store(
                self,
                helper_block: str,
                *,
                preamble: str,
                theorem_name: str,
                phase: str,
                deadline_exhausted: Any,
            ) -> DeferredCachePublication:
                del deadline_exhausted
                return DeferredCachePublication(
                    self.raw_cache,
                    {
                        "helper_block": helper_block,
                        "preamble": preamble,
                        "theorem_name": theorem_name,
                        "phase": phase,
                    },
                )

            def store(
                self,
                helper_block: str,
                *,
                preamble: str,
                theorem_name: str,
                phase: str,
            ) -> bool:
                if not tool_loop_transaction.can_mutate():
                    return False
                receipt = self.begin_deadline_aware_store(
                    helper_block,
                    preamble=preamble,
                    theorem_name=theorem_name,
                    phase=phase,
                    deadline_exhausted=tool_loop_deadline_exhausted,
                )
                tool_loop_transaction.add_participant(receipt)
                return True

            def __getattr__(self, name: str) -> Any:
                return getattr(self.raw_cache, name)

        turn_proof_cache = (
            DeadlineCacheFacade(session.proof_cache)
            if workspace_enabled and session.proof_cache is not None
            else session.proof_cache
        )
        with tool_loop_transaction:
            remaining_turn_elapsed_s = (
                max(0.0, turn_elapsed_s - (time.monotonic() - loop_started))
                if turn_elapsed_s > 0.0
                else 0.0
            )
            if answer_safe_pending_replay:
                recovered_replay_fields = dict(
                    answer_safe_pending.get("recovered_finalizer_receipt") or {}
                )
                loop_result = ToolLoopResult(
                    content=str(answer_safe_pending.get("content") or ""),
                    sent_messages=copy.deepcopy(
                        list(answer_safe_pending.get("sent_messages") or [])
                    ),
                    **recovered_replay_fields,
                )
            elif workspace_clone_error:
                loop_result = ToolLoopResult(
                    llm_error="deadline_workspace_clone_failed",
                    llm_failure_kind="deadline_workspace_clone_failed",
                    llm_retryable=True,
                    llm_failure_reason=workspace_clone_error,
                    elapsed_s=time.monotonic() - loop_started,
                    llm_turn_elapsed_budget_s=turn_elapsed_s,
                )
            elif turn_elapsed_s > 0.0 and remaining_turn_elapsed_s <= 0.0:
                loop_result = ToolLoopResult(
                    llm_error="llm_turn_elapsed_budget_exhausted",
                    llm_failure_kind="llm_turn_elapsed_budget_exhausted",
                    llm_retryable=True,
                    llm_failure_reason="llm_turn_elapsed_budget_exhausted",
                    elapsed_s=time.monotonic() - loop_started,
                    llm_turn_elapsed_budget_exhausted=True,
                    llm_turn_elapsed_budget_s=turn_elapsed_s,
                )
            else:
                try:
                    loop_result = await call_llm_with_tools_one_round(
                        conv=workspace_conv,
                        client=client,
                        lean=session.lean,
                        dossier=workspace_llm_dossier,
                        authority_dossier=workspace_dossier,
                        proof_state=workspace_proof_state,
                        searcher=searcher,
                        tools_list=tools_list,
                        use_tools=use_tools,
                        lean_check_tool_enabled=self.lean_check_tool_enabled,
                        try_lean_tool_enabled=effective_try_lean_tool_enabled,
                        compute_examples_tool_enabled=self.compute_examples_tool_enabled,
                        try_skeleton_tool_enabled=try_skeleton_tool_enabled,
                        apply_decl_to_goal_tool_enabled=(
                            self.apply_decl_to_goal_tool_enabled
                            and not local_micro_theory_suppresses_library
                        ),
                        max_tool_calls_per_turn=self.max_tool_calls_per_turn,
                        proof_state_child_goal_limit=self.proof_state_child_goal_limit,
                        proof_cache=turn_proof_cache,
                        temperature_override=(
                            temperature_decision.provider_temperature_override()
                        ),
                        temperature_metadata=temperature_metadata,
                        trace_prefix=session.trace_prefix,
                        turn=phase_turn,
                        goal_statement_override=llm_goal_statement_override,
                        try_lean_allow_declarations=bool(
                            formalization_helper_contract
                        ),
                        try_lean_require_declaration=bool(
                            formalization_helper_contract
                        ),
                        cost_controller=getattr(session, "cost_controller", None),
                        cost_role=self.role,
                        cost_scope=str(getattr(session, "scope", "") or ""),
                        session_scope=str(
                            getattr(session, "scope", "") or "problem"
                        ),
                        cost_action_id=self.id,
                        max_tokens_override=max_tokens_override,
                        max_turn_elapsed_s=(
                            remaining_turn_elapsed_s
                            if turn_elapsed_s > 0.0
                            else 0.0
                        ),
                        request_timeout_override_s=(
                            formalization_request_timeout_s
                            if formalization_request_timeout_s > 0.0
                            else None
                        ),
                        scheduler_call_quantum_enabled=True,
                        publication_guard=publication_guard,
                    )
                except asyncio.CancelledError as cancellation:
                    cancelled_tool_log = list(
                        getattr(cancellation, "mini_tool_call_log", ()) or ()
                    )
                    if cancelled_tool_log:
                        cancelled_record = {
                            "phase": self.role,
                            "turn_in_phase": phase_turn,
                            "session_scope": str(
                                getattr(session, "scope", "") or ""
                            ),
                            "action_id": self.id,
                            "tool_call_log": cancelled_tool_log,
                            "verdict": "llm_response_cancelled",
                            "llm_recovery_event_id": (
                                "cancelled-tool-receipt-v1:"
                                + uuid.uuid4().hex
                            ),
                        }
                        _emit_record(session, cancelled_record)
                    raise
            envelope_receipt = dict(
                getattr(client, "last_request_envelope_receipt", {}) or {}
            )
            if envelope_receipt:
                token_cap_metadata["request_envelope_receipt"] = (
                    envelope_receipt
                )
                token_cap_metadata["max_tokens_override"] = int(
                    envelope_receipt.get("max_output_tokens", 0) or 0
                )
            reported_elapsed_budget_exhaustion = bool(
                getattr(loop_result, "llm_turn_elapsed_budget_exhausted", False)
            ) or str(getattr(loop_result, "llm_error", "") or "") == (
                "llm_turn_elapsed_budget_exhausted"
            )
            if (
                workspace_enabled
                and not workspace_clone_error
                and not reported_elapsed_budget_exhaustion
                and not tool_loop_deadline_exhausted()
            ):
                # Cache receipts are still reversible here.  The transaction
                # exit below is the shared deadline gate for this prepared
                # state and every staged durable publication.
                prepared_workspace_commit = prepare_workspace_commit()
                workspace_publication.prepared = prepared_workspace_commit
        workspace_published = False
        if workspace_enabled:
            if tool_loop_transaction.committed and workspace_publication.applied:
                llm_dossier = prepared_workspace_commit["llm_dossier"]
                workspace_published = True
                for helper in dict(
                    getattr(dossier, "verified_helpers", {}) or {}
                ).values():
                    # Enqueue is content-addressed and idempotent. Restaging
                    # the committed set also captures metadata-only support,
                    # visibility, or policy changes with unchanged source.
                    _stage_verified_helper_receipt(session, helper, dossier)
            if not workspace_published:
                # Preserve only the owner-produced B1 timeout transcript.  A
                # resistant child can continue mutating its discarded private
                # workspace but can no longer overwrite live proof state.
                conv.history = copy.deepcopy(
                    list(getattr(workspace_conv, "history", []) or [])
                )
                # Replay queue position is operational ownership, not proof
                # state. Publish only an authenticated advancement of the
                # exact live queue, so a completed or timed call cannot starve
                # untouched closers after the proof workspace is rolled back.
                from ensemble_prover.mini_session.turn.tool_loop import (
                    _tool_call_signature,
                    _validated_durable_progress_tool_continuation_state,
                )

                live_replay_state = getattr(
                    conv,
                    "_provider_call_quantum_state",
                    {},
                ) or {}
                workspace_replay_state = getattr(
                    workspace_conv,
                    "_provider_call_quantum_state",
                    {},
                ) or {}
                live_target = str(
                    live_replay_state.get(
                        "durable_progress_tool_continuation_target"
                    )
                    or ""
                ).strip()
                candidate_target = str(
                    workspace_replay_state.get(
                        "durable_progress_tool_continuation_target"
                    )
                    or ""
                ).strip()
                validated_live_replay = (
                    _validated_durable_progress_tool_continuation_state(
                        live_replay_state,
                        conv=conv,
                        dossier=dossier,
                        goal_statement_override=live_target,
                        max_tool_calls_per_turn=self.max_tool_calls_per_turn,
                    )
                    if live_target
                    else {}
                )
                validated_workspace_replay = (
                    _validated_durable_progress_tool_continuation_state(
                        workspace_replay_state,
                        conv=conv,
                        dossier=dossier,
                        goal_statement_override=candidate_target,
                        max_tool_calls_per_turn=self.max_tool_calls_per_turn,
                    )
                    if candidate_target
                    else {}
                )

                def replay_signatures(state: Mapping[str, Any]) -> List[str]:
                    return [
                        _tool_call_signature(call)
                        for call in list(state.get("pending_tool_replay") or ())
                        if isinstance(call, Mapping)
                    ]

                original_signatures = replay_signatures(validated_live_replay)
                candidate_signatures = replay_signatures(
                    validated_workspace_replay
                )
                replay_cursor_advanced = False
                if original_signatures and candidate_signatures:
                    # Completed prefixes disappear. A call interrupted in
                    # flight may rotate behind the untouched suffix, retaining
                    # its value without letting it monopolize the next turn.
                    for consumed in range(1, len(original_signatures) + 1):
                        if candidate_signatures == original_signatures[consumed:]:
                            replay_cursor_advanced = True
                            break
                    if not replay_cursor_advanced:
                        for timed_index in range(len(original_signatures)):
                            rotated = (
                                original_signatures[timed_index + 1 :]
                                + [original_signatures[timed_index]]
                            )
                            if candidate_signatures == rotated:
                                replay_cursor_advanced = True
                                break
                replay_predecessor_identity = str(
                    getattr(
                        loop_result,
                        "durable_progress_tool_replay_predecessor_identity",
                        "",
                    )
                    or ""
                ).strip()
                replay_queue_exhausted = bool(
                    getattr(
                        loop_result,
                        "durable_progress_tool_replay_exhausted",
                        False,
                    )
                )
                live_identity = str(
                    validated_live_replay.get(
                        "durable_progress_tool_continuation_identity"
                    )
                    or ""
                ).strip()
                same_authority = bool(
                    live_target
                    and candidate_target == live_target
                    and str(
                        workspace_replay_state.get(
                            "durable_progress_tool_continuation_role"
                        )
                        or ""
                    ).strip()
                    == str(
                        validated_live_replay.get(
                            "durable_progress_tool_continuation_role"
                        )
                        or ""
                    ).strip()
                )
                workspace_used = int(
                    workspace_replay_state.get("tool_calls_used", 0) or 0
                )
                live_used = int(
                    validated_live_replay.get("tool_calls_used", 0) or 0
                )
                workspace_banked_progress = bool(
                    getattr(loop_result, "repair_self_check_accepted", False)
                    or list(
                        getattr(
                            loop_result,
                            "accepted_try_lean_helper_names",
                            (),
                        )
                        or ()
                    )
                    or int(getattr(loop_result, "tool_state_updates", 0) or 0)
                    > 0
                    or getattr(loop_result, "authoritative_falsification", False)
                    or getattr(loop_result, "proof_disproof_conflict", False)
                )
                authenticated_empty_successor = bool(
                    validated_live_replay
                    and replay_queue_exhausted
                    and replay_predecessor_identity == live_identity
                    and same_authority
                    and workspace_used > live_used
                    and not workspace_banked_progress
                    and not list(
                        workspace_replay_state.get("pending_tool_replay") or ()
                    )
                    and str(
                        workspace_replay_state.get(
                            "pending_tool_replay_disposition"
                        )
                        or ""
                    ).strip()
                    != "durable_progress_cutpoint"
                )
                if authenticated_empty_successor:
                    delattr(conv, "_provider_call_quantum_state")
                elif (
                    replay_cursor_advanced
                    and same_authority
                    and replay_predecessor_identity == live_identity
                    and not workspace_banked_progress
                    and int(
                        validated_workspace_replay.get("tool_calls_used", 0)
                        or 0
                    )
                    > live_used
                    and list(
                        validated_workspace_replay.get(
                            "durable_progress_tool_continuation_helper_receipts",
                            [],
                        )
                        or []
                    )
                    == list(
                        validated_live_replay.get(
                            "durable_progress_tool_continuation_helper_receipts",
                            [],
                        )
                        or []
                    )
                ):
                    conv._provider_call_quantum_state = copy.deepcopy(
                        validated_workspace_replay
                    )
                final_live_replay_state = getattr(
                    conv,
                    "_provider_call_quantum_state",
                    {},
                ) or {}
                final_live_target = str(
                    final_live_replay_state.get(
                        "durable_progress_tool_continuation_target"
                    )
                    or ""
                ).strip()
                validated_final_live_replay = (
                    _validated_durable_progress_tool_continuation_state(
                        final_live_replay_state,
                        conv=conv,
                        dossier=dossier,
                        goal_statement_override=final_live_target,
                        max_tool_calls_per_turn=self.max_tool_calls_per_turn,
                    )
                    if final_live_target
                    else {}
                )
                final_live_pending = list(
                    validated_final_live_replay.get("pending_tool_replay") or ()
                )
                loop_result.durable_progress_tool_replay_pending = bool(
                    final_live_pending
                )
                loop_result.durable_progress_tool_replay_count = len(
                    final_live_pending
                )
                loop_result.durable_progress_tool_continuation_identity = str(
                    validated_final_live_replay.get(
                        "durable_progress_tool_continuation_identity"
                    )
                    or ""
                ).strip()
                loop_result.durable_progress_tool_continuation_granted = bool(
                    final_live_pending
                    and loop_result.durable_progress_tool_continuation_identity
                )
                if tool_loop_deadline_exhausted():
                    reported_elapsed_budget_exhaustion = True
        elapsed_finalizer_artifact_ready = bool(
            reported_elapsed_budget_exhaustion
            and str(getattr(loop_result, "content", "") or "").strip()
            and str(
                getattr(loop_result, "final_no_tools_event", "") or ""
            ).strip()
            in {
                "accepted_try_lean_provider_failure_fallback",
                (
                    "final_no_tools_banked_mixed_proof_"
                    "provider_failure_fallback"
                ),
            }
        )
        if elapsed_finalizer_artifact_ready:
            # The proof candidate was fully produced before the failed final
            # serialization request. The private proof workspace remains
            # rolled back, but the immutable candidate can still go through
            # extraction and the independent primary Lean verifier, which has
            # its own lease. Do not turn that paid artifact back into a
            # scheduler-neutral provider retry merely because the provider
            # window closed while returning from the tool loop.
            reported_elapsed_budget_exhaustion = False
            loop_result.llm_error = None
            loop_result.llm_failure_kind = ""
            loop_result.llm_retryable = False
            loop_result.llm_terminal = False
            loop_result.llm_failure_reason = ""
            loop_result.llm_turn_elapsed_budget_exhausted = False
        if reported_elapsed_budget_exhaustion:
            loop_result.llm_error = "llm_turn_elapsed_budget_exhausted"
            loop_result.llm_failure_kind = "llm_turn_elapsed_budget_exhausted"
            loop_result.llm_retryable = True
            loop_result.llm_terminal = False
            loop_result.llm_failure_reason = "llm_turn_elapsed_budget_exhausted"
            loop_result.llm_turn_elapsed_budget_exhausted = True
            loop_result.llm_turn_elapsed_budget_s = turn_elapsed_s
        if (
            tool_loop_transaction.enabled
            and not tool_loop_transaction.committed
            and not elapsed_finalizer_artifact_ready
        ):
            # A deadline race (or an unrecoverable proof-state commit failure)
            # is a failed tool loop, never a late finalized root.  The normal
            # LLM-failure path below supplies retry/telemetry semantics.
            if not reported_elapsed_budget_exhaustion and not workspace_clone_error:
                loop_result.llm_error = "deadline_mutation_commit_failed"
                loop_result.llm_failure_kind = "deadline_mutation_commit_failed"
                loop_result.llm_retryable = True
                loop_result.llm_terminal = False
                loop_result.llm_failure_reason = "deadline_mutation_commit_failed"
            reported_elapsed_budget_exhaustion = True
        # Authenticate any ordinary provider/tool continuation while the
        # exact selected graph target and repair cycle that dispatched it are
        # still authoritative. Session.apply() may intentionally clear that
        # selection for frontier fairness before on_outcome_applied() runs;
        # deriving a binding only after application then mistakes a useful
        # no-proof/self-check continuation for a different lane and poisons
        # the next pre-select snapshot. This covers every persisted raw
        # continuation, not only cooperative provider-quantum yields.
        try:
            self.prepare_scheduler_runtime_state(session)
        except StateSnapshotCompatibilityError:
            # Keep the live state fail-closed. A direct scheduler snapshot
            # will expose the incompatibility instead of silently rebinding
            # provider work to a different target.
            self._provider_quantum_checkpoint = {}
        if (
            bool(getattr(loop_result, "proof_disproof_conflict", False))
            and not reported_elapsed_budget_exhaustion
            and (not workspace_enabled or workspace_published)
            and str(getattr(dossier, "session_failure_kind", "") or "").strip()
            == "proof_disproof_conflict"
        ):
            conflict_reason = str(
                getattr(dossier, "session_failure_reason", "") or ""
            ).strip() or "falsification_trust_boundary_conflict"
            _emit_record(session, {
                "phase": self.role,
                "turn_in_phase": phase_turn,
                "model": model_id,
                "terminal_failure": True,
                "terminal_failure_reason": conflict_reason,
                "terminal_failure_kind": "proof_disproof_conflict",
                "verdict": "counterexample_tool_proof_disproof_conflict",
            })
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    "lean_verdict": "proof_disproof_conflict",
                    "terminal_failure": True,
                    "terminal_failure_reason": conflict_reason,
                    "terminal_failure_kind": "proof_disproof_conflict",
                    "strong_progress": False,
                    "verdict": "counterexample_tool_proof_disproof_conflict",
                },
            )
        if (
            bool(getattr(loop_result, "authoritative_falsification", False))
            and not reported_elapsed_budget_exhaustion
            and (not workspace_enabled or workspace_published)
        ):
            falsified_statement = str(
                getattr(
                    loop_result,
                    "authoritative_falsification_target",
                    "",
                )
                or ""
            ).strip()
            certificate_hash = str(
                getattr(
                    loop_result,
                    "authoritative_falsification_certificate_hash",
                    "",
                )
                or ""
            ).strip()
            target_environment_hash = str(
                getattr(dossier, "current_lean_environment_hash", "") or ""
            ).strip()
            matching_authority = next(
                (
                    authority
                    for authority in dict(
                        getattr(dossier, "mini_authoritative_negations", {}) or {}
                    ).values()
                    if isinstance(authority, dict)
                    and str(authority.get("statement") or "").strip()
                    == falsified_statement
                    and str(authority.get("certificate_hash") or "").strip()
                    == certificate_hash
                    and str(
                        authority.get("target_environment_hash") or ""
                    ).strip()
                    == target_environment_hash
                ),
                None,
            )
            if matching_authority is not None:
                terminal_metadata = _root_falsification_terminal_metadata(
                    session,
                    falsified_statement,
                )
                _emit_record(session, {
                    "phase": self.role,
                    "turn_in_phase": phase_turn,
                    "model": model_id,
                    "authoritative_falsification": True,
                    "falsified_statement": falsified_statement,
                    "falsification_certificate_hash": certificate_hash,
                    **terminal_metadata,
                    "verdict": "counterexample_tool_authoritatively_falsified",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=True,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        "lean_verdict": "authoritative_target_falsified",
                        "authoritative_falsification": True,
                        "falsified_statement": falsified_statement,
                        "falsification_certificate_hash": certificate_hash,
                        **terminal_metadata,
                        "verdict": (
                            "counterexample_tool_authoritatively_falsified"
                        ),
                    },
                )
        temperature_metadata = refresh_temperature_metadata_from_client(
            temperature_metadata,
            client,
        )
        tool_repeat_metadata: Dict[str, Any] = {}
        if bool(getattr(loop_result, "tool_repeat_detected", False)):
            tool_repeat_metadata = {
                "tool_repeat_detected": True,
                "tool_repeat_action": str(
                    getattr(loop_result, "tool_repeat_action", "") or ""
                ),
                "tool_repeat_signature": str(
                    getattr(loop_result, "tool_repeat_signature", "") or ""
                ),
            }
        tool_progress_metadata: Dict[str, Any] = {
            "proof_tool_attempts": int(
                getattr(loop_result, "proof_tool_attempts", 0) or 0
            ),
            "consecutive_no_formal_progress": int(
                getattr(loop_result, "consecutive_no_formal_progress", 0) or 0
            ),
            "consecutive_search_tool_calls": int(
                getattr(loop_result, "consecutive_search_tool_calls", 0) or 0
            ),
            "semantic_diagnostic_progress_count": int(
                getattr(loop_result, "semantic_diagnostic_progress_count", 0) or 0
            ),
            "semantic_diagnostic_best_phase": int(
                getattr(loop_result, "semantic_diagnostic_best_phase", -1)
            ),
            "semantic_diagnostic_best_error_kind": str(
                getattr(
                    loop_result,
                    "semantic_diagnostic_best_error_kind",
                    "",
                )
                or ""
            ),
            "semantic_diagnostic_best_goal_count": int(
                getattr(loop_result, "semantic_diagnostic_best_goal_count", -1)
            ),
            "semantic_diagnostic_last_reason": str(
                getattr(loop_result, "semantic_diagnostic_last_reason", "") or ""
            ),
            "semantic_diagnostic_best_signature": str(
                getattr(loop_result, "semantic_diagnostic_best_signature", "") or ""
            ),
            "partial_try_lean_promotions": int(
                getattr(loop_result, "partial_try_lean_promotions", 0) or 0
            ),
            "in_turn_tool_history_compactions": int(
                getattr(loop_result, "in_turn_tool_history_compactions", 0) or 0
            ),
            "in_turn_tool_history_compacted_messages": int(
                getattr(
                    loop_result,
                    "in_turn_tool_history_compacted_messages",
                    0,
                )
                or 0
            ),
            "in_turn_tool_history_compacted_tool_rounds": int(
                getattr(
                    loop_result,
                    "in_turn_tool_history_compacted_tool_rounds",
                    0,
                )
                or 0
            ),
            "in_turn_tool_history_compacted_chars": int(
                getattr(loop_result, "in_turn_tool_history_compacted_chars", 0)
                or 0
            ),
            "provider_calls_completed": int(
                getattr(loop_result, "provider_calls_completed", 0) or 0
            ),
            "provider_dispatches_started": int(
                getattr(loop_result, "provider_dispatches_started", 0) or 0
            ),
            "provider_call_quantum_exhausted": bool(
                getattr(loop_result, "provider_call_quantum_exhausted", False)
            ),
            "provider_finalizer_continuation_exhausted": bool(
                getattr(
                    loop_result,
                    "provider_finalizer_continuation_exhausted",
                    False,
                )
            ),
            "provider_call_elapsed_s": float(
                getattr(loop_result, "provider_call_elapsed_s", 0.0) or 0.0
            ),
            "provider_call_quantum_max_retries": int(
                getattr(loop_result, "provider_call_quantum_max_retries", 0)
                or 0
            ),
            "provider_call_cumulative_elapsed_s": float(
                getattr(
                    loop_result,
                    "provider_call_cumulative_elapsed_s",
                    0.0,
                )
                or 0.0
            ),
            "provider_call_cumulative_wall_cap_s": float(
                getattr(
                    loop_result,
                    "provider_call_cumulative_wall_cap_s",
                    0.0,
                )
                or 0.0
            ),
            "provider_call_cumulative_wall_exhausted": bool(
                getattr(
                    loop_result,
                    "provider_call_cumulative_wall_exhausted",
                    False,
                )
            ),
            "paid_tool_infrastructure_disposition": str(
                getattr(
                    loop_result,
                    "paid_tool_infrastructure_disposition",
                    "",
                )
                or ""
            ),
            "paid_tool_continuation_identity": str(
                getattr(
                    loop_result,
                    "paid_tool_continuation_identity",
                    "",
                )
                or ""
            ),
            "paid_tool_continuation_granted": bool(
                getattr(
                    loop_result,
                    "paid_tool_continuation_granted",
                    False,
                )
            ),
        }
        if bool(getattr(loop_result, "semantic_no_progress_detected", False)):
            tool_progress_metadata.update({
                "semantic_no_progress_detected": True,
                "semantic_no_progress_reason": str(
                    getattr(loop_result, "semantic_no_progress_reason", "") or ""
                ),
                "semantic_no_progress_signature": str(
                    getattr(loop_result, "semantic_no_progress_signature", "") or ""
                ),
            })
        if str(getattr(loop_result, "final_no_tools_event", "") or ""):
            tool_progress_metadata.update({
                "final_no_tools_event": str(
                    getattr(loop_result, "final_no_tools_event", "") or ""
                ),
                "final_no_tools_finish_reason": str(
                    getattr(loop_result, "final_no_tools_finish_reason", "") or ""
                ),
                "final_no_tools_reasoning_content_chars": int(
                    getattr(
                        loop_result,
                        "final_no_tools_reasoning_content_chars",
                        0,
                    )
                    or 0
                ),
                "final_no_tools_used_accepted_proof": bool(
                    getattr(
                        loop_result,
                        "final_no_tools_used_accepted_proof",
                        False,
                    )
                ),
            })
        recovered_finalizer_event = str(
            getattr(loop_result, "final_no_tools_event", "") or ""
        ).strip()
        if recovered_finalizer_event in {
            "accepted_try_lean_provider_failure_fallback",
            "final_no_tools_banked_mixed_proof_provider_failure_fallback",
        }:
            # Keep this receipt inert until the recovered proof has passed or
            # failed the independent Lean gate. The outer run wrapper
            # activates it on every non-accepted return path.
            tool_progress_metadata.update({
                "recovered_finalizer_error": str(
                    getattr(loop_result, "recovered_finalizer_error", "") or ""
                ),
                "recovered_finalizer_failure_kind": str(
                    getattr(
                        loop_result,
                        "recovered_finalizer_failure_kind",
                        "",
                    )
                    or ""
                ),
                "recovered_finalizer_retryable": bool(
                    getattr(loop_result, "recovered_finalizer_retryable", False)
                ),
                "recovered_finalizer_terminal": bool(
                    getattr(loop_result, "recovered_finalizer_terminal", False)
                ),
                "recovered_finalizer_failure_reason": str(
                    getattr(
                        loop_result,
                        "recovered_finalizer_failure_reason",
                        "",
                    )
                    or ""
                ),
                "recovered_finalizer_retry_deadline": dict(
                    getattr(
                        loop_result,
                        "recovered_finalizer_retry_deadline",
                        {},
                    )
                    or {}
                ),
                "recovered_finalizer_provider_attempts": list(
                    getattr(
                        loop_result,
                        "recovered_finalizer_provider_attempts",
                        [],
                    )
                    or []
                ),
                "recovered_finalizer_provider_defer": dict(
                    getattr(
                        loop_result,
                        "recovered_finalizer_provider_defer",
                        {},
                    )
                    or {}
                ),
                "provider_turn_lane_identity": provider_turn_lane_identity,
            })
        loop_tool_call_log = list(loop_result.tool_call_log or [])
        skeleton_tool_logs = [
            item
            for item in loop_tool_call_log
            if isinstance(item, dict)
            if str(item.get("name") or "") == "try_skeleton"
        ]
        skeleton_banked_logs = [
            item
            for item in skeleton_tool_logs
            if str(item.get("proof_state_update_status") or "")
            == "spawned_remaining_goals"
        ]
        compute_receipt_logs = [
            item
            for item in loop_tool_call_log
            if isinstance(item, dict)
            if str(item.get("name") or "") == "compute_examples"
        ]
        compute_protocol_logs = [
            item
            for item in compute_receipt_logs
            if item.get("protocol_attempted") is not False
        ]
        compute_tool_logs = [
            item
            for item in compute_protocol_logs
            if (
                bool(item.get("runner_invoked"))
                if "runner_invoked" in item
                else not bool(item.get("args_parse_error"))
                and not bool(item.get("skipped_reason"))
                and str(item.get("result_preview") or "").startswith(
                    (
                        "compute_examples accepted",
                        "compute_examples rejected",
                        "compute_examples error:",
                        "compute_examples infrastructure error:",
                    )
                )
            )
        ]
        compute_malformed_logs = [
            item
            for item in compute_protocol_logs
            if bool(item.get("args_parse_error"))
            or str(item.get("skipped_reason") or "") == "malformed_arguments"
        ]
        compute_success_logs = [
            item
            for item in compute_tool_logs
            if str(item.get("result_preview") or "").startswith(
                "compute_examples accepted"
            )
        ]
        partial_try_lean_promotions = int(
            getattr(loop_result, "partial_try_lean_promotions", 0) or 0
        )
        accepted_try_lean_helper_names = tuple(
            str(name or "").strip()
            for name in list(
                getattr(
                    loop_result,
                    "accepted_try_lean_helper_names",
                    (),
                )
                or ()
            )
            if str(name or "").strip()
        )
        durable_progress_tool_replay_pending = bool(
            getattr(
                loop_result,
                "durable_progress_tool_replay_pending",
                False,
            )
        )
        durable_progress_tool_replay_count = int(
            getattr(
                loop_result,
                "durable_progress_tool_replay_count",
                0,
            )
            or 0
        )
        durable_progress_tool_continuation_identity = str(
            getattr(
                loop_result,
                "durable_progress_tool_continuation_identity",
                "",
            )
            or ""
        ).strip()
        durable_progress_tool_continuation_granted = bool(
            getattr(
                loop_result,
                "durable_progress_tool_continuation_granted",
                False,
            )
            and durable_progress_tool_continuation_identity
        )
        if not durable_progress_tool_replay_pending:
            # A deadline workspace is disposable.  If it times out after
            # partially consuming an owned replay, the live conversation
            # still holds the complete pre-run queue.  Preserve that existing
            # scheduler ownership instead of letting the failed workspace's
            # empty result strand the closing calls.
            existing_continuation = dict(
                getattr(
                    session,
                    "durable_progress_tool_continuation",
                    {},
                )
                or {}
            )
            existing_identity = str(
                existing_continuation.get("identity") or ""
            ).strip()
            existing_owned = False
            if existing_identity:
                try:
                    existing_owned = self.owns_durable_progress_tool_continuation(
                        existing_identity,
                        session,
                    )
                except Exception:
                    existing_owned = False
            if existing_owned:
                live_replay_state = getattr(
                    getattr(session, "conv", None),
                    "_provider_call_quantum_state",
                    {},
                ) or {}
                durable_progress_tool_replay_pending = True
                durable_progress_tool_replay_count = len(
                    list(live_replay_state.get("pending_tool_replay") or ())
                )
                durable_progress_tool_continuation_identity = existing_identity
                durable_progress_tool_continuation_granted = True
        durable_progress_replay_metadata = (
            {
                "durable_progress_tool_replay_pending": True,
                "durable_progress_tool_replay_count": (
                    durable_progress_tool_replay_count
                ),
                "preserve_frontier_work": True,
                "durable_progress_tool_continuation_identity": (
                    durable_progress_tool_continuation_identity
                ),
                "durable_progress_tool_continuation_granted": (
                    durable_progress_tool_continuation_granted
                ),
                "durable_progress_tool_continuation_selected_work": dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                ),
            }
            if durable_progress_tool_replay_pending
            else {}
        )
        skeleton_route_banked = bool(
            skeleton_banked_logs or partial_try_lean_promotions > 0
        )
        skeleton_route_metadata: Dict[str, Any] = {}
        if skeleton_tool_logs:
            skeleton_route_metadata = {
                "try_skeleton_tool_calls": len(skeleton_tool_logs),
                "try_skeleton_routes_banked": len(skeleton_banked_logs),
                "partial_try_lean_promotions": partial_try_lean_promotions,
                "unverified_decomposition_created": bool(skeleton_route_banked),
                "assembly_contracts_added": bool(skeleton_route_banked),
            }
        elif partial_try_lean_promotions > 0:
            skeleton_route_metadata = {
                "try_skeleton_tool_calls": 0,
                "try_skeleton_routes_banked": 0,
                "partial_try_lean_promotions": partial_try_lean_promotions,
                "unverified_decomposition_created": True,
                "assembly_contracts_added": True,
            }
        compute_tool_metadata: Dict[str, Any] = {}
        if compute_receipt_logs:
            compute_tool_metadata = {
                "compute_examples_protocol_attempts": len(compute_protocol_logs),
                "compute_examples_tool_calls": len(compute_tool_logs),
                "compute_examples_successes": len(compute_success_logs),
                "compute_examples_malformed_calls": len(compute_malformed_logs),
            }
        checked_bridge_metadata = (
            {
                "accepted_try_lean_helpers_banked": len(
                    accepted_try_lean_helper_names
                ),
                "accepted_try_lean_helper_names": list(
                    accepted_try_lean_helper_names
                ),
            }
            if accepted_try_lean_helper_names
            else {}
        )
        # The tool loop can have staged a route-local root result immediately
        # before its elapsed LLM/tool-loop budget expires.  Its deadline
        # result is authoritative: do not copy those staged helpers or hand
        # off its finalization into the real dossier/proof state before the
        # ordinary error path below reports the retryable timeout.
        llm_turn_elapsed_budget_exhausted = reported_elapsed_budget_exhaustion or bool(
            getattr(loop_result, "llm_turn_elapsed_budget_exhausted", False)
        ) or str(getattr(loop_result, "llm_error", "") or "") == (
            "llm_turn_elapsed_budget_exhausted"
        )
        route_scoped_tool_helpers: Tuple[str, ...] = ()
        if not llm_turn_elapsed_budget_exhausted:
            route_scoped_tool_helpers = _propagate_route_scoped_tool_helpers(
                source_dossier=llm_dossier,
                target_dossier=dossier,
            )
        durable_checked_tool_helpers = tuple(
            dict.fromkeys(
                [
                    *route_scoped_tool_helpers,
                    *[
                        name
                        for name in accepted_try_lean_helper_names
                        if name
                        in dict(
                            getattr(dossier, "verified_helpers", {}) or {}
                        )
                    ],
                ]
            )
        )
        if route_scoped_tool_helpers and assemble_route_goal_statement:
            selected_record = getattr(session, "selected_work_item_record", {}) or {}
            if not isinstance(selected_record, dict):
                selected_record = {}
            route_id = str(
                assemble_route_contract_status.get("route_id")
                or selected_record.get("route_id")
                or ""
            )
            updated_contract_status = _extend_route_contract_with_tool_helpers(
                dossier=dossier,
                route_id=route_id,
                helper_names=route_scoped_tool_helpers,
                target_statement=str(
                    getattr(dossier, "root_statement", "")
                    or getattr(conv, "goal_statement", "")
                    or ""
                ),
                phase=conv.role,
                turn_index=phase_turn,
            )
            if updated_contract_status:
                assemble_route_contract_status = updated_contract_status
            assemble_route_helper_blocks = _merge_route_scoped_tool_helper_blocks(
                assemble_route_helper_blocks,
                helper_names=route_scoped_tool_helpers,
                dossier=dossier,
            )
            assemble_route_helper_names = [
                name
                for block in assemble_route_helper_blocks
                for name in [helper_decl_name(block)]
                if name
            ]
        if route_scoped_tool_helpers and proof_state is not None:
            try:
                proof_state.reconcile_with_dossier(dossier)
            except Exception:
                pass
            sync_proof_state_to_graph(
                proof_state,
                dossier,
                session=session,
                phase="route_scoped_tool_helper_propagated",
                turn_index=phase_turn,
            )

        finalized_source = (
            llm_dossier
            if not llm_turn_elapsed_budget_exhausted
            and getattr(llm_dossier, "final_proof_hash", None)
            else dossier
            if not llm_turn_elapsed_budget_exhausted
            and getattr(dossier, "final_proof_hash", None)
            else None
        )
        finalized_proof = str(
            getattr(finalized_source, "final_proof", "") if finalized_source is not None else ""
        ).strip()
        if finalized_source is not None and finalized_proof:
            replay_helpers = tuple(
                str(block or "").strip()
                for block in list(getattr(finalized_source, "final_replay_helpers", []) or [])
                if str(block or "").strip()
            )
            helper_names = tuple(
                name
                for block in replay_helpers
                for name in [helper_decl_name(block)]
                if name
            )
            root_metadata: Dict[str, Any] = {}
            graph = (
                getattr(finalized_source, "proof_graph", None)
                if finalized_source is not None
                else None
            )
            if graph is None and dossier is not None:
                graph = getattr(dossier, "proof_graph", None)
            root_node = None
            if graph is not None:
                root_node = getattr(graph, "nodes", {}).get(
                    getattr(graph, "root_node_id", "")
                )
                root_metadata = dict(getattr(root_node, "metadata", {}) or {})
            dependency_key_present = (
                "root_finalization_dependency_helper_names" in root_metadata
            )
            dependency_source = (
                root_metadata.get("root_finalization_dependency_helper_names")
                if dependency_key_present
                else root_metadata.get("root_finalization_helper_names")
            )
            dependency_helper_names = tuple(
                str(name or "").strip()
                for name in list(dependency_source or ())
                if str(name or "").strip()
            )
            route_id = str(root_metadata.get("root_finalization_route_id") or "").strip()
            dependency_node_ids = tuple(
                str(node_id or "").strip()
                for node_id in list(
                    root_metadata.get("root_finalization_dependency_node_ids") or ()
                )
                if str(node_id or "").strip()
            )
            verification_certificate = dict(
                root_metadata.get("root_finalization_verification_certificate") or {}
            )
            if (
                dossier is not None
                and finalized_source is not dossier
                and not getattr(dossier, "final_proof_hash", None)
            ):
                try:
                    dossier.mark_solved(
                        finalized_proof,
                        replay_helpers=replay_helpers,
                        support_helper_names=(
                            dependency_helper_names
                            if dependency_key_present
                            else dependency_helper_names or None
                        ),
                    )
                except TypeError:
                    dossier.mark_solved(finalized_proof, replay_helpers=replay_helpers)
                except Exception:
                    pass
            if proof_state is not None and dossier is not None:
                sync_proof_state_to_graph(
                    proof_state,
                    dossier,
                    session=session,
                    phase="tool_root_finalization_handoff",
                    turn_index=phase_turn,
                )
            _emit_record(session, {
                "phase": "tool_root_finalization",
                "turn_in_phase": phase_turn,
                "model": model_id,
                "tool_calls_used": loop_result.tool_calls_used,
                "tool_call_log": loop_result.tool_call_log,
                "messages_sent": loop_result.sent_messages,
                **temperature_metadata,
                **token_cap_metadata,
                **compute_tool_metadata,
                "accepted_proof": finalized_proof,
                "replay_helpers": list(replay_helpers),
                "helper_names": list(helper_names),
                "dependency_helper_names": list(dependency_helper_names),
                "route_id": route_id,
                "dependency_node_ids": list(dependency_node_ids),
                "verdict": "root_finalized_by_tool",
                "llm_elapsed_s": loop_result.elapsed_s,
            })
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=True,
                proof=finalized_proof,
                helpers_added=(),
                progress=True,
                cost_seconds=cost,
                root_candidate=RootFinalizationCandidate(
                    proof=finalized_proof,
                    replay_helpers=replay_helpers,
                    helper_names=helper_names,
                    dependency_helper_names=dependency_helper_names,
                    phase="tool_root_finalization",
                    turn_index=phase_turn,
                    source_action_id=self.id,
                    route_id=route_id,
                    dependency_node_ids=dependency_node_ids,
                    target_statement=str(
                        getattr(dossier, "root_statement", "")
                        or getattr(conv, "goal_statement", "")
                        or ""
                    ),
                    require_route_contract=bool(
                        root_metadata.get("root_finalization_require_route_contract")
                    ),
                    verification_certificate=verification_certificate,
                    metadata={
                        **token_cap_metadata,
                        **compute_tool_metadata,
                        **skeleton_route_metadata,
                        "root_finalization_already_applied": True,
                        "llm_elapsed_s": loop_result.elapsed_s,
                    },
                ),
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **temperature_metadata,
                    **token_cap_metadata,
                    **compute_tool_metadata,
                    **skeleton_route_metadata,
                    "solved_via": "apply_decl_to_goal_tool",
                    "replay_helpers": list(replay_helpers),
                    "helper_names": list(helper_names),
                    "dependency_helper_names": list(dependency_helper_names),
                    "route_id": route_id,
                    "dependency_node_ids": list(dependency_node_ids),
                    "root_finalization_already_applied": True,
                    "llm_elapsed_s": loop_result.elapsed_s,
                },
            )

        repair_self_check_attempted = bool(
            getattr(loop_result, "repair_self_check_attempted", False)
        )
        repair_self_check_accepted = bool(
            getattr(loop_result, "repair_self_check_accepted", False)
        ) or bool(getattr(loop_result, "repair_self_check_codes", []))
        repair_self_check_budget_exhausted = bool(
            getattr(loop_result, "repair_self_check_budget_exhausted", False)
        )
        repair_self_check_helper_only_allowed = bool(
            getattr(loop_result, "repair_self_check_helper_only_allowed", False)
        )
        repair_self_check_status = str(
            getattr(loop_result, "repair_self_check_status", "")
            or getattr(loop_result, "repair_self_check_missing_kind", "")
            or ""
        ).strip()
        if not repair_self_check_status and bool(
            getattr(loop_result, "repair_self_check_required", False)
        ):
            if repair_self_check_accepted:
                repair_self_check_status = "accepted"
            elif repair_self_check_attempted:
                repair_self_check_status = "no_accepted_try_lean"
            elif repair_self_check_budget_exhausted:
                repair_self_check_status = "tool_budget_exhausted"
            elif repair_self_check_helper_only_allowed:
                repair_self_check_status = "helper_only_decomposition"
            else:
                repair_self_check_status = "no_try_lean_call"
        if (
            loop_result.llm_error == "repair_self_check_missing"
            and repair_self_check_status == "no_accepted_try_lean"
        ):
            loop_result.llm_error = None
        repair_self_check_policy_fields: Dict[str, Any] = {}
        if bool(getattr(loop_result, "repair_self_check_required", False)):
            repair_self_check_policy_fields = {
                "repair_self_check_required": True,
                "repair_self_check_attempted": repair_self_check_attempted,
                "repair_self_check_accepted": repair_self_check_accepted,
                "repair_self_check_status": repair_self_check_status,
                "repair_self_check_missing_kind": repair_self_check_status,
                "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                "repair_self_check_helper_only_allowed": (
                    repair_self_check_helper_only_allowed
                ),
                "repair_discovery_tool_calls_used": int(
                    getattr(
                        loop_result,
                        "repair_discovery_tool_calls_used",
                        0,
                    )
                    or 0
                ),
                "repair_verification_tool_calls_used": int(
                    getattr(
                        loop_result,
                        "repair_verification_tool_calls_used",
                        0,
                    )
                    or 0
                ),
            }
            if repair_self_check_status in {
                "no_try_lean_call",
                "no_accepted_try_lean",
                "tool_budget_exhausted",
                "try_lean_infrastructure_error",
                "try_lean_malformed_arguments",
                "try_lean_preflight_error",
            }:
                repair_self_check_policy_fields[
                    "repair_self_check_advisory"
                ] = True

        repair_self_check_policy_reasons = {
            "repair_self_check_missing",
            "repair_self_check_no_try_lean_call",
            "repair_self_check_no_accepted_try_lean",
            "repair_self_check_tool_budget_exhausted",
        }
        if loop_result.llm_error in repair_self_check_policy_reasons:
            durable_submission_evidence = False
            if (
                repair_self_check_status == "no_try_lean_call"
                and dossier is not None
            ):
                # A model that verified its EXACT proof body with an accepted
                # try_lean one turn
                # earlier and re-submits it unchanged has satisfied the
                # behavioral self-check. The durable stub is keyed by
                # normalized body + goal + preamble + context-helper identity,
                # so any drift forces a fresh check. Prose claims never match.
                try:
                    from ensemble_prover.mini_prover import (
                        _feedback_lemmas_for_answer_safe_recheck,
                    )

                    durable_submission_evidence = (
                        _repair_self_check_durable_submission_evidence(
                            loop_result.content,
                            dossier=dossier,
                            goal_statement=str(
                                getattr(conv, "goal_statement", "") or ""
                            ),
                            preamble=str(getattr(conv, "preamble", "") or ""),
                            context_lemmas=(
                                _feedback_lemmas_for_answer_safe_recheck(
                                    dossier.verified_helper_blocks(),
                                    conv,
                                )
                            ),
                        )
                    )
                except Exception:
                    durable_submission_evidence = False
                if durable_submission_evidence:
                    # Sol audit 2026-07-29 F3: rewrite the status so a later
                    # GENUINE Lean failure on this turn cannot be reclassified
                    # from the stale "no_try_lean_call" back into a policy
                    # refusal (which would recreate repair narrowing). The
                    # tool did NOT run this turn — attempted stays False; the
                    # evidence source is recorded explicitly.
                    repair_self_check_status = "accepted_durable"
                    repair_self_check_policy_fields.update(
                        {
                            "repair_self_check_status": "accepted_durable",
                            "repair_self_check_missing_kind": "",
                            "repair_self_check_compliant": True,
                            "repair_self_check_evidence_source": (
                                "durable_prior_stub"
                            ),
                        }
                    )
                    increment_metric = getattr(
                        session, "_increment_dossier_metric", None
                    )
                    if callable(increment_metric):
                        increment_metric(
                            "mini_repair_self_check_durable_evidence_accepted",
                            1,
                        )
            if (
                repair_self_check_status == "no_accepted_try_lean"
                or _repair_self_check_non_verdict_is_compliant(
                    repair_self_check_status
                )
                or durable_submission_evidence
                or _repair_protocol_error_is_advisory(loop_result.llm_error)
            ):
                # The self-check contract improves diagnostics; it is not a
                # second mathematical authority. Preserve compliance/evidence
                # telemetry, then let extraction and the independent final
                # Lean check decide any executable artifact. A prose-only
                # response will still take the ordinary no-proof/give-up path.
                repair_self_check_policy_fields[
                    "repair_self_check_advisory"
                ] = True
                loop_result.llm_error = None

        if loop_result.llm_error is not None:
            if loop_result.llm_error in repair_self_check_policy_reasons:
                repair_self_check_missing_kind = (
                    repair_self_check_status or "no_try_lean_call"
                )
                if loop_result.llm_error == "repair_self_check_tool_budget_exhausted":
                    repair_policy_reason = "repair_self_check_tool_budget_exhausted"
                elif loop_result.llm_error == "repair_self_check_no_accepted_try_lean":
                    repair_policy_reason = "repair_self_check_no_accepted_try_lean"
                elif loop_result.llm_error == "repair_self_check_no_try_lean_call":
                    repair_policy_reason = "repair_self_check_no_try_lean_call"
                elif repair_self_check_missing_kind == "tool_budget_exhausted":
                    repair_policy_reason = "repair_self_check_tool_budget_exhausted"
                elif repair_self_check_missing_kind == "no_accepted_try_lean":
                    repair_policy_reason = "repair_self_check_no_accepted_try_lean"
                else:
                    repair_policy_reason = "repair_self_check_no_try_lean_call"
                selected_scope = dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                )
                scope_identity = (
                    str(selected_scope.get("target_hash") or "").strip()
                    or str(selected_scope.get("node_id") or "").strip()
                    or text_hash(str(getattr(conv, "goal_statement", "") or ""))
                )
                continuation_key = hashlib.sha256(
                    (
                        "repair_self_check\n"
                        + scope_identity
                    ).encode("utf-8", errors="replace")
                ).hexdigest()[:24]
                continuation_counts = getattr(
                    session,
                    "repair_self_check_continuation_counts",
                    None,
                )
                if not isinstance(continuation_counts, dict):
                    continuation_counts = {}
                    session.repair_self_check_continuation_counts = (
                        continuation_counts
                    )
                prior_continuations = int(
                    continuation_counts.get(continuation_key, 0) or 0
                )
                # One action-level retry is free. The inner tool loop has
                # already issued its immediate reminder; this durable retry
                # protects the graph/repair lease from a single refusal while
                # remaining bounded if the model repeatedly ignores try_lean.
                non_consuming_self_check_continuation = (
                    prior_continuations < 1
                )
                if non_consuming_self_check_continuation:
                    continuation_counts[continuation_key] = (
                        prior_continuations + 1
                    )
                try:
                    from ensemble_prover.mini_prover import (
                        _bank_helpers_as_proposed,
                        _extract_helpers_and_main,
                        _extract_lemma_dag_helper_declarations,
                        _format_repair_self_check_missing_feedback,
                        _record_repair_policy_attempt,
                    )
                except Exception:
                    _bank_helpers_as_proposed = None  # type: ignore[assignment]
                    _extract_helpers_and_main = None  # type: ignore[assignment]
                    _extract_lemma_dag_helper_declarations = None  # type: ignore[assignment]
                    _format_repair_self_check_missing_feedback = None  # type: ignore[assignment]
                    _record_repair_policy_attempt = None  # type: ignore[assignment]
                content = loop_result.content
                extracted_helpers: list[str] = []
                banked_proposed_helpers: list[str] = []
                giveup: Optional[Dict[str, str]] = None
                try:
                    theorem_name = (
                        getattr(dossier, "theorem_name", "")
                        if dossier is not None
                        else ""
                    )
                    helpers, _proof = (
                        _extract_helpers_and_main(
                            content or "",
                            theorem_name=str(theorem_name or ""),
                            goal_statement=str(
                                getattr(conv, "goal_statement", "") or ""
                            ),
                            allow_decl_main=True,
                        )
                        if callable(_extract_helpers_and_main)
                        else ([], None)
                    )
                    lemma_dag_candidates = (
                        _extract_lemma_dag_helper_declarations(
                            content or "",
                            theorem_name=str(theorem_name or ""),
                            suppress_solution_placeholders=bool(
                                getattr(conv, "suppress_solution_placeholders", False)
                            ),
                        )
                        if callable(_extract_lemma_dag_helper_declarations)
                        else []
                    )
                    extracted_helpers = list(helpers or lemma_dag_candidates or [])
                    giveup = _classify_turn_giveup(content or "", _proof, helpers)
                    if giveup:
                        banked_proposed_helpers = []
                    elif callable(_bank_helpers_as_proposed):
                        banked_proposed_helpers = list(
                            _bank_helpers_as_proposed(
                                dossier,
                                helpers,
                                phase=str(getattr(conv, "role", "prove") or "prove"),
                                turn_index=phase_turn,
                                fallback_helpers=lemma_dag_candidates,
                                goal_statement=str(
                                    getattr(conv, "goal_statement", "") or ""
                                ),
                                allow_helper_decomposition=bool(
                                    getattr(conv, "allow_helper_decomposition", True)
                                ),
                            )
                        )
                except Exception:
                    extracted_helpers = []
                    banked_proposed_helpers = []
                if giveup and non_consuming_self_check_continuation:
                    # A mathematical give-up is not a verifier-compliance miss
                    # and must not receive a free action-level retry.
                    continuation_counts.pop(continuation_key, None)
                    non_consuming_self_check_continuation = False
                if giveup:
                    # Preserve the stronger semantic policy classification:
                    # active proof text attached to a give-up is neither a
                    # repair attempt nor a self-check-continuation candidate.
                    repair_policy_reason = "giveup_policy_active_proof_redirect"
                _emit_record(session, {
                    "phase": conv.role,
                    "turn_in_phase": phase_turn,
                    "model": model_id,
                    "tool_calls_used": loop_result.tool_calls_used,
                    "tool_call_log": loop_result.tool_call_log,
                    "messages_sent": loop_result.sent_messages,
                    **temperature_metadata,
                    **token_cap_metadata,
                    **compute_tool_metadata,
                    "llm_response": content,
                    "llm_elapsed_s": loop_result.elapsed_s,
                    **tool_repeat_metadata,
                    "extracted_helpers": list(extracted_helpers),
                    "rejection_reason": repair_policy_reason,
                    "lean_error_type": repair_policy_reason,
                    "banked_proposed_helpers": list(banked_proposed_helpers),
                    "giveup_cluster": (
                        str(giveup.get("cluster") or "") if giveup else None
                    ),
                    "giveup_match": str(giveup.get("match") or "") if giveup else "",
                    "banking_suppressed_by_giveup": bool(giveup),
                    **skeleton_route_metadata,
                    **repair_self_check_policy_fields,
                    "non_consuming_repair_self_check_continuation": (
                        non_consuming_self_check_continuation
                    ),
                    "repair_self_check_continuation_key": continuation_key,
                    "repair_self_check_attempted": repair_self_check_attempted,
                    "repair_self_check_accepted": repair_self_check_accepted,
                    "repair_self_check_status": repair_self_check_missing_kind,
                    "repair_self_check_missing_kind": repair_self_check_missing_kind,
                    "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                    "verdict": "proof_policy_rejected",
                })
                if callable(_record_repair_policy_attempt):
                    _record_repair_policy_attempt(
                        dossier,
                        phase=conv.role,
                        turn_index=phase_turn,
                        proof=content or "",
                        reason=repair_policy_reason,
                        metadata={
                            **dict(graph_native_attempt_metadata or {}),
                            "tool_calls_used": loop_result.tool_calls_used,
                            **tool_repeat_metadata,
                            **skeleton_route_metadata,
                            **repair_self_check_policy_fields,
                            "policy_repair_redirect": (
                                non_consuming_self_check_continuation
                            ),
                            "non_consuming_repair_self_check_continuation": (
                                non_consuming_self_check_continuation
                            ),
                            "repair_self_check_continuation_key": (
                                continuation_key
                            ),
                            "repair_self_check_attempted": repair_self_check_attempted,
                            "repair_self_check_accepted": repair_self_check_accepted,
                            "repair_self_check_status": repair_self_check_missing_kind,
                            "repair_self_check_missing_kind": repair_self_check_missing_kind,
                            "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                        },
                        node_id=graph_native_attempt_node_id or None,
                    )
                try:
                    if giveup:
                        conv.append_user(
                            _format_turn_giveup_feedback(
                                conv=conv,
                                session=session,
                                giveup=giveup,
                                turn=phase_turn,
                                max_turns=max_turns_footer,
                            )
                        )
                    elif callable(_format_repair_self_check_missing_feedback):
                        theorem_name = (
                            getattr(dossier, "theorem_name", "")
                            if dossier is not None
                            else ""
                        )
                        conv.append_user(
                            _format_repair_self_check_missing_feedback(
                                content,
                                require_try_lean=effective_try_lean_tool_enabled,
                                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                                theorem_name=str(theorem_name or ""),
                                role=str(getattr(conv, "role", "") or self.role or "prove"),
                            )
                        )
                except Exception:
                    pass
                cost = time.monotonic() - started
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=bool(skeleton_route_banked),
                    cost_seconds=cost,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **token_cap_metadata,
                        **tool_repeat_metadata,
                        **tool_progress_metadata,
                        **compute_tool_metadata,
                        "rejection_reason": repair_policy_reason,
                        "lean_error_type": repair_policy_reason,
                        "banked_proposed_helpers": list(banked_proposed_helpers),
                        "giveup_cluster": (
                            str(giveup.get("cluster") or "") if giveup else None
                        ),
                        "giveup_match": str(giveup.get("match") or "") if giveup else "",
                        "banking_suppressed_by_giveup": bool(giveup),
                        **skeleton_route_metadata,
                        **durable_progress_replay_metadata,
                        "strong_progress": False,
                        "unverified_decomposition_created": bool(skeleton_route_banked),
                        "assembly_contracts_added": bool(skeleton_route_banked),
                        **repair_self_check_policy_fields,
                        "policy_repair_redirect": (
                            non_consuming_self_check_continuation
                        ),
                        "repair_redirect_reason": (
                            repair_policy_reason
                            if non_consuming_self_check_continuation
                            else ""
                        ),
                        "preserve_action_budget": (
                            non_consuming_self_check_continuation
                        ),
                        "preserve_frontier_work": (
                            non_consuming_self_check_continuation
                        ),
                        "stagnation_neutral": (
                            non_consuming_self_check_continuation
                        ),
                        "hard_pivot_neutral": (
                            non_consuming_self_check_continuation
                        ),
                        "refund_conversation_phase_turn": (
                            non_consuming_self_check_continuation
                        ),
                        "refund_local_repair_quota": (
                            non_consuming_self_check_continuation
                        ),
                        "non_consuming_repair_self_check_continuation": (
                            non_consuming_self_check_continuation
                        ),
                        "repair_self_check_continuation_key": continuation_key,
                        "repair_self_check_attempted": repair_self_check_attempted,
                        "repair_self_check_accepted": repair_self_check_accepted,
                        "repair_self_check_status": repair_self_check_missing_kind,
                        "repair_self_check_missing_kind": repair_self_check_missing_kind,
                        "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                        "repair_self_check_metric_counted": True,
                        "llm_response": content,
                        "verdict": "proof_policy_rejected",
                    },
                )
            # H7 telemetry: emit verdict=llm_call_failed mirroring legacy
            # mini_prover.py:3538-3548.
            structured_failure_kind = str(
                getattr(loop_result, "llm_failure_kind", "") or ""
            ).strip()
            structured_failure_reason_text = str(
                getattr(loop_result, "llm_failure_reason", "") or ""
            ).strip()
            selected_work_projection_invalidated = False
            if structured_failure_kind:
                terminal_failure = bool(
                    getattr(loop_result, "llm_terminal", False)
                )
                terminal_failure_reason = (
                    structured_failure_reason_text if terminal_failure else ""
                )
                llm_retryable = bool(getattr(loop_result, "llm_retryable", False))
                if not terminal_failure and (
                    structured_failure_kind == "transient"
                    or structured_failure_kind == "transport"
                    or (structured_failure_kind == "rate_limit" and llm_retryable)
                    or (
                        structured_failure_kind.startswith("http_")
                        and llm_retryable
                    )
                ):
                    terminal_failure = True
                    terminal_failure_reason = "llm_network_error"
                llm_failure_kind = structured_failure_kind
                selected_work_projection_invalidated = bool(
                    structured_failure_kind
                    == "mini_selected_proof_idea_context_error"
                    and structured_failure_reason_text
                    == "selected_proof_idea_context_invalidated"
                )
            else:
                llm_error_classification = classify_llm_error_text(
                    loop_result.llm_error
                )
                terminal_failure_reason = (
                    llm_error_classification.failure_reason
                    if llm_error_classification.terminal
                    else ""
                )
                terminal_failure = bool(terminal_failure_reason)
                llm_failure_kind = llm_error_classification.kind
                llm_retryable = bool(llm_error_classification.retryable)
            provider_blocked_reason = _PROVIDER_BLOCKED_REASON_BY_KIND.get(
                llm_failure_kind,
                "",
            )
            provider_lane_run_closed = bool(
                llm_failure_kind == "provider_lane_run_closed"
            )
            if provider_lane_run_closed:
                # Closing one cancellation-resistant serving lane cannot
                # revoke an independent provider fingerprint.  The closed
                # lane is non-retryable in this run; the scheduler may still
                # dispatch another role/provider.
                terminal_failure = False
                terminal_failure_reason = ""
                llm_retryable = False
                scoped_failure_reason = "provider_lane_run_closed"
                failure_scope = "scoped"
            elif provider_blocked_reason:
                # Provider credentials, account state, or route capability can
                # recover independently of this mathematical lane.  They are
                # durable scheduler blocks, never implicit run termination.
                terminal_failure = False
                terminal_failure_reason = ""
                llm_retryable = True
                scoped_failure_reason = provider_blocked_reason
                failure_scope = "scoped"
            else:
                scoped_failure_reason = ""
                failure_scope = llm_failure_scope(terminal_failure_reason)
            provider_turn_lane_retired = bool(
                llm_failure_kind == "llm_provider_cumulative_wall_exhausted"
            )
            if provider_turn_lane_retired:
                terminal_failure = False
                terminal_failure_reason = ""
                scoped_failure_reason = (
                    "llm_provider_cumulative_wall_exhausted"
                )
                failure_scope = "scoped"
            if failure_scope == "scoped":
                scoped_failure_reason = (
                    scoped_failure_reason or terminal_failure_reason
                )
                terminal_failure_reason = ""
                terminal_failure = False
            if selected_work_projection_invalidated:
                scoped_failure_reason = structured_failure_reason_text
                failure_scope = llm_failure_scope(scoped_failure_reason)
            provider_calls_completed = int(
                getattr(loop_result, "provider_calls_completed", 0) or 0
            )
            provider_dispatches_started = int(
                getattr(loop_result, "provider_dispatches_started", 0) or 0
            )
            selected_work_projection_zero_provider = bool(
                selected_work_projection_invalidated
                and int(getattr(loop_result, "tool_calls_used", 0) or 0) == 0
            )
            if not scoped_failure_reason and llm_failure_kind in {
                "llm_network_error",
                "llm_retry_deadline_exhausted",
            }:
                scoped_failure_reason = llm_failure_kind
                failure_scope = llm_failure_scope(scoped_failure_reason)
            if (
                not scoped_failure_reason
                and llm_retryable
                and structured_failure_kind
                and llm_failure_scope(structured_failure_reason_text) == "scoped"
            ):
                # Preserve the precise producer kind for diagnostics while
                # routing its established retry reason through the scheduler's
                # bounded scoped-infrastructure lane.
                scoped_failure_reason = structured_failure_reason_text
                failure_scope = "scoped"
            if terminal_failure_reason:
                increment = getattr(session, "_increment_dossier_metric", None)
                if callable(increment):
                    increment("mini_session_terminal_llm_failures", 1)
                    if terminal_failure_reason == "llm_insufficient_quota":
                        increment("mini_session_terminal_llm_insufficient_quota", 1)
            if scoped_failure_reason:
                increment = getattr(session, "_increment_dossier_metric", None)
                if callable(increment):
                    increment("mini_session_llm_scoped_failures", 1)
                    if scoped_failure_reason == "llm_retry_deadline_exhausted":
                        increment("mini_session_llm_retry_deadline_scoped_failures", 1)
            llm_retry_deadline = dict(
                getattr(loop_result, "llm_retry_deadline", {}) or {}
            )
            provider_defer = dict(
                getattr(loop_result, "provider_defer", {}) or {}
            )
            failed_provider_pre_generation_rejection = bool(
                getattr(
                    loop_result,
                    "failed_provider_pre_generation_rejection",
                    False,
                )
            )
            provider_attempts = list(
                getattr(loop_result, "provider_attempts", []) or []
            )
            tool_state_updates = int(
                getattr(loop_result, "tool_state_updates", 0) or 0
            )
            tool_state_closures = int(
                getattr(loop_result, "tool_state_closures", 0) or 0
            )
            zero_provider_failure = bool(
                llm_retryable
                and provider_calls_completed == 0
                and (
                    provider_dispatches_started == 0
                    or bool(provider_defer.get("provider_defer_fingerprint"))
                )
                and tool_state_updates == 0
                and tool_state_closures == 0
            )
            paid_tool_infrastructure_disposition = str(
                getattr(
                    loop_result,
                    "paid_tool_infrastructure_disposition",
                    "",
                )
                or ""
            )
            refundable_zero_provider_failure = bool(
                zero_provider_failure
                and paid_tool_infrastructure_disposition
                != "infrastructure_after_launch"
            )
            tool_state_statuses = [
                str(item or "").strip()
                for item in list(
                    getattr(loop_result, "tool_state_update_statuses", []) or []
                )
                if str(item or "").strip()
            ]
            llm_turn_elapsed_budget_exhausted = bool(
                getattr(loop_result, "llm_turn_elapsed_budget_exhausted", False)
            )
            llm_turn_elapsed_budget_s = float(
                getattr(loop_result, "llm_turn_elapsed_budget_s", 0.0) or 0.0
            )
            request_timeout_override_s = getattr(
                loop_result,
                "request_timeout_override_s",
                None,
            )
            operation_timeout_override_s = getattr(
                loop_result,
                "operation_timeout_override_s",
                None,
            )
            provider_timeout_lease_partitioned = bool(
                getattr(
                    loop_result,
                    "provider_timeout_lease_partitioned",
                    False,
                )
            )
            counterexample_certification_infrastructure = bool(
                llm_failure_kind
                == "certify_counterexample_infrastructure_error"
                and scoped_failure_reason == "llm_network_error"
                and llm_retryable
            )
            cooperative_provider_yield = bool(
                getattr(loop_result, "provider_call_quantum_exhausted", False)
                and (
                    provider_calls_completed > 0
                    or getattr(
                        loop_result,
                        "provider_finalizer_continuation_exhausted",
                        False,
                    )
                )
                and llm_failure_kind
                in {
                    "llm_provider_quantum_exhausted",
                    "provider_dispatch_attempt_limit_exhausted",
                }
                and llm_retryable
            )
            refundable_cooperative_provider_yield = bool(
                cooperative_provider_yield and provider_calls_completed == 0
            )
            accounting_neutral_failure = bool(
                refundable_zero_provider_failure
                or selected_work_projection_zero_provider
                or counterexample_certification_infrastructure
                or cooperative_provider_yield
            )
            llm_failure_compaction_record: Dict[str, Any] = {}
            compact_after_failure = getattr(
                conv,
                "compact_history_for_refine_handoff",
                None,
            )
            permanent_nonretryable_kinds = {
                "llm_cost_budget_reserved_capacity",
                "llm_cost_budget_request_capacity",
                "llm_cost_budget_retry_capacity",
                "llm_cost_budget_exhausted",
                "llm_cost_budget_unknown_pricing",
            }
            nonretryable_http_failure = bool(
                llm_failure_kind.startswith("http_") and not llm_retryable
            )
            final_no_tools_failure = llm_failure_kind.startswith(
                "final_no_tools_"
            )
            compact_retry_history = bool(
                callable(compact_after_failure)
                and not terminal_failure
                and llm_failure_kind not in permanent_nonretryable_kinds
                and not nonretryable_http_failure
                and not cooperative_provider_yield
            )
            if compact_retry_history:
                compaction_kwargs: Dict[str, Any] = {
                    "force": True,
                    "reason": (
                        "final_no_tools_retry"
                        if final_no_tools_failure
                        else "llm_failure_retry"
                    ),
                    # Retain a bounded, protocol-complete suffix of recent
                    # Lean evidence for every retryable provider failure.
                    "keep_recent_tool_rounds": 3,
                }
                if final_no_tools_failure:
                    # Serialization failure does not justify deleting all
                    # productive Lean evidence. Retain a bounded recent suffix
                    # so repeated fresh action invocations cannot grow an
                    # unbounded tool transcript either.
                    compaction_kwargs["keep_recent_tool_rounds"] = 3
                elif counterexample_certification_infrastructure:
                    # The exact candidate is deterministic paid work. Keep its
                    # B1-complete tool round so a bounded scheduler retry can
                    # replay certification instead of asking the model to
                    # rediscover the same negation.
                    compaction_kwargs["keep_recent_tool_rounds"] = 1
                try:
                    llm_failure_compaction_record = dict(
                        compact_after_failure(**compaction_kwargs)
                        or {}
                    )
                except TypeError:
                    # Older compactors may reject keep_recent_tool_rounds
                    # and/or reason. Degrade gracefully: keep reason when
                    # possible so we do not fall straight to refine_handoff
                    # (which kills repair state and mis-applies keep=3 for
                    # llm_failure_retry).
                    llm_failure_compaction_record = {}
                    for attempt in (
                        {
                            "force": True,
                            "reason": compaction_kwargs["reason"],
                        },
                        {"force": True},
                    ):
                        try:
                            llm_failure_compaction_record = dict(
                                compact_after_failure(**attempt) or {}
                            )
                            break
                        except TypeError:
                            continue
                        except Exception:
                            llm_failure_compaction_record = {}
                            break
                except Exception:
                    llm_failure_compaction_record = {}
            llm_failure_compaction_metadata: Dict[str, Any] = {}
            if llm_failure_compaction_record:
                llm_failure_compaction_metadata = {
                    "llm_failure_tool_history_compacted": True,
                    "llm_failure_tool_history_compacted_messages": int(
                        llm_failure_compaction_record.get("removed_messages", 0)
                        or 0
                    ),
                    "llm_failure_tool_history_compacted_tool_rounds": int(
                        llm_failure_compaction_record.get("removed_tool_rounds", 0)
                        or 0
                    ),
                    "llm_failure_tool_history_compacted_chars": int(
                        llm_failure_compaction_record.get("removed_chars", 0)
                        or 0
                    ),
                }
                _emit_record(session, {
                    "phase": "session_llm_failure_history_compaction",
                    "turn_in_phase": phase_turn,
                    "action_id": self.id,
                    **llm_failure_compaction_metadata,
                    "verdict": "tool_history_compacted_for_retry",
                })
            tool_state_progress = tool_state_updates > 0
            _emit_record(session, {
                "phase": conv.role,
                "turn_in_phase": phase_turn,
                "model": model_id,
                "tool_calls_used": loop_result.tool_calls_used,
                "tool_call_log": loop_result.tool_call_log,
                "messages_sent": loop_result.sent_messages,
                **temperature_metadata,
                **token_cap_metadata,
                **compute_tool_metadata,
                "tool_state_updates": tool_state_updates,
                "tool_state_closures": tool_state_closures,
                "tool_state_update_statuses": list(tool_state_statuses),
                "llm_error": loop_result.llm_error,
                "llm_failure_kind": llm_failure_kind,
                "llm_failure_reason": structured_failure_reason_text,
                "llm_retryable": llm_retryable,
                "terminal_failure_reason": terminal_failure_reason,
                "scoped_failure_reason": scoped_failure_reason,
                "llm_failure_scope": failure_scope,
                "provider_turn_lane_retired": provider_turn_lane_retired,
                "provider_turn_lane_identity": (
                    provider_turn_lane_identity
                    if provider_turn_lane_retired
                    else ""
                ),
                "selected_work_projection_invalidated": (
                    selected_work_projection_invalidated
                ),
                **llm_retry_deadline,
                **provider_defer,
                "provider_attempts": provider_attempts,
                "retry_count": int(getattr(loop_result, "llm_retry_count", 0) or 0),
                "llm_elapsed_s": loop_result.elapsed_s,
                "llm_turn_elapsed_budget_exhausted": (
                    llm_turn_elapsed_budget_exhausted
                ),
                "llm_turn_elapsed_budget_s": llm_turn_elapsed_budget_s,
                "request_timeout_override_s": request_timeout_override_s,
                "operation_timeout_override_s": operation_timeout_override_s,
                "provider_timeout_lease_partitioned": (
                    provider_timeout_lease_partitioned
                ),
                **tool_repeat_metadata,
                **tool_progress_metadata,
                **skeleton_route_metadata,
                **durable_progress_replay_metadata,
                **llm_failure_compaction_metadata,
                "verdict": (
                    "provider_call_quantum_yielded"
                    if cooperative_provider_yield
                    else "llm_call_failed"
                ),
            })
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=tool_state_progress,
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **temperature_metadata,
                    **token_cap_metadata,
                    **compute_tool_metadata,
                    "tool_state_updates": tool_state_updates,
                    "tool_state_closures": tool_state_closures,
                    "tool_state_update_statuses": list(tool_state_statuses),
                    "llm_error": loop_result.llm_error,
                    "llm_failure_kind": llm_failure_kind,
                    "llm_failure_reason": structured_failure_reason_text,
                    "llm_retryable": llm_retryable,
                    "terminal_failure": bool(terminal_failure),
                    "terminal_failure_reason": terminal_failure_reason,
                    "scoped_failure_reason": scoped_failure_reason,
                    "llm_failure_scope": failure_scope,
                    "provider_turn_lane_retired": provider_turn_lane_retired,
                    "provider_turn_lane_identity": (
                        provider_turn_lane_identity
                        if provider_turn_lane_retired
                        else ""
                    ),
                    "selected_work_projection_invalidated": (
                        selected_work_projection_invalidated
                    ),
                    "selected_work_projection_zero_provider": (
                        selected_work_projection_zero_provider
                    ),
                    "zero_provider_failure": zero_provider_failure,
                    "provider_calls_completed": provider_calls_completed,
                    "provider_dispatches_started": provider_dispatches_started,
                    "failed_provider_pre_generation_rejection": (
                        failed_provider_pre_generation_rejection
                    ),
                    "refund_conversation_phase_turn": bool(
                        accounting_neutral_failure
                        and not (
                            cooperative_provider_yield
                            and not refundable_cooperative_provider_yield
                        )
                    ),
                    "refund_conversation_absolute_turn": bool(
                        refundable_zero_provider_failure
                        or selected_work_projection_zero_provider
                        or refundable_cooperative_provider_yield
                    ),
                    **llm_retry_deadline,
                    **provider_defer,
                    "provider_attempts": provider_attempts,
                    "retry_count": int(
                        getattr(loop_result, "llm_retry_count", 0) or 0
                    ),
                    "llm_turn_elapsed_budget_exhausted": (
                        llm_turn_elapsed_budget_exhausted
                    ),
                    "llm_turn_elapsed_budget_s": llm_turn_elapsed_budget_s,
                    "request_timeout_override_s": request_timeout_override_s,
                    "operation_timeout_override_s": (
                        operation_timeout_override_s
                    ),
                    "provider_timeout_lease_partitioned": (
                        provider_timeout_lease_partitioned
                    ),
                    **tool_repeat_metadata,
                    **tool_progress_metadata,
                    **skeleton_route_metadata,
                    **durable_progress_replay_metadata,
                    **llm_failure_compaction_metadata,
                    "preserve_frontier_work": not bool(
                        selected_work_projection_invalidated
                    ),
                    "defer_selected_frontier_action": bool(
                        not terminal_failure
                        and not selected_work_projection_invalidated
                        and not cooperative_provider_yield
                    ),
                    "non_consuming_repair_ticket_continuation": bool(
                        cooperative_provider_yield
                    ),
                    "preserve_action_budget": bool(
                        accounting_neutral_failure
                    ),
                    "scheduler_neutral": bool(
                        accounting_neutral_failure or provider_turn_lane_retired
                    ),
                    "stagnation_neutral": bool(
                        accounting_neutral_failure or provider_turn_lane_retired
                    ),
                    "hard_pivot_neutral": bool(
                        accounting_neutral_failure or provider_turn_lane_retired
                    ),
                    "iteration_neutral": bool(
                        refundable_zero_provider_failure
                        or cooperative_provider_yield
                    ),
                    "strong_progress": bool(tool_state_closures > 0),
                    "unverified_decomposition_created": bool(
                        skeleton_route_banked
                        or (tool_state_progress and tool_state_closures <= 0)
                    ),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                },
            )

        content = loop_result.content
        proof_patch = apply_proof_patch_from_reply(
            content,
            history=list(getattr(conv, "history", []) or []),
            theorem_name=(
                str(getattr(dossier, "theorem_name", "") or "")
                if dossier is not None
                else ""
            ),
            goal_statement=(
                selected_goal_statement_override
                or str(getattr(conv, "goal_statement", "") or "")
            ),
            suppress_solution_placeholders=bool(
                getattr(conv, "suppress_solution_placeholders", False)
            ),
        )
        proof_patch_metadata: Dict[str, Any] = {}
        if proof_patch.requested and not proof_patch.applied:
            _emit_record(session, {
                "phase": conv.role,
                "turn_in_phase": phase_turn,
                "model": model_id,
                "tool_calls_used": loop_result.tool_calls_used,
                "tool_call_log": loop_result.tool_call_log,
                "messages_sent": loop_result.sent_messages,
                **temperature_metadata,
                **token_cap_metadata,
                **compute_tool_metadata,
                "llm_response": content,
                "llm_elapsed_s": loop_result.elapsed_s,
                "rejection_reason": "proof_patch_failed",
                "lean_error_type": "proof_patch_failed",
                "proof_patch_error": proof_patch.error,
                "proof_patch_hunk_count": proof_patch.hunk_count,
                **tool_repeat_metadata,
                "verdict": "proof_policy_rejected",
            })
            try:
                conv.append_user(format_proof_patch_failure_feedback(proof_patch.error))
            except Exception:
                pass
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=bool(skeleton_route_banked),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **temperature_metadata,
                    **token_cap_metadata,
                    **compute_tool_metadata,
                    "rejection_reason": "proof_patch_failed",
                    "lean_error_type": "proof_patch_failed",
                    "proof_patch_error": proof_patch.error,
                    "llm_response": content,
                    "strong_progress": False,
                    **skeleton_route_metadata,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    **tool_repeat_metadata,
                    **_repair_self_check_metadata(repair_self_check_policy_fields),
                },
            )
        if proof_patch.applied:
            proof_patch_metadata = dict(proof_patch.metadata or {})
            proof_patch_metadata["proof_patch_original_response"] = content
            _emit_record(session, {
                "phase": "proof_patch",
                "turn_in_phase": phase_turn,
                "model": model_id,
                "tool_calls_used": loop_result.tool_calls_used,
                "tool_call_log": loop_result.tool_call_log,
                "messages_sent": loop_result.sent_messages,
                "llm_response": content,
                "llm_elapsed_s": loop_result.elapsed_s,
                **temperature_metadata,
                **token_cap_metadata,
                "proof_patch_hunk_count": proof_patch.hunk_count,
                "previous_proof_line_count": proof_patch_metadata.get(
                    "previous_proof_line_count"
                ),
                "patched_proof_line_count": proof_patch_metadata.get(
                    "patched_proof_line_count"
                ),
                "verdict": "proof_patch_applied",
            })
            content = proof_patch.content
        # Publish for post-Lean subactions (give-up gate classifier).
        session.last_llm_content = str(content or "")
        if conv is not None and session.last_llm_content:
            try:
                setattr(conv, "_last_llm_content", session.last_llm_content)
            except Exception:
                pass

        # ---- Step 2: extract helpers + proof + lemma_dag candidates -
        theorem_name = (
            getattr(dossier, "theorem_name", "") if dossier is not None else ""
        )
        framed_active_root_targets = _framed_active_root_targets_for_turn(
            dossier=dossier,
            conv=conv,
        )
        current_answer_safe_execution_binding["active_root_targets"] = (
            copy.deepcopy(list(framed_active_root_targets or []))
        )
        if (
            answer_safe_pending_replay
            and expected_answer_safe_execution_binding
            != current_answer_safe_execution_binding
        ):
            self._park_answer_safe_recheck(answer_safe_pending)
            self._answer_safe_recheck_pending = {}
            restore_live_turn_state()
            setattr(session, "answer_safe_recheck_pending", None)
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    "lean_verdict": "answer_safe_recheck_binding_rejected",
                    "lean_error_type": "answer_safe_recheck_target_changed",
                    "selected_work_projection_invalidated": True,
                    "answer_safe_recheck_pending": True,
                    "recovered_finalizer_candidate_adjudication_pending": True,
                    "answer_safe_recheck_parked": True,
                    "preserve_action_budget": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "strong_progress": False,
                },
            )
        active_root_extraction_goal = (
            active_root_target_statement(
                framed_active_root_targets,
                require_single=True,
                require_no_hypotheses=False,
                include_hypotheses=True,
            )
            if not selected_goal_statement_override
            else ""
        )
        extraction_goal_statement = (
            selected_goal_statement_override
            or active_root_extraction_goal
            or str(getattr(conv, "goal_statement", "") or "")
        )
        extraction = extract_helpers_and_proof(
            content,
            theorem_name=theorem_name,
            goal_statement=extraction_goal_statement,
            allow_decl_main=True,
            suppress_solution_placeholders=bool(
                getattr(conv, "suppress_solution_placeholders", False)
            ),
            preamble=str(
                getattr(conv, "lean_preamble", "")
                or getattr(conv, "preamble", "")
                or ""
            ),
        )
        # M4 wiring: publish the extraction on the session so direct replay
        # wrappers and helper salvage code can read it without knowing this
        # action's local state.
        session.last_turn_extraction = extraction
        helpers = list(extraction.helpers)
        proof = extraction.proof if isinstance(extraction.proof, str) else None
        lemma_dag_candidates = list(extraction.lemma_dag_candidates)
        submitted_stub_helpers = [
            helper for helper in helpers if has_sorry_or_admit(helper)
        ]
        required_same_turn_helpers = (
            _same_turn_replay_dependency_blocks(proof, helpers)
            if proof is not None
            else []
        )
        independent_main_without_stub_helpers = bool(
            proof is not None
            and submitted_stub_helpers
            and not any(
                has_sorry_or_admit(helper)
                for helper in required_same_turn_helpers
            )
        )
        checkable_submission_helpers = (
            [helper for helper in helpers if not has_sorry_or_admit(helper)]
            if independent_main_without_stub_helpers
            else list(helpers)
        )
        repair_submission_has_executable_lean = bool(
            str(proof or "").strip()
            or any(
                graph_statement_is_executable(helper_decl_statement(candidate))
                and bool(str(helper_decl_body(candidate) or "").strip())
                and not has_sorry_or_admit(candidate)
                for candidate in dict.fromkeys(
                    [*helpers, *lemma_dag_candidates]
                )
            )
        )
        provider_artifact_consumed = bool(
            str(proof or "").strip()
            or any(
                str(candidate or "").strip()
                for candidate in [*helpers, *lemma_dag_candidates]
            )
        )
        forced_final_no_artifact = bool(
            getattr(loop_result, "semantic_no_progress_detected", False)
            and not provider_artifact_consumed
        )
        if forced_final_no_artifact:
            # Only the authoritative turn extractor can decide whether the
            # forced no-tools response contained a usable Lean artifact.  A
            # lexical classifier here previously confused English "By
            # contradiction" and comment-only fences with proofs.  Preserve
            # the model response for audit, but expose the exact protocol miss
            # so this proof-only lane can hand off without another provider
            # call or a false helper-policy diagnosis.
            tool_progress_metadata.update({
                "final_no_tools_event": "final_no_tools_no_proof_artifact",
                "final_no_tools_finish_reason": str(
                    getattr(loop_result, "final_no_tools_finish_reason", "") or ""
                ),
                "final_no_tools_reasoning_content_chars": int(
                    getattr(
                        loop_result,
                        "final_no_tools_reasoning_content_chars",
                        0,
                    )
                    or 0
                ),
                "final_no_tools_used_accepted_proof": False,
            })
            increment_metric = getattr(session, "_increment_dossier_metric", None)
            if callable(increment_metric):
                increment_metric(
                    "mini_final_no_tools_no_proof_artifacts",
                    1,
                )
        if (
            provider_artifact_consumed
            and hasattr(conv, "_provider_call_quantum_state")
        ):
            # The lease belongs to a continuation until extraction proves the
            # response actually contains an artifact the outer action can
            # charge and adjudicate. Prose and malformed/no-artifact replies
            # retain the same lane's cumulative quota and wall accounting.
            delattr(conv, "_provider_call_quantum_state")

        # Build dossier-context helpers (legacy mini_prover.py:3756-3760).
        context_helpers = (
            list(assemble_route_helper_blocks)
            if assemble_route_goal_statement
            else (dossier.verified_helper_blocks() if dossier is not None else [])
        )

        # Common telemetry payload — every recorder.record_turn call in
        # the legacy run_conversation per-turn body (mini_prover.py:3535+)
        # carries phase / turn_in_phase / tool_calls_used / tool_call_log
        # / messages_sent / llm_response / llm_elapsed_s / extracted_*.
        # We assemble the shared subset here and merge per-event extras
        # at each emission site.
        same_target_decl_chunk_index = getattr(
            extraction,
            "same_target_decl_proof_chunk_index",
            -1,
        )
        try:
            same_target_decl_chunk_index = int(same_target_decl_chunk_index)
        except Exception:
            same_target_decl_chunk_index = -1
        common_payload: Dict[str, Any] = {
            "phase": conv.role,
            "turn_in_phase": phase_turn,
            "model": model_id,
            "tool_calls_used": loop_result.tool_calls_used,
            "tool_call_log": loop_result.tool_call_log,
            "messages_sent": loop_result.sent_messages,
            "llm_response": content,
            "llm_elapsed_s": loop_result.elapsed_s,
            "tool_state_updates": int(
                getattr(loop_result, "tool_state_updates", 0) or 0
            ),
            "tool_state_closures": int(
                getattr(loop_result, "tool_state_closures", 0) or 0
            ),
            "tool_state_update_statuses": list(
                getattr(loop_result, "tool_state_update_statuses", []) or []
            ),
            **compute_tool_metadata,
            "extracted_helpers": list(helpers),
            "extracted_proof": proof,
            "repair_submission_has_executable_lean": (
                repair_submission_has_executable_lean
            ),
            **temperature_metadata,
            **token_cap_metadata,
            **tool_progress_metadata,
        }
        if int(getattr(extraction, "demoted_main_chunks_dropped", 0) or 0) > 0:
            increment_metric = getattr(session, "_increment_dossier_metric", None)
            if callable(increment_metric):
                increment_metric(
                    "mini_extra_main_salvaged_last_main_checked",
                    int(extraction.demoted_main_chunks_dropped),
                )
            common_payload.update(
                {
                    "extra_main_salvaged_last_main_checked": int(
                        extraction.demoted_main_chunks_dropped
                    ),
                    "demoted_main_chunks_dropped": int(
                        extraction.demoted_main_chunks_dropped
                    ),
                }
            )
        redundant_redeclarations = list(
            getattr(extraction, "preamble_redeclarations_dropped", ()) or ()
        )
        if redundant_redeclarations:
            increment_metric = getattr(session, "_increment_dossier_metric", None)
            if callable(increment_metric):
                increment_metric(
                    "mini_preamble_redeclarations_dropped",
                    len(redundant_redeclarations),
                )
            common_payload.update(
                {
                    "preamble_redeclarations_dropped": redundant_redeclarations,
                }
            )
        if skeleton_tool_logs:
            common_payload.update(skeleton_route_metadata)
        if local_micro_theory_metadata:
            common_payload.update(local_micro_theory_metadata)
        if bool(getattr(extraction, "same_target_decl_proof_normalized", False)):
            common_payload.update({
                "same_target_decl_proof_normalized": True,
                "same_target_decl_proof_name": str(
                    getattr(extraction, "same_target_decl_proof_name", "") or ""
                ),
                "same_target_decl_proof_statement_match": bool(
                    getattr(
                        extraction,
                        "same_target_decl_proof_statement_match",
                        False,
                    )
                ),
                "same_target_decl_proof_name_match": bool(
                    getattr(
                        extraction,
                        "same_target_decl_proof_name_match",
                        False,
                    )
                ),
                "same_target_decl_proof_statement": str(
                    getattr(
                        extraction,
                        "same_target_decl_proof_statement",
                        "",
                    )
                    or ""
                ),
                "same_target_decl_proof_chunk_index": int(
                    same_target_decl_chunk_index
                ),
                "same_target_decl_proof_prefix_declaration_count": len(
                    list(
                        getattr(
                            extraction,
                            "same_target_decl_proof_prefix_declarations",
                            [],
                        )
                        or []
                    )
                ),
                "same_target_decl_proof_prefix_helper_names": [
                    helper_decl_name(block) or ""
                    for block in list(
                        getattr(
                            extraction,
                            "same_target_decl_proof_prefix_declarations",
                            [],
                        )
                        or []
                    )
                    if helper_decl_name(block)
                ],
            })
        if getattr(loop_result, "provider_protocol_event", ""):
            common_payload["provider_protocol_event"] = str(
                loop_result.provider_protocol_event or ""
            )
            common_payload["provider_protocol_original_response"] = str(
                getattr(loop_result, "provider_protocol_original_content", "") or ""
            )
        if bool(getattr(loop_result, "tool_repeat_detected", False)):
            common_payload.update({
                "tool_repeat_detected": True,
                "tool_repeat_action": str(
                    getattr(loop_result, "tool_repeat_action", "") or ""
                ),
                "tool_repeat_signature": str(
                    getattr(loop_result, "tool_repeat_signature", "") or ""
                ),
            })
        if proof_patch_metadata:
            common_payload.update(proof_patch_metadata)
        if bool(getattr(loop_result, "repair_self_check_required", False)):
            common_payload.update({
                **_repair_self_check_metadata(repair_self_check_policy_fields),
                "repair_self_check_required": True,
                "repair_self_check_attempted": repair_self_check_attempted,
                "repair_self_check_accepted": repair_self_check_accepted,
                "repair_self_check_status": repair_self_check_status,
                "repair_self_check_missing_kind": (
                    ""
                    if repair_self_check_status == "accepted_durable"
                    else repair_self_check_status
                ),
                **(
                    {
                        "repair_self_check_compliant": True,
                        "repair_self_check_evidence_source": (
                            "durable_prior_stub"
                        ),
                    }
                    if repair_self_check_status == "accepted_durable"
                    else {}
                ),
                "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                "repair_self_check_helper_only_allowed": (
                    repair_self_check_helper_only_allowed
                ),
            })
        if graph_native_prompt:
            common_payload["selected_graph_work"] = dict(
                getattr(session, "selected_work_item_record", {}) or {}
            )
        if formalization_helper_contract:
            common_payload["graph_native_formalization_contract"] = dict(
                formalization_helper_contract
            )
        if graph_native_goal_statement:
            common_payload["graph_native_goal_statement"] = graph_native_goal_statement
            common_payload["graph_native_target_node_id"] = graph_native_target.get("node_id")
            common_payload["graph_native_work_type"] = graph_native_target.get("work_type")
        if assemble_route_goal_statement:
            common_payload["assemble_route_goal_statement"] = assemble_route_goal_statement
            common_payload["assemble_route_authoring"] = True
            common_payload["assemble_route_contract_status"] = dict(
                assemble_route_contract_status
            )
            common_payload["assemble_route_helper_names"] = list(
                assemble_route_helper_names
            )
        llm_response_recorded = _emit_llm_response_record(
            session,
            common_payload,
            proof_present=proof is not None,
            helper_count=len(helpers),
            lemma_dag_candidate_count=len(lemma_dag_candidates),
        )
        common_payload["llm_response_recorded"] = llm_response_recorded

        # Accepted scratch work is mathematical evidence even when the final
        # response is later extracted under the positive-proof contract.  In
        # particular, ``example : ¬ target := by ...`` is otherwise reduced to
        # its bare body and Lean-checked *as a proof of target*, losing the exact
        # negative artifact.  Promote it at the shared authoritative boundary
        # before any positive policy/verification return path can consume it.
        authoritative_negation_target = str(
            graph_native_goal_statement
            or formalization_helper_contract.get("parent_statement")
            or active_root_extraction_goal
            or getattr(conv, "goal_statement", "")
            or ""
        ).strip()
        if authoritative_negation_target and dossier is not None:
            transcript_certification_results: list[Any] = []
            try:
                from ensemble_prover.mini_session.child_goal_falsification import (
                    record_authoritative_negation_from_transcript,
                )

                feedback_preamble, feedback_helpers = (
                    _accepted_negation_feedback_context(
                        conv,
                        tuple(context_helpers or ()),
                    )
                )
                (
                    transcript_falsified,
                    transcript_certificate_hash,
                    transcript_terminalized_aliases,
                ) = await record_authoritative_negation_from_transcript(
                    parent_session=session,
                    dossier=dossier,
                    target_statement=authoritative_negation_target,
                    conv=conv,
                    preamble=_accepted_negation_preamble(conv),
                    helper_blocks=tuple(context_helpers or ()),
                    feedback_preamble=feedback_preamble,
                    feedback_helper_blocks=feedback_helpers,
                    certification_results=transcript_certification_results,
                    engine="conversation_turn_accepted_try_lean",
                    reason="conversation_turn_exact_negation_artifact",
                    publication_guard=publication_guard,
                )
            except Exception:
                publication_guard()
                # The authority boundary persists the report before projecting
                # all graph/proof-state consequences.  A later projection
                # error must not let this turn continue down the positive-proof
                # path after the exact target has already become durably
                # invalidated.  Re-read typed dossier authority; never infer
                # falsity from the exception itself.
                try:
                    invalid_reason = dossier.invalidated_statement_reason(
                        authoritative_negation_target
                    )
                    target_environment_hash = str(
                        dossier.current_lean_environment_hash or ""
                    ).strip()
                    matching_authorities = [
                        authority
                        for authority in dict(
                            dossier.mini_authoritative_negations or {}
                        ).values()
                        if isinstance(authority, dict)
                        and str(authority.get("statement") or "").strip()
                        == authoritative_negation_target
                        and str(
                            authority.get("target_environment_hash") or ""
                        ).strip()
                        == target_environment_hash
                    ]
                    transcript_falsified = bool(
                        invalid_reason and matching_authorities
                    )
                    transcript_certificate_hash = str(
                        (matching_authorities[0] if matching_authorities else {}).get(
                            "certificate_hash"
                        )
                        or ""
                    ).strip()
                except Exception:
                    transcript_falsified = False
                    transcript_certificate_hash = ""
                transcript_terminalized_aliases = ()
            if _negation_certification_conflicted(
                dossier,
                transcript_certificate_hash,
            ):
                conflict_metadata = _proof_disproof_conflict_metadata(dossier)
                session.last_turn_extraction = None
                _emit_record(session, {
                    **common_payload,
                    **conflict_metadata,
                    "falsification_certificate_hash": (
                        transcript_certificate_hash
                    ),
                    "negative_evidence_source": "accepted_try_lean_transcript",
                    "verdict": "transcript_proof_disproof_conflict",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **_turn_budget_metadata(common_payload),
                        **conflict_metadata,
                        "falsification_certificate_hash": (
                            transcript_certificate_hash
                        ),
                        "lean_verdict": "proof_disproof_conflict",
                        "verdict": "transcript_proof_disproof_conflict",
                    },
                )
            transcript_retryable_result = next(
                (
                    result
                    for result in transcript_certification_results
                    if bool(getattr(result, "retryable", False))
                ),
                None,
            )
            if not transcript_falsified and transcript_retryable_result is not None:
                retry_reason = " ".join(
                    str(getattr(transcript_retryable_result, "reason", "") or "")
                    .split()
                )[:300]
                _emit_record(session, {
                    **common_payload,
                    "llm_failure_kind": (
                        "certify_counterexample_infrastructure_error"
                    ),
                    "llm_retryable": True,
                    "scoped_failure_reason": "llm_network_error",
                    "llm_failure_scope": "scoped",
                    "negative_evidence_source": "accepted_try_lean_transcript",
                    "retryable_infrastructure_reason": retry_reason,
                    "verdict": "transcript_negation_certification_deferred",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **_turn_budget_metadata(common_payload),
                        "llm_failure_kind": (
                            "certify_counterexample_infrastructure_error"
                        ),
                        "llm_retryable": True,
                        "terminal_failure": False,
                        "terminal_failure_reason": "",
                        "scoped_failure_reason": "llm_network_error",
                        "llm_failure_scope": "scoped",
                        "preserve_frontier_work": True,
                        "defer_selected_frontier_action": True,
                        "preserve_action_budget": True,
                        "refund_conversation_phase_turn": True,
                        "scheduler_neutral": True,
                        "stagnation_neutral": True,
                        "hard_pivot_neutral": True,
                        "retryable_infrastructure_reason": retry_reason,
                        "verdict": "transcript_negation_certification_deferred",
                    },
                )
            if transcript_falsified:
                effective_falsified_statement = authoritative_negation_target
                if active_root_disproof_certificate_is_valid(dossier):
                    root_certificate = dict(
                        getattr(dossier, "root_disproof_certificate", {}) or {}
                    )
                    root_certificate_hash = str(
                        root_certificate.get("certificate_hash") or ""
                    ).strip()
                    root_statement = str(
                        getattr(dossier, "root_statement", "") or ""
                    ).strip()
                    if root_certificate_hash and root_statement:
                        # The shared authority boundary may independently lift
                        # an accepted active-target negation through an exact
                        # answer shell. Publish that stronger typed result,
                        # rather than leaving the turn classified as a local
                        # helper falsification.
                        effective_falsified_statement = root_statement
                        transcript_certificate_hash = root_certificate_hash
                session.last_turn_extraction = None
                _emit_record(session, {
                    **common_payload,
                    "authoritative_falsification": True,
                    "falsified_statement": effective_falsified_statement,
                    "falsification_certificate_hash": (
                        transcript_certificate_hash
                    ),
                    "terminalized_proof_state_aliases": list(
                        transcript_terminalized_aliases
                    ),
                    "negative_evidence_source": "accepted_try_lean_transcript",
                    "rejection_reason": (
                        "positive submission bypassed; exact negation certified"
                    ),
                    "lean_error_type": "authoritative_exact_negation",
                    "verdict": "graph_native_target_authoritatively_falsified",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=True,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **_turn_budget_metadata(common_payload),
                        **skeleton_route_metadata,
                        "lean_verdict": "authoritative_target_falsified",
                        "authoritative_falsification": True,
                        "falsified_statement": effective_falsified_statement,
                        **_root_falsification_terminal_metadata(
                            session,
                            effective_falsified_statement,
                        ),
                        "falsification_certificate_hash": (
                            transcript_certificate_hash
                        ),
                        "terminalized_proof_state_aliases": list(
                            transcript_terminalized_aliases
                        ),
                        "negative_evidence_source": (
                            "accepted_try_lean_transcript"
                        ),
                        "graph_native_target_node_id": (
                            graph_native_target.get("node_id")
                        ),
                        "graph_native_work_type": graph_native_target.get(
                            "work_type"
                        ),
                        "selected_graph_work": dict(
                            getattr(
                                session,
                                "selected_work_item_record",
                                {},
                            )
                            or {}
                        ),
                        "rejection_reason": (
                            "positive submission bypassed; exact negation "
                            "certified"
                        ),
                        "strong_progress": True,
                    },
                )
        turn_giveup = _classify_turn_giveup(str(content or ""), proof, helpers)
        selected_ticket = getattr(session, "pending_repair_ticket", None)
        selected_ticket_id = str(
            getattr(session, "_repair_ticket_selected_id", "") or ""
        ).strip()
        selected_ticket_is_active = bool(
            selected_ticket is not None
            and selected_ticket_id
            and str(getattr(selected_ticket, "ticket_id", "") or "")
            == selected_ticket_id
        )
        selected_ticket_metadata = (
            dict(getattr(selected_ticket, "metadata", {}) or {})
            if selected_ticket_is_active
            else {}
        )
        unknown_identifier_for_api_search = str(
            selected_ticket_metadata.get("unknown_identifier") or ""
        ).strip()
        synthetic_unknown_analysis = {
            "error_type": "unknown_identifier",
            "details": {"unknown_identifier": unknown_identifier_for_api_search},
        }
        repair_requires_api_search = bool(
            unknown_identifier_for_api_search
            and needs_unknown_identifier_api_search(
                synthetic_unknown_analysis,
                parent_ticket=selected_ticket,
            )
        )
        exact_repair_submission_self_checked = False
        if repair_requires_api_search and repair_self_check_accepted:
            # The current turn's accepted try_lean code is direct evidence
            # that this exact submitted proof no longer uses the stale unknown
            # identifier.  Compare only accepted codes returned by this tool
            # loop: a different current probe plus an older durable matching
            # stub must not be mislabeled as current-turn evidence.  This
            # bypass grants no proof authority; the ordinary final Lean check
            # below still decides acceptance.
            exact_repair_submission_self_checked = (
                proof is not None
                and _policy_repair_self_check_matches_submission(
                    list(
                        getattr(loop_result, "repair_self_check_codes", [])
                        or []
                    ),
                    proof,
                    (),
                    exact_only=True,
                )
            )
            if exact_repair_submission_self_checked:
                common_payload[
                    "unknown_identifier_api_search_bypassed_by_exact_self_check"
                ] = True
                common_payload["repair_self_check_evidence_source"] = (
                    "current_turn_exact_accepted_code"
                )
        missing_recommended_api_grounding = bool(
            repair_requires_api_search
            and not exact_repair_submission_self_checked
            and not tool_log_has_api_grounding(
                loop_result.tool_call_log
            )
        )
        if missing_recommended_api_grounding:
            # API search remains useful repair guidance, but a complete proof
            # is governed by Lean. Never reject source text before the kernel
            # has had the opportunity to elaborate it.
            common_payload["unknown_identifier_api_search_advisory"] = True
        if (
            bool(getattr(loop_result, "repair_self_check_required", False))
            and turn_giveup is not None
            and proof is not None
            and (helpers or lemma_dag_candidates)
            and not independent_main_without_stub_helpers
        ):
            session.last_turn_extraction = None
            feedback = _format_turn_giveup_feedback(
                conv=conv,
                session=session,
                giveup=turn_giveup,
                turn=phase_turn,
                max_turns=max_turns_footer,
            )
            conv.append_user(feedback)
            _emit_record(session, {
                **common_payload,
                "rejection_reason": "giveup_policy_active_proof_redirect",
                "banked_proposed_helpers": [],
                "giveup_cluster": str(turn_giveup.get("cluster") or ""),
                "giveup_match": str(turn_giveup.get("match") or ""),
                "banking_suppressed_by_giveup": True,
                "verdict": "proof_policy_rejected",
            })
            cost = time.monotonic() - started
            repair_metadata = _repair_self_check_metadata(common_payload)
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=bool(skeleton_route_banked),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "rejection_reason": "giveup_policy_active_proof_redirect",
                    "verdict": "proof_policy_rejected",
                    "llm_response_recorded": llm_response_recorded,
                    "llm_response": content,
                    "giveup_cluster": str(turn_giveup.get("cluster") or ""),
                    "giveup_match": str(turn_giveup.get("match") or ""),
                    "banking_suppressed_by_giveup": True,
                    "strong_progress": False,
                    **skeleton_route_metadata,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    **repair_metadata,
                },
            )

        if turn_giveup is not None and independent_main_without_stub_helpers:
            common_payload.update(
                {
                    "giveup_advisory_main_proof_checked": True,
                    "ignored_unused_stub_helper_names": [
                        helper_decl_name(helper) or ""
                        for helper in submitted_stub_helpers
                    ],
                }
            )
            turn_giveup = None

        repair_self_check_codes: list[str] = []
        repair_context_lemmas: list[str] = []
        repair_has_accepted_evidence = False
        repair_self_check_mismatch = False
        repair_self_check_terminal_continuation = False
        repair_gate_error = ""
        try:
            from ensemble_prover.mini_prover import (
                _feedback_lemmas_for_answer_safe_recheck,
                _repair_self_check_has_accepted_evidence,
                _repair_self_check_has_terminal_continuation,
                _repair_self_check_matches_submission,
            )

            repair_self_check_codes = list(
                getattr(loop_result, "repair_self_check_codes", []) or []
            )
            repair_context_lemmas = (
                _feedback_lemmas_for_answer_safe_recheck(
                    dossier.verified_helper_blocks(),
                    conv,
                )
                if dossier is not None
                else []
            )
            repair_has_accepted_evidence = _repair_self_check_has_accepted_evidence(
                repair_self_check_codes,
                goal_statement=conv.goal_statement,
                preamble=conv.preamble,
                context_lemmas=repair_context_lemmas,
            )
            repair_self_check_mismatch = (
                bool(getattr(loop_result, "repair_self_check_required", False))
                and effective_try_lean_tool_enabled
                and proof is not None
                and repair_has_accepted_evidence
                and not _repair_self_check_matches_submission(
                    repair_self_check_codes,
                    proof,
                    (),
                    goal_statement=conv.goal_statement,
                    preamble=conv.preamble,
                    context_lemmas=repair_context_lemmas,
                )
            )
            if repair_self_check_mismatch:
                repair_self_check_terminal_continuation = (
                    _repair_self_check_has_terminal_continuation(
                        repair_self_check_codes,
                        proof,
                    )
                )
        except Exception as exc:
            repair_gate_error = f"{type(exc).__name__}: {exc}"
        if repair_self_check_mismatch:
            common_payload["repair_self_check_mismatch_observed"] = True
            if repair_self_check_terminal_continuation:
                common_payload["repair_self_check_terminal_continuation"] = True
            else:
                # A mismatch is useful telemetry, but the final answer-safe
                # Lean check below is the authority. Blocking here discards
                # valid repaired proofs whose final body differs from a
                # scratch probe. The terminal-continuation subset above is
                # different: it identifies an accepted closed proof body that
                # was pasted as a prefix and then extended with executable
                # tactics, so the exact final proof was never checked.
                repair_self_check_mismatch = False

        verdict = apply_policy_gates(
            extraction,
            conv=conv,
            content=content,
            context_helpers=context_helpers,
        )
        from ensemble_prover.mini_session.turn.policy import PolicyVerdictKind

        early_repair_policy_kinds = {
            PolicyVerdictKind.REJECT_HELPER_STUB_WITH_MAIN,
            PolicyVerdictKind.REJECT_POST_MAIN,
            PolicyVerdictKind.REJECT_EXTRA_MAIN,
            PolicyVerdictKind.REJECT_PREAMBLE_REDECLARATION,
        }
        repair_mismatch_preempts_policy = (
            repair_self_check_mismatch
            and not verdict.accept
            and verdict.kind not in early_repair_policy_kinds
        )
        policy_blocks_turn = (
            not verdict.accept
            and not repair_mismatch_preempts_policy
            and not (
                verdict.kind is PolicyVerdictKind.REJECT_HELPER_STUB_WITH_MAIN
                and independent_main_without_stub_helpers
            )
        )
        if (
            verdict.kind is PolicyVerdictKind.REJECT_HELPER_STUB_WITH_MAIN
            and independent_main_without_stub_helpers
        ):
            helpers = checkable_submission_helpers
            lemma_dag_candidates = [
                helper
                for helper in lemma_dag_candidates
                if not has_sorry_or_admit(helper)
            ]
            common_payload.update(
                {
                    "unused_stub_helpers_excluded_before_lean": True,
                    "ignored_unused_stub_helper_names": [
                        helper_decl_name(helper) or ""
                        for helper in submitted_stub_helpers
                    ],
                }
            )

        if (
            formalization_helper_contract
            and proof is not None
            and not policy_blocks_turn
        ):
            (
                same_target_formalization_candidate,
                same_target_prefix_blocks,
            ) = _same_target_decl_graph_formalization_candidate(
                extraction,
                theorem_name=theorem_name,
                goal_statement=extraction_goal_statement,
            )
            if same_target_formalization_candidate:
                session.last_turn_extraction = None
                prefix_names = [
                    helper_decl_name(block) or ""
                    for block in same_target_prefix_blocks
                    if helper_decl_name(block)
                ]
                increment = getattr(session, "_increment_dossier_metric", None)
                if callable(increment):
                    increment(
                        "mini_session_same_target_decl_proofs_graph_formalization_routed",
                        1,
                    )
                reroute_payload = {
                    **common_payload,
                    "same_target_decl_proof_graph_formalization_routed": True,
                    "same_target_decl_proof_candidate_name": (
                        helper_decl_name(same_target_formalization_candidate) or ""
                    ),
                    "same_target_decl_proof_statement": helper_decl_statement(
                        same_target_formalization_candidate
                    ),
                    "same_target_decl_proof_chunk_index": int(
                        same_target_decl_chunk_index
                    ),
                    "same_target_decl_proof_prefix_declaration_count": len(
                        same_target_prefix_blocks
                    ),
                    "same_target_decl_proof_prefix_helper_names": prefix_names,
                }
                _emit_record(session, {
                    **reroute_payload,
                    "verdict": "same_target_decl_proof_graph_formalization_routed",
                })
                routed_outcome = await _run_graph_native_formalization_helper_contract(
                    session=session,
                    action_id=self.id,
                    conv=conv,
                    lean=session.lean,
                    dossier=dossier,
                    contract=formalization_helper_contract,
                    helpers=[same_target_formalization_candidate],
                    lemma_dag_candidates=[],
                    context_helpers=context_helpers,
                    common_payload=reroute_payload,
                    phase_turn=phase_turn,
                    conv_turn_offset=conv_turn_offset,
                    absolute_turn=absolute_turn,
                    started=started,
                    seed_same_turn_prefix_blocks=same_target_prefix_blocks,
                    allow_prefix_scoped_candidate_statements=True,
                    publication_guard=publication_guard,
                )
                routed_metadata = dict(routed_outcome.metadata or {})
                dependency_names = list(
                    routed_metadata.get("same_turn_dependency_helper_names") or []
                )
                if callable(increment):
                    routed_verdict = str(
                        routed_metadata.get("lean_verdict") or ""
                    )
                    if routed_verdict == (
                        "graph_native_formalization_bridge_support_recorded"
                    ):
                        increment(
                            "mini_session_same_target_decl_proofs_graph_formalization_bridge_support_recorded",
                            1,
                        )
                    elif routed_verdict == (
                        "graph_native_formalization_duplicate_bridge_support_suppressed"
                    ):
                        pass
                    elif bool(routed_outcome.progress):
                        increment(
                            "mini_session_same_target_decl_proofs_graph_formalization_accepted",
                            1,
                        )
                    else:
                        increment(
                            "mini_session_same_target_decl_proofs_graph_formalization_rejected",
                            1,
                        )
                    if dependency_names:
                        increment(
                            "mini_session_same_target_decl_proofs_graph_formalization_dependencies_banked",
                            len(dependency_names),
                        )
                routed_metadata.update({
                    "same_target_decl_proof_graph_formalization_routed": True,
                    "same_target_decl_proof_candidate_name": (
                        helper_decl_name(same_target_formalization_candidate) or ""
                    ),
                    "same_target_decl_proof_prefix_helper_names": prefix_names,
                    "same_target_decl_proof_prefix_declaration_count": len(
                        same_target_prefix_blocks
                    ),
                    **_repair_self_check_metadata(common_payload),
                })
                return replace(routed_outcome, metadata=routed_metadata)
            (
                proof_turn_formalization_candidate,
                proof_turn_prefix_blocks,
            ) = _proof_turn_decl_graph_formalization_candidate(
                extraction,
                contract=formalization_helper_contract,
                proof_text=proof or "",
            )
            if proof_turn_formalization_candidate:
                session.last_turn_extraction = None
                prefix_names = [
                    helper_decl_name(block) or ""
                    for block in proof_turn_prefix_blocks
                    if helper_decl_name(block)
                ]
                increment = getattr(session, "_increment_dossier_metric", None)
                if callable(increment):
                    increment(
                        "mini_session_proof_turn_decl_graph_formalization_routed",
                        1,
                    )
                reroute_payload = {
                    **common_payload,
                    "proof_turn_decl_graph_formalization_routed": True,
                    "proof_turn_decl_proof_candidate_name": (
                        helper_decl_name(proof_turn_formalization_candidate) or ""
                    ),
                    "proof_turn_decl_proof_statement": helper_decl_statement(
                        proof_turn_formalization_candidate
                    ),
                    "proof_turn_decl_proof_prefix_declaration_count": len(
                        proof_turn_prefix_blocks
                    ),
                    "proof_turn_decl_proof_prefix_helper_names": prefix_names,
                }
                _emit_record(session, {
                    **reroute_payload,
                    "verdict": "proof_turn_decl_graph_formalization_routed",
                })
                routed_outcome = await _run_graph_native_formalization_helper_contract(
                    session=session,
                    action_id=self.id,
                    conv=conv,
                    lean=session.lean,
                    dossier=dossier,
                    contract=formalization_helper_contract,
                    helpers=[proof_turn_formalization_candidate],
                    lemma_dag_candidates=[],
                    context_helpers=context_helpers,
                    common_payload=reroute_payload,
                    phase_turn=phase_turn,
                    conv_turn_offset=conv_turn_offset,
                    absolute_turn=absolute_turn,
                    started=started,
                    seed_same_turn_prefix_blocks=proof_turn_prefix_blocks,
                    allow_prefix_scoped_candidate_statements=True,
                    publication_guard=publication_guard,
                )
                routed_metadata = dict(routed_outcome.metadata or {})
                dependency_names = list(
                    routed_metadata.get("same_turn_dependency_helper_names") or []
                )
                if callable(increment):
                    routed_verdict = str(
                        routed_metadata.get("lean_verdict") or ""
                    )
                    if routed_verdict == (
                        "graph_native_formalization_bridge_support_recorded"
                    ):
                        increment(
                            "mini_session_proof_turn_decl_graph_formalization_bridge_support_recorded",
                            1,
                        )
                    elif routed_verdict == (
                        "graph_native_formalization_duplicate_bridge_support_suppressed"
                    ):
                        pass
                    elif bool(routed_outcome.progress):
                        increment(
                            "mini_session_proof_turn_decl_graph_formalization_accepted",
                            1,
                        )
                    else:
                        increment(
                            "mini_session_proof_turn_decl_graph_formalization_rejected",
                            1,
                        )
                    if dependency_names:
                        increment(
                            "mini_session_proof_turn_decl_graph_formalization_dependencies_banked",
                            len(dependency_names),
                        )
                routed_metadata.update({
                    "proof_turn_decl_graph_formalization_routed": True,
                    "proof_turn_decl_proof_candidate_name": (
                        helper_decl_name(proof_turn_formalization_candidate) or ""
                    ),
                    "proof_turn_decl_proof_prefix_helper_names": prefix_names,
                    "proof_turn_decl_proof_prefix_declaration_count": len(
                        proof_turn_prefix_blocks
                    ),
                    **_repair_self_check_metadata(common_payload),
                })
                return replace(routed_outcome, metadata=routed_metadata)
            session.last_turn_extraction = None
            required_name = str(
                formalization_helper_contract.get("required_declaration_name")
                or formalization_helper_contract.get("name")
                or ""
            ).strip()
            shape_detail = (
                f" Submit `theorem {required_name} : ... := by ...` or "
                f"`lemma {required_name} : ... := by ...` as the final "
                "declaration."
                if required_name
                else " Submit a named `theorem` or `lemma` declaration as "
                "the final declaration."
            )
            feedback = _formalization_helper_feedback(
                "received a proof body, but this graph task does not yet have "
                "an executable target for a proof body. Anonymous `example` "
                "blocks and bare `by ...` proofs are not accepted here."
                + shape_detail
            )
            try:
                conv.append_user(feedback)
            except Exception:
                pass
            _emit_record(session, {
                **common_payload,
                "rejection_reason": "formalization_requires_declaration",
                "lean_error_type": "formalization_requires_declaration",
                "verdict": "proof_policy_rejected",
            })
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=bool(skeleton_route_banked),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "rejection_reason": "formalization_requires_declaration",
                    "lean_error_type": "formalization_requires_declaration",
                    "formalization_declaration_retry_required": True,
                    "graph_work_consumed_verdict": (
                        "formalization_declaration_retry_required"
                    ),
                    "graph_work_consumed_error_type": (
                        "formalization_requires_declaration"
                    ),
                    "graph_native_formalization_contract": dict(
                        formalization_helper_contract
                    ),
                    "llm_response": content,
                    "strong_progress": False,
                    **skeleton_route_metadata,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    **_repair_self_check_metadata(common_payload),
                },
            )

        # ---- Step 3: policy gates ------------------------------------
        if policy_blocks_turn:
            banked_policy_names: list[str] = []
            certified_policy_helper_names: list[str] = []
            visible_certified_policy_helper_names: list[str] = []
            certified_policy_helper_progress = False
            certified_policy_helper_strong_progress = False
            format_policy_redirect = False
            format_policy_retains_selected_ticket = False
            format_policy_redirect_key = ""
            format_policy_redirect_count = 0
            format_policy_repair_quota: Dict[str, Any] = {}
            format_policy_kind = verdict.kind in early_repair_policy_kinds
            if format_policy_kind and not turn_giveup:
                selected_scope = dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                )
                scope_identity = (
                    str(selected_scope.get("target_hash") or "").strip()
                    or str(selected_scope.get("node_id") or "").strip()
                    or str(graph_native_attempt_node_id or "").strip()
                    or text_hash(str(getattr(conv, "goal_statement", "") or ""))
                )
                format_policy_redirect_key = hashlib.sha256(
                    ("format_policy\n" + scope_identity).encode(
                        "utf-8", errors="replace"
                    )
                ).hexdigest()[:24]
                continuation_counts = getattr(
                    session,
                    "repair_self_check_continuation_counts",
                    None,
                )
                if not isinstance(continuation_counts, dict):
                    continuation_counts = {}
                    session.repair_self_check_continuation_counts = (
                        continuation_counts
                    )
                prior = int(
                    continuation_counts.get(format_policy_redirect_key, 0) or 0
                )
                format_policy_redirect_count = prior
                global_limit = max(
                    0,
                    int(
                        getattr(
                            session,
                            "policy_repair_redirect_global_limit",
                            4,
                        )
                        or 0
                    ),
                )
                global_used = int(
                    getattr(session, "_policy_repair_redirect_total_count", 0)
                    or 0
                )
                format_policy_redirect = prior < 1 and global_used < global_limit
                if format_policy_redirect:
                    format_policy_redirect_count = prior + 1
                    continuation_counts[format_policy_redirect_key] = (
                        format_policy_redirect_count
                    )
                    session._policy_repair_redirect_total_count = global_used + 1
                    session.repair_first_until_conversation_turn = max(
                        int(
                            getattr(
                                session,
                                "repair_first_until_conversation_turn",
                                0,
                            )
                            or 0
                        ),
                        int(absolute_turn or 0) + 1,
                    )
                    session.repair_first_reason = "post_policy_format_repair"
                    format_policy_retains_selected_ticket = bool(
                        repair_ticket_active
                    )
                    increment_metric = getattr(
                        session, "_increment_dossier_metric", None
                    )
                    if callable(increment_metric):
                        increment_metric(
                            "mini_format_policy_redirect_granted",
                            1,
                        )
                else:
                    increment_metric = getattr(
                        session, "_increment_dossier_metric", None
                    )
                    if callable(increment_metric):
                        increment_metric(
                            "mini_policy_rejection_final_turn_no_retry",
                            1,
                        )
                if (
                    _has_concrete_local_repair_target(
                        proof=proof,
                        helpers=helpers,
                        lemma_dag_candidate_helpers=lemma_dag_candidates,
                    )
                    and graph_native_attempt_node_id
                    and not str(
                        getattr(session, "_repair_ticket_selected_id", "") or ""
                    ).strip()
                ):
                    arm = getattr(session, "arm_local_repair_quota", None)
                    if callable(arm):
                        try:
                            format_policy_repair_quota = dict(
                                arm(
                                    action_id=self.id,
                                    reason="post_policy_format_repair",
                                    failure_signature=hashlib.sha256(
                                        (
                                            _rejection_reason_for(verdict)
                                            + "\n"
                                            + scope_identity
                                        ).encode("utf-8", errors="replace")
                                    ).hexdigest()[:24],
                                    requested_turns=1,
                                    selected_work_record=selected_scope,
                                )
                                or {}
                            )
                        except Exception:
                            format_policy_repair_quota = {
                                "armed": False,
                                "verdict": "arm_error",
                            }
                common_payload.update(
                    {
                        "policy_repair_redirect": format_policy_redirect,
                        "repair_redirect_reason": (
                            "post_policy_format_repair"
                            if format_policy_redirect
                            else ""
                        ),
                        "policy_repair_redirect_key": format_policy_redirect_key,
                        "policy_repair_redirect_count": (
                            format_policy_redirect_count
                        ),
                        "policy_repair_redirect_total_count": int(
                            getattr(
                                session,
                                "_policy_repair_redirect_total_count",
                                0,
                            )
                            or 0
                        ),
                        "policy_repair_redirect_global_limit": global_limit,
                        "local_repair_quota_armed": bool(
                            format_policy_repair_quota.get("armed")
                        ),
                        "local_repair_quota_verdict": str(
                            format_policy_repair_quota.get("verdict") or ""
                        ),
                        "policy_rejection_final_turn_no_retry": int(
                            not format_policy_redirect
                        ),
                        "non_consuming_repair_ticket_continuation": (
                            format_policy_retains_selected_ticket
                        ),
                    }
                )
            if (
                verdict.kind is PolicyVerdictKind.REJECT_FORBIDDEN_CMD
                and not turn_giveup
            ):
                try:
                    quarantine_result = await _salvage_policy_rejected_helpers(
                        verdict_kind=verdict.kind,
                        lean=session.lean,
                        dossier=dossier,
                        proof_state=proof_state,
                        helper_candidates=[*helpers, *lemma_dag_candidates],
                        preamble=str(
                            getattr(conv, "lean_preamble", "")
                            or getattr(conv, "preamble", "")
                            or ""
                        ),
                        answer_safe_preamble=str(
                            getattr(conv, "preamble", "") or ""
                        ),
                        root_statement=str(
                            getattr(dossier, "root_statement", "") or ""
                        ),
                        phase=f"{conv.role}:policy_quarantine",
                        turn_index=phase_turn,
                        timeout_s=self.proof_state_child_tactic_timeout_s,
                        session=session,
                    )
                    certified_policy_helper_names = list(
                        getattr(quarantine_result, "accepted", ()) or ()
                    )
                    context_visible_policy_helper_names = (
                        dossier.visible_accepted_helper_names(
                            certified_policy_helper_names
                        )
                        if dossier is not None
                        and hasattr(dossier, "visible_accepted_helper_names")
                        else list(certified_policy_helper_names)
                    )
                    certified_policy_helper_strong_progress = (
                        _strong_progress_for_accepted_helpers(
                            dossier, certified_policy_helper_names
                        )
                    )
                    certified_policy_helper_theory_progress = (
                        _theory_progress_for_accepted_helpers(
                            dossier, certified_policy_helper_names
                        )
                    )
                    certified_policy_helper_progress = bool(
                        certified_policy_helper_strong_progress
                        or certified_policy_helper_theory_progress
                    )
                    # ``helpers_added`` is itself a scheduler progress signal.
                    # Publish only helpers with graph impact or novel reusable
                    # theory; valid but vacuous diagnostics may remain in the
                    # dossier without extending a stagnant proof lane.
                    visible_certified_policy_helper_names = [
                        name
                        for name in context_visible_policy_helper_names
                        if _strong_progress_for_accepted_helpers(dossier, [name])
                        or _theory_progress_for_accepted_helpers(dossier, [name])
                    ]
                    if (
                        getattr(session, "proof_cache", None) is not None
                        and dossier is not None
                    ):
                        for helper_name in certified_policy_helper_names:
                            helper_record = dossier.verified_helpers.get(helper_name)
                            if helper_record is None:
                                continue
                            try:
                                store_verified_helper_for_dossier(
                                    session.proof_cache,
                                    helper_record.source,
                                    preamble=str(
                                        getattr(conv, "lean_preamble", "")
                                        or getattr(conv, "preamble", "")
                                        or ""
                                    ),
                                    dossier=dossier,
                                    phase=f"{conv.role}:policy_quarantine",
                                )
                            except Exception:
                                pass
                    common_payload.update(
                        {
                            "policy_quarantine_candidate_count": len(
                                dict.fromkeys(
                                    [*helpers, *lemma_dag_candidates]
                                )
                            ),
                            "policy_quarantine_accepted_helpers": list(
                                certified_policy_helper_names
                            ),
                            "policy_quarantine_rejected_helpers": list(
                                getattr(quarantine_result, "rejected", ()) or ()
                            ),
                            "policy_quarantine_skipped_helpers": list(
                                getattr(quarantine_result, "skipped", ()) or ()
                            ),
                        }
                    )
                except Exception as exc:
                    common_payload["policy_quarantine_error"] = (
                        f"{type(exc).__name__}: {exc}"
                    )
                    _emit_repair_gate_side_effect_error(
                        session,
                        common_payload,
                        operation="salvage_forbidden_policy_helpers",
                        exc=exc,
                    )
            # H4 fix (2026-05-08): the construction-collapse rejection
            # carries proof_state side effects in legacy
            # mini_prover.py:4154-4188 (record_construction_collapse +
            # sync_to_graph + recorder.record_turn(verdict=known_answer_no_construction_collapse)).
            # Restore them here so downstream scheduling sees the
            # collapse history.
            proof_state_update: Optional[Dict[str, Any]] = None
            if verdict.kind is PolicyVerdictKind.REJECT_CONSTRUCTION_COLLAPSE:
                if proof_state is not None:
                    try:
                        proof_state_update = proof_state.record_construction_collapse(
                            phase=conv.role,
                            turn_index=phase_turn,
                            reason=verdict.detail or "",
                            proof_preview=str(proof or ""),
                            response_preview=content,
                        )
                    except Exception:
                        proof_state_update = None
                    if dossier is not None:
                        sync_proof_state_to_graph(
                            proof_state,
                            dossier,
                            session=session,
                            phase="proof_state_construction_collapse",
                            turn_index=phase_turn,
                        )
                # H7 telemetry: known_answer_no_construction_collapse.
                check_lemmas_for_record = merge_context_helpers(
                    context_helpers, helpers
                ) if proof is not None else helpers
                # Round-5 fix: bank helpers from the construction-collapse
                # branch (the explicit verdict-kind path missed by the
                # umbrella `else`). Round-3 umbrella covered the other
                # verdict kinds; this one was still discarding.
                _banked_collapse: list[str] = []
                if not turn_giveup:
                    _banked_collapse = _bank_turn_sources_as_proposed(
                        dossier,
                        conv,
                        helpers,
                        phase=str(getattr(conv, "role", "prove") or "prove"),
                        turn_index=int(absolute_turn or 0),
                        fallback_helpers=lemma_dag_candidates,
                    )
                banked_policy_names = list(_banked_collapse)
                collapse_record: Dict[str, Any] = {
                    **common_payload,
                    "dossier_context_helpers": list(context_helpers)
                    if proof is not None
                    else [],
                    "replay_helpers": list(check_lemmas_for_record),
                    "collapse_reason": verdict.detail or "",
                    "collapse_match": verdict.match or "",
                    "proof_state_update": proof_state_update,
                    "banked_proposed_helpers": list(_banked_collapse),
                    "giveup_cluster": (
                        str(turn_giveup.get("cluster") or "")
                        if turn_giveup
                        else None
                    ),
                    "giveup_match": (
                        str(turn_giveup.get("match") or "") if turn_giveup else ""
                    ),
                    "banking_suppressed_by_giveup": bool(turn_giveup),
                    "verdict": "known_answer_no_construction_collapse",
                }
                if proof_state is not None:
                    try:
                        collapse_record["proof_state"] = proof_state.to_record()
                    except Exception:
                        pass
                _emit_record(session, collapse_record)
            else:
                # Other policy rejections — emit verdict=proof_policy_rejected
                # mirroring mini_prover.py:3593-3607, 3635-3649, 3669-3691,
                # 4104-4120, 4207-4222.
                # Round-3 fix: bank any helpers the LLM proposed in this
                # turn BEFORE rejecting. This umbrella branch is the
                # largest unbanked rejection path — covered forbidden
                # command / post-main-helper / extra-main /
                # helper-stub-with-main and silently discarded the
                # prover's decomposition signal on all of them.
                banked_umbrella_names: list[str] = []
                if (
                    not turn_giveup
                    and verdict.kind is not PolicyVerdictKind.REJECT_FORBIDDEN_CMD
                ):
                    banked_umbrella_names = _bank_turn_sources_as_proposed(
                        dossier,
                        conv,
                        helpers,
                        phase=str(getattr(conv, "role", "prove") or "prove"),
                        turn_index=int(absolute_turn or 0),
                        fallback_helpers=lemma_dag_candidates,
                    )
                banked_policy_names = list(banked_umbrella_names)
                _emit_record(session, {
                    **common_payload,
                    "rejection_reason": _rejection_reason_for(verdict),
                    "lean_error_type": _rejection_reason_for(verdict),
                    "rejection_match": verdict.match,
                    "banked_proposed_helpers": list(banked_umbrella_names),
                    "giveup_cluster": (
                        str(turn_giveup.get("cluster") or "")
                        if turn_giveup
                        else None
                    ),
                    "giveup_match": (
                        str(turn_giveup.get("match") or "") if turn_giveup else ""
                    ),
                    "banking_suppressed_by_giveup": bool(turn_giveup),
                    "verdict": (
                        "proof_policy_repair_redirect"
                        if format_policy_redirect
                        else "proof_policy_rejected"
                    ),
                })
            if graph_native_attempt_node_id:
                try:
                    from ensemble_prover.mini_prover import _record_repair_policy_attempt

                    _record_repair_policy_attempt(
                        dossier,
                        phase=conv.role,
                        turn_index=phase_turn,
                        proof=proof or content or "",
                        reason=_rejection_reason_for(verdict),
                        metadata={
                            **dict(graph_native_attempt_metadata or {}),
                            "rejection_match": verdict.match or "",
                            "rejection_detail": verdict.detail or "",
                            "policy_repair_redirect": format_policy_redirect,
                            "policy_repair_redirect_key": (
                                format_policy_redirect_key
                            ),
                        },
                        node_id=graph_native_attempt_node_id,
                        swallow=False,
                    )
                except Exception as exc:
                    _emit_repair_gate_side_effect_error(
                        session,
                        common_payload,
                        operation="record_graph_native_policy_attempt",
                        exc=exc,
                    )
            if turn_giveup:
                feedback = _format_turn_giveup_feedback(
                    conv=conv,
                    session=session,
                    giveup=turn_giveup,
                    turn=phase_turn,
                    max_turns=max_turns_footer,
                )
            else:
                feedback = _format_policy_rejection(
                    verdict,
                    helpers=helpers,
                    goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                    banked_names=list(banked_policy_names),
                )
            conv.append_user(feedback)
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=tuple(visible_certified_policy_helper_names),
                progress=bool(
                    visible_certified_policy_helper_names
                    or certified_policy_helper_progress
                    or skeleton_route_banked
                ),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "rejection_reason": (
                        _rejection_reason_for(verdict)
                        if verdict.kind is PolicyVerdictKind.REJECT_CONSTRUCTION_COLLAPSE
                        else verdict.kind.value
                    ),
                    **(
                        {"lean_error_type": _rejection_reason_for(verdict)}
                        if verdict.kind is PolicyVerdictKind.REJECT_CONSTRUCTION_COLLAPSE
                        else {}
                    ),
                    "rejection_match": verdict.match,
                    "banked_proposed_helpers": list(banked_policy_names),
                    "policy_quarantine_accepted_helpers": list(
                        certified_policy_helper_names
                    ),
                    "visible_helpers_added_count": len(
                        visible_certified_policy_helper_names
                    ),
                    "llm_response": content,
                    "giveup_cluster": (
                        str(turn_giveup.get("cluster") or "")
                        if turn_giveup
                        else None
                    ),
                    "giveup_match": (
                        str(turn_giveup.get("match") or "") if turn_giveup else ""
                    ),
                    "banking_suppressed_by_giveup": bool(turn_giveup),
                    "strong_progress": bool(
                        certified_policy_helper_strong_progress
                    ),
                    "policy_repair_redirect": format_policy_redirect,
                    "repair_redirect_reason": (
                        "post_policy_format_repair"
                        if format_policy_redirect
                        else ""
                    ),
                    "policy_repair_redirect_key": format_policy_redirect_key,
                    "policy_repair_redirect_count": format_policy_redirect_count,
                    "preserve_action_budget": format_policy_redirect,
                    "preserve_frontier_work": format_policy_redirect,
                    "stagnation_neutral": format_policy_redirect,
                    "hard_pivot_neutral": format_policy_redirect,
                    "refund_conversation_phase_turn": format_policy_redirect,
                    "refund_local_repair_quota": format_policy_redirect,
                    "non_consuming_repair_ticket_continuation": (
                        format_policy_retains_selected_ticket
                    ),
                    "local_repair_quota_armed": bool(
                        format_policy_repair_quota.get("armed")
                    ),
                    "local_repair_quota_verdict": str(
                        format_policy_repair_quota.get("verdict") or ""
                    ),
                    **skeleton_route_metadata,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    **_repair_self_check_metadata(common_payload),
                },
            )

        try:
            from ensemble_prover.mini_prover import (
                _format_reused_fragment_feedback,
                _format_self_check_mismatch_feedback,
                _format_self_check_terminal_continuation_feedback,
                _proof_reuses_rejected_fragments,
                _proof_repackages_transient_goal_target,
                _record_repair_policy_attempt,
                _rejected_fragments_from_latest_feedback,
            )

            reuse_scan_text = "\n\n".join([*helpers, proof or ""])
            reused_rejected_fragments = _proof_reuses_rejected_fragments(
                conv,
                reuse_scan_text,
            )
            # Narrow companion gate (2026-05-13 regression fix):
            # detects goal-as-sorry-helper repackaging without banning
            # the goal expression itself from honest proofs.
            repackaged_goal_targets = _proof_repackages_transient_goal_target(
                conv,
                reuse_scan_text,
            )
            # Channel-split (2026-05-13 round-2 fix): keep the two
            # lists separate so the strict-fragment feedback formatter
            # doesn't poison ``rejected_code_fragments`` on the next
            # turn with goal-target text.
        except Exception as exc:
            repair_self_check_mismatch = False
            reused_rejected_fragments = []
            repackaged_goal_targets = []
            repair_gate_error = f"{type(exc).__name__}: {exc}"
        if repair_gate_error:
            # Round-4 fix: bank helpers from ordinary rejected turns so the
            # prover's decomposition signal survives the gate failure. Do
            # not bank give-up helper stubs.
            if turn_giveup:
                _banked_gate_error = []
            else:
                _banked_gate_error = _bank_turn_sources_as_proposed(
                    dossier,
                    conv,
                    helpers,
                    phase=str(getattr(conv, "role", "prove") or "prove"),
                    turn_index=int(absolute_turn or 0),
                    fallback_helpers=lemma_dag_candidates,
                )
            _emit_record(session, {
                **common_payload,
                "rejection_reason": "repair_gate_error",
                "repair_gate_error": repair_gate_error,
                "lean_error_type": "repair_gate_error",
                "banked_proposed_helpers": list(_banked_gate_error),
                "giveup_cluster": (
                    str(turn_giveup.get("cluster") or "") if turn_giveup else None
                ),
                "giveup_match": (
                    str(turn_giveup.get("match") or "") if turn_giveup else ""
                ),
                "banking_suppressed_by_giveup": bool(turn_giveup),
                "verdict": "proof_policy_rejected",
            })
            try:
                from ensemble_prover.mini_prover import _record_repair_policy_attempt
                _record_repair_policy_attempt(
                    dossier,
                    phase=conv.role,
                    turn_index=phase_turn,
                    proof=proof or content or "",
                    reason="repair_gate_error",
                    metadata={
                        **dict(graph_native_attempt_metadata or {}),
                        "error": repair_gate_error,
                    },
                    node_id=graph_native_attempt_node_id or None,
                    swallow=False,
                )
            except Exception as exc:
                _emit_repair_gate_side_effect_error(
                    session,
                    common_payload,
                    operation="record_repair_policy_attempt",
                    exc=exc,
                )
            try:
                conv.append_user(
                    "[repair self-check required]\n"
                    "The repair verifier hit an internal guard error while "
                    "checking this Lean block, so the proof was rejected "
                    "closed instead of silently bypassing the repair gate. "
                    "Call `try_lean` on a revised block and resubmit."
                )
            except Exception as exc:
                _emit_repair_gate_side_effect_error(
                    session,
                    common_payload,
                    operation="append_repair_feedback",
                    exc=exc,
                )
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=bool(skeleton_route_banked),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "rejection_reason": "repair_gate_error",
                    "lean_error_type": "repair_gate_error",
                    "banked_proposed_helpers": list(_banked_gate_error),
                    **skeleton_route_metadata,
                    "strong_progress": False,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    **_repair_self_check_metadata(common_payload),
                },
            )
        if repair_self_check_mismatch:
            mismatch_reason = (
                "repair_self_check_terminal_continuation"
                if repair_self_check_terminal_continuation
                else "repair_self_check_mismatch"
            )
            mismatch_feedback = (
                _format_self_check_terminal_continuation_feedback()
                if repair_self_check_terminal_continuation
                else _format_self_check_mismatch_feedback()
            )
            if repair_self_check_terminal_continuation:
                increment = getattr(session, "_increment_dossier_metric", None)
                if callable(increment):
                    increment(
                        "mini_session_repair_self_check_terminal_continuation",
                        1,
                    )
            try:
                _record_repair_policy_attempt(
                    dossier,
                    phase=conv.role,
                    turn_index=phase_turn,
                    proof=proof or "",
                    reason=mismatch_reason,
                    metadata={
                        **dict(graph_native_attempt_metadata or {}),
                        "tool_calls_used": loop_result.tool_calls_used,
                        "repair_self_check_terminal_continuation": (
                            repair_self_check_terminal_continuation
                        ),
                    },
                    node_id=graph_native_attempt_node_id or None,
                    swallow=False,
                )
            except Exception as exc:
                _emit_repair_gate_side_effect_error(
                    session,
                    common_payload,
                    operation="record_repair_policy_attempt",
                    exc=exc,
                )
            # Round-4 fix: bank helpers from ordinary rejected turns so the
            # prover's decomposition signal survives the mismatch. Give-up
            # turns are excluded: those helper stubs describe the route the
            # model is avoiding, not a planner-ready subgoal.
            if turn_giveup:
                _banked_mismatch = []
            else:
                _banked_mismatch = _bank_turn_sources_as_proposed(
                    dossier,
                    conv,
                    helpers,
                    phase=str(getattr(conv, "role", "prove") or "prove"),
                    turn_index=int(absolute_turn or 0),
                    fallback_helpers=lemma_dag_candidates,
                )
            _emit_record(session, {
                **common_payload,
                "rejection_reason": mismatch_reason,
                "lean_error_type": mismatch_reason,
                "banked_proposed_helpers": list(_banked_mismatch),
                "giveup_cluster": (
                    str(turn_giveup.get("cluster") or "") if turn_giveup else None
                ),
                "giveup_match": (
                    str(turn_giveup.get("match") or "") if turn_giveup else ""
                ),
                "banking_suppressed_by_giveup": bool(turn_giveup),
                "verdict": "proof_policy_rejected",
            })
            try:
                conv.append_user(mismatch_feedback)
            except Exception as exc:
                _emit_repair_gate_side_effect_error(
                    session,
                    common_payload,
                    operation="append_repair_feedback",
                    exc=exc,
                )
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=bool(skeleton_route_banked),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "rejection_reason": mismatch_reason,
                    "lean_error_type": mismatch_reason,
                    "banked_proposed_helpers": list(_banked_mismatch),
                    "giveup_cluster": (
                        str(turn_giveup.get("cluster") or "") if turn_giveup else None
                    ),
                    "giveup_match": (
                        str(turn_giveup.get("match") or "") if turn_giveup else ""
                    ),
                    "banking_suppressed_by_giveup": bool(turn_giveup),
                    **skeleton_route_metadata,
                    "strong_progress": False,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    **_repair_self_check_metadata(common_payload),
                },
            )
        if reused_rejected_fragments or repackaged_goal_targets:
            # Bank proposed helpers BEFORE rejecting (Claim 1 banking
            # ordering fix): the no_proof_extracted path is unreachable
            # from here. Proposed helpers extracted in a policy-rejected
            # turn still encode the prover's decomposition signal.
            if turn_giveup:
                banked_proposed_helpers = []
            else:
                try:
                    from ensemble_prover.mini_prover import _bank_helpers_as_proposed

                    banked_proposed_helpers = _bank_helpers_as_proposed(
                        dossier,
                        helpers,
                        phase=str(getattr(conv, "role", "prove") or "prove"),
                        turn_index=int(absolute_turn or 0),
                        fallback_helpers=lemma_dag_candidates,
                        goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                        allow_helper_decomposition=bool(
                            getattr(conv, "allow_helper_decomposition", True)
                        ),
                    )
                except Exception:
                    banked_proposed_helpers = []
            # Route each channel to its own rejection reason and
            # feedback formatter. Mixing them re-poisoned the strict
            # channel on the next round-trip — adversarial-review
            # finding 2026-05-13 round-2.
            primary_reason = (
                "reused_rejected_lean_fragment"
                if reused_rejected_fragments
                else "transient_goal_target_sorry_helper"
            )
            policy_repair_redirect = False
            redirect_key = ""
            redirect_count = 0
            redirect_limit = max(
                0,
                int(getattr(session, "policy_repair_redirect_limit", 2) or 0),
            )
            redirect_global_limit = max(
                0,
                int(
                    getattr(
                        session,
                        "policy_repair_redirect_global_limit",
                        4,
                    )
                    or 0
                ),
            )
            redirect_total_count = int(
                getattr(session, "_policy_repair_redirect_total_count", 0) or 0
            )
            redirect_items = list(reused_rejected_fragments or repackaged_goal_targets)
            if redirect_items and not turn_giveup and redirect_limit > 0:
                selected = dict(getattr(session, "selected_work_item_record", {}) or {})
                selected_scope = (
                    str(selected.get("target_hash") or "").strip()
                    or str(selected.get("node_id") or "").strip()
                    or str(selected.get("work_type") or "").strip()
                )
                fragment_hash = hashlib.sha256(
                    "\n".join(str(f) for f in redirect_items).encode(
                        "utf-8",
                        errors="replace",
                    )
                ).hexdigest()[:16]
                redirect_key = ":".join(
                    part
                    for part in (primary_reason, selected_scope, fragment_hash)
                    if part
                )
                counts = getattr(session, "_policy_repair_redirect_counts", None)
                if not isinstance(counts, dict):
                    counts = {}
                redirect_count = int(counts.get(redirect_key, 0) or 0)
                policy_repair_redirect = (
                    redirect_count < redirect_limit
                    and redirect_total_count < redirect_global_limit
                )
                if policy_repair_redirect:
                    redirect_count += 1
                    redirect_total_count += 1
                    counts[redirect_key] = redirect_count
                    session._policy_repair_redirect_counts = counts
                    session._policy_repair_redirect_total_count = redirect_total_count
                    session.repair_first_until_conversation_turn = max(
                        int(
                            getattr(
                                session,
                                "repair_first_until_conversation_turn",
                                0,
                            )
                            or 0
                        ),
                        int(absolute_turn or 0) + 1,
                    )
                    session.repair_first_reason = primary_reason
            try:
                _record_repair_policy_attempt(
                    dossier,
                    phase=conv.role,
                    turn_index=phase_turn,
                    proof="\n\n".join([*helpers, proof or ""]),
                    reason=primary_reason,
                    metadata={
                        **dict(graph_native_attempt_metadata or {}),
                        "tool_calls_used": loop_result.tool_calls_used,
                        "rejection_fragments": list(reused_rejected_fragments),
                        "repackaged_goal_targets": list(repackaged_goal_targets),
                        "policy_repair_redirect": policy_repair_redirect,
                        "policy_repair_redirect_key": redirect_key,
                        "policy_repair_redirect_count": redirect_count,
                        "policy_repair_redirect_limit": redirect_limit,
                        "policy_repair_redirect_total_count": redirect_total_count,
                        "policy_repair_redirect_global_limit": redirect_global_limit,
                    },
                    node_id=graph_native_attempt_node_id or None,
                    swallow=False,
                )
            except Exception as exc:
                _emit_repair_gate_side_effect_error(
                    session,
                    common_payload,
                    operation="record_repair_policy_attempt",
                    exc=exc,
                )
            record_verdict = (
                "proof_policy_repair_redirect"
                if policy_repair_redirect
                else "proof_policy_rejected"
            )
            _emit_record(session, {
                **common_payload,
                "rejection_reason": primary_reason,
                "rejection_fragments": list(reused_rejected_fragments),
                "repackaged_goal_targets": list(repackaged_goal_targets),
                "lean_error_type": primary_reason,
                "policy_repair_redirect": policy_repair_redirect,
                "repair_redirect_reason": (
                    primary_reason if policy_repair_redirect else ""
                ),
                "policy_repair_redirect_key": redirect_key,
                "policy_repair_redirect_count": redirect_count,
                "policy_repair_redirect_limit": redirect_limit,
                "policy_repair_redirect_total_count": redirect_total_count,
                "policy_repair_redirect_global_limit": redirect_global_limit,
                "banked_proposed_helpers": list(banked_proposed_helpers),
                "giveup_cluster": (
                    str(turn_giveup.get("cluster") or "") if turn_giveup else None
                ),
                "giveup_match": (
                    str(turn_giveup.get("match") or "") if turn_giveup else ""
                ),
                "banking_suppressed_by_giveup": bool(turn_giveup),
                "verdict": record_verdict,
            })
            try:
                from ensemble_prover.mini_prover import (
                    _format_repackaged_goal_target_feedback,
                    _transient_goal_targets_from_latest_feedback,
                )
                if turn_giveup:
                    conv.append_user(
                        _format_turn_giveup_feedback(
                            conv=conv,
                            session=session,
                            giveup=turn_giveup,
                            turn=phase_turn,
                            max_turns=max_turns_footer,
                        )
                    )
                else:
                    if reused_rejected_fragments:
                        conv.append_user(
                            _format_reused_fragment_feedback(
                                reused_rejected_fragments,
                                _rejected_fragments_from_latest_feedback(conv),
                            ),
                            repair_payload={
                                "fragments": [
                                    *reused_rejected_fragments,
                                    *_rejected_fragments_from_latest_feedback(conv),
                                ],
                                "transient_goal_targets": [],
                            },
                        )
                    if repackaged_goal_targets:
                        conv.append_user(
                            _format_repackaged_goal_target_feedback(
                                repackaged_goal_targets,
                                _transient_goal_targets_from_latest_feedback(conv),
                            ),
                            repair_payload={
                                "fragments": [],
                                "transient_goal_targets": [
                                    *repackaged_goal_targets,
                                    *_transient_goal_targets_from_latest_feedback(conv),
                                ],
                            },
                        )
            except Exception as exc:
                _emit_repair_gate_side_effect_error(
                    session,
                    common_payload,
                    operation="append_repair_feedback",
                    exc=exc,
                )
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=bool(skeleton_route_banked),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "rejection_reason": primary_reason,
                    "rejection_fragments": list(reused_rejected_fragments),
                    "repackaged_goal_targets": list(repackaged_goal_targets),
                    "lean_error_type": primary_reason,
                    "policy_repair_redirect": policy_repair_redirect,
                    "repair_redirect_reason": (
                        primary_reason if policy_repair_redirect else ""
                    ),
                    "policy_repair_redirect_key": redirect_key,
                    "policy_repair_redirect_count": redirect_count,
                    "policy_repair_redirect_limit": redirect_limit,
                    "policy_repair_redirect_total_count": redirect_total_count,
                    "policy_repair_redirect_global_limit": redirect_global_limit,
                    "preserve_action_budget": policy_repair_redirect,
                    "preserve_frontier_work": policy_repair_redirect,
                    "stagnation_neutral": policy_repair_redirect,
                    "hard_pivot_neutral": policy_repair_redirect,
                    "refund_conversation_phase_turn": policy_repair_redirect,
                    "refund_local_repair_quota": policy_repair_redirect,
                    "banked_proposed_helpers": list(banked_proposed_helpers),
                    "giveup_cluster": (
                        str(turn_giveup.get("cluster") or "")
                        if turn_giveup
                        else None
                    ),
                    "giveup_match": (
                        str(turn_giveup.get("match") or "") if turn_giveup else ""
                    ),
                    "banking_suppressed_by_giveup": bool(turn_giveup),
                    **skeleton_route_metadata,
                    "strong_progress": False,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    **_repair_self_check_metadata(common_payload),
                },
            )

        # No proof to verify — the LLM emitted helpers only. Run the
        # full legacy helpers-only salvage cascade (H2 fix). The
        # cascade's 5 pathways are:
        #   (1) lemma-DAG decomposition (when has_open_decomposition_task)
        #   (2) post-decomp child-closure (may solve root)
        #   (3) HelperSalvager.salvage
        #   (4) salvaged-helper assembly (may solve root)
        #   (5) post-salvage child-closure (may solve root)
        #   (6) try_close_with_tactics — root tactic close (may solve root)
        #
        # Live-trace fix (2026-05-08): clear ``session.last_turn_extraction``
        # before returning. ``HelperOnlySalvageAction`` and
        # ``LemmaDagDecomposeAction`` consult this signal in their
        # ``is_applicable`` checks; with the cascade running inline, a
        # subsequent outer-loop dispatch would re-run the same salvage
        # work on stale data when conv_turn budget runs low.
        if proof is None:
            if formalization_helper_contract:
                session.last_turn_extraction = None
                return await _run_graph_native_formalization_helper_contract(
                    session=session,
                    action_id=self.id,
                    conv=conv,
                    lean=session.lean,
                    dossier=dossier,
                    contract=formalization_helper_contract,
                    helpers=helpers,
                    lemma_dag_candidates=lemma_dag_candidates,
                    context_helpers=context_helpers,
                    common_payload=common_payload,
                    phase_turn=phase_turn,
                    conv_turn_offset=conv_turn_offset,
                    absolute_turn=absolute_turn,
                    started=started,
                    publication_guard=publication_guard,
                )
            # A helper-only answer can still contain the only mathematically
            # useful artifact from this turn: a declaration of the exact
            # negation of the selected graph-native target.  It remains a
            # target mismatch (never bank it as a positive helper), but route
            # its proof body through authoritative falsification before the
            # generic helper-banking cascade can detach it from the target.
            graph_target_key = graph_statement_key(graph_native_goal_statement)
            negative_candidates = _formalization_helper_candidates(
                helpers,
                lemma_dag_candidates,
                require_executable_statement=True,
            )
            raw_local_declarations = [
                *list(helpers or ()),
                *list(lemma_dag_candidates or ()),
            ]
            replay_only_local_declarations = [
                str(block or "").strip()
                for block in raw_local_declarations
                if helper_decl_kind(block) in {"def", "abbrev", "instance"}
                and (helper_decl_name(block) or helper_decl_kind(block) == "instance")
                and helper_decl_body(block)
                and not has_sorry_or_admit(helper_decl_body(block))
            ]
            valid_local_declarations: List[str] = []
            seen_local_declarations: set[str] = set()
            bankable_local_set = set(negative_candidates)
            replay_only_local_set = set(replay_only_local_declarations)
            for raw_block in raw_local_declarations:
                block = str(raw_block or "").strip()
                if (
                    not block
                    or block in seen_local_declarations
                    or (
                        block not in bankable_local_set
                        and block not in replay_only_local_set
                    )
                ):
                    continue
                seen_local_declarations.add(block)
                valid_local_declarations.append(block)
            for negative_candidate in negative_candidates:
                negative_statement = helper_decl_statement(negative_candidate)
                if not (
                    graph_target_key
                    and graph_negated_statement_key(negative_statement)
                    == graph_target_key
                ):
                    continue
                from ensemble_prover.mini_session.child_goal_falsification import (
                    record_authoritative_negation_artifact,
                )

                # Lean declarations are ordered: the exact-negation theorem
                # may use only valid declarations which precede it.  Restrict
                # same-response context further to the transitive reference
                # closure, so an unrelated or broken later candidate cannot
                # erase already-checkable negative evidence.  Dossier-backed
                # context remains present independently below.
                try:
                    declaration_index = valid_local_declarations.index(
                        negative_candidate
                    )
                except ValueError:
                    declaration_index = -1
                local_dependencies = (
                    _same_turn_replay_dependency_blocks(
                        negative_candidate,
                        valid_local_declarations[:declaration_index],
                    )
                    if declaration_index >= 0
                    else []
                )
                authority_helpers = tuple(
                    [
                        *list(context_helpers or ()),
                        *local_dependencies,
                    ]
                )
                feedback_preamble, feedback_helpers = (
                    _accepted_negation_feedback_context(
                        conv,
                        authority_helpers,
                    )
                )
                try:
                    authoritative, certificate_hash, terminalized_aliases = (
                        await record_authoritative_negation_artifact(
                            parent_session=session,
                            dossier=dossier,
                            target_statement=graph_native_goal_statement,
                            negation_declarations=(negative_candidate,),
                            preamble=_accepted_negation_preamble(conv),
                            helper_blocks=authority_helpers,
                            feedback_preamble=feedback_preamble,
                            feedback_helper_blocks=feedback_helpers,
                            engine="graph_native_helper_only",
                            reason="graph_native_exact_negation_artifact",
                            publication_guard=publication_guard,
                        )
                    )
                except Exception:
                    publication_guard()
                    # Falsification infrastructure failure cannot change the
                    # ordinary helper-only mismatch/banking behavior.
                    continue
                if _negation_certification_conflicted(
                    dossier,
                    certificate_hash,
                ):
                    conflict_metadata = _proof_disproof_conflict_metadata(dossier)
                    session.last_turn_extraction = None
                    _emit_record(session, {
                        **common_payload,
                        **conflict_metadata,
                        "falsification_certificate_hash": certificate_hash,
                        "verdict": "graph_native_proof_disproof_conflict",
                    })
                    return MiniOutcome(
                        action_id=self.id,
                        solved=False,
                        proof=None,
                        helpers_added=(),
                        progress=False,
                        cost_seconds=time.monotonic() - started,
                        metadata={
                            "role": self.role,
                            "conv_turn_index_offset": conv_turn_offset,
                            "conv_turn_index_absolute": absolute_turn,
                            "conv_turn_index_phase": phase_turn,
                            **_turn_budget_metadata(common_payload),
                            **conflict_metadata,
                            "falsification_certificate_hash": certificate_hash,
                            "lean_verdict": "proof_disproof_conflict",
                            "verdict": "graph_native_proof_disproof_conflict",
                        },
                    )
                if not authoritative:
                    continue
                session.last_turn_extraction = None
                _emit_record(session, {
                    **common_payload,
                    "helper_statement": negative_statement,
                    "negative_evidence_helper": True,
                    "authoritative_falsification": True,
                    "falsified_statement": graph_native_goal_statement,
                    "falsification_certificate_hash": certificate_hash,
                    "terminalized_proof_state_aliases": list(
                        terminalized_aliases
                    ),
                    "rejection_reason": (
                        "declaration target mismatch; exact negation certified"
                    ),
                    "lean_error_type": "authoritative_exact_negation",
                    "verdict": "graph_native_target_authoritatively_falsified",
                })
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=True,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **_turn_budget_metadata(common_payload),
                        "lean_verdict": "authoritative_target_falsified",
                        "authoritative_falsification": True,
                        "falsified_statement": graph_native_goal_statement,
                        **_root_falsification_terminal_metadata(
                            session,
                            graph_native_goal_statement,
                        ),
                        "falsification_certificate_hash": certificate_hash,
                        "terminalized_proof_state_aliases": list(
                            terminalized_aliases
                        ),
                        "graph_native_target_node_id": graph_native_target.get(
                            "node_id"
                        ),
                        "graph_native_work_type": graph_native_target.get(
                            "work_type"
                        ),
                        "selected_graph_work": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                        "rejection_reason": (
                            "declaration target mismatch; exact negation certified"
                        ),
                        "verdict": (
                            "graph_native_target_authoritatively_falsified"
                        ),
                        "strong_progress": True,
                    },
                )
            try:
                no_proof_responses = list(
                    getattr(conv, "_no_proof_llm_responses", []) or []
                )
                no_proof_responses.append(content)
                setattr(conv, "_no_proof_llm_responses", no_proof_responses[-8:])
                setattr(conv, "_last_llm_content", content)
                if not str(getattr(conv, "_last_no_proof_llm_response", "") or ""):
                    setattr(conv, "_last_no_proof_llm_response", content)
            except Exception:
                pass
            no_proof_target_integrity = _no_proof_target_integrity_metadata(
                session=session,
                conv=conv,
                dossier=dossier,
                llm_output=content,
                selected_work_record=dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                ),
                target_statement=graph_native_goal_statement,
                role=self.role,
                turn=phase_turn,
                common_payload=common_payload,
            )
            recoverable_giveup_helpers = _extractable_helper_blocks_for_giveup_recovery(
                helpers,
                lemma_dag_candidates,
            )
            helper_decomposition_allowed = bool(
                getattr(conv, "allow_helper_decomposition", True)
            )
            if (
                turn_giveup
                and recoverable_giveup_helpers
                and helper_decomposition_allowed
            ):
                _mark_no_proof_giveup_extractable_helper_recovery(
                    session=session,
                    common_payload=common_payload,
                    turn_giveup=turn_giveup,
                    recoverable_giveup_helpers=recoverable_giveup_helpers,
                )
            elif turn_giveup and not recoverable_giveup_helpers:
                session.last_turn_extraction = None
                feedback = _format_turn_giveup_feedback(
                    conv=conv,
                    session=session,
                    giveup=turn_giveup,
                    turn=phase_turn,
                    max_turns=max_turns_footer,
                )
                conv.append_user(feedback)
                _emit_record(session, {
                    **common_payload,
                    "rejection_reason": "giveup_no_proof_active_proof_redirect",
                    "banked_proposed_helpers": [],
                    "giveup_cluster": str(turn_giveup.get("cluster") or ""),
                    "giveup_match": str(turn_giveup.get("match") or ""),
                    "banking_suppressed_by_giveup": True,
                    **no_proof_target_integrity,
                    "verdict": "no_proof_extracted",
                })
                cost = time.monotonic() - started
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=bool(skeleton_route_banked),
                    cost_seconds=cost,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **_turn_budget_metadata(common_payload),
                        "no_proof": True,
                        "rejection_reason": "giveup_no_proof_active_proof_redirect",
                        "verdict": "no_proof_extracted",
                        "llm_response_recorded": llm_response_recorded,
                        "llm_response": content,
                        "giveup_cluster": str(turn_giveup.get("cluster") or ""),
                        "giveup_match": str(turn_giveup.get("match") or ""),
                        "banking_suppressed_by_giveup": True,
                        **no_proof_target_integrity,
                        **skeleton_route_metadata,
                        "strong_progress": False,
                        "unverified_decomposition_created": bool(skeleton_route_banked),
                        "assembly_contracts_added": bool(skeleton_route_banked),
                        **_repair_self_check_metadata(common_payload),
                    },
                )
            if not helper_decomposition_allowed:
                recovered_contracts = _recovered_formalization_helper_contracts(
                    session,
                    helpers,
                    lemma_dag_candidates,
                    graph_native_goal_statement=graph_native_goal_statement,
                )
                for recovered_contract in recovered_contracts:
                    recovered_name = str(
                        recovered_contract.get("name")
                        or recovered_contract.get("recovered_from_helper_name")
                        or ""
                    ).strip()
                    recovered_helpers = [
                        helper
                        for helper in helpers
                        if (helper_decl_name(helper) or "") == recovered_name
                    ]
                    recovered_lemma_dag_candidates = [
                        helper
                        for helper in lemma_dag_candidates
                        if (helper_decl_name(helper) or "") == recovered_name
                    ]
                    if not recovered_helpers and not recovered_lemma_dag_candidates:
                        continue
                    _emit_record(session, {
                        **common_payload,
                        "graph_native_formalization_contract": dict(
                            recovered_contract
                        ),
                        "recovered_formalization_contract": True,
                        "recovered_from_helper_name": recovered_name,
                        "verdict": "graph_native_formalization_contract_recovered",
                    })
                    recovered_outcome = await _run_graph_native_formalization_helper_contract(
                        session=session,
                        action_id=self.id,
                        conv=conv,
                        lean=session.lean,
                        dossier=dossier,
                        contract=recovered_contract,
                        helpers=recovered_helpers,
                        lemma_dag_candidates=recovered_lemma_dag_candidates,
                        context_helpers=context_helpers,
                        common_payload={
                            **common_payload,
                            "graph_native_formalization_contract": dict(
                                recovered_contract
                            ),
                            "recovered_formalization_contract": True,
                            "recovered_from_helper_name": recovered_name,
                        },
                        phase_turn=phase_turn,
                        conv_turn_offset=conv_turn_offset,
                        absolute_turn=absolute_turn,
                        started=started,
                        publication_guard=publication_guard,
                    )
                    session.last_turn_extraction = None
                    if (
                        turn_giveup
                        and recoverable_giveup_helpers
                        and (
                            recovered_outcome.progress
                            or bool(recovered_outcome.helpers_added)
                        )
                    ):
                        _mark_no_proof_giveup_extractable_helper_recovery(
                            session=session,
                            common_payload=common_payload,
                            turn_giveup=turn_giveup,
                            recoverable_giveup_helpers=recoverable_giveup_helpers,
                        )
                        recovered_outcome = replace(
                            recovered_outcome,
                            metadata={
                                **dict(recovered_outcome.metadata or {}),
                                **_no_proof_giveup_recovery_metadata(
                                    common_payload
                                ),
                            },
                        )
                    return recovered_outcome
                materialized_support = (
                    await _try_materialize_proof_only_helper_support(
                        session=session,
                        action_id=self.id,
                        conv=conv,
                        lean=session.lean,
                        dossier=dossier,
                        helpers=helpers,
                        lemma_dag_candidates=lemma_dag_candidates,
                        context_helpers=context_helpers,
                        common_payload=common_payload,
                        phase_turn=phase_turn,
                        conv_turn_offset=conv_turn_offset,
                        absolute_turn=absolute_turn,
                        started=started,
                        publication_guard=publication_guard,
                    )
                )
                if materialized_support is not None:
                    session.last_turn_extraction = None
                    if (
                        turn_giveup
                        and recoverable_giveup_helpers
                        and (
                            materialized_support.progress
                            or bool(materialized_support.helpers_added)
                        )
                    ):
                        _mark_no_proof_giveup_extractable_helper_recovery(
                            session=session,
                            common_payload=common_payload,
                            turn_giveup=turn_giveup,
                            recoverable_giveup_helpers=recoverable_giveup_helpers,
                        )
                        materialized_support = replace(
                            materialized_support,
                            metadata={
                                **dict(materialized_support.metadata or {}),
                                **_no_proof_giveup_recovery_metadata(
                                    common_payload
                                ),
                            },
                        )
                    return materialized_support
                session.last_turn_extraction = None
                giveup_metadata = (
                    {
                        "giveup_cluster": str(turn_giveup.get("cluster") or ""),
                        "giveup_match": str(turn_giveup.get("match") or ""),
                        "banking_suppressed_by_giveup": True,
                    }
                    if turn_giveup
                    else {}
                )
                _emit_record(session, {
                    **common_payload,
                    **giveup_metadata,
                    "rejection_reason": (
                        "forced_final_no_artifact"
                        if forced_final_no_artifact
                        else "helper_decomposition_disabled"
                    ),
                    "banked_proposed_helpers": [],
                    **no_proof_target_integrity,
                    "verdict": "no_proof_extracted",
                })
                if forced_final_no_artifact:
                    conv.append_user(
                        "The semantic proof-tool budget ended this attempt, "
                        "and the required final response contained commentary "
                        "instead of an executable Lean artifact. Do not describe "
                        "a future tool call. On the next scheduled proof lane, "
                        "submit the proof itself as one fenced `lean` block."
                    )
                else:
                    conv.append_user(
                        "This scoped session is proof-only. Do not replace the "
                        "active target with helper declarations, sorry stubs, or "
                        "scheduler requests. Submit one executable proof attempt "
                        "for the displayed target; any helper declaration must be "
                        "fully proved and used in that same Lean block. Since "
                        "helper declarations are disabled here, manufacture local "
                        "theory inside the proof body using `have`/`suffices`; "
                        "every intermediate fact must be proved before use."
                    )
                cost = time.monotonic() - started
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=durable_checked_tool_helpers,
                    progress=bool(
                        skeleton_route_banked or durable_checked_tool_helpers
                    ),
                    cost_seconds=cost,
                    metadata={
                        "role": self.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **_turn_budget_metadata(common_payload),
                        "no_proof": True,
                        "rejection_reason": (
                            "forced_final_no_artifact"
                            if forced_final_no_artifact
                            else "helper_decomposition_disabled"
                        ),
                        "verdict": "no_proof_extracted",
                        "llm_response_recorded": llm_response_recorded,
                        "llm_response": content,
                        **_repair_self_check_metadata(common_payload),
                        **giveup_metadata,
                        **no_proof_target_integrity,
                        **skeleton_route_metadata,
                        **checked_bridge_metadata,
                        **durable_progress_replay_metadata,
                        "strong_progress": False,
                        "unverified_decomposition_created": bool(skeleton_route_banked),
                        "assembly_contracts_added": bool(skeleton_route_banked),
                    },
                )
            try:
                cascade_outcome = await _run_helpers_only_cascade(
                    session=session,
                    action=self,
                    conv=conv,
                    lean=session.lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    content=content,
                    helpers=helpers,
                    lemma_dag_candidate_helpers=lemma_dag_candidates,
                    common_payload=common_payload,
                    absolute_turn=absolute_turn,
                    phase_turn=phase_turn,
                    conv_turn_offset=conv_turn_offset,
                    started=started,
                )
            finally:
                # Mark the extraction as consumed so subactions don't
                # re-fire on stale data.
                session.last_turn_extraction = None
            if cascade_outcome is not None:
                return _with_llm_response_metadata(
                    session,
                    cascade_outcome,
                    recorded=llm_response_recorded,
                    phase=str(conv.role or self.role or ""),
                    turn_in_phase=phase_turn,
                    common_payload=common_payload,
                )
            # No cascade pathway solved AND the LLM emitted no proof —
            # H6 fix: emit verdict=no_proof_extracted and nudge the LLM.
            # Mirrors mini_prover.py:4051-4076.
            #
            # Bank the proposed helpers into the dossier so the
            # recursive planner can seed claims from the prover's own
            # decomposition signal instead of asking the LLM to
            # re-invent helpers it already named.
            banked_proposed_names: list[str] = []
            banked_proposed_names = _bank_turn_sources_as_proposed(
                dossier,
                conv,
                helpers,
                phase=str(getattr(conv, "role", "prove") or "prove"),
                turn_index=int(absolute_turn or 0),
                fallback_helpers=lemma_dag_candidates,
            )
            _emit_record(session, {
                **common_payload,
                "rejection_reason": "no_main_proof",
                "post_main_declarations": [],
                "banked_proposed_helpers": list(banked_proposed_names),
                **no_proof_target_integrity,
                "verdict": "no_proof_extracted",
            })
            try:
                no_proof_responses = list(
                    getattr(conv, "_no_proof_llm_responses", []) or []
                )
                no_proof_responses.append(content)
                setattr(conv, "_no_proof_llm_responses", no_proof_responses[-8:])
                setattr(conv, "_last_llm_content", content)
                if not str(getattr(conv, "_last_no_proof_llm_response", "") or ""):
                    setattr(conv, "_last_no_proof_llm_response", content)
            except Exception:
                pass
            try:
                from ensemble_prover.mini_prover import (
                    _format_no_proof_extracted_feedback,
                )

                conv.append_user(
                    _format_no_proof_extracted_feedback(
                        helpers=helpers,
                        lemma_dag_candidate_helpers=lemma_dag_candidates,
                        role=str(getattr(conv, "role", self.role) or self.role),
                        banked_names=banked_proposed_names,
                    )
                )
            except Exception:
                conv.append_user(
                    "I don't see a main proof in your reply. Submit one Lean "
                    "proof attempt for the active goal; any helper declarations "
                    "must be fully proved. Do not submit an unproved local "
                    "bridge as a placeholder. If the active goal will not "
                    "close, submit the smallest executable Lean attempt that "
                    "exposes the next failing local `have`/`suffices`; do not "
                    "switch to prose, lemma requests, or assembly commentary."
                )
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=durable_checked_tool_helpers,
                progress=bool(
                    skeleton_route_banked or durable_checked_tool_helpers
                ),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "no_proof": True,
                    "rejection_reason": "no_main_proof",
                    "verdict": "no_proof_extracted",
                    "banked_proposed_helpers": list(banked_proposed_names),
                    "giveup_suppressed_by_extractable_helpers": common_payload.get(
                        "giveup_suppressed_by_extractable_helpers"
                    ),
                    "extractable_helper_count_under_giveup": common_payload.get(
                        "extractable_helper_count_under_giveup"
                    ),
                    "extractable_helper_names_under_giveup": common_payload.get(
                        "extractable_helper_names_under_giveup"
                    ),
                    "llm_response_recorded": llm_response_recorded,
                    "llm_response": content,
                    **_repair_self_check_metadata(common_payload),
                    **no_proof_target_integrity,
                    **skeleton_route_metadata,
                    **checked_bridge_metadata,
                    **durable_progress_replay_metadata,
                    "strong_progress": False,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                },
            )

        correction_names = [
            name
            for helper in helpers
            if (name := helper_decl_name(helper))
            and (existing := dossier.verified_helpers.get(name)) is not None
            and verified_helper_surface_statement_changed(
                existing,
                SimpleNamespace(source=helper),
            )
        ] if dossier is not None and not assemble_route_goal_statement else []
        replay_fresh_helpers = [] if assemble_route_goal_statement else helpers
        if dossier is not None:
            correction_recheck = merge_helpers_for_correction_recheck(
                dossier,
                context_helpers,
                replay_fresh_helpers,
                correction_names,
            )
            check_lemmas = list(correction_recheck.check_lemmas)
            stale_dependents_by_correction = dict(
                correction_recheck.stale_dependents_by_correction
            )
            context_helpers = list(correction_recheck.context_helpers)
            lean_verification_helpers = list(
                correction_recheck.verification_helpers
            )
            correction_recheck_fallback_lemmas = (
                correction_recheck.fallback_check_lemmas
            )
            correction_recheck_fallback_context_helpers = (
                correction_recheck.fallback_context_helpers
            )
            correction_recheck_fallback_verification_helpers = (
                list(replay_fresh_helpers)
                if correction_recheck_fallback_lemmas is not None
                else None
            )
        else:
            check_lemmas = merge_context_helpers(
                context_helpers,
                replay_fresh_helpers,
            )
            stale_dependents_by_correction = {}
            lean_verification_helpers = list(replay_fresh_helpers)
            correction_recheck_fallback_lemmas = None
            correction_recheck_fallback_context_helpers = None
            correction_recheck_fallback_verification_helpers = None
        pending_verification_check_lemmas = answer_safe_pending.get(
            "verification_check_lemmas"
        )
        pending_verification_context_helpers = answer_safe_pending.get(
            "verification_context_helpers"
        )
        pending_verification_helpers = answer_safe_pending.get(
            "verification_helpers"
        )
        pending_fallback_check_lemmas = answer_safe_pending.get(
            "fallback_verification_check_lemmas"
        )
        pending_fallback_context_helpers = answer_safe_pending.get(
            "fallback_verification_context_helpers"
        )
        pending_fallback_verification_helpers = answer_safe_pending.get(
            "fallback_verification_helpers"
        )
        if (
            answer_safe_pending_replay
            and isinstance(pending_verification_check_lemmas, list)
            and isinstance(pending_verification_context_helpers, list)
            and isinstance(pending_verification_helpers, list)
        ):
            check_lemmas = list(pending_verification_check_lemmas)
            context_helpers = list(pending_verification_context_helpers)
            lean_verification_helpers = list(pending_verification_helpers)
            if (
                isinstance(pending_fallback_check_lemmas, list)
                and isinstance(pending_fallback_context_helpers, list)
                and isinstance(pending_fallback_verification_helpers, list)
            ):
                correction_recheck_fallback_lemmas = (
                    list(pending_fallback_check_lemmas)
                    if pending_fallback_check_lemmas
                    else None
                )
                correction_recheck_fallback_context_helpers = (
                    list(pending_fallback_context_helpers)
                    if pending_fallback_check_lemmas
                    else None
                )
                correction_recheck_fallback_verification_helpers = (
                    list(pending_fallback_verification_helpers)
                    if pending_fallback_check_lemmas
                    else None
                )
            else:
                pending_replay_is_fallback = bool(
                    correction_recheck_fallback_lemmas is not None
                    and correction_recheck_fallback_context_helpers is not None
                    and list(pending_verification_check_lemmas)
                    == list(correction_recheck_fallback_lemmas)
                    and list(pending_verification_context_helpers)
                    == list(correction_recheck_fallback_context_helpers)
                    and list(pending_verification_helpers)
                    == list(replay_fresh_helpers)
                )
                if pending_replay_is_fallback:
                    correction_recheck_fallback_lemmas = None
                    correction_recheck_fallback_context_helpers = None
                    correction_recheck_fallback_verification_helpers = None

        # H3 fix (2026-05-08): pre-Lean lemma-DAG decomposition runs
        # BEFORE the primary Lean check when the proof_state has open
        # decomposition work. Mirrors mini_prover.py:4264-4286. Without
        # it, beam search sees stale decomposition state during the
        # 30+s primary Lean check.
        if (
            not answer_safe_pending_replay
            and not turn_giveup
            and bool(getattr(conv, "allow_helper_decomposition", True))
        ):
            await _run_pre_lean_lemma_dag_decomposition(
                session=session,
                conv=conv,
                lean=session.lean,
                dossier=dossier,
                proof_state=proof_state,
                lemma_dag_candidate_helpers=lemma_dag_candidates,
                helpers=helpers,
                absolute_turn=absolute_turn,
                phase_turn=phase_turn,
                common_payload=common_payload,
                timeout_s=self.proof_state_child_tactic_timeout_s,
            )
        elif lemma_dag_candidates and not answer_safe_pending_replay:
            _emit_record(session, {
                **common_payload,
                "lemma_dag_candidate_count": len(lemma_dag_candidates),
                "giveup_cluster": (
                    str(turn_giveup.get("cluster") or "") if turn_giveup else None
                ),
                "giveup_match": str(turn_giveup.get("match") or "") if turn_giveup else "",
                "verdict": (
                    "pre_lean_lemma_dag_suppressed_by_giveup"
                    if turn_giveup
                    else "pre_lean_lemma_dag_suppressed_proof_only"
                ),
            })

        # Only now is the assistant reply a valid main-proof attempt worth
        # keeping in the conversation. Policy-rejected replies and helper-only
        # decomposition stubs are recorded in telemetry, but not replayed as
        # assistant history where they can anchor the next turn.
        conv.append_assistant(content)

        # ---- Step 4: Lean check (primary + answer-safe recheck) ------
        # H5 fix (2026-05-08): wrap verify_with_lean in try/except so
        # exceptions surface as ``verdict=lean_infra_error`` + a user
        # nudge instead of bubbling out as a generic action exception.
        # Legacy: mini_prover.py:4292-4328.
        lean_started = time.monotonic()
        lean_verdict = None
        lean_infra_error: Optional[str] = None
        answer_safe_primary_accepted = False
        active_root_targets: Sequence[Dict[str, Any]] = ()
        if not selected_goal_statement_override and dossier is not None:
            active_root_targets = framed_active_root_targets

        def answer_safe_recovery_window() -> tuple[float, float]:
            configured_timeout_s = max(
                float(
                    getattr(getattr(session.lean, "cfg", None), "timeout_s", 0.0)
                    or 0.0
                ),
                float(getattr(session.lean, "timeout_s", 0.0) or 0.0),
            )
            verifier_timeout_s = max(300.0, configured_timeout_s)
            wall_allowance_s = verifier_timeout_s
            governor_remaining_getter = getattr(
                session,
                "_run_governor_remaining_s",
                None,
            )
            governor_remaining = (
                governor_remaining_getter()
                if callable(governor_remaining_getter)
                else None
            )
            if governor_remaining is not None:
                wall_allowance_s = min(
                    wall_allowance_s,
                    max(0.0, float(governor_remaining or 0.0)),
                )
            return verifier_timeout_s, time.monotonic() + wall_allowance_s

        # Provider/tool generation and kernel verification are distinct
        # operations. A valid proof produced near the end of a configured
        # provider-turn lease must still receive the verifier's allowance,
        # bounded by the outer run governor. Pending answer-safe replay uses
        # the same verifier window.
        def recovered_finalizer_receipt_for_pending() -> Dict[str, Any]:
            retained = dict(
                answer_safe_pending.get("recovered_finalizer_receipt") or {}
            )
            if retained:
                return copy.deepcopy(retained)
            if not str(
                common_payload.get("recovered_finalizer_failure_kind") or ""
            ).strip():
                return {}
            return {
                key: copy.deepcopy(getattr(loop_result, key))
                for key in self._ANSWER_SAFE_RECHECK_RECEIPT_KEYS
            }

        def verifier_pending_state(
            *,
            primary_accepted: bool,
            recovery_attempts: int,
            recovered_receipt: Optional[Mapping[str, Any]] = None,
        ) -> Dict[str, Any]:
            state = {
                "active": True,
                "role": self.role,
                "content": content,
                "sent_messages": copy.deepcopy(
                    list(getattr(loop_result, "sent_messages", []) or [])
                ),
                "proof": proof,
                "goal_statement_override": selected_goal_statement_override,
                "primary_accepted": bool(primary_accepted),
                "execution_binding": copy.deepcopy(
                    current_answer_safe_execution_binding
                ),
                "selected_work_record": copy.deepcopy(selected_record),
                "conv_turn_offset": int(conv_turn_offset),
                "phase_turn": int(phase_turn),
                "turn_entry": copy.deepcopy(turn_entry_replay_snapshot),
                "recovery_attempts": max(0, int(recovery_attempts or 0)),
                "verification_check_lemmas": copy.deepcopy(
                    list(check_lemmas)
                ),
                "verification_context_helpers": copy.deepcopy(
                    list(context_helpers)
                ),
                "verification_helpers": copy.deepcopy(
                    list(lean_verification_helpers)
                ),
                "fallback_verification_check_lemmas": copy.deepcopy(
                    list(correction_recheck_fallback_lemmas or [])
                ),
                "fallback_verification_context_helpers": copy.deepcopy(
                    list(correction_recheck_fallback_context_helpers or [])
                ),
                "fallback_verification_helpers": copy.deepcopy(
                    list(
                        correction_recheck_fallback_verification_helpers or []
                    )
                ),
            }
            if recovered_receipt:
                state["recovered_finalizer_receipt"] = copy.deepcopy(
                    dict(recovered_receipt)
                )
            return state

        verifier_pending_owned = bool(answer_safe_pending_replay)
        exact_verification_replay_active = bool(
            verifier_pending_owned
            or correction_recheck_fallback_lemmas is not None
        )
        recovered_finalizer_kind = str(
            common_payload.get("recovered_finalizer_failure_kind") or ""
        ).strip()

        async def call_current_verifier(
            *,
            timeout_s: float,
            deadline: float,
        ) -> Any:
            return await verify_with_lean(
                conv=conv,
                lean=session.lean,
                proof=proof,
                helpers=lean_verification_helpers,
                context_helpers=context_helpers,
                check_lemmas=check_lemmas,
                goal_statement_override=selected_goal_statement_override,
                active_root_targets=active_root_targets,
                deadline_monotonic=deadline,
                verifier_timeout_override_s=timeout_s,
            )

        def publish_current_verifier_pending(
            *,
            primary_accepted: bool,
            recovery_attempts: int,
        ) -> Dict[str, Any]:
            nonlocal verifier_pending_owned
            pending_state = verifier_pending_state(
                primary_accepted=primary_accepted,
                recovery_attempts=recovery_attempts,
                recovered_receipt=recovered_finalizer_receipt_for_pending(),
            )
            self._answer_safe_recheck_pending = copy.deepcopy(pending_state)
            setattr(
                session,
                "answer_safe_recheck_pending",
                copy.deepcopy(pending_state),
            )
            verifier_pending_owned = True
            return pending_state

        def clear_current_verifier_pending() -> None:
            nonlocal verifier_pending_owned
            setattr(session, "answer_safe_recheck_pending", None)
            self._answer_safe_recheck_pending = {}
            answer_safe_pending.clear()
            verifier_pending_owned = False

        async def settle_current_verification(
            *,
            timeout_s: float,
            deadline: float,
        ) -> tuple[Any, Optional[str], bool, bool]:
            """Settle one exact verifier variant with one verifier-only retry."""

            base_attempts = int(
                (
                    self._answer_safe_recheck_pending
                    or answer_safe_pending
                    or {}
                ).get("recovery_attempts", 0)
                or 0
            )
            try:
                verdict = await call_current_verifier(
                    timeout_s=timeout_s,
                    deadline=deadline,
                )
            except AnswerSafeRecheckInfrastructureError as exc:
                pending_state = publish_current_verifier_pending(
                    primary_accepted=bool(exc.primary_accepted),
                    recovery_attempts=base_attempts,
                )
                retry_timeout_s, retry_deadline = answer_safe_recovery_window()
                try:
                    verdict = await call_current_verifier(
                        timeout_s=retry_timeout_s,
                        deadline=retry_deadline,
                    )
                except Exception as retry_exc:
                    retry_primary_accepted = bool(
                        exc.primary_accepted
                        or getattr(retry_exc, "primary_accepted", False)
                    )
                    pending_state["primary_accepted"] = retry_primary_accepted
                    pending_state["recovery_attempts"] = base_attempts + 1
                    self._answer_safe_recheck_pending = copy.deepcopy(
                        pending_state
                    )
                    setattr(
                        session,
                        "answer_safe_recheck_pending",
                        copy.deepcopy(pending_state),
                    )
                    return (
                        None,
                        f"{type(retry_exc).__name__}: {retry_exc}",
                        True,
                        retry_primary_accepted,
                    )
                common_payload["answer_safe_recheck_verifier_only_retry"] = True
                common_payload["answer_safe_recheck_retry_attempts"] = (
                    base_attempts + 1
                )
                common_payload["answer_safe_recheck_retry_timeout_s"] = round(
                    retry_timeout_s,
                    3,
                )
                clear_current_verifier_pending()
                return verdict, None, False, False
            except Exception as exc:
                prior_primary_accepted = bool(
                    (
                        self._answer_safe_recheck_pending
                        or answer_safe_pending
                        or {}
                    ).get("primary_accepted", False)
                )
                primary_accepted = bool(
                    prior_primary_accepted
                    or getattr(exc, "primary_accepted", False)
                )
                should_persist = bool(
                    verifier_pending_owned
                    or exact_verification_replay_active
                    or recovered_finalizer_kind
                )
                if recovered_finalizer_kind:
                    common_payload[
                        "recovered_finalizer_candidate_adjudication_pending"
                    ] = True
                if should_persist:
                    publish_current_verifier_pending(
                        primary_accepted=primary_accepted,
                        recovery_attempts=base_attempts,
                    )
                return (
                    None,
                    f"{type(exc).__name__}: {exc}",
                    should_persist,
                    primary_accepted,
                )
            if verifier_pending_owned:
                common_payload["answer_safe_recheck_verifier_only_retry"] = True
                common_payload["answer_safe_recheck_retry_attempts"] = max(
                    1,
                    base_attempts + 1,
                )
                common_payload["answer_safe_recheck_retry_timeout_s"] = round(
                    float(timeout_s or 300.0),
                    3,
                )
                clear_current_verifier_pending()
            return verdict, None, False, False

        recovery_timeout_s, recovery_deadline = answer_safe_recovery_window()
        if answer_safe_pending_replay:
            common_payload["answer_safe_recheck_verifier_only_retry"] = True
            common_payload["answer_safe_recheck_retry_attempts"] = max(
                1,
                int(answer_safe_pending.get("recovery_attempts", 0) or 0) + 1,
            )
            common_payload["answer_safe_recheck_retry_timeout_s"] = round(
                float(recovery_timeout_s or 300.0),
                3,
            )
        (
            lean_verdict,
            lean_infra_error,
            answer_safe_recheck_infra,
            answer_safe_primary_accepted,
        ) = await settle_current_verification(
            timeout_s=recovery_timeout_s,
            deadline=recovery_deadline,
        )
        if (
            lean_infra_error is None
            and lean_verdict is not None
            and not bool(lean_verdict.accepted)
            and correction_recheck_fallback_lemmas is not None
            and correction_recheck_fallback_context_helpers is not None
            and correction_recheck_fallback_verification_helpers is not None
        ):
            check_lemmas = list(correction_recheck_fallback_lemmas)
            context_helpers = list(
                correction_recheck_fallback_context_helpers
            )
            lean_verification_helpers = list(
                correction_recheck_fallback_verification_helpers
            )
            correction_recheck_fallback_lemmas = None
            correction_recheck_fallback_context_helpers = None
            correction_recheck_fallback_verification_helpers = None
            exact_verification_replay_active = True
            fallback_timeout_s, fallback_deadline = (
                answer_safe_recovery_window()
            )
            (
                lean_verdict,
                lean_infra_error,
                answer_safe_recheck_infra,
                answer_safe_primary_accepted,
            ) = await settle_current_verification(
                timeout_s=fallback_timeout_s,
                deadline=fallback_deadline,
            )
        lean_elapsed = round(time.monotonic() - lean_started, 3)

        if lean_infra_error is not None:
            # M9 fix (2026-05-08): dedupe consecutive infra errors. The
            # first occurrence appends a nudge; if the IMMEDIATELY-PRIOR
            # error was identical, suppress the nudge text so conv.history
            # doesn't accumulate duplicate "infrastructure error" lines
            # turn after turn. The session's
            # ``consecutive_lean_infra_errors`` counter trips a durable timed
            # scheduler defer once it reaches the cap. Infrastructure cannot
            # establish mathematical exhaustion or terminate Mini.
            prev_error = getattr(session, "last_lean_infra_error", None)
            consecutive = int(getattr(session, "consecutive_lean_infra_errors", 0) or 0)
            same_as_prev = bool(prev_error == lean_infra_error)
            consecutive = consecutive + 1
            session.last_lean_infra_error = lean_infra_error
            session.consecutive_lean_infra_errors = consecutive
            cap = int(getattr(session, "max_consecutive_lean_infra_errors", 3) or 3)
            retry_deferred = consecutive >= cap
            verdict_name = "lean_infra_error"
            # Round-5 fix: bank helpers from ordinary rejected turns even
            # when Lean's infra fails. Give-up/off-ramp helper stubs are
            # still suppressed: infra flakiness must not turn "missing
            # bridge" prose into durable decomposition work.
            if turn_giveup:
                _banked_infra = []
            else:
                _banked_infra = _bank_turn_sources_as_proposed(
                    dossier,
                    conv,
                    helpers,
                    phase=str(getattr(conv, "role", "prove") or "prove"),
                    turn_index=int(absolute_turn or 0),
                    fallback_helpers=lemma_dag_candidates,
                )
            _emit_record(session, {
                **common_payload,
                "dossier_context_helpers": list(context_helpers),
                "replay_helpers": list(check_lemmas),
                "lean_error": lean_infra_error,
                "lean_elapsed_s": lean_elapsed,
                "consecutive_infra_errors": consecutive,
                "duplicate_of_prior": same_as_prev,
                "banked_proposed_helpers": list(_banked_infra),
                "answer_safe_recheck_infrastructure": bool(
                    answer_safe_recheck_infra
                ),
                "primary_lean_check_accepted": bool(
                    answer_safe_primary_accepted
                ),
                "giveup_cluster": (
                    str(turn_giveup.get("cluster") or "") if turn_giveup else None
                ),
                "giveup_match": (
                    str(turn_giveup.get("match") or "") if turn_giveup else ""
                ),
                "banking_suppressed_by_giveup": bool(turn_giveup),
                "verdict": verdict_name,
            })
            if turn_giveup:
                try:
                    from ensemble_prover.mini_prover import _drop_last_assistant_if_content

                    _drop_last_assistant_if_content(conv, content)
                except Exception:
                    pass
            if retry_deferred:
                conv.append_user(
                    f"Lean infrastructure has failed {consecutive} times "
                    "in a row. This verifier lane is paused with bounded "
                    "backoff while other proof work remains available."
                )
            elif (
                answer_safe_recheck_infra
                and answer_safe_primary_accepted
                and not same_as_prev
            ):
                conv.append_user(
                    "Lean's primary check accepted this exact proof, but the "
                    "required answer-safe recheck could not run because of a "
                    "verifier infrastructure failure. Retry the identical "
                    "proof/check; do not change the mathematical approach "
                    "solely because of this infrastructure error."
                )
            elif turn_giveup:
                conv.append_user(
                    _format_turn_giveup_feedback(
                        conv=conv,
                        session=session,
                        giveup=turn_giveup,
                        turn=phase_turn,
                        max_turns=max_turns_footer,
                    )
                )
            elif not same_as_prev:
                conv.append_user(
                    f"Lean infrastructure error: {lean_infra_error}\n\n"
                    "Try a different approach."
                )
            session.last_turn_extraction = None
            session.last_lean_verdict = None
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=bool(skeleton_route_banked),
                cost_seconds=cost,
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "lean_infra_error": lean_infra_error,
                    "lean_verdict": verdict_name,
                    "lean_error_type": "infra_error",
                    "lean_elapsed_s": lean_elapsed,
                    "consecutive_infra_errors": consecutive,
                    "banked_proposed_helpers": list(_banked_infra),
                    "answer_safe_recheck_infrastructure": bool(
                        answer_safe_recheck_infra
                    ),
                    "primary_lean_check_accepted": bool(
                        answer_safe_primary_accepted
                    ),
                    "answer_safe_recheck_pending": bool(
                        answer_safe_recheck_infra
                        and self._answer_safe_recheck_pending
                    ),
                    "answer_safe_recheck_verifier_only_retry": bool(
                        common_payload.get(
                            "answer_safe_recheck_verifier_only_retry"
                        )
                    ),
                    "answer_safe_recheck_retry_attempts": int(
                        common_payload.get(
                            "answer_safe_recheck_retry_attempts",
                            0,
                        )
                        or 0
                    ),
                    "answer_safe_recheck_retry_timeout_s": common_payload.get(
                        "answer_safe_recheck_retry_timeout_s"
                    ),
                    "llm_response_recorded": common_payload.get(
                        "llm_response_recorded"
                    ),
                    "verdict": verdict_name,
                    "giveup_cluster": (
                        str(turn_giveup.get("cluster") or "")
                        if turn_giveup
                        else None
                    ),
                    "giveup_match": (
                        str(turn_giveup.get("match") or "") if turn_giveup else ""
                    ),
                    "banking_suppressed_by_giveup": bool(turn_giveup),
                    **skeleton_route_metadata,
                    "strong_progress": False,
                    "unverified_decomposition_created": bool(skeleton_route_banked),
                    "assembly_contracts_added": bool(skeleton_route_banked),
                    "preserve_action_budget": bool(
                        answer_safe_recheck_infra
                    ),
                    "preserve_frontier_work": bool(
                        answer_safe_recheck_infra or retry_deferred
                    ),
                    "llm_failure_kind": (
                        "lean_verifier_infrastructure_unavailable"
                        if retry_deferred
                        else ""
                    ),
                    "llm_retryable": bool(retry_deferred),
                    "llm_failure_scope": "scoped" if retry_deferred else "",
                    "scoped_failure_reason": (
                        "lean_verifier_infrastructure_unavailable"
                        if retry_deferred
                        else ""
                    ),
                    # Before the cap, an already-paid answer-safe replay may
                    # retry immediately. At the cap, every verifier lane gets
                    # a timed scheduler defer so a persistent outage cannot
                    # hot-loop or starve alternate proof actions.
                    "defer_selected_frontier_action": bool(retry_deferred),
                    "scheduler_neutral": bool(
                        answer_safe_recheck_infra or retry_deferred
                    ),
                    "iteration_neutral": bool(
                        answer_safe_recheck_infra or retry_deferred
                    ),
                    "stagnation_neutral": bool(
                        answer_safe_recheck_infra or retry_deferred
                    ),
                    "hard_pivot_neutral": bool(
                        answer_safe_recheck_infra or retry_deferred
                    ),
                    "refund_conversation_phase_turn": bool(
                        answer_safe_recheck_infra
                    ),
                    **_repair_self_check_metadata(common_payload),
                },
            )

        assert lean_verdict is not None  # noqa: S101 — exhaustive case handling
        # M9 fix: a successful Lean check (returned a verdict at all,
        # accepted or rejected) means the runtime is healthy. Reset the
        # consecutive infra-error counter so a future intermittent
        # failure doesn't immediately trip the termination cap.
        session.consecutive_lean_infra_errors = 0
        session.last_lean_infra_error = None
        # M4 wiring: publish the verdict for the inline post-failure cascade
        # and direct replay wrappers. Normal scheduler registration has a
        # single owner and does not dispatch PostLeanFailureAction separately.
        session.last_lean_verdict = lean_verdict

        if lean_verdict.accepted:
            if str(
                common_payload.get("recovered_finalizer_failure_kind") or ""
            ).strip():
                common_payload["recovered_finalizer_candidate_lean_accepted"] = True
            accepted_proof = getattr(lean_verdict, "accepted_proof", None)
            accepted_source = str(getattr(lean_verdict, "primary_source", "") or "")
            if (
                isinstance(accepted_proof, str)
                and accepted_proof.strip()
                and accepted_proof != proof
            ):
                proof = accepted_proof
                common_payload["accepted_proof"] = proof
                common_payload["accepted_proof_source"] = accepted_source
            # Record helper side effects here; root finalization itself is
            # centralized in MiniSession.apply().
            helpers_added: List[str] = []
            helper_names = [
                helper_decl_name(b) or "" for b in check_lemmas if helper_decl_name(b)
            ]
            if dossier is not None:
                checked_helper_sources = set(check_lemmas)
                semantic_replacement_names: List[str] = []
                for helper in helpers:
                    name = helper_decl_name(helper)
                    if not name or helper not in checked_helper_sources:
                        continue
                    prior_helper = dossier.verified_helpers.get(name)
                    checked_index = check_lemmas.index(helper)
                    replay_context_names = [
                        helper_decl_name(block) or ""
                        for block in check_lemmas[:checked_index]
                        if helper_decl_name(block)
                    ]
                    helper_record = dossier.record_verified_helper(
                        helper,
                        phase=conv.role,
                        turn_index=phase_turn,
                        replay_context_names=replay_context_names,
                        # The accepted main proof was checked with this exact
                        # declaration block.  Preserve that replay identity
                        # instead of silently keeping an older same-name
                        # helper from a prior turn.
                        replace_existing_same_name=True,
                    )
                    if helper_record is None:
                        continue
                    _stage_verified_helper_receipt(session, helper_record, dossier)
                    if (
                        prior_helper is not None
                        and verified_helper_semantic_statement_changed(
                            prior_helper,
                            helper_record,
                        )
                    ):
                        semantic_replacement_names.append(name)
                    helpers_added.extend(
                        dossier.visible_accepted_helper_names([name])
                        if hasattr(dossier, "visible_accepted_helper_names")
                        else [name]
                    )
                    if session.proof_cache is not None:
                        from ensemble_prover.proof_state_executor import (
                            _proof_state_check_preamble,
                        )

                        store_verified_helper_for_dossier(
                            session.proof_cache,
                            helper,
                            preamble=_proof_state_check_preamble(conv),
                            dossier=dossier,
                            phase=conv.role,
                        )
                if semantic_replacement_names:
                    stale_dependents = set().union(
                        *(
                            stale_dependents_by_correction.get(name, set())
                            for name in semantic_replacement_names
                        )
                    )
                    checked_names = {
                        helper_decl_name(block) or "" for block in check_lemmas
                    }
                    checked_names.discard("")
                    checked_sources = {
                        helper_decl_name(block) or "": block
                        for block in check_lemmas
                        if helper_decl_name(block)
                    }
                    for stale_name in sorted(stale_dependents - checked_names):
                        dossier.remove_verified_helper(stale_name)
                    for stale_name in sorted(stale_dependents & checked_names):
                        recorded = dossier.verified_helpers.get(stale_name)
                        if str(getattr(recorded, "source", "") or "") != str(
                            checked_sources.get(stale_name, "") or ""
                        ):
                            dossier.remove_verified_helper(stale_name)
                    for replacement_name in semantic_replacement_names:
                        refresh_revalidated_dependent_support_hashes(
                            dossier,
                            replacement_name,
                        )
                    for stale_name in sorted(stale_dependents & checked_names):
                        if stale_name not in dossier.verified_helpers:
                            continue
                        integrity = dossier.root_replay_integrity_status(
                            helper_names=[stale_name]
                        )
                        if not bool(integrity.get("ready")):
                            dossier.remove_verified_helper(stale_name)
                if graph_native_goal_statement and graph_native_target:
                    graph_native_replay_context_names = [
                        helper_decl_name(block) or ""
                        for block in check_lemmas
                        if helper_decl_name(block)
                    ]
                    target_id = str(graph_native_target.get("node_id") or "").strip()
                    helper_name = _graph_native_helper_name(
                        theorem_name=str(theorem_name or ""),
                        node_id=target_id,
                        node_name=str(graph_native_target.get("name") or ""),
                        work_type=str(graph_native_target.get("work_type") or ""),
                    )
                    helper_source = _graph_native_helper_source(
                        helper_name=helper_name,
                        statement=graph_native_goal_statement,
                        proof=proof,
                    )
                    helper_record = dossier.record_verified_helper(
                        helper_source,
                        phase=f"{conv.role}_graph_native",
                        turn_index=phase_turn,
                        replay_context_names=graph_native_replay_context_names,
                    )
                    graph_native_verdict = "proved"
                    graph_native_error_type = ""
                    graph_native_attempt_proof = proof
                    if helper_record is not None:
                        _stage_verified_helper_receipt(
                            session,
                            helper_record,
                            dossier,
                        )
                        helpers_added.extend(
                            dossier.visible_accepted_helper_names([helper_name])
                            if hasattr(dossier, "visible_accepted_helper_names")
                            else [helper_name]
                        )
                        if session.proof_cache is not None:
                            from ensemble_prover.proof_state_executor import (
                                _proof_state_check_preamble,
                            )

                            store_verified_helper_for_dossier(
                                session.proof_cache,
                                helper_source,
                                preamble=_proof_state_check_preamble(conv),
                                dossier=dossier,
                                phase=f"{conv.role}_graph_native",
                            )
                        helper_names = list(dict.fromkeys([*helper_names, helper_name]))
                    else:
                        graph_native_verdict = "proof_policy_rejected"
                        graph_native_error_type = "graph_native_helper_record_failed"
                        graph_native_attempt_proof = ""
                    dossier.record_attempt(
                        phase=f"{conv.role}_graph_native",
                        turn_index=phase_turn,
                        proof=graph_native_attempt_proof,
                        helper_names=helper_names,
                        verdict=graph_native_verdict,
                        error_type=graph_native_error_type,
                        node_id=target_id or None,
                        metadata={
                            "selected_graph_work": dict(
                                getattr(session, "selected_work_item_record", {}) or {}
                            ),
                            "graph_native_goal_statement": graph_native_goal_statement,
                            "graph_native_helper_name": helper_name,
                        },
                    )
                    if helper_record is None:
                        # The target's own record was rejected. Auxiliary
                        # support helpers recorded above stay durable in the
                        # dossier and are synced to the graph so assembly can
                        # use them — but the OUTCOME must not signal
                        # progress/helpers for a rejected target:
                        # session.apply() treats outcome.progress and
                        # outcome.helpers_added as target-level success
                        # (repair tickets resolve as "repair_turn_consumed",
                        # the stagnation safety net resets, and the failing
                        # frontier key is never consumed), which would let a
                        # dead target be re-selected indefinitely.
                        if helpers_added and proof_state is not None:
                            sync_proof_state_to_graph(
                                proof_state,
                                dossier,
                                session=session,
                                phase=f"{conv.role}_graph_native_support",
                                turn_index=phase_turn,
                            )
                        _emit_record(session, {
                            **common_payload,
                            "dossier_context_helpers": list(context_helpers),
                            "replay_helpers": list(check_lemmas),
                            "lean_ok": True,
                            "lean_output": getattr(
                                lean_verdict.primary_result, "output", ""
                            ),
                            "lean_elapsed_s": lean_elapsed,
                            "helper_name": helper_name,
                            "helpers_added": list(helpers_added),
                            "solved_root": False,
                            "verdict": "proof_policy_rejected",
                            "error_type": graph_native_error_type,
                        })
                        cost = time.monotonic() - started
                        return MiniOutcome(
                            action_id=self.id,
                            solved=False,
                            proof=None,
                            helpers_added=(),
                            progress=bool(skeleton_route_banked),
                            cost_seconds=cost,
                            metadata={
                                "role": self.role,
                                "conv_turn_index_offset": conv_turn_offset,
                                "conv_turn_index_absolute": absolute_turn,
                                "conv_turn_index_phase": phase_turn,
                                **_turn_budget_metadata(common_payload),
                                "feedback_source": lean_verdict.feedback_source,
                                "lean_verdict": graph_native_error_type,
                                "lean_elapsed_s": lean_elapsed,
                                "llm_response_recorded": llm_response_recorded,
                                "graph_native_target_node_id": target_id,
                                "graph_native_work_type": graph_native_target.get(
                                    "work_type"
                                ),
                                "graph_native_helper_name": helper_name,
                                "verdict": graph_native_verdict,
                                "error_type": graph_native_error_type,
                                **skeleton_route_metadata,
                                "strong_progress": False,
                                "unverified_decomposition_created": bool(
                                    skeleton_route_banked
                                ),
                                "assembly_contracts_added": bool(
                                    skeleton_route_banked
                                ),
                                **_repair_self_check_metadata(common_payload),
                            },
                        )
                    if proof_state is not None:
                        sync_proof_state_to_graph(
                            proof_state,
                            dossier,
                            session=session,
                            phase=f"{conv.role}_graph_native_proved",
                            turn_index=phase_turn,
                        )
                    _emit_record(session, {
                        **common_payload,
                        "dossier_context_helpers": list(context_helpers),
                        "replay_helpers": list(check_lemmas),
                        "lean_ok": True,
                        "lean_output": getattr(
                            lean_verdict.primary_result, "output", ""
                        ),
                        "lean_elapsed_s": lean_elapsed,
                        "helper_name": helper_name,
                        "helpers_added": list(helpers_added),
                        "solved_root": False,
                        "verdict": "graph_native_proved",
                    })
                    cost = time.monotonic() - started
                    return MiniOutcome(
                        action_id=self.id,
                        solved=False,
                        proof=None,
                        helpers_added=tuple(helpers_added),
                        progress=True,
                        cost_seconds=cost,
                        metadata={
                            "role": self.role,
                            "conv_turn_index_offset": conv_turn_offset,
                            "conv_turn_index_absolute": absolute_turn,
                            "conv_turn_index_phase": phase_turn,
                            **_turn_budget_metadata(common_payload),
                            **skeleton_route_metadata,
                            "feedback_source": lean_verdict.feedback_source,
                            "lean_verdict": "graph_native_lean_accepted",
                            "lean_elapsed_s": lean_elapsed,
                            "llm_response_recorded": llm_response_recorded,
                            "answer_safe_recheck_verifier_only_retry": bool(
                                common_payload.get(
                                    "answer_safe_recheck_verifier_only_retry"
                                )
                            ),
                            "answer_safe_recheck_retry_attempts": int(
                                common_payload.get(
                                    "answer_safe_recheck_retry_attempts",
                                    0,
                                )
                                or 0
                            ),
                            "answer_safe_recheck_retry_timeout_s": (
                                common_payload.get(
                                    "answer_safe_recheck_retry_timeout_s"
                                )
                            ),
                            "graph_native_target_node_id": target_id,
                            "graph_native_work_type": graph_native_target.get("work_type"),
                            "graph_native_helper_name": helper_name,
                            **_repair_self_check_metadata(common_payload),
                        },
                    )
            # H7 telemetry: verdict=solved.
            _emit_record(session, {
                **common_payload,
                "dossier_context_helpers": list(context_helpers),
                "replay_helpers": list(check_lemmas),
                "lean_ok": True,
                "lean_output": getattr(
                    lean_verdict.primary_result, "output", ""
                ),
                "lean_elapsed_s": lean_elapsed,
                "verdict": "solved",
            })
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=True,
                proof=proof,
                helpers_added=tuple(helpers_added),
                progress=True,
                cost_seconds=cost,
                root_candidate=RootFinalizationCandidate(
                    proof=proof,
                    replay_helpers=tuple(check_lemmas),
                    helper_names=tuple(helper_names),
                    phase=conv.role,
                    turn_index=phase_turn,
                    source_action_id=self.id,
                    route_id=str(
                        assemble_route_contract_status.get("route_id")
                        or common_payload.get("route_id")
                        or ""
                    ),
                    dependency_node_ids=tuple(
                        str(node_id or "").strip()
                        for node_id in list(
                            assemble_route_contract_status.get("dependency_node_ids")
                            or assemble_route_contract_status.get("required_node_ids")
                            or []
                        )
                        if str(node_id or "").strip()
                    ),
                    target_statement=str(
                        getattr(dossier, "root_statement", "")
                        or getattr(conv, "goal_statement", "")
                        or ""
                    ),
                    require_route_contract=bool(assemble_route_goal_statement),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=proof,
                        phase=conv.role,
                        turn_index=phase_turn,
                        target_statement=str(
                            getattr(dossier, "root_statement", "")
                            or getattr(conv, "goal_statement", "")
                            or ""
                        ),
                        replay_helpers=tuple(check_lemmas),
                        helper_names=tuple(helper_names),
                        output=str(
                            getattr(
                                getattr(lean_verdict, "primary_result", None),
                                "output",
                                "",
                            )
                            or ""
                        ),
                        source=str(getattr(lean_verdict, "primary_source", "") or ""),
                    ),
                    metadata=(
                        {
                            **skeleton_route_metadata,
                            "assemble_route_authoring": True,
                            "route_assembly_contract_status": dict(
                                assemble_route_contract_status
                            ),
                        }
                        if assemble_route_goal_statement
                        else dict(skeleton_route_metadata)
                    ),
                ),
                metadata={
                    "role": self.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    **skeleton_route_metadata,
                    "feedback_source": lean_verdict.feedback_source,
                    "lean_verdict": "lean_accepted",
                    "lean_elapsed_s": lean_elapsed,
                    "llm_response_recorded": llm_response_recorded,
                    "answer_safe_recheck_verifier_only_retry": bool(
                        common_payload.get(
                            "answer_safe_recheck_verifier_only_retry"
                        )
                    ),
                    "answer_safe_recheck_retry_attempts": int(
                        common_payload.get("answer_safe_recheck_retry_attempts", 0)
                        or 0
                    ),
                    "answer_safe_recheck_retry_timeout_s": common_payload.get(
                        "answer_safe_recheck_retry_timeout_s"
                    ),
                    "replay_helpers": list(check_lemmas),
                    "helper_names": list(helper_names),
                    **_repair_self_check_metadata(common_payload),
                },
            )

        # ---- Step 5: Post-failure cascade ----------------------------
        # Record the rejected attempt before the cascade so failure
        # accounting matches legacy semantics.
        if dossier is not None:
            failure_helper_names = [
                helper_decl_name(b) or "" for b in check_lemmas if helper_decl_name(b)
            ]
            error_type = ""
            failure_signature = ""
            try:
                from ensemble_prover.mini_prover import _analyze_lean_failure

                if lean_verdict.feedback_result is not None:
                    failure_analysis = _analyze_lean_failure(
                        lean_verdict.feedback_result
                    )
                    error_type = str(failure_analysis.get("error_type", ""))
                    failure_signature = _lean_failure_wall_signature(
                        failure_analysis
                    )
            except Exception:
                error_type = ""
                failure_signature = ""
            graph_failure_node_id = None
            graph_failure_metadata = None
            if graph_native_goal_statement and graph_native_target:
                graph_failure_node_id = str(
                    graph_native_target.get("node_id") or ""
                ).strip() or None
                graph_failure_metadata = {
                    "selected_graph_work": dict(
                        getattr(session, "selected_work_item_record", {}) or {}
                    ),
                    "graph_native_goal_statement": graph_native_goal_statement,
                    "graph_native_work_type": graph_native_target.get("work_type"),
                }
            if graph_failure_node_id is None:
                selected_record = dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                )
                candidate_node_id = str(
                    selected_record.get("graph_node_id")
                    or selected_record.get("node_id")
                    or ""
                ).strip()
                graph = getattr(dossier, "proof_graph", None)
                graph_nodes = getattr(graph, "nodes", {}) if graph is not None else {}
                if candidate_node_id and candidate_node_id in graph_nodes:
                    graph_failure_node_id = candidate_node_id
                    graph_failure_metadata = {
                        "selected_graph_work": selected_record,
                        "graph_native_work_type": selected_record.get("work_type"),
                    }
            graph_failure_metadata = dict(graph_failure_metadata or {})
            if failure_signature:
                graph_failure_metadata["lean_failure_signature"] = (
                    failure_signature
                )
            dossier.record_attempt(
                phase=conv.role,
                turn_index=phase_turn,
                proof=proof,
                helper_names=failure_helper_names,
                verdict="lean_rejected",
                error_type=error_type,
                node_id=graph_failure_node_id,
                metadata=graph_failure_metadata,
            )

        # Always run the cascade inline so all 8 phases (analyze →
        # repair retrieval → record_failure → child-closure → salvage
        # → assembly → root-tactic-close → feedback compose) execute
        # with full telemetry. The dispatch_subaction path is reserved
        # for the outer loop's frontier-first scheduling between turns;
        # mid-turn the cascade always runs inline.
        #
        # Live-trace fix (2026-05-08): clear ``session.last_lean_verdict``
        # AFTER the inline cascade returns. The post-failure cascade is owned
        # here; the standalone PostLeanFailureAction remains importable for
        # replay tests but is not registered in normal sessions. Consuming the
        # signal here prevents stale verdict state from re-running the same
        # 8-phase work on a later turn.
        try:
            return await _run_post_failure_cascade_inline(
                session=session,
                action=self,
                conv=conv,
                dossier=dossier,
                proof_state=proof_state,
                proof=proof,
                helpers=helpers,
                lemma_dag_candidate_helpers=lemma_dag_candidates,
                check_lemmas=list(check_lemmas),
                context_helpers=list(context_helpers),
                lean_verdict=lean_verdict,
                lean_elapsed=lean_elapsed,
                common_payload=common_payload,
                absolute_turn=absolute_turn,
                phase_turn=phase_turn,
                conv_turn_offset=conv_turn_offset,
                started=started,
                max_turns_footer=max_turns_footer,
                searcher=base_searcher,
                llm_output=content,
                turn_giveup=turn_giveup,
            )
        finally:
            # Mark the verdict as consumed for replay/debug paths too.
            session.last_lean_verdict = None


# ---------------------------------------------------------------------------
# Helper-only cascade: replicates legacy mini_prover.py:3693-3991 (no-proof
# branch). Returns a MiniOutcome on solve OR continues-with-progress; returns
# None when the no-proof fallback path should run (no helpers, no decomp,
# no salvage acceptance, no construction-collapse).
# ---------------------------------------------------------------------------


async def _run_helpers_only_cascade(
    *,
    session: Any,
    action: Any,
    conv: Any,
    lean: Any,
    dossier: Any,
    proof_state: Any,
    content: str,
    helpers: List[str],
    lemma_dag_candidate_helpers: List[str],
    common_payload: Dict[str, Any],
    absolute_turn: int,
    phase_turn: int,
    conv_turn_offset: int,
    started: float,
) -> Optional[MiniOutcome]:
    """Legacy helpers-only cascade.

    Defect H2 + MED-2 + MED-3 fix (2026-05-08): restores the full
    five-pathway cascade that legacy mini_prover.py:3693-3991 ran in
    the no-proof branch. Without these pathways, helpers-only replies
    that legacy could solve via lemma-DAG → assembly → root-tactic
    were silently re-prompted in the new pipeline.
    """

    from ensemble_prover.helper_salvage import HelperSalvager
    from ensemble_prover.mini_root_tactic import (
        root_tactic_success_contract_status,
        try_close_root_with_active_lift,
    )
    from ensemble_prover.proof_dossier import helper_decl_name
    from ensemble_prover.proof_state_executor import (
        _proof_state_acceptance_preamble,
        _proof_state_check_preamble,
        _try_proof_state_child_closures,
        _try_proof_state_lemma_dag_helpers,
        _try_proof_state_salvaged_helper_assembly,
    )

    timeout_s = float(action.proof_state_child_tactic_timeout_s or 0.0)
    max_candidates = int(action.proof_state_child_tactic_max_candidates or 0)
    max_nodes = int(action.proof_state_child_goal_limit or 0)
    max_decl_apps = int(action.proof_state_decl_application_limit or 0)
    parallelism = int(action.proof_state_batch_parallelism or 1)
    child_tactics_enabled = bool(action.proof_state_child_tactics_enabled)
    root_target_statement = str(
        getattr(dossier, "root_statement", "")
        or getattr(conv, "goal_statement", "")
        or ""
    )
    lemma_dag_helpers: List[str] = []
    lemma_dag_child_node_ids: List[str] = []
    lemma_dag_linked_child_node_ids: List[str] = []
    lemma_dag_ps_helpers: List[str] = []
    defer_fresh_children_to_llm = False
    skeleton_route_banked, skeleton_route_metadata = _skeleton_route_metadata(
        common_payload
    )

    try:
        from ensemble_prover.mini_prover import (
            _bank_helpers_as_proposed,
            _format_root_equivalent_helper_feedback,
            _root_equivalent_sorry_stub_helper_names_from_blocks,
        )

        root_equivalent_names = _root_equivalent_sorry_stub_helper_names_from_blocks(
            list(lemma_dag_candidate_helpers or helpers or []),
            goal_statement=str(getattr(conv, "goal_statement", "") or ""),
        )
    except Exception:
        root_equivalent_names = []
    if root_equivalent_names:
        bankable_sources = [
            src
            for src in list(helpers or lemma_dag_candidate_helpers or [])
            if isinstance(src, str)
            and (helper_decl_name(src) or "") not in set(root_equivalent_names)
        ]
        _banked_root_equiv = _bank_helpers_as_proposed(
            dossier,
            bankable_sources,
            phase=str(getattr(conv, "role", "prove") or "prove"),
            turn_index=int(absolute_turn or 0),
            goal_statement=str(getattr(conv, "goal_statement", "") or ""),
            allow_helper_decomposition=bool(
                getattr(conv, "allow_helper_decomposition", True)
            ),
        )
        _emit_record(session, {
            **common_payload,
            "rejection_reason": "root_equivalent_helper_stub",
            "rejection_match": ", ".join(root_equivalent_names),
            "banked_proposed_helpers": list(_banked_root_equiv),
            "verdict": "proof_policy_rejected",
        })
        try:
            conv.append_user(_format_root_equivalent_helper_feedback(root_equivalent_names))
        except Exception:
            conv.append_user(
                "The helper decomposition restated the root goal instead of "
                "making progress. Put needed smaller facts inside one "
                "active-goal proof attempt only if they are fully proved; "
                "otherwise pivot the proof route instead of asking for the "
                "same goal as a helper."
            )
        cost = time.monotonic() - started
        return MiniOutcome(
            action_id=action.id,
            solved=False,
            proof=None,
            helpers_added=(),
            progress=bool(skeleton_route_banked),
            cost_seconds=cost,
            metadata={
                "role": action.role,
                "conv_turn_index_offset": conv_turn_offset,
                "conv_turn_index_absolute": absolute_turn,
                "conv_turn_index_phase": phase_turn,
                **_turn_budget_metadata(common_payload),
                "rejection_reason": "root_equivalent_helper_stub",
                "rejection_match": ", ".join(root_equivalent_names),
                "banked_proposed_helpers": list(_banked_root_equiv),
                **skeleton_route_metadata,
                **({"strong_progress": False} if skeleton_route_banked else {}),
                **_repair_self_check_metadata(common_payload),
            },
        )

    # ---- Pathway (1) + (2): lemma-DAG decomposition + child closure ----
    # Mirrors mini_prover.py:3693-3795.
    # D2 gate-side fix (2026-05-09): open ad-hoc decomposition_task when
    # the LLM emitted sorry-stub helpers as a decomposition request.
    # Without this, the gate immediately below skips and the helpers
    # fall on the floor — observed in putnam_2020_a2 run 22:57 with
    # repeated lemma-DAG no-open-task events on real sorry-stubs.
    if (
        lemma_dag_candidate_helpers
        and proof_state is not None
        and dossier is not None
        and bool(getattr(conv, "allow_helper_decomposition", True))
        and not proof_state.has_open_decomposition_task()
    ):
        from ensemble_prover.proof_state_executor import (
            ensure_decomposition_task_open_for_lemma_dag_candidates,
        )
        lemma_dag_open_attempt = ensure_decomposition_task_open_for_lemma_dag_candidates(
            proof_state,
            lemma_dag_candidate_helpers,
            source=f"lemma_dag_helpers_volunteered:helpers_only_cascade:turn={absolute_turn}",
        )
    else:
        lemma_dag_open_attempt = {}
    if (
        lemma_dag_candidate_helpers
        and proof_state is not None
        and dossier is not None
        and bool(getattr(conv, "allow_helper_decomposition", True))
        and not proof_state.has_open_decomposition_task()
    ):
        # MED-3 + M5: no-open-task observability record. Both the
        # helpers-only cascade (no-proof branch) and the pre-Lean
        # decomposition (proof-extracted branch) can observe the same
        # content; track per-turn fired-state on the session to ensure
        # exactly one event per turn.
        if not _already_fired_lemma_dag_skipped(session):
            _emit_record(session, {
                **common_payload,
                "lemma_dag_candidate_count": len(lemma_dag_candidate_helpers),
                "lemma_dag_open_attempt": dict(lemma_dag_open_attempt or {}),
                "verdict": "lemma_dag_no_decomposition_task_opened",
            })
            _mark_lemma_dag_skipped_fired(session)

    if (
        lemma_dag_candidate_helpers
        and proof_state is not None
        and dossier is not None
        and bool(getattr(conv, "allow_helper_decomposition", True))
        and proof_state.has_open_decomposition_task()
    ):
        child_goal_ids_before = {
            nid
            for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
            if getattr(node, "kind", "") == "child_goal"
        }
        decomposition_links_before = {
            str(nid): set(str(cid) for cid in getattr(node, "child_node_ids", ()) or ())
            for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
            if getattr(node, "kind", "") == "decomposition_task"
        }
        lemma_dag_helpers = await _try_proof_state_lemma_dag_helpers(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            helpers=lemma_dag_candidate_helpers,
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=phase_turn,
            timeout_s=timeout_s,
            proof_cache=session.proof_cache,
        )
        child_goal_ids_after = {
            nid
            for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
            if getattr(node, "kind", "") == "child_goal"
        }
        new_child_node_ids = sorted(child_goal_ids_after - child_goal_ids_before)
        lemma_dag_linked_child_node_ids = sorted(
            {
                str(cid)
                for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
                if getattr(node, "kind", "") == "decomposition_task"
                for cid in getattr(node, "child_node_ids", ()) or ()
                if str(cid) in child_goal_ids_before
                and str(cid) not in decomposition_links_before.get(str(nid), set())
            }
        )
        lemma_dag_child_node_ids = sorted(
            set(new_child_node_ids) | set(lemma_dag_linked_child_node_ids)
        )
        if (
            proof_state.has_open_decomposition_task() is False
            or lemma_dag_helpers
            or lemma_dag_child_node_ids
        ):
            sync_proof_state_to_graph(
                proof_state,
                dossier,
                session=session,
                phase="proof_state_lemma_dag_decomposition",
                turn_index=phase_turn,
            )
            action_available = getattr(session, "action_available", None)
            registered_action = getattr(session, "registered_action", None)
            recursive_action = (
                registered_action("recursive_helper_prover")
                if callable(registered_action)
                else None
            )
            recursive_helper_active = (
                bool(action_available("recursive_helper_prover"))
                if callable(action_available)
                else False
            )
            # Fresh lemma-DAG children are a scheduler boundary.  If the
            # recursive helper action is registered, has budget, and is
            # immediately applicable, leave brand-new decomposition work for
            # the next scheduler turn rather than consuming it inline in the
            # conversation action.
            if recursive_action is None:
                recursive_helper_active = False
            elif recursive_helper_active:
                is_applicable = getattr(recursive_action, "is_applicable", None)
                try:
                    recursive_helper_active = bool(
                        is_applicable(session) if callable(is_applicable) else False
                    )
                except Exception:
                    recursive_helper_active = False
                if recursive_helper_active and lemma_dag_child_node_ids:
                    node_is_candidate = getattr(recursive_action, "_node_is_candidate", None)
                    nodes = getattr(proof_state, "nodes", {}) or {}
                    if callable(node_is_candidate):
                        recursive_helper_active = any(
                            node_is_candidate(nodes.get(child_id))
                            for child_id in lemma_dag_child_node_ids
                            if nodes.get(child_id) is not None
                        )
            defer_fresh_children_to_llm = bool(
                lemma_dag_child_node_ids and recursive_helper_active
            )
            if defer_fresh_children_to_llm:
                _emit_record(session, {
                    **common_payload,
                    "phase": "proof_state_lemma_dag_child_routing",
                    "turn_in_phase": phase_turn,
                    "new_child_node_ids": list(lemma_dag_child_node_ids),
                    "verdict": "deferred_to_recursive_helper_prover",
                })
            if (
                (lemma_dag_helpers or lemma_dag_child_node_ids)
                and child_tactics_enabled
                and not defer_fresh_children_to_llm
            ):
                state_ok, state_proof, lemma_dag_ps_helpers = await _try_proof_state_child_closures(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    recorder=session.recorder,
                    trace_prefix=session.trace_prefix,
                    turn=phase_turn,
                    timeout_s=timeout_s,
                    max_candidates=max_candidates,
                    max_nodes=max_nodes,
                    max_decl_applications=max_decl_apps,
                    batch_parallelism=parallelism,
                    proof_cache=session.proof_cache,
                    target_node_ids=(
                        tuple(lemma_dag_child_node_ids)
                        if lemma_dag_child_node_ids
                        else None
                    ),
                )
                sync_proof_state_to_graph(
                    proof_state,
                    dossier,
                    session=session,
                    phase="proof_state_lemma_dag_root_check",
                    turn_index=phase_turn,
                )
                if state_ok and state_proof:
                    _emit_record(session, {
                        **common_payload,
                        "phase": "proof_state_lemma_dag_root_check",
                        "turn_in_phase": phase_turn,
                        "accepted_helpers": list(lemma_dag_ps_helpers or ()),
                        "proof_state": _safe_record(proof_state),
                        "verdict": "solved_after_lemma_dag_helper",
                    })
                    replay_helpers = tuple(dossier.verified_helper_blocks())
                    helper_names_list = tuple(
                        name
                        for block in replay_helpers
                        for name in [helper_decl_name(block)]
                        if name
                    )
                    cost = time.monotonic() - started
                    visible_lemma_dag_ps_helpers = (
                        dossier.visible_accepted_helper_names(
                            lemma_dag_ps_helpers or ()
                        )
                        if hasattr(dossier, "visible_accepted_helper_names")
                        else list(lemma_dag_ps_helpers or ())
                    )
                    return MiniOutcome(
                        action_id=action.id,
                        solved=True,
                        proof=state_proof,
                        helpers_added=tuple(visible_lemma_dag_ps_helpers),
                        progress=True,
                        cost_seconds=cost,
                        root_candidate=RootFinalizationCandidate(
                            proof=state_proof,
                            replay_helpers=replay_helpers,
                            helper_names=helper_names_list,
                            phase="proof_state_lemma_dag_root_check",
                            turn_index=phase_turn,
                            source_action_id=action.id,
                            target_statement=str(
                                getattr(dossier, "root_statement", "")
                                or getattr(conv, "goal_statement", "")
                                or ""
                            ),
                            verification_certificate=root_verification_certificate(
                                accepted=True,
                                proof=state_proof,
                                phase="proof_state_lemma_dag_root_check",
                                turn_index=phase_turn,
                                target_statement=str(
                                    getattr(dossier, "root_statement", "")
                                    or getattr(conv, "goal_statement", "")
                                    or ""
                                ),
                                replay_helpers=replay_helpers,
                                helper_names=helper_names_list,
                                source="proof_state_lemma_dag_root_check",
                            ),
                            metadata={"root_finalization_already_applied": True},
                        ),
                        metadata={
                            "role": action.role,
                            "conv_turn_index_offset": conv_turn_offset,
                            "conv_turn_index_absolute": absolute_turn,
                            "conv_turn_index_phase": phase_turn,
                            **_turn_budget_metadata(common_payload),
                            "solved_via": "lemma_dag_helper",
                            "replay_helpers": list(replay_helpers),
                            "helper_names": list(helper_names_list),
                            "root_finalization_already_applied": True,
                            "visible_helpers_added_count": len(
                                visible_lemma_dag_ps_helpers
                            ),
                        },
                    )
            # Lemma-DAG processed. If it only produced open child goals,
            # return now and let the frontier route them to recursive
            # helper proving. If it also accepted helpers, continue into
            # salvage/assembly/root-tactic below so accepted facts can be
            # used immediately while the fresh child nodes stay deferred.
            if not lemma_dag_helpers:
                if defer_fresh_children_to_llm:
                    conv.append_user(
                        "The controller recorded your helper declarations as "
                        "open proof-state child goals. Recursive helper proving "
                        "is enabled, so the scheduler will attack those child "
                        "goals with scoped LLM sub-sessions before using "
                        "retrieval and deterministic tactic fallback."
                    )
                else:
                    conv.append_user(
                        "The controller recorded your helper declarations as "
                        "open proof-state child goals and started deterministic "
                        "closure on them. Open proof-state child goals are "
                        "not facts yet; prove or repair them before root "
                        "assembly. The scheduler will continue with "
                        "retrieval, tactic search, and recursive helper proving "
                        "before re-engaging the root proof."
                        )
                cost = time.monotonic() - started
                visible_lemma_dag_ps_helpers = (
                    dossier.visible_accepted_helper_names(lemma_dag_ps_helpers or ())
                    if hasattr(dossier, "visible_accepted_helper_names")
                    else list(lemma_dag_ps_helpers or ())
                )
                lemma_dag_ps_parent_progress = (
                    _strong_progress_for_accepted_helpers(
                        dossier,
                        list(lemma_dag_ps_helpers or ()),
                    )
                )
                return MiniOutcome(
                    action_id=action.id,
                    solved=False,
                    proof=None,
                    helpers_added=tuple(visible_lemma_dag_ps_helpers),
                    progress=bool(
                        visible_lemma_dag_ps_helpers
                        or lemma_dag_ps_parent_progress
                        or skeleton_route_banked
                    ),
                    cost_seconds=cost,
                    metadata={
                        "role": action.role,
                        "conv_turn_index_offset": conv_turn_offset,
                        "conv_turn_index_absolute": absolute_turn,
                        "conv_turn_index_phase": phase_turn,
                        **_turn_budget_metadata(common_payload),
                        "lemma_dag_helper_count": 0,
                        "visible_helpers_added_count": len(
                            visible_lemma_dag_ps_helpers
                        ),
                        "lemma_dag_recorded_child_count": len(lemma_dag_child_node_ids),
                        "new_child_node_ids": list(lemma_dag_child_node_ids),
                        "linked_child_node_ids": list(lemma_dag_linked_child_node_ids),
                        **skeleton_route_metadata,
                        # HIGH #4 follow-up (2026-05-22): use the strict
                        # classifier so statement-duplicate helpers don't
                        # falsely reset the stagnation counter.
                        "strong_progress": _strong_progress_for_accepted_helpers(
                            dossier, list(lemma_dag_ps_helpers or ())
                        ),
                        "unverified_decomposition_created": bool(
                            lemma_dag_child_node_ids or skeleton_route_banked
                        ),
                        "deferred_fresh_children_to_recursive_helper": defer_fresh_children_to_llm,
                    },
                )

    # ---- Pathways (3)-(6): salvage → assembly → child-closure → root tactic ----
    # Mirrors mini_prover.py:3796-3990.
    if not (lemma_dag_candidate_helpers and dossier is not None and timeout_s > 0.0):
        if lemma_dag_helpers or lemma_dag_child_node_ids or lemma_dag_ps_helpers:
            conv.append_user(
                "The controller processed your helper declarations as "
                "lemma-DAG decomposition work. Now submit one main proof "
                "that assembles the root from verified helpers only. Open "
                "proof-state child goals are not facts yet; prove or repair "
                "them before using them in root assembly."
            )
            cost = time.monotonic() - started
            raw_lemma_dag_helpers = [*lemma_dag_helpers, *lemma_dag_ps_helpers]
            visible_lemma_dag_helpers = (
                dossier.visible_accepted_helper_names(raw_lemma_dag_helpers)
                if hasattr(dossier, "visible_accepted_helper_names")
                else list(raw_lemma_dag_helpers)
            )
            lemma_dag_parent_progress = _strong_progress_for_accepted_helpers(
                dossier,
                raw_lemma_dag_helpers,
            )
            return MiniOutcome(
                action_id=action.id,
                solved=False,
                proof=None,
                helpers_added=tuple(visible_lemma_dag_helpers),
                progress=bool(
                    visible_lemma_dag_helpers
                    or lemma_dag_parent_progress
                    or skeleton_route_banked
                ),
                cost_seconds=cost,
                metadata={
                    "role": action.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "lemma_dag_helper_count": len(lemma_dag_helpers),
                    "visible_helpers_added_count": len(visible_lemma_dag_helpers),
                    "lemma_dag_recorded_child_count": len(lemma_dag_child_node_ids),
                    "new_child_node_ids": list(lemma_dag_child_node_ids),
                    "linked_child_node_ids": list(lemma_dag_linked_child_node_ids),
                    **skeleton_route_metadata,
                    # HIGH #4 follow-up (2026-05-22): see comment at the
                    # sibling site above.
                    "strong_progress": _strong_progress_for_accepted_helpers(
                        dossier,
                        list(lemma_dag_helpers or ()) + list(lemma_dag_ps_helpers or ()),
                    ),
                    "unverified_decomposition_created": bool(
                        lemma_dag_child_node_ids or skeleton_route_banked
                    ),
                    "deferred_fresh_children_to_recursive_helper": defer_fresh_children_to_llm,
                },
            )
        return None

    from ensemble_prover.helper_salvage import collect_open_child_targets

    salvager = HelperSalvager(
        lean,
        preamble=_proof_state_check_preamble(conv),
        answer_safe_preamble=str(getattr(conv, "preamble", "") or ""),
        timeout_s=timeout_s,
        relevance_gate_root_statement=str(
            getattr(dossier, "root_statement", "") or ""
        ),
        relevance_gate_open_targets=collect_open_child_targets(proof_state),
        verified_helper_accept_callback=getattr(
            session,
            "theory_verified_helper_accept_callback",
            None,
        ),
    )
    salvage_result = await salvager.salvage(
        lemma_dag_candidate_helpers,
        dossier=dossier,
        phase=f"{conv.role}:helper_only_salvage",
        turn_index=phase_turn,
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
                phase=f"{conv.role}:helper_only_salvage",
                turn_index=phase_turn,
                conservative=True,
            )
        except Exception:
            pass
    _emit_record(session, {
        **common_payload,
        "phase": "helper_only_salvage",
        "turn_in_phase": phase_turn,
        "candidate_count": len(lemma_dag_candidate_helpers),
        "accepted_helpers": list(
            dict.fromkeys([*lemma_dag_helpers, *salvage_result.accepted])
        ),
        "rejected_helpers": list(salvage_result.rejected),
        "skipped_helpers": list(salvage_result.skipped),
        "verdict": (
            "helpers_accepted"
            if lemma_dag_helpers or salvage_result.accepted
            else "helpers_rejected"
        ),
    })

    accepted_helper_names = list(
        dict.fromkeys([*lemma_dag_helpers, *salvage_result.accepted])
    )
    if not accepted_helper_names:
        return None
    visible_accepted_helper_names = (
        dossier.visible_accepted_helper_names(accepted_helper_names)
        if hasattr(dossier, "visible_accepted_helper_names")
        else list(accepted_helper_names)
    )
    accepted_parent_helper_progress = _strong_progress_for_accepted_helpers(
        dossier,
        accepted_helper_names,
    )

    # Cache successfully salvaged helpers.
    if session.proof_cache is not None:
        for helper_name in salvage_result.accepted:
            helper_record = dossier.verified_helpers.get(helper_name)
            if helper_record is not None:
                try:
                    store_verified_helper_for_dossier(
                        session.proof_cache,
                        helper_record.source,
                        preamble=_proof_state_check_preamble(conv),
                        dossier=dossier,
                        phase=f"{conv.role}:helper_only_salvage",
                    )
                except Exception:
                    pass
    if proof_state is not None:
        sync_proof_state_to_graph(
            proof_state,
            dossier,
            session=session,
            phase="helper_only_salvage",
            turn_index=phase_turn,
        )

    # ---- Pathway (4): salvaged-helper assembly --------------------
    if proof_state is not None and child_tactics_enabled:
        state_ok, state_proof, salvaged_state_helpers = await _try_proof_state_salvaged_helper_assembly(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            helper_names=accepted_helper_names,
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=phase_turn,
            timeout_s=timeout_s,
            max_nodes=max_nodes,
            proof_cache=session.proof_cache,
            phase="helper_only_salvage",
        )
        sync_proof_state_to_graph(
            proof_state,
            dossier,
            session=session,
            phase="helper_only_salvage_proof_state_assembly",
            turn_index=phase_turn,
        )
        if state_ok and state_proof:
            _emit_record(session, {
                **common_payload,
                "phase": "helper_only_salvage_proof_state_assembly",
                "turn_in_phase": phase_turn,
                "accepted_helpers": list(salvaged_state_helpers or ()),
                "proof_state": _safe_record(proof_state),
                "verdict": "solved_after_helper_only_salvage",
            })
            replay_helpers = tuple(dossier.verified_helper_blocks())
            helper_names_list = tuple(
                name
                for block in replay_helpers
                for name in [helper_decl_name(block)]
                if name
            )
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=action.id,
                solved=True,
                proof=state_proof,
                helpers_added=tuple(visible_accepted_helper_names),
                progress=True,
                cost_seconds=cost,
                root_candidate=RootFinalizationCandidate(
                    proof=state_proof,
                    replay_helpers=replay_helpers,
                    helper_names=helper_names_list,
                    phase="helper_only_salvage_proof_state_assembly",
                    turn_index=phase_turn,
                    source_action_id=action.id,
                    target_statement=str(
                        getattr(dossier, "root_statement", "")
                        or getattr(conv, "goal_statement", "")
                        or ""
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=state_proof,
                        phase="helper_only_salvage_proof_state_assembly",
                        turn_index=phase_turn,
                        target_statement=str(
                            getattr(dossier, "root_statement", "")
                            or getattr(conv, "goal_statement", "")
                            or ""
                        ),
                        replay_helpers=replay_helpers,
                        helper_names=helper_names_list,
                        source="helper_only_salvage_proof_state_assembly",
                    ),
                    metadata={"root_finalization_already_applied": True},
                ),
                metadata={
                    "role": action.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "solved_via": "helper_only_salvage_assembly",
                    "replay_helpers": list(replay_helpers),
                    "helper_names": list(helper_names_list),
                    "root_finalization_already_applied": True,
                    "visible_helpers_added_count": len(
                        visible_accepted_helper_names
                    ),
                },
            )

    # ---- Pathway (5): post-salvage child-closure ------------------
    if (
        proof_state is not None
        and child_tactics_enabled
        and not defer_fresh_children_to_llm
    ):
        state_ok, state_proof, ps_helpers = await _try_proof_state_child_closures(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=phase_turn,
            timeout_s=timeout_s,
            max_candidates=max_candidates,
            max_nodes=max_nodes,
            max_decl_applications=max_decl_apps,
            batch_parallelism=parallelism,
            proof_cache=session.proof_cache,
        )
        sync_proof_state_to_graph(
            proof_state,
            dossier,
            session=session,
            phase="helper_only_salvage_root_check",
            turn_index=phase_turn,
        )
        if state_ok and state_proof:
            _emit_record(session, {
                **common_payload,
                "phase": "helper_only_salvage_root_check",
                "turn_in_phase": phase_turn,
                "accepted_helpers": list(ps_helpers or ()),
                "proof_state": _safe_record(proof_state),
                "verdict": "solved_after_helper_only_salvage",
            })
            replay_helpers = tuple(dossier.verified_helper_blocks())
            helper_names_list = tuple(
                name
                for block in replay_helpers
                for name in [helper_decl_name(block)]
                if name
            )
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=action.id,
                solved=True,
                proof=state_proof,
                helpers_added=tuple(visible_accepted_helper_names),
                progress=True,
                cost_seconds=cost,
                root_candidate=RootFinalizationCandidate(
                    proof=state_proof,
                    replay_helpers=replay_helpers,
                    helper_names=helper_names_list,
                    phase="helper_only_salvage_root_check",
                    turn_index=phase_turn,
                    source_action_id=action.id,
                    target_statement=str(
                        getattr(dossier, "root_statement", "")
                        or getattr(conv, "goal_statement", "")
                        or ""
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=state_proof,
                        phase="helper_only_salvage_root_check",
                        turn_index=phase_turn,
                        target_statement=str(
                            getattr(dossier, "root_statement", "")
                            or getattr(conv, "goal_statement", "")
                            or ""
                        ),
                        replay_helpers=replay_helpers,
                        helper_names=helper_names_list,
                        source="helper_only_salvage_root_check",
                    ),
                    metadata={"root_finalization_already_applied": True},
                ),
                metadata={
                    "role": action.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "solved_via": "helper_only_salvage_child_closure",
                    "replay_helpers": list(replay_helpers),
                    "helper_names": list(helper_names_list),
                    "root_finalization_already_applied": True,
                    "visible_helpers_added_count": len(
                        visible_accepted_helper_names
                    ),
                },
            )

    # ---- Pathway (6): root tactic close ---------------------------
    # H6 fix (2026-05-08): charge inline cascade Lean spend against the
    # ``helper_only_salvage`` budget. Without this, the inline cascade
    # ignores the budget the factory allocated for it, and a session
    # with many failed turns can spend 12s/turn × N turns on tactic
    # close work beyond the 120s budget cap. Skip the call entirely
    # once the budget is exhausted.
    inline_timeout_s = _budget_clamped_timeout(
        session, action_id="helper_only_salvage", requested_s=timeout_s
    )
    if max_candidates > 0 and inline_timeout_s > 0.0:
        tactic_started = time.monotonic()
        helper_blocks = dossier.verified_helper_blocks()
        root_tactic = await try_close_root_with_active_lift(
            lean=lean,
            goal_statement=conv.goal_statement,
            preamble=_proof_state_acceptance_preamble(conv),
            helpers=helper_blocks,
            active_root_targets=tuple(
                item
                for item in list(getattr(dossier, "active_root_targets", []) or ())
                if isinstance(item, dict)
            ),
            active_root_frame_helper_blocks=dossier.verified_helper_blocks(),
            timeout_s=inline_timeout_s,
            max_candidates=max(1, max_candidates),
            suppress_solution_placeholders=bool(
                getattr(conv, "suppress_solution_placeholders", True)
            ),
            opaque_mode=bool(getattr(conv, "opaque_mode", True)),
            allow_official_answer_visibility=bool(
                getattr(conv, "allow_official_answer_visibility", False)
            ),
            official_answer_payload_present=getattr(
                conv,
                "official_answer_payload_present",
                getattr(dossier, "official_answer_payload_present", None),
            ),
            tactic_source_suppression_records=tactic_source_suppression_records(
                session
            ),
            tactic_source_suppression_helper_blocks=helper_blocks,
            attempt_observer=dossier_lean_attempt_observer(
                dossier,
                "salvage_root_tactic",
            ),
        )
        tactic_elapsed = time.monotonic() - tactic_started
        _charge_inline_cascade_budget(
            session, action_id="helper_only_salvage", elapsed_s=tactic_elapsed
        )
        success_attempt = next(
            (
                attempt
                for attempt in root_tactic.attempts
                if isinstance(attempt, dict) and attempt.get("ok")
            ),
            None,
        )
        root_tactic_record = {
            **common_payload,
            "phase": "helper_only_salvage_root_tactic",
            "turn_in_phase": phase_turn,
            "accepted_helpers": list(accepted_helper_names),
            "tactic_candidate_count": root_tactic.candidate_count,
            **tactic_attempt_telemetry_fields(root_tactic.attempts),
            "tactic_attempts": root_tactic.attempts[:10],
            "tactic_success_attempt": success_attempt,
            "tactic_elapsed_s": root_tactic.elapsed_s,
            "tactic_exit_reason": root_tactic.exit_reason,
            "verdict": (
                "tactic_solved" if root_tactic.ok else "tactic_rejected"
            ),
        }
        root_tactic_contract_status: Dict[str, Any] = {}
        if root_tactic.ok and root_tactic.proof:
            root_tactic_contract_status = root_tactic_success_contract_status(
                dossier,
                proof=root_tactic.proof,
                helper_blocks=dossier.verified_helper_blocks(),
                success_attempt=success_attempt,
                phase="helper_only_salvage_root_tactic",
                turn_index=phase_turn,
                target_statement=root_target_statement,
            )
            root_tactic_record["route_assembly_contract_status"] = (
                root_tactic_contract_status
            )
            if not bool(root_tactic_contract_status.get("ready")):
                root_tactic_record["verdict"] = "root_route_contract_not_ready"
                root_tactic_record["route_contract_verdict"] = str(
                    root_tactic_contract_status.get("verdict") or ""
                )
        _emit_record(session, root_tactic_record)
        if (
            root_tactic.ok
            and root_tactic.proof
            and bool(root_tactic_contract_status.get("ready"))
        ):
            replay_helpers = dossier.verified_helper_blocks()
            route_helper_names = tuple(
                str(name or "").strip()
                for name in list(root_tactic_contract_status.get("helper_names") or [])
                if str(name or "").strip()
            )
            if not route_helper_names:
                route_helper_names = tuple(
                    helper_decl_name(b) or ""
                    for b in replay_helpers
                    if helper_decl_name(b)
                )
            route_replay_helpers = [
                block
                for block in replay_helpers
                if (helper_decl_name(block) or "") in set(route_helper_names)
            ]
            if not route_replay_helpers:
                route_replay_helpers = list(replay_helpers)
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=action.id,
                solved=True,
                proof=root_tactic.proof,
                helpers_added=tuple(visible_accepted_helper_names),
                progress=True,
                cost_seconds=cost,
                root_candidate=RootFinalizationCandidate(
                    proof=root_tactic.proof,
                    replay_helpers=tuple(route_replay_helpers),
                    helper_names=tuple(route_helper_names),
                    phase="helper_only_salvage_root_tactic",
                    turn_index=phase_turn,
                    source_action_id=action.id,
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
                    target_statement=root_target_statement,
                    # Helper-free closes have no route to bind; requiring a route
                    # contract would reject a Lean-accepted proof.  Match
                    # try_root_tactic_close's conditional flag.
                    require_route_contract=(
                        str(root_tactic_contract_status.get("verdict") or "")
                        != "root_tactic_no_helper_dependencies"
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=root_tactic.proof,
                        phase="helper_only_salvage_root_tactic",
                        turn_index=phase_turn,
                        target_statement=root_target_statement,
                        replay_helpers=tuple(route_replay_helpers),
                        helper_names=tuple(route_helper_names),
                        output=str(
                            (success_attempt or {}).get("output")
                            or (success_attempt or {}).get("output_preview")
                            or ""
                        ),
                        source="root_tactic",
                    ),
                    metadata={
                        "route_assembly_contract_status": dict(
                            root_tactic_contract_status
                        )
                    },
                ),
                metadata={
                    "role": action.role,
                    "conv_turn_index_offset": conv_turn_offset,
                    "conv_turn_index_absolute": absolute_turn,
                    "conv_turn_index_phase": phase_turn,
                    **_turn_budget_metadata(common_payload),
                    "solved_via": "helper_only_salvage_root_tactic",
                    "replay_helpers": list(route_replay_helpers),
                    "helper_names": list(route_helper_names),
                    "route_id": str(
                        root_tactic_contract_status.get("route_id")
                        or root_tactic_contract_status.get("created_route_id")
                        or ""
                    ),
                    "visible_helpers_added_count": len(
                        visible_accepted_helper_names
                    ),
                },
            )
        if root_tactic.ok and root_tactic.proof:
            replay_helpers = dossier.verified_helper_blocks()
            helper_names_list = [
                helper_decl_name(b) or "" for b in replay_helpers if helper_decl_name(b)
            ]
            dossier.record_attempt(
                phase="helper_only_salvage_root_tactic",
                turn_index=phase_turn,
                proof=root_tactic.proof,
                helper_names=helper_names_list,
                verdict="root_route_contract_not_ready",
                metadata={
                    "route_assembly_contract_status": root_tactic_contract_status,
                },
            )

    # H6: when the inline tactic-close was skipped because the
    # helper_only_salvage budget exhausted, surface a record so RCA can
    # see the cascade WAS attempted, just bounded out.
    if max_candidates > 0 and inline_timeout_s <= 0.0:
        _emit_record(session, {
            **common_payload,
            "phase": "helper_only_salvage_root_tactic",
            "turn_in_phase": phase_turn,
            "tactic_candidate_count": 0,
            "tactic_attempts": [],
            "tactic_exit_reason": "helper_only_salvage_budget_exhausted",
            "verdict": "tactic_skipped",
        })

    # Salvage accepted helpers but no pathway closed root — nudge.
    if defer_fresh_children_to_llm:
        conv.append_user(
            "The controller verified helper declaration(s) from your reply "
            "and recorded additional open proof-state child goals. Recursive "
            "helper proving is enabled, so the scheduler will attack those "
            "child goals with scoped LLM sub-sessions before deterministic "
            "fallback. Then submit the main proof that assembles the root."
        )
    else:
        conv.append_user(
            "The controller verified helper declaration(s) from your "
            "reply. Now submit the main proof that assembles the root "
            "from those named helpers."
        )
    cost = time.monotonic() - started
    return MiniOutcome(
        action_id=action.id,
        solved=False,
        proof=None,
        helpers_added=tuple(visible_accepted_helper_names),
        progress=bool(
            visible_accepted_helper_names
            or accepted_parent_helper_progress
            or skeleton_route_banked
        ),
        cost_seconds=cost,
        metadata={
            "role": action.role,
            "conv_turn_index_offset": conv_turn_offset,
            "conv_turn_index_absolute": absolute_turn,
            "conv_turn_index_phase": phase_turn,
            **_turn_budget_metadata(common_payload),
            "salvage_accepted": list(salvage_result.accepted),
            "salvage_rejected": list(salvage_result.rejected),
            "lemma_dag_helper_count": len(lemma_dag_helpers),
            "visible_helpers_added_count": len(visible_accepted_helper_names),
            "lemma_dag_recorded_child_count": len(lemma_dag_child_node_ids),
            "new_child_node_ids": list(lemma_dag_child_node_ids),
            "linked_child_node_ids": list(lemma_dag_linked_child_node_ids),
            **skeleton_route_metadata,
            # Fix HIGH-#4 (2026-05-22): the previous expression
            # `bool(accepted_helper_names)` was identical to `progress`,
            # which defeated Fix 3's strict-progress accounting — bogus
            # contradiction-route helpers were classified as "strong
            # progress" and kept resetting the stagnation counter.
            # Strong helper progress now comes from the dossier's graph
            # impact ledger: accepted helpers are strong only when they
            # discharge a parent claim/variant/obligation. Novel helpers
            # without graph impact remain valuable theory progress.
            "strong_progress": _strong_progress_for_accepted_helpers(
                dossier, accepted_helper_names
            ),
            "unverified_decomposition_created": bool(
                lemma_dag_child_node_ids or skeleton_route_banked
            ),
            "deferred_fresh_children_to_recursive_helper": defer_fresh_children_to_llm,
        },
    )


# ---------------------------------------------------------------------------
# Pre-Lean lemma-DAG decomposition: H3 + MED-2 fix.
# Legacy mini_prover.py:4264-4286.
# ---------------------------------------------------------------------------


async def _run_pre_lean_lemma_dag_decomposition(
    *,
    session: Any,
    conv: Any,
    lean: Any,
    dossier: Any,
    proof_state: Any,
    lemma_dag_candidate_helpers: Sequence[str],
    helpers: Sequence[str],
    absolute_turn: int,
    phase_turn: int,
    common_payload: Dict[str, Any],
    timeout_s: float,
) -> None:
    """Run the pre-Lean lemma-DAG decomposition step.

    Mirrors mini_prover.py:4264-4286 — when the LLM produced helpers
    AND there is open decomposition work, walk the helpers into open
    decomposition slots BEFORE the primary Lean check. Without this,
    beam search sees stale decomposition state during the long Lean
    call.
    """

    from ensemble_prover.proof_state_executor import (
        _try_proof_state_lemma_dag_helpers,
        ensure_decomposition_task_open_for_lemma_dag_candidates,
    )

    if not (lemma_dag_candidate_helpers and proof_state is not None and dossier is not None):
        return
    if not bool(getattr(conv, "allow_helper_decomposition", True)):
        return
    # D2 gate-side fix (2026-05-09): open ad-hoc decomposition_task when
    # sorry-stubs are present so the gate below proceeds.
    if not proof_state.has_open_decomposition_task():
        lemma_dag_open_attempt = ensure_decomposition_task_open_for_lemma_dag_candidates(
            proof_state,
            lemma_dag_candidate_helpers,
            source=f"lemma_dag_helpers_volunteered:pre_lean_dag:turn={absolute_turn}",
        )
    else:
        lemma_dag_open_attempt = {}
    if not proof_state.has_open_decomposition_task():
        # MED-3 + M5: no-open-task observability record (legacy
        # mini_prover.py). Dedupe per-turn so we don't emit the event
        # from BOTH the no-proof branch and the proof-extracted branch
        # on the same turn.
        if not _already_fired_lemma_dag_skipped(session):
            _emit_record(session, {
                **common_payload,
                "lemma_dag_candidate_count": len(lemma_dag_candidate_helpers),
                "lemma_dag_open_attempt": dict(lemma_dag_open_attempt or {}),
                "verdict": "lemma_dag_no_decomposition_task_opened",
            })
            _mark_lemma_dag_skipped_fired(session)
        return

    try:
        await _try_proof_state_lemma_dag_helpers(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            helpers=lemma_dag_candidate_helpers,
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=phase_turn,
            timeout_s=timeout_s,
            proof_cache=session.proof_cache,
        )
    except Exception:
        # Decomposition primitive owns its own logging; we proceed to
        # the Lean check regardless.
        return
    sync_proof_state_to_graph(
        proof_state,
        dossier,
        session=session,
        phase="proof_state_lemma_dag_decomposition",
        turn_index=phase_turn,
    )


# ---------------------------------------------------------------------------
# Inline post-failure cascade: H7 + MED-1 fix.
# ---------------------------------------------------------------------------


async def _run_post_failure_cascade_inline(
    *,
    session: Any,
    action: Any,
    conv: Any,
    dossier: Any,
    proof_state: Any,
    proof: str,
    helpers: List[str],
    lemma_dag_candidate_helpers: List[str],
    check_lemmas: List[str],
    context_helpers: List[str],
    lean_verdict: Any,
    lean_elapsed: float,
    common_payload: Dict[str, Any],
    absolute_turn: int,
    phase_turn: int,
    conv_turn_offset: int,
    started: float,
    max_turns_footer: int,
    searcher: Any,
    llm_output: str = "",
    turn_giveup: Optional[Dict[str, str]] = None,
) -> MiniOutcome:
    """Run the post-failure cascade inline with full legacy telemetry.

    H7 fix: emits ``proof_state_update``, child-closure-solved,
    helper-salvage-assembly-solved, helper-salvage-root-tactic-solved/-rejected,
    and the rejected-with-feedback record.

    MED-1 fix: emits ``dossier.record_attempt(verdict=tactic_rejected)``
    for the tactic-close arm of the salvage cascade.
    """

    from ensemble_prover.mini_prover import (
        _bank_helpers_as_proposed,
        _classify_giveup_signal,
        _drop_last_assistant_if_content,
    )
    from ensemble_prover.mini_session.turn import run_post_failure_cascade

    action_available = getattr(session, "action_available", None)
    raw_depth_cap = getattr(session, "max_recursion_depth", 3)
    depth_cap = int(raw_depth_cap if raw_depth_cap is not None else 3)
    recursion_depth = int(getattr(session, "recursion_depth", 0) or 0)
    depth_allows_recursive_helper = depth_cap <= 0 or recursion_depth < depth_cap
    defer_rejected_helper_children_to_llm = (
        bool(action_available("recursive_helper_prover"))
        if callable(action_available)
        else False
    )
    defer_rejected_helper_children_to_llm = bool(
        defer_rejected_helper_children_to_llm
        and depth_allows_recursive_helper
        and session.dossier is not None
        and session.lean is not None
        and session.conv is not None
        and getattr(session, "prover_client", None) is not None
        and proof_state is not None
    )
    cascade_timeout_s = _budget_clamped_timeout(
        session,
        action_id="post_lean_failure",
        requested_s=action.proof_state_child_tactic_timeout_s,
    )
    post_failure_budget_exhausted = False
    try:
        budget = getattr(session, "budgets", {}).get("post_lean_failure")
        post_failure_budget_exhausted = bool(
            budget is not None
            and hasattr(budget, "exhausted")
            and budget.exhausted()
        )
    except Exception:
        post_failure_budget_exhausted = False
    selected_work_record = dict(getattr(session, "selected_work_item_record", {}) or {})
    selected_work_type = str(selected_work_record.get("work_type") or "").strip()
    graph_native_failure_context = (
        selected_work_type in _GRAPH_NATIVE_CONVERSATION_WORK_TYPES
        and str(selected_work_record.get("mapped_action_id") or "").strip()
        in {
            "",
            action.id,
            "conversation_turn",
            "conversation_turn_prove",
            "conversation_turn_refine",
        }
    )
    concrete_local_repair_target = _has_concrete_local_repair_target(
        proof=proof,
        helpers=helpers,
        lemma_dag_candidate_helpers=lemma_dag_candidate_helpers,
    )
    post_lean_giveup_preview = turn_giveup
    if post_lean_giveup_preview is None:
        try:
            post_lean_giveup_preview = _classify_giveup_signal(
                str(llm_output or ""),
                proof,
                require_structural_collapse=False,
            )
        except Exception:
            post_lean_giveup_preview = None
    defer_deterministic_search = _should_defer_post_failure_search(
        proof=proof,
        helpers=helpers,
        lemma_dag_candidate_helpers=lemma_dag_candidate_helpers,
        proof_state=proof_state,
        proof_state_child_tactics_enabled=action.proof_state_child_tactics_enabled,
        proof_state_child_tactic_timeout_s=cascade_timeout_s,
        proof_state_child_tactic_max_candidates=(
            action.proof_state_child_tactic_max_candidates
        ),
        proof_state_decl_application_limit=action.proof_state_decl_application_limit,
        phase_turn=phase_turn,
        max_turns=max_turns_footer,
        graph_native_failure_context=graph_native_failure_context,
        repair_self_check_status=str(
            common_payload.get("repair_self_check_status")
            or common_payload.get("repair_self_check_missing_kind")
            or ""
        ),
        giveup_cluster=str((post_lean_giveup_preview or {}).get("cluster") or ""),
    )
    force_local_repair_first = bool(concrete_local_repair_target)
    if defer_deterministic_search:
        try:
            session.repair_first_until_conversation_turn = max(
                int(getattr(session, "_conversation_turn_count", 0) or 0) + 1,
                int(getattr(session, "repair_first_until_conversation_turn", 0) or 0),
            )
            session.repair_first_reason = "post_failure_local_repair"
        except Exception:
            pass
        _emit_record(session, {
            "phase": "post_failure_repair_first",
            "turn_in_phase": phase_turn,
            "role": str(getattr(conv, "role", "") or action.role or "prove"),
            "proof_chars": len(str(proof or "")),
            "proof_lines": len(str(proof or "").splitlines()),
            "verdict": "deterministic_search_deferred",
        })
    cascade_started = time.monotonic()
    local_repair_first = bool(force_local_repair_first)
    local_micro_theory_suppresses_library = bool(
        common_payload.get("local_micro_theory_search_suppressed")
    )
    local_micro_theory_grounding_escape = False
    local_micro_theory_grounding_unknown_identifier = ""
    if local_micro_theory_suppresses_library and not local_repair_first:
        pre_cascade_failure_analysis = (
            _analyze_feedback_for_local_micro_theory_grounding(lean_verdict)
        )
        (
            local_micro_theory_grounding_escape,
            local_micro_theory_grounding_unknown_identifier,
        ) = _local_micro_theory_allows_post_failure_api_grounding(
            session,
            pre_cascade_failure_analysis,
            target_statement=str(
                common_payload.get("graph_native_goal_statement")
                or common_payload.get("selected_target_statement")
                or selected_work_record.get("target_statement")
                or getattr(conv, "goal_statement", "")
                or ""
            ),
        )
        if local_micro_theory_grounding_escape:
            common_payload[
                "local_micro_theory_unknown_identifier_grounding_escape"
            ] = True
            common_payload[
                "local_micro_theory_unknown_identifier"
            ] = local_micro_theory_grounding_unknown_identifier
            _emit_record(session, {
                "phase": "session_local_micro_theory",
                "turn_in_phase": phase_turn,
                "role": str(getattr(conv, "role", "") or action.role or "prove"),
                "unknown_identifier": local_micro_theory_grounding_unknown_identifier,
                "verdict": "unknown_identifier_grounding_escape",
            })
    suppress_library_first_repair = bool(
        local_repair_first
        or (
            local_micro_theory_suppresses_library
            and not local_micro_theory_grounding_escape
        )
    )
    graph_native_child_repair_retrieval_target = bool(
        graph_native_failure_context
        and (
            common_payload.get("graph_native_goal_statement")
            or common_payload.get("selected_target_statement")
            or selected_work_record.get("target_statement")
        )
    )
    suppress_repair_retrieval = bool(
        suppress_library_first_repair
        and not graph_native_child_repair_retrieval_target
    )
    if (
        local_micro_theory_suppresses_library
        and not local_repair_first
        and suppress_library_first_repair
    ):
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment("mini_premise_zero_hit_repair_retrieval_suppressed", 1)
    try:
        cascade = await run_post_failure_cascade(
            conv=conv,
            lean=session.lean,
            dossier=dossier,
            proof_state=proof_state,
            proof=proof,
            helpers=helpers,
            lemma_dag_candidate_helpers=lemma_dag_candidate_helpers,
            check_lemmas=check_lemmas,
            context_helpers=context_helpers,
            feedback_result=lean_verdict.feedback_result,
            feedback_source=lean_verdict.feedback_source,
            proof_cache=session.proof_cache,
            searcher=None if suppress_repair_retrieval else searcher,
            repair_retrieval_enabled=(
                bool(action.repair_retrieval_enabled)
                and not post_failure_budget_exhausted
                and not suppress_repair_retrieval
            ),
            repair_retrieval_top_k=action.repair_retrieval_top_k,
            proof_state_child_tactics_enabled=(
                bool(action.proof_state_child_tactics_enabled)
                and cascade_timeout_s > 0.0
                and not post_failure_budget_exhausted
                and not local_repair_first
            ),
            proof_state_child_tactic_timeout_s=(
                0.0 if local_repair_first else cascade_timeout_s
            ),
            proof_state_child_tactic_max_candidates=(
                0
                if local_repair_first
                else action.proof_state_child_tactic_max_candidates
            ),
            proof_state_child_goal_limit=action.proof_state_child_goal_limit,
            proof_state_decl_application_limit=action.proof_state_decl_application_limit,
            proof_state_batch_parallelism=action.proof_state_batch_parallelism,
            raw_feedback=action.raw_feedback,
            lean_check_tool_enabled=action.lean_check_tool_enabled,
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=phase_turn,
            max_turns=max_turns_footer,
            role=conv.role,
            llm_output=llm_output,
            # opaque_mode default per Conversation.opaque_mode (mini_prover.py:435):
            # default=True (the no-answer-leaderboard target variant). Wrong
            # default would invert the answer_opaque cluster's nudge framing.
            opaque_mode=bool(getattr(conv, "opaque_mode", True)),
            allow_official_answer_visibility=bool(
                getattr(conv, "allow_official_answer_visibility", False)
            ),
            official_answer_payload_present=getattr(
                conv,
                "official_answer_payload_present",
                getattr(dossier, "official_answer_payload_present", None),
            ),
            allow_helper_decomposition=bool(
                getattr(conv, "allow_helper_decomposition", True)
            ),
            # Phase 2 (2026-05-09): plumb the session's recursion depth so
            # the give-up nudge can swap to "depth-cap reached" framing in
            # child sessions spawned by RecursiveHelperProverAction.
            recursion_depth=int(getattr(session, "recursion_depth", 0) or 0),
            max_recursion_depth=int(
                getattr(session, "max_recursion_depth", 3)
                if getattr(session, "max_recursion_depth", 3) is not None
                else 3
            ),
            defer_fresh_helper_children_to_llm=defer_rejected_helper_children_to_llm,
            proof_state_failure_context_enabled=not graph_native_failure_context,
            defer_proof_state_child_search=(
                defer_deterministic_search or force_local_repair_first
            ),
            repair_goal_statement=str(
                common_payload.get("graph_native_goal_statement")
                or (
                    common_payload.get("selected_target_statement")
                    or selected_work_record.get("target_statement")
                    if graph_native_failure_context
                    else ""
                )
                or ""
            ),
            selected_work_item=dict(
                getattr(session, "selected_work_item_record", {}) or {}
            ),
            target_statement=str(
                common_payload.get("graph_native_goal_statement")
                or common_payload.get("selected_target_statement")
                or (
                    selected_work_record.get("target_statement")
                    if graph_native_failure_context
                    else ""
                )
                or (
                    ""
                    if graph_native_failure_context
                    else getattr(conv, "goal_statement", "")
                )
                or ""
            ),
            event_context={
                "session_scope": str(getattr(session, "scope", "") or ""),
                "conv_turn_absolute": common_payload.get(
                    "conv_turn_index_absolute"
                ),
                "conv_turn_index_absolute": common_payload.get(
                    "conv_turn_index_absolute"
                ),
            },
            suppress_nonstructural_giveup_for_repair=force_local_repair_first,
            include_local_repair_diagnostic_spans=force_local_repair_first,
        )
        try:
            session.last_post_failure_result = cascade
        except Exception:
            pass
    finally:
        _charge_inline_cascade_budget(
            session,
            action_id="post_lean_failure",
            elapsed_s=time.monotonic() - cascade_started,
        )

    # H7: proof_state_update + child-closure observability records when
    # the cascade engaged proof_state but did NOT solve. The cascade
    # itself does not emit these high-level verdicts; we mirror legacy
    # mini_prover.py:4589-4598 + 4626-4654 here.
    if proof_state is not None and cascade.proof_state_update is not None:
        _emit_record(session, {
            "phase": "proof_state_update",
            "turn_in_phase": phase_turn,
            "update": cascade.proof_state_update,
            "node_retrieval": cascade.proof_state_retrieval,
            "proof_state": _safe_record(proof_state),
            "verdict": "proof_state_updated",
        })

    err = ""
    if lean_verdict.feedback_result is not None:
        err = (getattr(lean_verdict.feedback_result, "output", "") or "").strip() or "(no output)"
    else:
        err = (
            "answer-safe Lean feedback unavailable; raw checker-preamble "
            "output suppressed"
        )

    lean_error_type = ""
    if isinstance(cascade.failure_analysis, dict):
        lean_error_type = str(cascade.failure_analysis.get("error_type") or "").strip()
    lean_failure_signature = (
        _lean_failure_wall_signature(cascade.failure_analysis)
        if isinstance(cascade.failure_analysis, dict)
        else ""
    )
    local_repair_quota_record: Dict[str, Any] = {}
    selected_repair_ticket_id = str(
        getattr(session, "_repair_ticket_selected_id", "") or ""
    ).strip()
    if (
        concrete_local_repair_target
        and not cascade.solved
        and not cascade.giveup_cluster
        and not cascade.target_integrity_bypass_local_repair
        and not selected_repair_ticket_id
    ):
        arm = getattr(session, "arm_local_repair_quota", None)
        if callable(arm):
            local_repair_reason = (
                "post_lean_code_generation_repair"
                if lean_error_type == "parse_error"
                else "post_lean_concrete_local_repair"
            )
            selected_work_record = dict(
                getattr(session, "selected_work_item_record", {}) or {}
            )
            if lean_error_type == "parse_error":
                selected_work_record["formalization_failure_class"] = (
                    "code_generation"
                )
            try:
                local_repair_quota_record = dict(
                    arm(
                        action_id=action.id,
                        reason=local_repair_reason,
                        failure_signature=lean_failure_signature,
                        requested_turns=1,
                        selected_work_record=selected_work_record,
                    )
                    or {}
                )
            except Exception:
                local_repair_quota_record = {"armed": False, "verdict": "arm_error"}
    elif (
        concrete_local_repair_target
        and not cascade.solved
        and bool(cascade.target_integrity_bypass_local_repair)
    ):
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment("mini_session_target_integrity_local_repair_bypassed", 1)
        _emit_record(session, {
            "phase": "target_integrity_local_repair",
            "turn_in_phase": phase_turn,
            "role": str(getattr(conv, "role", "") or action.role or "prove"),
            "signals": list(cascade.target_integrity_signals),
            "target_integrity_signals": list(cascade.target_integrity_signals),
            "target_integrity_signal_kinds": [
                str(signal.get("kind") or "")
                for signal in cascade.target_integrity_signals
            ],
            "verdict": "local_repair_bypassed",
        })

    skeleton_route_banked, skeleton_route_metadata = _skeleton_route_metadata(
        common_payload
    )
    if cascade.solved:
        # H3 fix (2026-05-08): emit the legacy verdict that matches the
        # cascade phase that solved, instead of collapsing all paths to
        # ``solved_after_proof_state_child``. RCA tooling filters by
        # verdict tag.
        _solved_via_to_verdict = {
            "proof_state_child": "solved_after_proof_state_child",
            "helper_salvage_assembly": "solved_after_helper_salvage",
            "helper_salvage_root_tactic": "tactic_solved",
        }
        verdict_name = _solved_via_to_verdict.get(
            cascade.solved_via or "",
            "solved_after_proof_state_child",
        )
        # The cascade already passed through root finalization; emit a top-level solved
        # record mirroring legacy mini_prover.py:4625-4654.
        _emit_record(session, {
            **common_payload,
            "dossier_context_helpers": list(context_helpers),
            "replay_helpers": list(check_lemmas),
            "lean_ok": False,
            "lean_output": err,
            "lean_failure_analysis": cascade.failure_analysis,
            "lean_feedback_source": lean_verdict.feedback_source,
            "lean_feedback_mode": "post_failure_cascade_solved",
            "repair_retrieval": cascade.repair_retrieval_record,
            "proof_state_update": cascade.proof_state_update,
            "proof_state_retrieval": cascade.proof_state_retrieval,
            "proof_state_helpers": cascade.proof_state_helpers,
            "failure_residual_obligation_node_ids": list(
                getattr(cascade, "failure_residual_obligation_node_ids", []) or []
            ),
            "failure_residual_replan_node_ids": list(
                getattr(cascade, "failure_residual_replan_node_ids", []) or []
            ),
            "rejected_helper_triage": {
                "accepted_helpers": list(cascade.rejected_helper_triage_accepted),
                "new_child_node_ids": list(cascade.rejected_helper_child_node_ids),
                "deferred_fresh_children_to_recursive_helper": bool(
                    cascade.deferred_rejected_helper_children_to_recursive_helper
                ),
            },
            "lean_elapsed_s": lean_elapsed,
            "lean_failure_signature": lean_failure_signature,
            "solved_via": cascade.solved_via,
            "verdict": verdict_name,
        })
        cost = time.monotonic() - started
        root_target_statement = str(
            getattr(dossier, "root_statement", "")
            or getattr(conv, "goal_statement", "")
            or ""
        )
        cascade_helper_names = [
            helper_decl_name(block) or ""
            for block in check_lemmas
            if helper_decl_name(block)
        ]
        raw_cascade_helpers_added = list(cascade.salvaged_helper_names) + list(
            cascade.rejected_helper_triage_accepted
        )
        visible_cascade_helpers_added = (
            dossier.visible_accepted_helper_names(raw_cascade_helpers_added)
            if hasattr(dossier, "visible_accepted_helper_names")
            else list(raw_cascade_helpers_added)
        )
        return MiniOutcome(
            action_id=action.id,
            solved=True,
            proof=cascade.proof,
            helpers_added=tuple(visible_cascade_helpers_added),
            progress=True,
            cost_seconds=cost,
            root_candidate=RootFinalizationCandidate(
                proof=cascade.proof or "",
                replay_helpers=tuple(check_lemmas),
                helper_names=tuple(cascade_helper_names),
                phase=cascade.solved_via or "post_failure_cascade_inline",
                turn_index=phase_turn,
                source_action_id=action.id,
                target_statement=root_target_statement,
                verification_certificate=root_verification_certificate(
                    accepted=True,
                    proof=cascade.proof or "",
                    phase=cascade.solved_via or "post_failure_cascade_inline",
                    turn_index=phase_turn,
                    target_statement=root_target_statement,
                    replay_helpers=tuple(check_lemmas),
                    helper_names=tuple(cascade_helper_names),
                    source="post_failure_cascade_inline",
                ),
                metadata={
                    **skeleton_route_metadata,
                    "root_finalization_already_applied": True,
                },
            ),
            metadata={
                "role": action.role,
                "conv_turn_index_offset": conv_turn_offset,
                "conv_turn_index_absolute": absolute_turn,
                "conv_turn_index_phase": phase_turn,
                **_turn_budget_metadata(common_payload),
                **skeleton_route_metadata,
                "solved_via": cascade.solved_via or "post_failure_cascade_inline",
                "verdict": verdict_name,
                "lean_verdict": "lean_rejected",
                "lean_error_type": lean_error_type,
                "lean_failure_signature": lean_failure_signature,
                "lean_elapsed_s": lean_elapsed,
                "lean_feedback_source": lean_verdict.feedback_source,
                "llm_response_recorded": common_payload.get(
                    "llm_response_recorded"
                ),
                "answer_safe_recheck_verifier_only_retry": bool(
                    common_payload.get(
                        "answer_safe_recheck_verifier_only_retry"
                    )
                ),
                "answer_safe_recheck_retry_attempts": int(
                    common_payload.get("answer_safe_recheck_retry_attempts", 0)
                    or 0
                ),
                "answer_safe_recheck_retry_timeout_s": common_payload.get(
                    "answer_safe_recheck_retry_timeout_s"
                ),
                "replay_helpers": list(check_lemmas),
                "helper_names": list(cascade_helper_names),
                "root_finalization_already_applied": True,
                **_repair_self_check_metadata(common_payload),
                "rejected_helper_triage_accepted_count": len(
                    cascade.rejected_helper_triage_accepted
                ),
                "visible_helpers_added_count": len(visible_cascade_helpers_added),
                "rejected_helper_child_node_count": len(
                    cascade.rejected_helper_child_node_ids
                ),
                "rejected_helper_linked_child_node_count": len(
                    getattr(cascade, "rejected_helper_linked_child_node_ids", [])
                ),
            },
        )

    # MED-1: when the salvage cascade ran the root-tactic close arm
    # but did not solve, legacy mini_prover.py:4787-4798 records a
    # tactic_rejected attempt on the dossier. The orchestrator in
    # post_failure.py does not own this; we replicate it here when the
    # cascade exposed a salvage but did not solve.
    if (
        dossier is not None
        and cascade.salvaged_helper_names
        and cascade.helper_salvage_root_tactic_record is not None
        and not cascade.solved
        and int(action.proof_state_child_tactic_max_candidates or 0) > 0
    ):
        try:
            dossier.record_attempt(
                phase="helper_salvage_root_tactic",
                turn_index=phase_turn,
                proof="",
                helper_names=list(cascade.salvaged_helper_names),
                verdict="tactic_rejected",
                error_type="",
                metadata={
                    "tactic_exit_reason": "tactic_did_not_close_root",
                },
            )
        except Exception:
            pass

    # Cascade did not solve — append feedback for the next turn AND
    # emit the rejected-with-feedback recorder record (H7).
    if cascade.feedback_text:
        if cascade.giveup_cluster or cascade.target_integrity_signals:
            _drop_last_assistant_if_content(conv, llm_output)
        try:
            from ensemble_prover.mini_prover import (
                _repair_payload_from_failure_analysis,
            )

            repair_payload = _repair_payload_from_failure_analysis(
                cascade.failure_analysis,
            )
        except Exception:
            repair_payload = None
        conv.append_user(cascade.feedback_text, repair_payload=repair_payload)

    if cascade.giveup_cluster:
        # Give-up/off-ramp responses may contain parseable helper stubs
        # that describe the work the model is avoiding. Do not bank those
        # stubs or leave them for lemma-DAG actions; the next step is an
        # active-proof pivot, not recursive proof of the abandoned bridge.
        banked_proposed_names = []
        session.last_turn_extraction = None
    else:
        banked_proposed_names = _bank_helpers_as_proposed(
            dossier,
            helpers,
            phase=str(getattr(conv, "role", "prove") or "prove"),
            turn_index=int(absolute_turn or 0),
            fallback_helpers=lemma_dag_candidate_helpers,
            goal_statement=str(getattr(conv, "goal_statement", "") or ""),
            allow_helper_decomposition=bool(
                getattr(conv, "allow_helper_decomposition", True)
            ),
        )

    helper_salvage_block: Optional[Dict[str, Any]] = None
    if cascade.salvaged_helper_names:
        helper_salvage_block = {
            "accepted": list(cascade.salvaged_helper_names),
            "rejected": [],
            "skipped": [],
        }
    rejected_record: Dict[str, Any] = {
        **common_payload,
        "dossier_context_helpers": list(context_helpers),
        "replay_helpers": list(check_lemmas),
        "lean_ok": False,
        "lean_output": err,
        "lean_failure_analysis": cascade.failure_analysis,
        "lean_feedback_source": lean_verdict.feedback_source,
        "lean_feedback_mode": cascade.feedback_mode,
        "repair_retrieval": cascade.repair_retrieval_record,
        "proof_state_update": cascade.proof_state_update,
        "proof_state_retrieval": cascade.proof_state_retrieval,
        "proof_state_helpers": cascade.proof_state_helpers,
        "failure_residual_obligation_node_ids": list(
            getattr(cascade, "failure_residual_obligation_node_ids", []) or []
        ),
        "failure_residual_replan_node_ids": list(
            getattr(cascade, "failure_residual_replan_node_ids", []) or []
        ),
        "rejected_helper_triage": {
            "accepted_helpers": list(cascade.rejected_helper_triage_accepted),
            "new_child_node_ids": list(cascade.rejected_helper_child_node_ids),
            "deferred_fresh_children_to_recursive_helper": bool(
                cascade.deferred_rejected_helper_children_to_recursive_helper
            ),
        },
        "lean_elapsed_s": lean_elapsed,
        "lean_failure_signature": lean_failure_signature,
        "helper_salvage": helper_salvage_block,
        "post_failure_repair_first_deferred": bool(defer_deterministic_search),
        "local_repair_target": bool(concrete_local_repair_target),
        "local_repair_quota_armed": bool(
            local_repair_quota_record.get("armed")
        ),
        "local_repair_quota_record": dict(local_repair_quota_record),
        "local_repair_giveup_suppressed": bool(
            cascade.local_repair_giveup_suppressed
        ),
        "suppressed_giveup_cluster": cascade.suppressed_giveup_cluster,
        "suppressed_giveup_match": cascade.suppressed_giveup_match,
        "local_repair_diagnostics_included": bool(
            cascade.local_repair_diagnostics_included
        ),
        "target_integrity_signals": list(cascade.target_integrity_signals),
        "target_integrity_bypass_local_repair": bool(
            cascade.target_integrity_bypass_local_repair
        ),
        "target_integrity_disable_proof_state_repair": bool(
            cascade.target_integrity_disable_proof_state_repair
        ),
        "target_integrity_obligation_node_ids": list(
            cascade.target_integrity_obligation_node_ids
        ),
        "target_integrity_replan_node_ids": list(
            cascade.target_integrity_replan_node_ids
        ),
        "target_integrity_adjudication_materialized": bool(
            cascade.target_integrity_adjudication_materialized
        ),
        "banked_proposed_helpers": list(banked_proposed_names),
        "banking_suppressed_by_giveup": bool(cascade.giveup_cluster),
        "verdict": "lean_rejected",
    }
    linked_rejected_child_ids = list(
        getattr(cascade, "rejected_helper_linked_child_node_ids", []) or []
    )
    if linked_rejected_child_ids:
        rejected_record["rejected_helper_triage"]["linked_child_node_ids"] = (
            linked_rejected_child_ids
        )
    if cascade.giveup_cluster:
        # Decomposition-request redirect fired. Surface the cluster id
        # and matched phrase so post-mortem analysis can distinguish
        # "Lean rejected and we redirected to decomposition" from "Lean
        # rejected with generic feedback".
        #
        # User-mandated debug-visibility (2026-05-09): KEEP verdict
        # ``lean_rejected`` so existing RCA tooling that filters by
        # ``verdict==lean_rejected`` continues to count these turns.
        # The redirect is exposed as a parallel field, not by replacing
        # the verdict. Tools that want the redirect-specific view can
        # filter on ``redirect=="decomposition_request"`` or
        # ``giveup_cluster IS NOT NULL``.
        rejected_record["giveup_cluster"] = cascade.giveup_cluster
        rejected_record["giveup_match"] = cascade.giveup_match
        rejected_record["redirect"] = "decomposition_request"
    if cascade.target_integrity_signals:
        rejected_record["redirect"] = "target_integrity_adjudication"
        rejected_record["formalization_failure_class"] = "target_integrity"
    _emit_record(session, rejected_record)

    schedulable_decomposition_created = bool(cascade.rejected_helper_child_node_ids)
    quarantined_residual_diagnostics_created = bool(
        getattr(cascade, "failure_residual_obligation_node_ids", [])
        or getattr(cascade, "failure_residual_replan_node_ids", [])
    )
    if schedulable_decomposition_created:
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment("mini_session_schedulable_decompositions_created", 1)
    if quarantined_residual_diagnostics_created:
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment("mini_session_quarantined_residual_diagnostics_created", 1)
    unverified_decomposition_created = schedulable_decomposition_created
    target_integrity_adjudication_available = bool(
        cascade.target_integrity_obligation_node_ids
        or cascade.target_integrity_replan_node_ids
    )
    target_integrity_adjudication_created = bool(
        cascade.target_integrity_adjudication_materialized
    )
    raw_helpers_added = list(cascade.salvaged_helper_names) + list(
        cascade.rejected_helper_triage_accepted
    )
    visible_helpers_added = (
        dossier.visible_accepted_helper_names(raw_helpers_added)
        if hasattr(dossier, "visible_accepted_helper_names")
        else list(raw_helpers_added)
    )
    visible_proof_state_helpers = (
        dossier.visible_accepted_helper_names(cascade.proof_state_helpers)
        if hasattr(dossier, "visible_accepted_helper_names")
        else list(cascade.proof_state_helpers or ())
    )
    raw_parent_progress_helpers = raw_helpers_added + list(
        cascade.proof_state_helpers or ()
    )
    parent_helper_progress = _strong_progress_for_accepted_helpers(
        dossier,
        raw_parent_progress_helpers,
    )
    target_integrity_progress_suppressed = bool(
        target_integrity_adjudication_created
        and not visible_helpers_added
        and not visible_proof_state_helpers
        and not parent_helper_progress
    )
    if target_integrity_progress_suppressed:
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            try:
                increment(
                    "mini_session_target_integrity_adjudication_progress_suppressed",
                    1,
                )
            except Exception:
                pass
    progressed = bool(
        visible_helpers_added
        or visible_proof_state_helpers
        or parent_helper_progress
        or skeleton_route_banked
    )
    repair_ticket = None
    if not cascade.target_integrity_bypass_local_repair:
        repair_ticket = _repair_ticket_from_lean_rejection(
            session=session,
            action_id=action.id,
            proof=proof,
            check_lemmas=check_lemmas,
            lean_output=err,
            feedback_text=cascade.feedback_text,
            feedback_source=lean_verdict.feedback_source,
            error_type=lean_error_type,
            failure_signature=lean_failure_signature,
            turn_index=phase_turn,
            metadata={
                "feedback_mode": cascade.feedback_mode,
                "giveup_cluster": cascade.giveup_cluster,
                "failure_analysis": dict(cascade.failure_analysis or {}),
                "tool_calls_used": common_payload.get("tool_calls_used"),
                "tool_call_log": list(common_payload.get("tool_call_log") or []),
                "formalization_failure_class": (
                    "code_generation"
                    if lean_error_type == "parse_error"
                    else (
                        "api_grounding"
                        if lean_error_type == "unknown_identifier"
                        else "proof_search"
                    )
                ),
                "selected_work_item": dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                ),
            },
        )
    cost = time.monotonic() - started
    recovered_provider_capacity_defer = bool(
        str(common_payload.get("provider_defer_fingerprint") or "").strip()
        or common_payload.get("provider_turn_lane_retired")
    )
    return MiniOutcome(
        action_id=action.id,
        solved=False,
        proof=None,
        helpers_added=tuple(visible_helpers_added),
        progress=progressed,
        cost_seconds=cost,
        repair_ticket=repair_ticket,
        metadata={
            "role": action.role,
            "conv_turn_index_offset": conv_turn_offset,
            "conv_turn_index_absolute": absolute_turn,
            "conv_turn_index_phase": phase_turn,
            **_turn_budget_metadata(common_payload),
            "feedback_source": lean_verdict.feedback_source,
            "lean_verdict": "lean_rejected",
            "lean_error_type": lean_error_type,
            "lean_failure_signature": lean_failure_signature,
            "repair_ticket_id": (
                repair_ticket.ticket_id if repair_ticket is not None else ""
            ),
            "lean_elapsed_s": lean_elapsed,
            "lean_feedback_source": lean_verdict.feedback_source,
            "llm_response_recorded": common_payload.get("llm_response_recorded"),
            "answer_safe_recheck_verifier_only_retry": bool(
                common_payload.get("answer_safe_recheck_verifier_only_retry")
            ),
            "answer_safe_recheck_retry_attempts": int(
                common_payload.get("answer_safe_recheck_retry_attempts", 0) or 0
            ),
            "answer_safe_recheck_retry_timeout_s": common_payload.get(
                "answer_safe_recheck_retry_timeout_s"
            ),
            **_repair_self_check_metadata(common_payload),
            "salvaged_helper_count": len(cascade.salvaged_helper_names),
            "proof_state_helper_count": len(cascade.proof_state_helpers),
            "rejected_helper_triage_accepted_count": len(
                cascade.rejected_helper_triage_accepted
            ),
            "visible_helpers_added_count": len(visible_helpers_added),
            "visible_proof_state_helper_count": len(visible_proof_state_helpers),
            "rejected_helper_child_node_count": len(
                cascade.rejected_helper_child_node_ids
            ),
            "rejected_helper_linked_child_node_count": len(
                getattr(cascade, "rejected_helper_linked_child_node_ids", [])
            ),
            "failure_residual_obligation_node_count": len(
                getattr(cascade, "failure_residual_obligation_node_ids", []) or []
            ),
            "failure_residual_replan_node_count": len(
                getattr(cascade, "failure_residual_replan_node_ids", []) or []
            ),
            # HIGH #4 follow-up (2026-05-22): this is the post-failure
            # cascade emitter — the most-exercised one. Use the strict
            # classifier so a salvaged statement-duplicate doesn't
            # falsely reset stagnation. The cascade.solved gate is
            # preserved (a real solve is always strong progress).
            "strong_progress": (
                bool(cascade.solved)
                or parent_helper_progress
            ),
            "preserve_frontier_work": recovered_provider_capacity_defer,
            "defer_selected_frontier_action": (
                recovered_provider_capacity_defer
            ),
            "post_failure_repair_first_deferred": bool(defer_deterministic_search),
            "local_repair_target": bool(concrete_local_repair_target),
            "local_repair_quota_armed": bool(
                local_repair_quota_record.get("armed")
            ),
            "local_repair_quota_verdict": str(
                local_repair_quota_record.get("verdict") or ""
            ),
            "local_repair_giveup_suppressed": bool(
                cascade.local_repair_giveup_suppressed
            ),
            "suppressed_giveup_cluster": cascade.suppressed_giveup_cluster,
            "suppressed_giveup_match": cascade.suppressed_giveup_match,
            "local_repair_diagnostics_included": bool(
                cascade.local_repair_diagnostics_included
            ),
            "target_integrity_signals": list(cascade.target_integrity_signals),
            "target_integrity_bypass_local_repair": bool(
                cascade.target_integrity_bypass_local_repair
            ),
            "target_integrity_disable_proof_state_repair": bool(
                cascade.target_integrity_disable_proof_state_repair
            ),
            "target_integrity_obligation_node_ids": list(
                cascade.target_integrity_obligation_node_ids
            ),
            "target_integrity_replan_node_ids": list(
                cascade.target_integrity_replan_node_ids
            ),
            "target_integrity_adjudication_available": (
                target_integrity_adjudication_available
            ),
            "target_integrity_adjudication_created": (
                target_integrity_adjudication_created
            ),
            "target_integrity_adjudication_progress_suppressed": (
                target_integrity_progress_suppressed
            ),
            **skeleton_route_metadata,
            "unverified_decomposition_created": bool(
                unverified_decomposition_created or skeleton_route_banked
            ),
            "schedulable_decomposition_created": (
                schedulable_decomposition_created
            ),
            "quarantined_residual_diagnostics_created": (
                quarantined_residual_diagnostics_created
            ),
            "deferred_rejected_helper_children_to_recursive_helper": bool(
                cascade.deferred_rejected_helper_children_to_recursive_helper
            ),
            "giveup_cluster": cascade.giveup_cluster,
            "giveup_match": cascade.giveup_match,
            "banking_suppressed_by_giveup": bool(cascade.giveup_cluster),
        },
    )


# ---------------------------------------------------------------------------
# Recorder helpers.
# ---------------------------------------------------------------------------


def _emit_repair_gate_side_effect_error(
    session: Any,
    common_payload: Dict[str, Any],
    *,
    operation: str,
    exc: BaseException,
) -> None:
    """Make repair-gate side-effect failures visible without aborting the turn."""

    _emit_record(session, {
        "phase": "repair_gate_error",
        "role": common_payload.get("phase"),
        "turn_in_phase": common_payload.get("turn_in_phase"),
        "model": common_payload.get("model"),
        "verdict": "repair_gate_error",
        "lean_error_type": "repair_gate_error",
        "rejection_reason": "repair_gate_error",
        "repair_gate_operation": operation,
        "repair_gate_error": f"{type(exc).__name__}: {exc}",
    })


def _emit_llm_response_record(
    session: Any,
    common_payload: Dict[str, Any],
    *,
    proof_present: bool,
    helper_count: int,
    lemma_dag_candidate_count: int,
) -> bool:
    """Emit the role-level LLM response before any branch-specific outcome."""

    _emit_record(session, {
        **common_payload,
        "extracted_proof_present": bool(proof_present),
        "extracted_helper_count": int(helper_count or 0),
        "lemma_dag_candidate_count": int(lemma_dag_candidate_count or 0),
        "llm_response_recorded": True,
        "verdict": "llm_response",
    })
    return True


def _with_llm_response_metadata(
    session: Any,
    outcome: MiniOutcome,
    *,
    recorded: bool,
    phase: str,
    turn_in_phase: int,
    common_payload: Optional[Dict[str, Any]] = None,
) -> MiniOutcome:
    """Annotate helper-only outcomes with the response-record invariant."""

    payload = common_payload or {}
    existing_metadata = dict(outcome.metadata or {})
    skeleton_route_banked, skeleton_route_fields = _skeleton_route_metadata(
        payload,
        soft_only=not bool(existing_metadata.get("strong_progress")),
    )
    if recorded:
        metadata = {
            **existing_metadata,
            **skeleton_route_fields,
            **_repair_self_check_metadata(payload),
            **_no_proof_giveup_recovery_metadata(payload),
            **_turn_budget_metadata(payload),
            "llm_response_recorded": True,
        }
        root_candidate = getattr(outcome, "root_candidate", None)
        if skeleton_route_fields and root_candidate is not None:
            candidate_metadata = {
                **dict(getattr(root_candidate, "metadata", {}) or {}),
                **skeleton_route_fields,
            }
            try:
                root_candidate = (
                    replace(root_candidate, metadata=candidate_metadata)
                    if is_dataclass(root_candidate)
                    else root_candidate
                )
            except Exception:
                root_candidate = getattr(outcome, "root_candidate", None)
        return replace(
            outcome,
            progress=bool(outcome.progress or skeleton_route_banked),
            root_candidate=root_candidate,
            metadata=metadata,
        )
    _emit_record(session, {
        "phase": "conversation_turn_telemetry_invariant",
        "role": str(phase or ""),
        "turn_in_phase": int(turn_in_phase or 0),
        "action_id": outcome.action_id,
        "verdict": "llm_response_record_missing",
    })
    metadata = {
        **existing_metadata,
        **skeleton_route_fields,
        **_repair_self_check_metadata(payload),
        **_no_proof_giveup_recovery_metadata(payload),
        **_turn_budget_metadata(payload),
        "llm_response_recorded": False,
    }
    root_candidate = getattr(outcome, "root_candidate", None)
    if skeleton_route_fields and root_candidate is not None:
        candidate_metadata = {
            **dict(getattr(root_candidate, "metadata", {}) or {}),
            **skeleton_route_fields,
        }
        try:
            root_candidate = (
                replace(root_candidate, metadata=candidate_metadata)
                if is_dataclass(root_candidate)
                else root_candidate
            )
        except Exception:
            root_candidate = getattr(outcome, "root_candidate", None)
    return replace(
        outcome,
        progress=bool(outcome.progress or skeleton_route_banked),
        root_candidate=root_candidate,
        metadata=metadata,
    )


def _stage_verified_helper_receipt(
    session: Any,
    helper: Any,
    dossier: Any,
) -> None:
    """Stage immediately after an authoritative helper acceptance."""

    callback = getattr(session, "theory_verified_helper_accept_callback", None)
    if not callable(callback):
        return
    try:
        callback(helper, dossier)
    except Exception as exc:
        _emit_record(
            session,
            {
                "phase": "domain_theory_promotion_receipt",
                "helper_name": str(getattr(helper, "name", "") or ""),
                "error": f"{type(exc).__name__}: {exc}",
                "verdict": "helper_promotion_receipt_callback_failed",
            },
        )


def _emit_record(session: Any, record: Dict[str, Any]) -> None:
    """Send a record through the session's recorder, normalized.

    Wraps ``session._record_event`` but also writes through to the raw
    recorder when present so legacy JSONL tooling that reads
    ``recorder.record_turn`` payloads keeps working. Best-effort: any
    exception here is swallowed because telemetry must never break the
    proof loop.

    M10 fix (2026-05-08): stamp ``conv_turn_absolute`` on every per-turn
    recorder record so post-mortem JSONL grep can disambiguate the
    always-1 inner ``turn_in_phase`` from the absolute outer turn
    counter. R12.5's promise was previously fulfilled only on the outer
    ``session_action_outcome`` event.
    """

    record = dict(record)
    if "conv_turn_absolute" not in record:
        absolute = getattr(session, "_conversation_turn_count", None)
        if isinstance(absolute, int) and absolute > 0:
            record["conv_turn_absolute"] = absolute
    try:
        dossier = getattr(session, "dossier", None)
        conserve = getattr(dossier, "record_proof_idea_turn_record", None)
        if callable(conserve):
            lifecycle_record = copy.deepcopy(record)
            tool_results: Dict[str, str] = {}
            tool_arguments: Dict[str, Dict[str, Any]] = {}
            conv = getattr(session, "conv", None)
            for message in list(getattr(conv, "history", ()) or ()):
                if not isinstance(message, Mapping):
                    continue
                if str(message.get("role") or "") == "tool":
                    tool_call_id = str(message.get("tool_call_id") or "").strip()
                    if tool_call_id:
                        tool_results[tool_call_id] = str(
                            message.get("content") or ""
                        )
                for tool_call in list(message.get("tool_calls") or ()):
                    if not isinstance(tool_call, Mapping):
                        continue
                    tool_call_id = str(tool_call.get("id") or "").strip()
                    function = tool_call.get("function")
                    if not tool_call_id or not isinstance(function, Mapping):
                        continue
                    try:
                        decoded = json.loads(str(function.get("arguments") or "{}"))
                    except (TypeError, ValueError, json.JSONDecodeError):
                        continue
                    if isinstance(decoded, dict):
                        tool_arguments[tool_call_id] = decoded
            for tool_record in list(lifecycle_record.get("tool_call_log") or ()):
                if not isinstance(tool_record, dict):
                    continue
                tool_call_id = str(tool_record.get("tool_call_id") or "").strip()
                if tool_call_id in tool_results:
                    tool_record["result_text"] = tool_results[tool_call_id]
                if tool_call_id in tool_arguments:
                    tool_record["args"] = tool_arguments[tool_call_id]
            conserve(lifecycle_record)
    except Exception:
        # Strategy memory is advisory telemetry and must never interrupt the
        # proof loop. Malformed tool receipts fail closed inside the reducer.
        pass
    try:
        emit = getattr(session, "_record_event", None)
        if callable(emit):
            emit(record)
            return
        recorder = getattr(session, "recorder", None)
        if recorder is not None and hasattr(recorder, "record_turn"):
            recorder.record_turn(record)
    except Exception:
        pass


def _budget_clamped_timeout(
    session: Any,
    *,
    action_id: str,
    requested_s: float,
) -> float:
    """H6: clamp a requested timeout to the named action's remaining budget.

    Returns the smaller of the action's remaining wall-time budget and
    the requested timeout. Returns 0.0 (caller skips the work) when the
    budget is exhausted. When no budget is registered for ``action_id``,
    returns the requested timeout unchanged (matches legacy behavior of
    the inline cascade, which had no budget at all).
    """

    requested = float(requested_s or 0.0)
    if requested <= 0.0:
        return 0.0
    budgets = getattr(session, "budgets", None) or {}
    budget = budgets.get(action_id) if hasattr(budgets, "get") else None
    if budget is None:
        return requested
    if hasattr(budget, "exhausted") and budget.exhausted():
        return 0.0
    cap = float(getattr(budget, "max_total_seconds", 0.0) or 0.0)
    used = float(getattr(budget, "total_seconds", 0.0) or 0.0)
    if cap <= 0.0:
        return requested
    remaining = cap - used
    if remaining <= 0.0:
        return 0.0
    return min(requested, remaining)


def _charge_inline_cascade_budget(
    session: Any,
    *,
    action_id: str,
    elapsed_s: float,
) -> None:
    """H6: charge wall-time spent in an inline cascade against the named budget.

    The ConversationTurnAction's inline post-Lean cascade fires
    sub-pipelines (helper-only salvage, pre-Lean lemma-DAG decomposition,
    root tactic close) that the outer-loop scheduler ALSO has registered
    actions for, with their own time/invocation budgets. Without this
    accounting, the inline cascade is invisible to those budgets and
    can consume far more time than configured.
    """

    if elapsed_s <= 0.0:
        return
    budgets = getattr(session, "budgets", None) or {}
    if not hasattr(budgets, "get"):
        return
    budget = budgets.get(action_id)
    if budget is None or not hasattr(budget, "consume"):
        return
    try:
        budget.consume(float(elapsed_s))
    except Exception:
        pass


def _reset_per_turn_fired_flags(session: Any, absolute_turn: int) -> None:
    """Reset the per-turn dedup flags carried on the session.

    M5 (2026-05-08): some observability events used to fire from both
    the no-proof and proof-extracted branches in the same turn. We
    dedupe by tagging the session with the turn we last reset for; if
    the turn has advanced, clear the flags.
    """

    last_reset = getattr(session, "_per_turn_flags_turn", -1)
    if last_reset != absolute_turn:
        session._per_turn_flags_turn = absolute_turn
        session._lemma_dag_skipped_emitted = False


def _already_fired_lemma_dag_skipped(session: Any) -> bool:
    return bool(getattr(session, "_lemma_dag_skipped_emitted", False))


def _mark_lemma_dag_skipped_fired(session: Any) -> None:
    session._lemma_dag_skipped_emitted = True


def _safe_record(proof_state: Any) -> Any:
    if proof_state is None:
        return None
    try:
        to_record = getattr(proof_state, "to_record", None)
        if callable(to_record):
            return to_record()
    except Exception:
        return None
    return None


def _rejection_reason_for(verdict: Any) -> str:
    """Map PolicyVerdictKind values to legacy ``rejection_reason`` strings."""

    from ensemble_prover.mini_session.turn import PolicyVerdictKind

    kind = verdict.kind
    if kind is PolicyVerdictKind.REJECT_FORBIDDEN_CMD:
        return "forbidden_lean_command"
    if kind is PolicyVerdictKind.REJECT_CONSTRUCTION_COLLAPSE:
        return "known_answer_no_construction_collapse"
    if kind is PolicyVerdictKind.REJECT_POST_MAIN:
        return "post_main_helper_declaration"
    if kind is PolicyVerdictKind.REJECT_EXTRA_MAIN:
        return "multiple_main_proofs"
    if kind is PolicyVerdictKind.REJECT_HELPER_STUB_WITH_MAIN:
        return "helper_stub_with_main_proof"
    if kind is PolicyVerdictKind.REJECT_PREAMBLE_REDECLARATION:
        return "preamble_redeclaration_conflict"
    return kind.value


def _format_policy_rejection(
    verdict: Any,
    *,
    helpers: Optional[Sequence[str]] = None,
    goal_statement: str = "",
    banked_names: Optional[Sequence[str]] = None,
) -> str:
    """Compose the user-facing feedback for each PolicyVerdict kind.

    Mirrors the legacy phrasings at mini_prover.py:3669, 3743, 3835, 3893,
    and the post-main / extra-main user messages.
    """

    from ensemble_prover.mini_session.turn import PolicyVerdictKind

    kind = verdict.kind
    match = verdict.match or ""
    if kind is PolicyVerdictKind.REJECT_FORBIDDEN_CMD:
        return (
            "Your Lean block contains a top-level command "
            f"({match!r}). The proof block may contain helper "
            "declarations and the main proof only; do not use `#eval`, "
            "`#check`, `#print`, `import`, or `axiom` commands in proof "
            "submissions."
        )
    if kind is PolicyVerdictKind.REJECT_CONSTRUCTION_COLLAPSE:
        return (
            "Controller detected known-answer/no-construction collapse: "
            "you gave no durable helper lemma construction and only a no-op "
            "root tactic. Retry the root proof with a concrete mathematical "
            "construction. In the next Lean block, submit one active-goal "
            "proof attempt. Do not submit unproved intermediate facts as "
            "local placeholders; if an intermediate fact will not close, "
            "convert it into a proved local `have` step, a fully proved helper "
            "declaration before the main proof, or a concrete failed local "
            "`have`/`suffices` attempt with Lean diagnostics."
        )
    if kind is PolicyVerdictKind.REJECT_HELPER_STUB_WITH_MAIN:
        try:
            from ensemble_prover.mini_prover import (
                _format_invalid_helper_stub_with_main_feedback,
                _root_equivalent_sorry_stub_helper_names_from_blocks,
            )
            names = [item.strip(" `") for item in str(match or "").split(",") if item.strip()]
            root_equiv = _root_equivalent_sorry_stub_helper_names_from_blocks(
                list(helpers or []),
                goal_statement=goal_statement,
            )
            return _format_invalid_helper_stub_with_main_feedback(
                stub_names=names,
                root_equivalent_names=root_equiv,
            )
        except Exception:
            return (
                "Your Lean block mixed sorry-stub helper declarations with a "
                "main proof. Sorry stubs are not proof code. Submit one "
                "active-goal proof attempt whose helper declarations, if any, "
                "are fully proved. Do not submit unproved intermediate facts as "
                "unproved local targets inside that proof; convert needed facts "
                "into proved local `have` steps or strictly smaller helper "
                "obligations."
            )
    if kind is PolicyVerdictKind.REJECT_POST_MAIN:
        safe_match = _prompt_safe_inline_text(match, limit=400)
        return (
            "Your Lean block contains helper declaration(s) after the "
            f"main proof: {safe_match}. Helper declarations must come BEFORE "
            "the final `example : <main_goal_type> := by ...` or bare "
            "`by ...` proof block. Move those helpers above the main "
            "proof, then end the fenced Lean block with the main proof. "
            "Convert needed intermediate facts into proved local `have` steps "
            "or fully proved helper declarations before the single main proof; "
            "never restate the root as a helper."
        )
    if kind is PolicyVerdictKind.REJECT_EXTRA_MAIN:
        return (
            "Your Lean block contains multiple main-proof candidates. "
            "Submit exactly one `example : <goal> := by ...` (or bare "
            "`by ...`) block as the main proof. If you have alternative "
            "routes, encode the selected supporting facts as named helpers "
            "and reference one of them from the single main proof. Convert "
            "needed intermediate facts into proved local `have` steps or "
            "fully proved helper declarations before the single main proof."
        )
    if kind is PolicyVerdictKind.REJECT_PREAMBLE_REDECLARATION:
        names = str(verdict.match or "").strip()
        return (
            f"Your Lean block redefines declaration(s) already fixed by the "
            f"immutable preamble with DIFFERENT content: {names}. The "
            "preamble's definitions are authoritative and cannot be shadowed "
            "or replaced. Remove the redeclaration(s) and write the proof "
            "against the existing definitions; if you believe a definition "
            "unfolds differently, derive that as a proved local `have` step "
            "instead of redefining the name."
        )
    return f"Policy gate rejected this turn: {kind.value}."
