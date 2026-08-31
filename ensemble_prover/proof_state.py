"""Proof-state graph, goal normalization, and node scheduling primitives."""

from __future__ import annotations

import copy
import hashlib
import inspect
import itertools
import json
import math
import re
import time
import uuid
from dataclasses import dataclass, field, replace
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple

from .state_data import clone_json_value
from .contract_identity import (
    LEAN_CONTRACT_IDENTITY_VERSION,
    has_current_lean_contract_identity,
    lean_contract_evidence_receipt_matches,
    make_lean_contract_evidence_receipt,
    parse_lean_contract_identity,
)
from .lean_syntax import lean_relation_binder_parts
from .lean_parser import sanitize_goal_hypothesis, split_goal_definition_binding
from .proof_dossier import (
    ProofDossier,
    _prompt_safe_inline_text,
    _redact_prompt_control_text,
    _redact_split_prompt_control_text,
    is_answer_unsafe_statement_text,
    text_hash,
)
from .proof_graph import (
    FORMALIZATION_BRIDGE_OPEN_PREMISE_TRUST,
    graph_node_frontier_quarantined,
    graph_root_equivalent_suppression_decision,
    graph_statement_is_executable,
    helper_decl_statement,
)
from .utils import (
    _lean_lexical_skip_end,
    _layout_local_let_prefix_expects_term_continuation,
    _layout_local_let_prefix_has_open_rhs,
    _layout_local_let_trailer_looks_like_body,
    _line_ends_with_open_proof_tail,
    _line_has_layout_local_let_without_body,
    _looks_like_tactic_proof_continuation_line,
    has_sorry_or_admit,
    normalize_subgoal_statement,
)

_LEAN_NAME_SEGMENT_PATTERN = r"(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)"
_LEAN_QUALIFIED_NAME_PATTERN = (
    rf"{_LEAN_NAME_SEGMENT_PATTERN}(?:\.{_LEAN_NAME_SEGMENT_PATTERN})*"
)
_CHECK_TERM_RE = re.compile(rf"^@?{_LEAN_QUALIFIED_NAME_PATTERN}$")
# Persisted retrieval candidates are executable inputs.  Bump this whenever
# the execution-relevance policy changes so older broad candidate pages cannot
# bypass the current scheduler gate after checkpoint restore/graph hydration.
PROOF_STATE_DECL_EXECUTION_POLICY_VERSION = "proof_state_decl_execution_v4"
PROOF_STATE_RESIDUAL_GOAL_ATTESTATION_SCHEMA_VERSION = 2
PROOF_STATE_RESIDUAL_RUNNER_FORMAT_VERSION = 2
PROOF_STATE_PENDING_RESIDUAL_EXTRACTION_SCHEMA_VERSION = 1
PROOF_STATE_VERIFIER_RETRY_SCHEMA_VERSION = 1
PROOF_STATE_VERIFIER_RETRY_MAX_COOLDOWN_S = 1800.0
PROOF_STATE_VERIFIER_RETRY_MAX_STATES_PER_NODE = 64
PROOF_STATE_EXECUTION_SCHEMA_VERSION = 2
PROOF_STATE_ROOT_TACTIC_PORTFOLIO_SCHEMA_VERSION = 1
PROOF_STATE_ROOT_TACTIC_PORTFOLIO_MAX_CANDIDATES = 256
_PROOF_STATE_KNOWN_RESIDUAL_SOURCE_PREFIXES = (
    "try_skeleton_tool",
    "decl_application",
    "llm_tool_decl_application",
    "tactic",
    "lemma_dag_parent_stub",
    "cast_normalization",
    "finset_reindexing",
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_PROOF_STATE_MAX_DURABLE_COUNTER = (1 << 63) - 1
_PROOF_STATE_MAX_DURABLE_FINITE_FLOAT = 1.0e15
_TYPED_TRANSITION_RING = 12
_TYPED_TRANSITION_POLICY_MARKERS = frozenset(
    {
        "lemma_dag_decomposition_scheduled",
        "lemma_dag_decomposition_reopened",
        "llm_lemma_dag_decomposition_all_candidates_rejected",
        "llm_lemma_dag_decomposition_empty_all_unverified_retry",
        "llm_lemma_dag_decomposition_partial_verified",
        "assembly_route_invalidated_by_falsified_child",
        "child_goal_falsification_preflight_transient",
        "child_goal_falsification_preflight_complete",
    }
)
_TYPED_TRANSITION_POLICY_SOURCES = frozenset(
    {
        "falsification_preflight",
        "falsification",
    }
)
_LEAN_LOCAL_IDENT_RE = re.compile(r"^(?:[^\W\d]|_)[\w']*$", flags=re.UNICODE)
_LEAN_LOCAL_TOKEN_RE = re.compile(
    r"«[^»]+»|(?:[^\W\d]|_)[\w'✝]*",
    flags=re.UNICODE,
)
_LEAN_IDENTIFIER_RE = re.compile(_LEAN_QUALIFIED_NAME_PATTERN)
_GENERATED_SOLUTION_REF_ALIAS_RE = re.compile(
    r"\bsolution_ref_hidden_[A-Za-z0-9_]+\b"
)
_OFFICIAL_ANSWER_REFERENCE_HIDDEN = "[official-answer reference hidden]"
_LEAN_RELATION_BINDER_TOKENS = (
    "∈",
    "∉",
    "≤",
    "≥",
    "≠",
    "<=",
    ">=",
    "=",
    "<",
    ">",
    "∣",
)
_LEAN_KNOWN_DOT_METHOD_SUFFIXES = {
    "left",
    "right",
    "fst",
    "snd",
    "1",
    "2",
    "mp",
    "mpr",
    "symm",
    "trans",
}
_LEAN_RESERVED_LOCAL_NAMES = {
    "by",
    "calc",
    "do",
    "else",
    "fun",
    "have",
    "if",
    "in",
    "let",
    "match",
    "namespace",
    "then",
    "where",
}
_LEAN_BUILTIN_WORDS = _LEAN_RESERVED_LOCAL_NAMES | {
    "axiom",
    "classical",
    "def",
    "example",
    "exact",
    "forall",
    "intro",
    "lemma",
    "namespace",
    "noncomputable",
    "open",
    "simp",
    "theorem",
}
_RESIDUAL_TARGET_CONTINUATION_SUFFIXES = (
    "→",
    "->",
    "=>",
    "↔",
    "<->",
    "∧",
    "∨",
    ",",
    "(",
    "[",
    "{",
    "⦃",
    "+",
    "-",
    "*",
    "/",
    "=",
    "≠",
    "≤",
    "<",
    "≥",
    ">",
    "·",
    "∘",
    "∣",
    "^",
    "%",
    "⊕",
    "⊗",
    "⊔",
    "⊓",
    "∪",
    "∩",
    "∈",
    "∉",
)
_LEAN_TYPE_SYMBOLS = {
    "ℕ": "Nat",
    "ℤ": "Int",
    "ℚ": "Rat",
    "ℝ": "Real",
    "ℂ": "Complex",
}


def _proof_state_exact_sha256(value: Any) -> str:
    return hashlib.sha256(str(value or "").encode("utf-8")).hexdigest()


def _proof_state_canonical_json_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _proof_state_is_sha256(value: Any) -> bool:
    return _SHA256_RE.fullmatch(str(value or "").strip()) is not None


def _proof_state_durable_nonnegative_int(value: Any) -> int:
    """Decode persisted counters without letting corrupt shape grant progress."""

    if (
        isinstance(value, bool)
        or not isinstance(value, int)
        or value > _PROOF_STATE_MAX_DURABLE_COUNTER
    ):
        return 0
    return max(0, value)


def _proof_state_durable_int(value: Any, *, default: int = 0) -> int:
    if (
        isinstance(value, bool)
        or not isinstance(value, int)
        or abs(value) > _PROOF_STATE_MAX_DURABLE_COUNTER
    ):
        return int(default)
    return value


def _proof_state_durable_finite_float(
    value: Any,
    *,
    default: float = 0.0,
) -> float:
    if isinstance(value, bool):
        return float(default)
    try:
        parsed = float(value)
    except (TypeError, ValueError, OverflowError):
        return float(default)
    return (
        parsed
        if math.isfinite(parsed)
        and abs(parsed) <= _PROOF_STATE_MAX_DURABLE_FINITE_FLOAT
        else float(default)
    )


def _proof_state_durable_mapping(value: Any) -> Dict[str, Any]:
    return dict(value) if isinstance(value, Mapping) else {}


def _proof_state_durable_sequence(value: Any) -> List[Any]:
    return list(value) if isinstance(value, (list, tuple)) else []


def validated_root_tactic_portfolio_continuation(value: Any) -> Dict[str, Any]:
    """Return a bounded executable root-tactic cursor or fail closed."""

    if not isinstance(value, Mapping):
        return {}
    if value.get("schema_version") != PROOF_STATE_ROOT_TACTIC_PORTFOLIO_SCHEMA_VERSION:
        return {}
    phase = str(value.get("phase") or "")
    if phase not in {"direct", "active", "fallback"}:
        return {}
    context_key = str(value.get("context_key") or "")
    if re.fullmatch(r"[0-9a-f]{16}", context_key) is None:
        return {}
    raw_candidates = value.get("candidates")
    if not isinstance(raw_candidates, (list, tuple)):
        return {}
    raw_next_candidate_index = value.get("next_candidate_index")
    if (
        isinstance(raw_next_candidate_index, bool)
        or not isinstance(raw_next_candidate_index, int)
        or raw_next_candidate_index < 0
        or raw_next_candidate_index > _PROOF_STATE_MAX_DURABLE_COUNTER
    ):
        return {}
    next_candidate_index = raw_next_candidate_index
    if not raw_candidates:
        # Active-target exhaustion hands ownership to the fallback phase at a
        # scheduler boundary.  This is the sole empty executable cursor: the
        # fallback portfolio has intentionally not been generated or checked.
        if phase != "fallback" or next_candidate_index != 0:
            return {}
        return {
            "schema_version": PROOF_STATE_ROOT_TACTIC_PORTFOLIO_SCHEMA_VERSION,
            "context_key": context_key,
            "phase": phase,
            "candidates": [],
            "next_candidate_index": 0,
        }
    if len(raw_candidates) > PROOF_STATE_ROOT_TACTIC_PORTFOLIO_MAX_CANDIDATES:
        return {}
    candidates: List[Dict[str, Any]] = []
    seen_proofs: Set[str] = set()
    for raw_candidate in raw_candidates:
        if not isinstance(raw_candidate, Mapping):
            return {}
        proof = raw_candidate.get("proof")
        tactic = raw_candidate.get("tactic")
        source = raw_candidate.get("source")
        helper = raw_candidate.get("helper")
        if not all(isinstance(item, str) for item in (proof, tactic, source)):
            return {}
        if (
            not proof.strip()
            or not tactic.strip()
            or not source.strip()
            or len(proof) > 16_384
            or len(tactic) > 8_192
            or len(source) > 256
            or (helper is not None and not isinstance(helper, str))
            or (isinstance(helper, str) and len(helper) > 512)
            or proof in seen_proofs
        ):
            return {}
        seen_proofs.add(proof)
        candidates.append(
            {
                "proof": proof,
                "tactic": tactic,
                "source": source,
                "helper": helper,
            }
        )
    if next_candidate_index >= len(candidates):
        return {}
    return {
        "schema_version": PROOF_STATE_ROOT_TACTIC_PORTFOLIO_SCHEMA_VERSION,
        "context_key": context_key,
        "phase": phase,
        "candidates": candidates,
        "next_candidate_index": next_candidate_index,
    }


_RESIDUAL_ATTESTATION_QUARANTINE_SCHEMA_VERSION = 1
_RESIDUAL_ATTESTATION_QUARANTINE_ACTION = (
    "residual_elaboration_attestation_required"
)


def _proof_state_residual_attestation_quarantine_snapshot(
    value: Any,
    *,
    node_status: Any,
    node_action: Any,
    node_blocker: Any,
) -> Dict[str, Any]:
    """Validate exact inverse provenance, failing closed on malformed state."""

    if (
        str(node_status or "") != "blocked"
        or str(node_action or "") != _RESIDUAL_ATTESTATION_QUARANTINE_ACTION
        or str(node_blocker or "") != _RESIDUAL_ATTESTATION_QUARANTINE_ACTION
        or not isinstance(value, Mapping)
        or set(value)
        != {"schema_version", "status", "action", "blocker", "priority"}
        or value.get("schema_version")
        != _RESIDUAL_ATTESTATION_QUARANTINE_SCHEMA_VERSION
        or value.get("status") != "open"
        or not isinstance(value.get("action"), str)
        or not isinstance(value.get("blocker"), str)
    ):
        return {}
    raw_priority = value.get("priority")
    if (
        isinstance(raw_priority, bool)
        or not isinstance(raw_priority, (int, float))
        or not math.isfinite(float(raw_priority))
        or abs(float(raw_priority)) > _PROOF_STATE_MAX_DURABLE_FINITE_FLOAT
    ):
        return {}
    return {
        "schema_version": _RESIDUAL_ATTESTATION_QUARANTINE_SCHEMA_VERSION,
        "status": "open",
        "action": value["action"],
        "blocker": value["blocker"],
        "priority": float(raw_priority),
    }


def _proof_state_prompt_safe_attestation_quarantine_snapshot(
    value: Any,
    *,
    node_status: Any,
    node_action: Any,
    node_blocker: Any,
    redact_solution_refs: bool,
) -> Dict[str, Any]:
    snapshot = _proof_state_residual_attestation_quarantine_snapshot(
        value,
        node_status=node_status,
        node_action=node_action,
        node_blocker=node_blocker,
    )
    if not snapshot:
        return {}
    return {
        "schema_version": _RESIDUAL_ATTESTATION_QUARANTINE_SCHEMA_VERSION,
        "status": "open",
        "action": _proof_state_prompt_safe_text(
            snapshot["action"],
            limit=240,
            redact_solution_refs=redact_solution_refs,
        ),
        "blocker": _proof_state_prompt_safe_text(
            snapshot["blocker"],
            limit=1000,
            redact_solution_refs=redact_solution_refs,
        ),
        "priority": snapshot["priority"],
    }


def proof_state_source_requires_residual_goal_attestation(source: Any) -> bool:
    """Whether ``source`` is a production residual-goal admission boundary."""

    text = str(source or "").strip()
    return any(
        text == prefix or text.startswith(prefix + ":")
        for prefix in _PROOF_STATE_KNOWN_RESIDUAL_SOURCE_PREFIXES
    )


def proof_state_residual_goal_environment_binding(
    statement_environment_hash: Any,
    elaboration_context_hash: Any,
) -> str:
    """Bind a Lean environment stamp to the exact residual replay context."""

    return _proof_state_canonical_json_sha256(
        {
            "elaboration_context_hash": str(elaboration_context_hash or ""),
            "statement_environment_hash": str(statement_environment_hash or ""),
        }
    )


def proof_state_residual_goal_batch_digest(
    attestations: Sequence[Mapping[str, Any]],
) -> str:
    """Digest a complete ordered admission batch, including ordered receipts."""

    payloads: List[Dict[str, Any]] = []
    receipts: List[str] = []
    for raw in list(attestations or ()):
        if not isinstance(raw, Mapping) or any(
            not isinstance(key, str) for key in raw
        ):
            return ""
        try:
            payloads.append(
                clone_json_value(
                    {
                        key: value
                        for key, value in raw.items()
                        if key not in {"batch_digest", "contract_evidence_receipt"}
                    },
                    label="residual goal attestation digest payload",
                )
            )
        except (TypeError, ValueError):
            return ""
        receipts.append(str(raw.get("contract_evidence_receipt") or ""))
    if not payloads:
        return ""
    return _proof_state_canonical_json_sha256(
        {
            "format": (
                "proof-state-residual-goal-admission-v"
                f"{PROOF_STATE_RESIDUAL_GOAL_ATTESTATION_SCHEMA_VERSION}"
            ),
            "ordered_attestations": payloads,
            "ordered_contract_evidence_receipts": receipts,
        }
    )


def _proof_state_residual_expr_hash(canonical_expr_json: Any) -> str:
    text = str(canonical_expr_json or "")
    try:
        parsed = json.loads(text)
    except (TypeError, ValueError, json.JSONDecodeError):
        return ""
    canonical = json.dumps(
        parsed,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    if canonical != text:
        return ""
    return _proof_state_canonical_json_sha256(
        {
            "expr": parsed,
            "format": LEAN_CONTRACT_IDENTITY_VERSION,
        }
    )


def _proof_state_runner_batch_digest(
    attestations: Sequence[Mapping[str, Any]],
) -> str:
    """Recompute the Lean runner's batch receipt from bound goal records."""

    records = list(attestations or ())
    if not records:
        return ""
    first = records[0]
    goals: List[Dict[str, Any]] = []
    for record in records:
        goals.append(
            {
                "canonical_expr_json": str(
                    record.get("canonical_expr_json") or ""
                ),
                "expr_hash": str(record.get("expr_hash") or ""),
                "slot_count": record.get("slot_count"),
                "slot_index": record.get("slot_index"),
                "statement": str(record.get("statement") or ""),
                "statement_sha256": str(
                    record.get("statement_sha256") or ""
                ),
                "structural_identity": str(
                    record.get("structural_identity") or ""
                ),
            }
        )
    return _proof_state_canonical_json_sha256(
        {
            "elaboration_context_hash": str(
                first.get("elaboration_context_hash") or ""
            ),
            "format_version": int(first.get("runner_format_version") or 0),
            "goals": goals,
            "parent_canonical_expr_json": str(
                first.get("parent_canonical_expr_json") or ""
            ),
            "parent_expr_hash": str(first.get("parent_expr_hash") or ""),
            "parent_statement_sha256": str(
                first.get("parent_target_sha256") or ""
            ),
            "parent_structural_identity": str(
                first.get("parent_structural_identity") or ""
            ),
            "proof_stub_sha256": str(
                first.get("parent_proof_stub_sha256") or ""
            ),
        }
    )


class TypedResidualBindResult(list):
    """Bound residual attestations, or an empty classified bind failure.

    Empty contents remain equal to ``[]``. ``status`` distinguishes a
    self-inconsistent Lean receipt (terminal; pending must settle) from a
    missing/clone/format failure the executor may retry.
    """

    status: str
    reason: str

    def __init__(
        self,
        attestations: Optional[Sequence[Mapping[str, Any]]] = None,
        *,
        status: str = "",
        reason: str = "",
    ) -> None:
        items = list(attestations or ())
        super().__init__(items)
        if status:
            self.status = str(status)
        else:
            self.status = "admitted" if items else "deferred"
        self.reason = str(reason or "")


def _typed_residual_bind_unavailable(
    reason: str = "bind_unavailable",
) -> TypedResidualBindResult:
    return TypedResidualBindResult(status="deferred", reason=reason)


def _typed_residual_bind_contract_rejected(
    reason: str = "bind_contract_rejected",
) -> TypedResidualBindResult:
    return TypedResidualBindResult(status="terminal_rejected", reason=reason)


def bind_typed_residual_batch_attestations(
    batch_receipt: Any,
    *,
    source: str,
    parent_node_id: str,
    parent_statement: str,
    parent_proof_stub: str,
    statement_environment_hash: str,
) -> TypedResidualBindResult:
    """Validate one runner receipt and bind it to proof-state admission.

    This is the sole conversion boundary from ``LeanResidualBatchReceipt`` to
    durable proof-state attestations. Callers must not mint per-goal receipts or
    admission digests independently. Empty results still compare equal to
    ``[]``; ``status``/``reason`` say whether the receipt is retryable.
    """

    to_record = getattr(batch_receipt, "to_record", None)
    raw = to_record() if callable(to_record) else batch_receipt
    if not isinstance(raw, Mapping):
        return _typed_residual_bind_unavailable()
    try:
        receipt = clone_json_value(
            dict(raw),
            label="typed residual batch receipt",
        )
    except (TypeError, ValueError):
        return _typed_residual_bind_unavailable()
    if (
        int(receipt.get("format_version") or 0)
        != PROOF_STATE_RESIDUAL_RUNNER_FORMAT_VERSION
    ):
        return _typed_residual_bind_unavailable()
    exact_parent = str(parent_statement or "").strip()
    exact_stub = str(parent_proof_stub or "").strip()
    exact_source = str(source or "").strip()
    exact_parent_id = str(parent_node_id or "").strip()
    if (
        not exact_parent
        or not exact_stub
        or not exact_source
        or not exact_parent_id
        or not proof_state_source_requires_residual_goal_attestation(exact_source)
    ):
        return _typed_residual_bind_unavailable()
    parent_target_sha256 = _proof_state_exact_sha256(exact_parent)
    proof_stub_sha256 = _proof_state_exact_sha256(exact_stub)
    if (
        str(receipt.get("parent_statement_sha256") or "")
        != parent_target_sha256
        or str(receipt.get("proof_stub_sha256") or "") != proof_stub_sha256
    ):
        return _typed_residual_bind_contract_rejected()
    elaboration_context_hash = str(
        receipt.get("elaboration_context_hash") or ""
    )
    parent_expr_json = str(receipt.get("parent_canonical_expr_json") or "")
    parent_expr_hash = str(receipt.get("parent_expr_hash") or "")
    parent_identity = str(receipt.get("parent_structural_identity") or "")
    if (
        not _proof_state_is_sha256(elaboration_context_hash)
        or _proof_state_residual_expr_hash(parent_expr_json) != parent_expr_hash
        or not has_current_lean_contract_identity(parent_identity)
        or parse_lean_contract_identity(parent_identity) != (
            parent_expr_hash,
            "dependent",
        )
    ):
        return _typed_residual_bind_contract_rejected()
    goals = list(receipt.get("goals") or ())
    if not goals:
        return _typed_residual_bind_unavailable()
    runner_records: List[Dict[str, Any]] = []
    slot_count = len(goals)
    for slot_index, goal in enumerate(goals):
        if not isinstance(goal, Mapping):
            return _typed_residual_bind_contract_rejected()
        record = dict(goal)
        statement = str(record.get("statement") or "")
        statement_sha256 = str(record.get("statement_sha256") or "")
        expr_json = str(record.get("canonical_expr_json") or "")
        expr_hash = str(record.get("expr_hash") or "")
        identity = str(record.get("structural_identity") or "")
        if (
            isinstance(record.get("slot_index"), bool)
            or isinstance(record.get("slot_count"), bool)
            or record.get("slot_index") != slot_index
            or record.get("slot_count") != slot_count
            or not statement
            or _proof_state_exact_sha256(statement) != statement_sha256
            or _proof_state_residual_expr_hash(expr_json) != expr_hash
            or not has_current_lean_contract_identity(identity)
            or parse_lean_contract_identity(identity) != (expr_hash, "dependent")
        ):
            return _typed_residual_bind_contract_rejected()
        runner_records.append(
            {
                "slot_index": slot_index,
                "slot_count": slot_count,
                "statement": statement,
                "statement_sha256": statement_sha256,
                "canonical_expr_json": expr_json,
                "expr_hash": expr_hash,
                "structural_identity": identity,
            }
        )
    expected_runner_digest = _proof_state_canonical_json_sha256(
        {
            "elaboration_context_hash": elaboration_context_hash,
            "format_version": PROOF_STATE_RESIDUAL_RUNNER_FORMAT_VERSION,
            "goals": runner_records,
            "parent_canonical_expr_json": parent_expr_json,
            "parent_expr_hash": parent_expr_hash,
            "parent_statement_sha256": parent_target_sha256,
            "parent_structural_identity": parent_identity,
            "proof_stub_sha256": proof_stub_sha256,
        }
    )
    runner_batch_digest = str(receipt.get("batch_digest") or "")
    if runner_batch_digest != expected_runner_digest:
        return _typed_residual_bind_contract_rejected()

    environment_hash = str(statement_environment_hash or "")
    environment_binding = proof_state_residual_goal_environment_binding(
        environment_hash,
        elaboration_context_hash,
    )
    attestations: List[Dict[str, Any]] = []
    for runner_goal in runner_records:
        identity = str(runner_goal["structural_identity"])
        statement_sha256 = str(runner_goal["statement_sha256"])
        attestation = {
            "schema_version": PROOF_STATE_RESIDUAL_GOAL_ATTESTATION_SCHEMA_VERSION,
            **runner_goal,
            "source": exact_source,
            "statement_environment_hash": environment_hash,
            "elaboration_context_hash": elaboration_context_hash,
            "parent_node_id": exact_parent_id,
            "parent_target_sha256": parent_target_sha256,
            "parent_structural_identity": parent_identity,
            "parent_canonical_expr_json": parent_expr_json,
            "parent_expr_hash": parent_expr_hash,
            "parent_proof_stub_sha256": proof_stub_sha256,
            "runner_format_version": PROOF_STATE_RESIDUAL_RUNNER_FORMAT_VERSION,
            "runner_batch_digest": runner_batch_digest,
            "contract_evidence_receipt": make_lean_contract_evidence_receipt(
                identity,
                statement_sha256,
                environment_binding,
            ),
        }
        attestations.append(attestation)
    admission_digest = proof_state_residual_goal_batch_digest(attestations)
    if not admission_digest:
        return _typed_residual_bind_unavailable()
    for attestation in attestations:
        attestation["batch_digest"] = admission_digest
    return TypedResidualBindResult(attestations)


class ResidualBatchAdmission(list):
    """Typed residual-batch admission result.

    Empty contents remain equal to ``[]`` for existing callers. ``status``
    distinguishes a terminal rejection (pending must be settled) from a
    deferrable infrastructure failure (executor may re-arm pending).
    """

    def __init__(
        self,
        node_ids: Optional[Sequence[str]] = None,
        *,
        status: str = "terminal_rejected",
        reason: str = "",
        goal_count: int = 0,
    ) -> None:
        super().__init__(
            str(item) for item in list(node_ids or ()) if str(item or "")
        )
        self.status = str(status or "")
        self.reason = str(reason or "")
        self.goal_count = max(0, int(goal_count or 0))


def _validate_bound_residual_goal_attestation_batch(
    attestations: Sequence[Mapping[str, Any]],
    *,
    statements: Sequence[str],
    source: str,
    parent_node_id: str,
    parent_statement: str,
    parent_proof_stub: str,
    statement_environment_hash: str,
    elaboration_context_hash: str,
    expected_parent_structural_identity: str = "",
) -> bool:
    """Validate a complete bound batch without trusting any caller flag."""

    records = list(attestations or ())
    exact_statements = list(statements or ())
    exact_source = str(source or "").strip()
    exact_parent_id = str(parent_node_id or "").strip()
    exact_parent = str(parent_statement or "").strip()
    exact_stub = str(parent_proof_stub or "").strip()
    environment_hash = str(statement_environment_hash or "")
    context_hash = str(elaboration_context_hash or "")
    if (
        not records
        or len(records) != len(exact_statements)
        or not exact_source
        or not exact_parent_id
        or not exact_parent
        or not exact_stub
        or not proof_state_source_requires_residual_goal_attestation(exact_source)
        or not _proof_state_is_sha256(context_hash)
    ):
        return False
    slot_count = len(records)
    parent_target_sha256 = _proof_state_exact_sha256(exact_parent)
    proof_stub_sha256 = _proof_state_exact_sha256(exact_stub)
    environment_binding = proof_state_residual_goal_environment_binding(
        environment_hash,
        context_hash,
    )
    batch_digest = str(records[0].get("batch_digest") or "")
    runner_batch_digest = str(records[0].get("runner_batch_digest") or "")
    parent_identity = str(records[0].get("parent_structural_identity") or "")
    parent_expr_json = str(records[0].get("parent_canonical_expr_json") or "")
    parent_expr_hash = str(records[0].get("parent_expr_hash") or "")
    if (
        not _proof_state_is_sha256(batch_digest)
        or not _proof_state_is_sha256(runner_batch_digest)
        or _proof_state_residual_expr_hash(parent_expr_json) != parent_expr_hash
        or not has_current_lean_contract_identity(parent_identity)
        or parse_lean_contract_identity(parent_identity)
        != (parent_expr_hash, "dependent")
        or (
            expected_parent_structural_identity
            and parent_identity != expected_parent_structural_identity
        )
    ):
        return False
    for slot_index, (record, statement) in enumerate(
        zip(records, exact_statements)
    ):
        if not isinstance(record, Mapping):
            return False
        exact_statement = str(statement)
        statement_sha256 = str(record.get("statement_sha256") or "")
        expr_json = str(record.get("canonical_expr_json") or "")
        expr_hash = str(record.get("expr_hash") or "")
        identity = str(record.get("structural_identity") or "")
        if (
            isinstance(record.get("schema_version"), bool)
            or record.get("schema_version")
            != PROOF_STATE_RESIDUAL_GOAL_ATTESTATION_SCHEMA_VERSION
            or isinstance(record.get("slot_index"), bool)
            or isinstance(record.get("slot_count"), bool)
            or record.get("slot_index") != slot_index
            or record.get("slot_count") != slot_count
            or str(record.get("statement") or "") != exact_statement
            or _proof_state_exact_sha256(exact_statement) != statement_sha256
            or str(record.get("source") or "") != exact_source
            or str(record.get("statement_environment_hash") or "")
            != environment_hash
            or str(record.get("elaboration_context_hash") or "")
            != context_hash
            or str(record.get("parent_node_id") or "") != exact_parent_id
            or str(record.get("parent_target_sha256") or "")
            != parent_target_sha256
            or str(record.get("parent_proof_stub_sha256") or "")
            != proof_stub_sha256
            or str(record.get("parent_structural_identity") or "")
            != parent_identity
            or str(record.get("parent_canonical_expr_json") or "")
            != parent_expr_json
            or str(record.get("parent_expr_hash") or "") != parent_expr_hash
            or record.get("runner_format_version")
            != PROOF_STATE_RESIDUAL_RUNNER_FORMAT_VERSION
            or str(record.get("runner_batch_digest") or "")
            != runner_batch_digest
            or str(record.get("batch_digest") or "") != batch_digest
            or _proof_state_residual_expr_hash(expr_json) != expr_hash
            or not has_current_lean_contract_identity(identity)
            or parse_lean_contract_identity(identity) != (expr_hash, "dependent")
            or not lean_contract_evidence_receipt_matches(
                str(record.get("contract_evidence_receipt") or ""),
                identity=identity,
                statement_key=statement_sha256,
                environment_hash=environment_binding,
            )
        ):
            return False
    return (
        _proof_state_runner_batch_digest(records) == runner_batch_digest
        and proof_state_residual_goal_batch_digest(records) == batch_digest
    )


def _residual_goal_attestation_authority_key(
    attestation: Mapping[str, Any],
) -> str:
    batch_digest = str(attestation.get("batch_digest") or "")
    slot_index = attestation.get("slot_index")
    if (
        not _proof_state_is_sha256(batch_digest)
        or isinstance(slot_index, bool)
        or not isinstance(slot_index, int)
        or slot_index < 0
    ):
        return ""
    return f"{batch_digest}:{slot_index}"


def _residual_goal_attestation_authorities(
    ledger: Any,
) -> List[Dict[str, Any]]:
    """Return exact authority records from the persisted node ledger."""

    if not isinstance(ledger, Mapping):
        return []
    authorities: List[Dict[str, Any]] = []
    for key, raw in ledger.items():
        if not isinstance(key, str) or not isinstance(raw, Mapping):
            return []
        authority_key = _residual_goal_attestation_authority_key(raw)
        if not authority_key or key != authority_key:
            return []
        try:
            authorities.append(
                clone_json_value(
                    dict(raw),
                    label="residual goal attestation authority",
                )
            )
        except (TypeError, ValueError):
            return []
    return authorities


def _erase_lean_comments_text(text: str) -> str:
    """Erase Lean comments while preserving their lexical whitespace role.

    Comments carry no proposition identity, but deleting them byte-for-byte can
    join adjacent identifiers into a different token.  Replace each comment
    with its line breaks (or one separating space when it has none) for
    layout-sensitive syntax.  Strings, raw strings, character literals, and
    quoted identifiers remain verbatim.
    """

    raw = str(text or "")
    out: List[str] = []
    index = 0
    while index < len(raw):
        lexical_end = _lean_lexical_skip_end(raw, index)
        if lexical_end is None:
            out.append(raw[index])
            index += 1
            continue
        lexical = raw[index:lexical_end]
        if raw.startswith(("/-", "--"), index):
            line_breaks = "".join(ch for ch in lexical if ch in "\r\n")
            out.append(line_breaks or " ")
        else:
            out.append(lexical)
        index = lexical_end
    return "".join(out)


def _replace_outside_lean_quotes_text(text: str, replacer: Any) -> str:
    """Apply ``replacer`` only to executable Lean surface text.

    Identity normalization must never rewrite bytes inside strings, raw
    strings, character literals, comments, or quoted identifiers.  Protecting
    only ``«...»`` made a local named ``c`` rewrite the literal ``"c"`` and
    made the type glyph ``"ℝ"`` collide with ``"Real"``.  Reuse the shared
    Lean lexer boundary so every lexical island is copied verbatim.
    """

    raw = str(text or "")
    parts: List[str] = []
    segment_start = 0
    index = 0
    while index < len(raw):
        lexical_end = _lean_lexical_skip_end(raw, index)
        if lexical_end is None:
            index += 1
            continue
        if segment_start < index:
            parts.append(str(replacer(raw[segment_start:index])))
        parts.append(raw[index:lexical_end])
        index = lexical_end
        segment_start = index
    if segment_start < len(raw):
        parts.append(str(replacer(raw[segment_start:])))
    return "".join(parts)


def _normalize_ascii_arrows_outside_lean_quotes(text: str) -> str:
    return _replace_outside_lean_quotes_text(
        text,
        lambda segment: re.sub(r"\s*(?:->|=>)\s*", " → ", str(segment or "")),
    )


def _replace_type_symbols_outside_lean_quotes(text: str) -> str:
    def replace_segment(segment: str) -> str:
        out = str(segment or "")
        for symbol, replacement in _LEAN_TYPE_SYMBOLS.items():
            out = re.sub(
                rf"(?<![\w'✝.]){re.escape(symbol)}(?![\w'✝])",
                replacement,
                out,
            )
        return out

    return _replace_outside_lean_quotes_text(text, replace_segment)


_ALPHA_NAME_TOKEN_RE = re.compile(r"(?<![\w'✝])_b(\d+)(?![\w'✝])")


def _next_free_alpha_index(text: str) -> int:
    indices = [int(m.group(1)) for m in _ALPHA_NAME_TOKEN_RE.finditer(str(text or ""))]
    return (max(indices) + 1) if indices else 0


def _replace_type_symbols_capture_safe(text: str) -> str:
    """Glyph->name normalization that cannot merge distinct identifiers.

    Rewriting ``ℕ`` to ``Nat`` inside a statement that ALSO binds or uses the
    identifier ``Nat`` textually merges two different things — external
    review reproduced `∀ (Nat : Type), Nonempty ℕ` (TRUE) colliding with
    `∀ (Foo : Type), Nonempty Foo` (FALSE). When both spellings of a pair
    coexist, skip that pair (false-mismatch direction only; single-spelling
    statements keep full unification).
    """

    # Raw-text token scan: a spelling inside a string literal that skips a
    # rewrite is a conservative false-mismatch, never a merge.
    # Capture happens only when the replacement NAME is BOUND in the
    # statement (a binder named Nat shadowing the real ℕ). Mixed statements
    # where both spellings appear free (e.g. ``∀ n : Nat, (0 : ℕ) < n``)
    # unify safely and keep doing so.
    try:
        bound = set(lean_statement_bound_names(str(text or "")))
    except Exception:
        bound = set()

    def replace_segment(segment: str) -> str:
        out = str(segment or "")
        for symbol, replacement in _LEAN_TYPE_SYMBOLS.items():
            if replacement in bound:
                continue
            out = re.sub(
                rf"(?<![\w'✝.]){re.escape(symbol)}(?![\w'✝])",
                replacement,
                out,
            )
        return out

    return _replace_outside_lean_quotes_text(text, replace_segment)


# A bare ascription/binder colon — not the first/second half of ``:=`` or
# ``::``. Identity must be invariant under colon spacing (``(0:ℝ)`` ≡
# ``(0 : ℝ)``): before this normalization, spacing depended on which
# canonicalization path a subterm happened to take (b2 digest-pin regression).
_IDENTITY_COLON_SPACING_RE = re.compile(r"[ \t]*(?<!:)(:)(?![:=])[ \t]*")


def _normalize_colon_spacing_outside_lean_quotes(text: str) -> str:
    def replace_segment(segment: str) -> str:
        return _IDENTITY_COLON_SPACING_RE.sub(" : ", str(segment or ""))

    return _replace_outside_lean_quotes_text(text, replace_segment)


def normalize_lean_colon_spacing_for_identity(text: str) -> str:
    """Public conservative normalization for exact-source identity checks."""

    return _normalize_colon_spacing_outside_lean_quotes(str(text or ""))


_LEMMA_DAG_TERMINAL_SOURCE_REJECTIONS = {
    "empty_helper",
    "not_single_helper_declaration",
    "not_safe_theorem_or_lemma",
    "missing_helper_name",
    "answer_unsafe_helper",
    "missing_helper_statement",
    "missing_helper_name_or_statement",
    "statement_mismatch",
}
_MATHLIB_SHAPE_KEYWORDS = {
    "Nat",
    "Int",
    "Rat",
    "Real",
    "Complex",
    "Finset",
    "Fintype",
    "Set",
    "List",
    "Multiset",
    "Polynomial",
    "MvPolynomial",
    "Nat.choose",
    "choose",
    "Nat.Prime",
    "Prime",
    "Even",
    "Odd",
    "Function",
    "Equiv",
    "Matrix",
    "Interval",
    "Icc",
    "Ico",
    "range",
    "sum",
    "prod",
    "card",
    "dvd",
    "gcd",
    "lcm",
    "pow",
    "cast",
}


def _normalize_proof_state_goal_text(value: Any) -> str:
    text = str(value or "").strip()
    if "⊢" in text:
        text = text.split("⊢", 1)[1].strip()
    normalized = normalize_subgoal_statement(text)
    # Never collapse internal whitespace in executable Lean text.  Spaces in
    # string literals, syntax quotations, and layout-sensitive terms are
    # semantic.  A missed syntactic dedup is safe; conflating two different
    # propositions is not.  Higher-level identity canonicalization already
    # handles binder renaming without rewriting the executable target.
    return normalized.strip()


def _normalize_rendered_proof_state_target_text(value: Any) -> str:
    text = str(value or "").strip()
    if "⊢" in text:
        text = text.split("⊢", 1)[1].strip()
    text = normalize_subgoal_statement(text)
    return _normalize_proof_state_goal_text(text)


def _has_layout_sensitive_local_let(text: str) -> bool:
    for line in str(text or "").splitlines()[:-1]:
        if _line_has_layout_local_let_without_body(line):
            return True
        match = re.search(r"\blet\s+[^;\n]*:=", line)
        if match is None:
            continue
        let_line = line[match.start() :]
        tail = let_line[match.end() - match.start() :]
        if _has_top_level_semicolon(let_line):
            continue
        if re.search(r"\bin\b", tail):
            continue
        return True
    return False


def _has_top_level_semicolon(text: str) -> bool:
    depth = 0
    for ch in str(text or ""):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ";" and depth == 0:
            return True
    return False


def _contextual_statement_residual_target(
    statement: str,
    context: Sequence[str],
) -> str:
    expected_names: List[str] = []
    for raw_hyp in context:
        hyp = str(raw_hyp or "").strip()
        if not hyp or ":" not in hyp or "\n" in hyp or "⊢" in hyp:
            continue
        head, body = split_goal_definition_binding(hyp)
        if head and body:
            continue
        names = hyp.split(":", 1)[0].strip().split()
        expected_names.extend(name for name in names if name)
    original_text = str(statement or "").strip()
    text = original_text
    for raw_hyp in context:
        text = _strip_contextual_local_definition_prefix(text, raw_hyp)
    if not expected_names:
        residual = _normalize_proof_state_goal_text(text)
        for raw_hyp in context:
            residual = _strip_contextual_local_definition_prefix(residual, raw_hyp)
        original_normalized = _normalize_proof_state_goal_text(original_text)
        return residual if residual and residual != original_normalized else ""

    if not text.startswith("∀"):
        return ""
    idx = 1
    found_names: List[str] = []
    while idx < len(text):
        while idx < len(text) and text[idx].isspace():
            idx += 1
        if idx >= len(text) or text[idx] != "(":
            break
        depth = 0
        end = idx
        while end < len(text):
            ch = text[end]
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    break
            end += 1
        if end >= len(text) or depth != 0:
            return ""
        group = text[idx + 1 : end].strip()
        if ":" not in group:
            return ""
        found_names.extend(name for name in group.split(":", 1)[0].strip().split() if name)
        idx = end + 1
        if found_names[: len(expected_names)] == expected_names:
            while idx < len(text) and text[idx].isspace():
                idx += 1
            if idx < len(text) and text[idx] == ",":
                residual = _normalize_proof_state_goal_text(text[idx + 1 :])
                for raw_hyp in context:
                    residual = _strip_contextual_local_definition_prefix(
                        residual,
                        raw_hyp,
                    )
                return residual
    return ""


def _strip_contextual_local_definition_prefix(residual: str, hyp: Any) -> str:
    head, body = split_goal_definition_binding(str(hyp or "").strip())
    if not head or not body:
        return str(residual or "").strip()
    head = head.strip()
    if not head.startswith("let "):
        head = f"let {head}"
    body = _normalize_proof_state_goal_text(body.strip())
    prefix = f"{head} := {body}".strip()
    text = str(residual or "").strip()
    for separator in (";", " in "):
        candidate = f"{prefix}{separator}"
        if text.startswith(candidate):
            return _normalize_proof_state_goal_text(text[len(candidate) :])
    return text


def _normalize_proof_state_context_item(value: Any) -> str:
    hypothesis = sanitize_goal_hypothesis(str(value or ""))
    if not hypothesis:
        return ""
    head, body = split_goal_definition_binding(hypothesis)
    if head and body:
        return hypothesis.replace("⊢", "").strip()[:500]
    colon = _find_top_level_colon(hypothesis)
    if colon >= 0:
        lhs = hypothesis[:colon].strip()
        rhs = _normalize_proof_state_goal_text(hypothesis[colon + 1 :])
        if lhs and rhs:
            return f"{lhs} : {rhs}"[:500]
    return hypothesis.replace("⊢", "").strip()[:500]


def _identity_source_text(statement: str) -> str:
    raw = _erase_lean_comments_text(str(statement or "")).strip()
    # Identity is allowed to normalize binders in the lexer-aware routines
    # below, but it must not pre-collapse raw whitespace inside Lean literals
    # or quotations.  Preserve the executable spelling here.
    # Identity must preserve Lean's actual operator precedence. The optional
    # planner convenience rewrite treats ambiguous ``H → A ↔ B`` as the
    # mathematical shorthand ``H → (A ↔ B)`` and is therefore unsuitable for
    # cache/graph keys of Lean-checked declarations.
    return normalize_subgoal_statement(raw, canonicalize_guarded_iff=False)


def lemma_dag_rejection_is_terminal_policy(rejection: str) -> bool:
    """Whether a helper-source policy rejection must not enter the DAG."""

    reason = str(rejection or "").strip()
    if not reason:
        return False
    return (
        reason in _LEMMA_DAG_TERMINAL_SOURCE_REJECTIONS
        or reason.startswith("forbidden_lean_command:")
    )


_GOAL_OPERATOR_TAGS = (
    ("≤", "inequality le"),
    ("≥", "inequality ge"),
    ("<", "inequality lt"),
    (">", "inequality gt"),
    ("∣", "divisibility dvd"),
    ("∑'", "tsum infinite sum"),
    ("∑", "finset sum"),
    ("∏", "finset product"),
    ("∈", "membership set"),
    ("⊆", "subset set"),
    ("¬", "negation"),
    ("∃", "exists"),
    ("↔", "iff"),
    ("=", "equality rewrite"),
)


def _compact_search_text(value: Any, *, limit: int) -> str:
    text = " ".join(str(value or "").split())
    if limit > 0 and len(text) > limit:
        return text[: max(0, limit - 4)].rstrip() + " ..."
    return text


def _proof_state_text_has_prompt_control(value: Any) -> bool:
    raw = str(value or "")
    if not raw:
        return False
    return _redact_split_prompt_control_text(_redact_prompt_control_text(raw)) != raw


def _proof_state_prompt_safe_text(
    value: Any,
    *,
    limit: int = 1000,
    redact_solution_refs: bool = True,
) -> str:
    return _prompt_safe_inline_text(
        str(value or ""),
        limit=max(0, int(limit or 0)),
        redact_solution_refs=bool(redact_solution_refs),
    )


def _proof_state_model_prompt_text(
    value: Any,
    *,
    limit: int,
    suppress_solution_placeholders: bool,
    statement: bool = False,
) -> str:
    """Render text for a model without exposing executable answer aliases.

    Ordinary prompt redaction intentionally returns stable identifier-shaped
    aliases because many callers use its output as compact durable metadata.
    A proof-state scheduler prompt is different: models can copy identifiers
    from it directly into Lean.  Convert any generated alias to an explicit
    non-executable marker, and hide an entire answer-dependent statement when
    requested, while preserving exact symbols in capability-backed visible
    mode.
    """

    raw = str(value or "")
    suppress = bool(suppress_solution_placeholders)
    if (
        suppress
        and statement
        and is_answer_unsafe_statement_text(
            raw,
            suppress_solution_placeholders=True,
        )
    ):
        return _OFFICIAL_ANSWER_REFERENCE_HIDDEN
    safe = _prompt_safe_inline_text(
        raw,
        limit=max(0, int(limit or 0)),
        redact_solution_refs=suppress,
    )
    if suppress:
        safe = _GENERATED_SOLUTION_REF_ALIAS_RE.sub(
            _OFFICIAL_ANSWER_REFERENCE_HIDDEN,
            safe,
        )
    return safe


def _proof_state_durable_text(
    value: Any,
    *,
    limit: int = 2000,
    suppress_solution_placeholders: bool = True,
) -> str:
    raw = str(value or "")
    if is_answer_unsafe_statement_text(
        raw,
        suppress_solution_placeholders=suppress_solution_placeholders,
    ) or _proof_state_text_has_prompt_control(raw):
        return _proof_state_prompt_safe_text(
            raw,
            limit=limit,
            redact_solution_refs=suppress_solution_placeholders,
        )
    return raw


def _proof_state_prompt_safe_value(
    value: Any,
    *,
    limit: int = 2000,
    redact_solution_refs: bool = True,
) -> Any:
    if isinstance(value, str):
        return _proof_state_prompt_safe_text(
            value,
            limit=limit,
            redact_solution_refs=redact_solution_refs,
        )
    if isinstance(value, Mapping):
        out: Dict[str, Any] = {}
        for raw_key, raw_value in value.items():
            safe_key = _proof_state_prompt_safe_text(
                raw_key,
                limit=240,
                redact_solution_refs=redact_solution_refs,
            )
            if not safe_key:
                safe_key = f"key_hidden_{text_hash(str(raw_key))}"
            if safe_key in out:
                safe_key = f"{safe_key}_{text_hash(str(raw_key))[:8]}"
            out[safe_key] = _proof_state_prompt_safe_value(
                raw_value,
                limit=limit,
                redact_solution_refs=redact_solution_refs,
            )
        return out
    if isinstance(value, list):
        return [
            _proof_state_prompt_safe_value(
                item,
                limit=limit,
                redact_solution_refs=redact_solution_refs,
            )
            for item in value
        ]
    if isinstance(value, tuple):
        return [
            _proof_state_prompt_safe_value(
                item,
                limit=limit,
                redact_solution_refs=redact_solution_refs,
            )
            for item in value
        ]
    return value


def _proof_state_prompt_safe_code(
    value: Any,
    *,
    limit: int = 4000,
    redact_solution_refs: bool = True,
) -> str:
    raw = str(value or "")
    safe_lines: list[str] = []
    for line in raw.splitlines():
        body = line
        if "--" in body:
            body = body.split("--", 1)[0]
        body = body.rstrip()
        if not body.strip():
            continue
        leading = re.match(r"\s*", body).group(0)
        content = body[len(leading) :]
        safe_content = _proof_state_prompt_safe_text(
            content,
            limit=max(1, limit),
            redact_solution_refs=redact_solution_refs,
        )
        if safe_content.strip():
            safe_lines.append(f"{leading}{safe_content}")
    safe = "\n".join(safe_lines).strip()
    if len(safe) > limit:
        safe = safe[: max(0, limit - 3)].rstrip() + "..."
    return safe


def _strip_lean_comments_and_strings(src: str) -> str:
    text = str(src or "")
    out: List[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        ch = text[index]
        nxt = text[index + 1] if index + 1 < len(text) else ""
        if in_string:
            out.append("\n" if ch in "\r\n" else " ")
            if ch == "\\" and index + 1 < len(text):
                index += 2
                out.append(" ")
                continue
            if ch == '"':
                in_string = False
            index += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                index += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                index += 2
                continue
            out.append("\n" if ch in "\r\n" else " ")
            index += 1
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            index += 1
            continue
        if ch == "-" and nxt == "-":
            out.extend("  ")
            index += 2
            while index < len(text) and text[index] not in "\r\n":
                out.append(" ")
                index += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            index += 2
            continue
        out.append(ch)
        index += 1
    return "".join(out)


def _line_indent(text: str) -> int:
    return len(text) - len(text.lstrip(" \t"))


def _lean_identifier_has_root_qualifier(text: str, start: int) -> bool:
    return start >= len("_root_.") and text[start - len("_root_.") : start] == "_root_."


def _lean_identifier_is_record_field_label(text: str, end: int) -> bool:
    index = max(0, end)
    while index < len(text) and text[index].isspace():
        index += 1
    return text.startswith(":=", index)


def _lean_identifier_is_projection_field(text: str, start: int) -> bool:
    return start > 0 and text[start - 1] == "."


def _lean_local_binder_ranges_in_proof(src: str) -> Dict[str, List[Tuple[int, int]]]:
    code = _strip_lean_comments_and_strings(src)
    ranges: Dict[str, List[Tuple[int, int]]] = {}
    lines = code.splitlines(keepends=True)
    line_starts: List[int] = []
    offset = 0
    for line in lines:
        line_starts.append(offset)
        offset += len(line)

    def scope_end(line_index: int, scope_indent: int) -> int:
        for next_index in range(line_index + 1, len(lines)):
            line = lines[next_index]
            if not line.strip():
                continue
            indent = _line_indent(line)
            if indent <= scope_indent:
                return line_starts[next_index]
        return len(code)

    def same_line_decl_separator(line: str, start: int) -> int:
        depth = 0
        for index in range(max(0, start), len(line)):
            ch = line[index]
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth = max(0, depth - 1)
            elif ch == ";" and depth == 0:
                if index > 0 and line[index - 1] == "<":
                    continue
                if index + 1 < len(line) and line[index + 1] == ">":
                    continue
                return index
        return -1

    def local_decl_scope_start(line_index: int, line: str, decl_indent: int) -> int:
        if ":=" in line and ":= by" not in line:
            after_assign = line.split(":=", 1)[1].strip()
            if after_assign:
                assign_index = line.find(":=")
                semicolon_index = same_line_decl_separator(line, assign_index + 2)
                if semicolon_index >= 0:
                    return line_starts[line_index] + semicolon_index + 1
                return line_starts[line_index] + len(line)
            for next_index in range(line_index + 1, len(lines)):
                next_line = lines[next_index]
                if not next_line.strip():
                    continue
                if _line_indent(next_line) <= decl_indent:
                    return line_starts[line_index] + len(line)
                stripped = next_line.strip()
                if stripped.startswith("by"):
                    if stripped != "by":
                        return line_starts[next_index] + len(next_line)
                    for body_end_index in range(next_index + 1, len(lines)):
                        body_line = lines[body_end_index]
                        if not body_line.strip():
                            continue
                        if _line_indent(body_line) <= decl_indent:
                            return line_starts[body_end_index]
                    return len(code)
                return line_starts[next_index] + len(next_line)
            return len(code)
        if ":= by" not in line:
            for next_index in range(line_index + 1, len(lines)):
                next_line = lines[next_index]
                if not next_line.strip():
                    continue
                if _line_indent(next_line) <= decl_indent:
                    return line_starts[line_index] + len(line)
                if ":=" not in next_line:
                    continue
                if ":= by" not in next_line:
                    return line_starts[next_index] + len(next_line)
                after_by = next_line.split(":= by", 1)[1].strip()
                if after_by:
                    return line_starts[next_index] + len(next_line)
                for body_end_index in range(next_index + 1, len(lines)):
                    body_line = lines[body_end_index]
                    if not body_line.strip():
                        continue
                    if _line_indent(body_line) <= decl_indent:
                        return line_starts[body_end_index]
                return len(code)
            return line_starts[line_index] + len(line)
        after_by = line.split(":= by", 1)[1].strip()
        if after_by:
            return line_starts[line_index] + len(line)
        for next_index in range(line_index + 1, len(lines)):
            next_line = lines[next_index]
            if not next_line.strip():
                continue
            if _line_indent(next_line) <= decl_indent:
                return line_starts[next_index]
        return len(code)

    def same_line_tactic_scope_start(line_index: int, line: str, start: int) -> int:
        separator_positions: List[Tuple[int, int]] = []
        seq_index = line.find("<;>", start)
        if seq_index >= 0:
            separator_positions.append((seq_index, 3))
        semicolon_index = same_line_decl_separator(line, start)
        if semicolon_index >= 0:
            separator_positions.append((semicolon_index, 1))
        if separator_positions:
            index, width = min(separator_positions, key=lambda item: item[0])
            return line_starts[line_index] + index + width
        return line_starts[line_index] + len(line)

    def lean_depth_before(line: str, stop: int) -> int:
        depth = 0
        for index in range(max(0, min(stop, len(line)))):
            depth = _scan_lean_depth(line, index, depth)
        return depth

    def same_line_alternative_end(line: str, start: int, target_depth: int) -> int:
        depth = lean_depth_before(line, start)
        for index in range(max(0, start), len(line)):
            if depth < target_depth:
                return index
            ch = line[index]
            if ch == "|" and depth == target_depth:
                return index
            depth = _scan_lean_depth(line, index, depth)
        return -1

    def record(name: str, start: int, end: int) -> None:
        clean = str(name or "").strip()
        if clean:
            ranges.setdefault(clean, []).append((max(0, start), max(0, end)))

    def mask_binder_type_annotations(text: str) -> str:
        source = str(text or "")
        chars = list(source)
        depth = 0
        index = 0
        while index < len(source):
            ch = source[index]
            if ch == ":":
                annotation_depth = depth
                chars[index] = " "
                index += 1
                nested_depth = depth
                while index < len(source):
                    inner = source[index]
                    if nested_depth <= annotation_depth and inner in ",)]}⟩":
                        break
                    chars[index] = " "
                    if inner in "([{⟨":
                        nested_depth += 1
                    elif inner in ")]}⟩":
                        nested_depth = max(0, nested_depth - 1)
                    index += 1
                depth = nested_depth
                continue
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth = max(0, depth - 1)
            index += 1
        return "".join(chars)

    def mask_record_field_labels(text: str) -> str:
        source = str(text or "")
        chars = list(source)
        for match in re.finditer(
            r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_']*)\s*:=",
            source,
        ):
            for index in range(match.start(1), match.end(1)):
                chars[index] = " "
        return "".join(chars)

    def binder_pattern_name_matches(text: str) -> List[re.Match[str]]:
        # Identifiers inside explicit type annotations are global/type terms,
        # not local binders introduced by intro/rintro.
        pattern_text = mask_binder_type_annotations(text)
        return list(_LEAN_IDENTIFIER_RE.finditer(pattern_text))

    def pattern_local_name_matches(text: str) -> List[Tuple[str, int, int]]:
        pattern_text = mask_binder_type_annotations(mask_record_field_labels(text))
        stripped = pattern_text.strip()
        constructor_app = bool(
            re.match(
                r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*\.?[A-Za-z_][A-Za-z0-9_']+\s+",
                stripped,
            )
        )
        matches = list(_LEAN_IDENTIFIER_RE.finditer(pattern_text))
        out: List[Tuple[str, int, int]] = []
        for index, name_match in enumerate(matches):
            raw_name = name_match.group(0)
            name = raw_name.rsplit(".", 1)[-1]
            if name in _LEAN_BUILTIN_WORDS or name == "_":
                continue
            if "." in raw_name:
                continue
            if name_match.start() > 0 and pattern_text[name_match.start() - 1] == ".":
                continue
            if constructor_app and index == 0:
                continue
            out.append((name, name_match.start(), name_match.end()))
        return out

    def strip_balanced_outer_pattern_parens(text: str) -> Tuple[str, int]:
        source = str(text or "")
        leading = len(source) - len(source.lstrip())
        stripped = source.strip()
        if not (stripped.startswith("(") and stripped.endswith(")")):
            return source, 0
        depth = 0
        for index, _ch in enumerate(stripped):
            depth = _scan_lean_depth(stripped, index, depth)
            if depth == 0 and index < len(stripped) - 1:
                return source, 0
        return stripped[1:-1], leading + 1

    def split_pattern_alternatives(text: str) -> List[Tuple[str, int]]:
        candidate, base_offset = strip_balanced_outer_pattern_parens(text)
        parts: List[Tuple[str, int]] = []
        depth = 0
        start = 0
        for index, ch in enumerate(candidate):
            if ch == "|" and depth == 0:
                raw = candidate[start:index]
                stripped = raw.strip()
                if stripped:
                    leading = len(raw) - len(raw.lstrip())
                    parts.append((stripped, base_offset + start + leading))
                start = index + 1
                continue
            depth = _scan_lean_depth(candidate, index, depth)
        raw = candidate[start:]
        stripped = raw.strip()
        if stripped:
            leading = len(raw) - len(raw.lstrip())
            parts.append((stripped, base_offset + start + leading))
        return parts

    def child_bullet_scope_ranges(
        line_index: int,
        parent_scope_indent: int,
        count: int,
    ) -> List[Tuple[int, int]]:
        bullets: List[Tuple[int, int]] = []
        bullet_indent: Optional[int] = None
        for next_index in range(line_index + 1, len(lines)):
            next_line = lines[next_index]
            if not next_line.strip():
                continue
            indent = _line_indent(next_line)
            if indent <= parent_scope_indent:
                break
            stripped = next_line.lstrip()
            if not stripped.startswith("·"):
                continue
            bullet_pos = next_line.find("·")
            if bullet_indent is None:
                bullet_indent = bullet_pos
            if bullet_pos != bullet_indent:
                continue
            bullets.append(
                (
                    line_starts[next_index] + bullet_pos + 1,
                    scope_end(next_index, bullet_pos),
                )
            )
        if count > 0 and len(bullets) >= count and len(bullets) % count == 0:
            group_size = len(bullets) // count
            return [
                (
                    bullets[index * group_size][0],
                    bullets[((index + 1) * group_size) - 1][1],
                )
                for index in range(count)
            ]
        return bullets[:count]

    def same_line_first_scope_ranges(
        line_index: int,
        line: str,
        start: int,
        count: int,
        required_names: Set[str],
    ) -> List[Tuple[int, int]]:
        seq_index = line.find("<;>", start)
        if seq_index < 0:
            return []
        first_match = re.search(r"\bfirst\b", line[seq_index + 3 :])
        if first_match is None:
            return []
        scan_start = seq_index + 3 + first_match.end()
        target_depth = lean_depth_before(line, scan_start)
        ranges: List[Tuple[int, int]] = []
        depth = target_depth
        index = scan_start
        while index < len(line):
            ch = line[index]
            if ch == "|" and depth == target_depth:
                body_start = index + 1
                body_end = same_line_alternative_end(line, body_start, target_depth)
                if body_end < 0:
                    body_end = len(line)
                ranges.append(
                    (
                        line_starts[line_index] + body_start,
                        line_starts[line_index] + body_end,
                    )
                )
                index = body_end
                depth = lean_depth_before(line, index)
                continue
            depth = _scan_lean_depth(line, index, depth)
            index += 1
        if count > 0 and len(ranges) > count:
            block_text = code[ranges[0][0] : ranges[-1][1]]
            if not all(first_block_handles_name(block_text, name) for name in required_names):
                return []
            return [(ranges[0][0], ranges[-1][1]) for _ in range(count)]
        if count > 0 and len(ranges) < count:
            return []
        return ranges

    def multiline_first_scope_ranges(
        line_index: int,
        line: str,
        scope_indent: int,
        start: int,
        count: int,
        required_names: Set[str],
    ) -> List[Tuple[int, int]]:
        seq_index = line.find("<;>", start)
        if seq_index < 0:
            return []
        first_line_index = line_index
        if re.search(r"\bfirst\b", line[seq_index + 3 :]) is None:
            first_line_index = -1
            for next_index in range(line_index + 1, len(lines)):
                next_line = lines[next_index]
                if not next_line.strip():
                    continue
                indent = _line_indent(next_line)
                if indent <= scope_indent:
                    break
                if next_line.lstrip().startswith("first"):
                    first_line_index = next_index
                break
            if first_line_index < 0:
                return []
        ranges: List[Tuple[int, int]] = []
        pipe_indent: Optional[int] = None
        for next_index in range(first_line_index + 1, len(lines)):
            next_line = lines[next_index]
            if not next_line.strip():
                continue
            indent = _line_indent(next_line)
            if indent <= scope_indent:
                break
            stripped = next_line.lstrip()
            if not stripped.startswith("|"):
                continue
            pipe_pos = next_line.find("|")
            if pipe_indent is None:
                pipe_indent = pipe_pos
            if pipe_pos != pipe_indent:
                continue
            ranges.append(
                (
                    line_starts[next_index] + pipe_pos + 1,
                    scope_end(next_index, pipe_pos),
                )
            )
        if count > 0 and len(ranges) > count:
            block_text = code[ranges[0][0] : ranges[-1][1]]
            if not all(first_block_handles_name(block_text, name) for name in required_names):
                return []
            return [(ranges[0][0], ranges[-1][1]) for _ in range(count)]
        if count > 0 and len(ranges) < count:
            return []
        return ranges

    def first_block_handles_name(block_text: str, name: str) -> bool:
        name_pattern = re.escape(name)
        return any(
            re.search(pattern, block_text)
            for pattern in (
                rf"(?<![A-Za-z0-9_'.])cases\s+{name_pattern}(?![A-Za-z0-9_'])",
                rf"(?<![A-Za-z0-9_'.])False\.elim\s+{name_pattern}(?![A-Za-z0-9_'])",
                rf"(?<![A-Za-z0-9_'.])And\.intro\s+{name_pattern}(?![A-Za-z0-9_'])",
            )
        ) or (
            "cases " in block_text
            and re.search(
                rf"(?<![A-Za-z0-9_'.])exact\s+{name_pattern}(?![A-Za-z0-9_'])",
                block_text,
            )
            is not None
        )

    def tactic_alternative_scope_ranges(
        line_index: int,
        line: str,
        scope_indent: int,
        after_pattern: int,
        alternatives: Sequence[Tuple[str, int]],
    ) -> List[Tuple[int, int]]:
        count = len(alternatives)
        required_names = {
            name
            for pattern_text, _pattern_offset in alternatives
            for name, _name_start, _name_end in pattern_local_name_matches(pattern_text)
        }
        ranges = child_bullet_scope_ranges(line_index, scope_indent, count)
        if len(ranges) >= count:
            return ranges
        ranges = same_line_first_scope_ranges(
            line_index,
            line,
            after_pattern,
            count,
            required_names,
        )
        if len(ranges) >= count:
            return ranges
        return multiline_first_scope_ranges(
            line_index,
            line,
            scope_indent,
            after_pattern,
            count,
            required_names,
        )

    def record_pattern_scope(
        absolute_pattern_start: int,
        pattern_text: str,
        scope_start: int,
        scope_stop: int,
    ) -> None:
        for name, name_start, name_end in pattern_local_name_matches(pattern_text):
            record(
                name,
                absolute_pattern_start + name_start,
                absolute_pattern_start + name_end,
            )
            record(name, scope_start, scope_stop)

    def fun_scope_end(line: str, fun_start: int, body_start: int) -> int:
        open_index = fun_start - 1
        while open_index >= 0 and line[open_index].isspace():
            open_index -= 1
        if open_index >= 0 and line[open_index] == "(":
            depth = 0
            for index in range(open_index, len(line)):
                ch = line[index]
                if ch in "([{⟨":
                    depth += 1
                elif ch in ")]}⟩":
                    depth = max(0, depth - 1)
                    if depth == 0:
                        return index
            return len(line)
        depth = 0
        for index in range(max(0, body_start), len(line)):
            ch = line[index]
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                if depth <= 0:
                    return index
                depth -= 1
            elif depth == 0 and ch in ",;":
                return index
        return len(line)

    local_decl_re = re.compile(
        r"(?<![A-Za-z0-9_'.])(?:have|let|obtain)\s+([A-Za-z_][A-Za-z0-9_']*)\s*(?::|:=)"
    )
    local_pattern_decl_re = re.compile(
        r"(?<![A-Za-z0-9_'.])(?:have|let)\s+(.+?)\s*(?::=|:)"
    )
    obtain_pattern_re = re.compile(r"(?<![A-Za-z0-9_'.])obtain\s+(.+?)\s*(?::|:=)")
    by_cases_re = re.compile(
        r"(?<![A-Za-z0-9_'.])by_cases\s+([A-Za-z_][A-Za-z0-9_']*)\s*(?::|$)"
    )
    rcases_re = re.compile(
        r"(?<![A-Za-z0-9_'.])rcases\b[^\n;·]*?\bwith\b(.+?)(?=\s*(?:<;>|;|·|$))"
    )
    intro_re = re.compile(
        r"(?<![A-Za-z0-9_'.])intro(?:s)?\s+(.+?)(?=\s*(?:<;>|;|·|$))"
    )
    rintro_re = re.compile(
        r"(?<![A-Za-z0-9_'.])rintro\s+(.+?)(?=\s*(?:<;>|;|·|$))"
    )
    rename_i_re = re.compile(
        r"(?<![A-Za-z0-9_'.])rename_i\s+(.+?)(?=\s*(?:<;>|;|·|$))"
    )
    pattern_alt_re = re.compile(r"\|\s*(.+?)=>")
    case_alt_re = re.compile(
        r"(?<![A-Za-z0-9_'.])case\s+[A-Za-z_][A-Za-z0-9_']*\s+([^=|]+)=>"
    )
    fun_re = re.compile(r"(?<![A-Za-z0-9_'.])fun\s+([^=]+?)=>")
    for line_index, line in enumerate(lines):
        line_start = line_starts[line_index]
        line_indent = _line_indent(line)
        for match in local_decl_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            decl_indent = match.start(0)
            record(
                match.group(1),
                line_start + match.start(1),
                line_start + match.end(1),
            )
            record(
                match.group(1),
                local_decl_scope_start(line_index, line, decl_indent),
                scope_end(line_index, scope_indent),
            )
        for match in obtain_pattern_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            decl_indent = match.start(0)
            scope_start = local_decl_scope_start(line_index, line, decl_indent)
            scope_stop = scope_end(line_index, scope_indent)
            alternatives = split_pattern_alternatives(match.group(1))
            if len(alternatives) > 1:
                branch_ranges = tactic_alternative_scope_ranges(
                    line_index,
                    line,
                    scope_indent,
                    match.end(1),
                    alternatives,
                )
                for alt_index, (pattern_text, pattern_offset) in enumerate(alternatives):
                    if alt_index >= len(branch_ranges):
                        continue
                    branch_start, branch_stop = branch_ranges[alt_index]
                    record_pattern_scope(
                        line_start + match.start(1) + pattern_offset,
                        pattern_text,
                        branch_start,
                        branch_stop,
                    )
                continue
            record_pattern_scope(
                line_start + match.start(1),
                match.group(1),
                scope_start,
                scope_stop,
            )
        for match in local_pattern_decl_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            decl_indent = match.start(0)
            scope_start = local_decl_scope_start(line_index, line, decl_indent)
            scope_stop = scope_end(line_index, scope_indent)
            for name, name_start, name_end in pattern_local_name_matches(match.group(1)):
                record(
                    name,
                    line_start + match.start(1) + name_start,
                    line_start + match.start(1) + name_end,
                )
                record(name, scope_start, scope_stop)
        for match in by_cases_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            record(
                match.group(1),
                line_start + match.start(1),
                line_start + match.end(1),
            )
            record(
                match.group(1),
                same_line_tactic_scope_start(line_index, line, match.end(1)),
                scope_end(line_index, scope_indent),
            )
        for match in rcases_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            scope_start = same_line_tactic_scope_start(line_index, line, match.end(1))
            end = scope_end(line_index, scope_indent)
            alternatives = split_pattern_alternatives(match.group(1))
            if len(alternatives) > 1:
                branch_ranges = tactic_alternative_scope_ranges(
                    line_index,
                    line,
                    scope_indent,
                    match.end(1),
                    alternatives,
                )
                for alt_index, (pattern_text, pattern_offset) in enumerate(alternatives):
                    if alt_index >= len(branch_ranges):
                        continue
                    branch_start, branch_stop = branch_ranges[alt_index]
                    record_pattern_scope(
                        line_start + match.start(1) + pattern_offset,
                        pattern_text,
                        branch_start,
                        branch_stop,
                    )
                continue
            record_pattern_scope(
                line_start + match.start(1),
                match.group(1),
                scope_start,
                end,
            )
        for match in intro_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            end = scope_end(line_index, scope_indent)
            scope_start = same_line_tactic_scope_start(line_index, line, match.end(1))
            for name_match in binder_pattern_name_matches(match.group(1)):
                name = name_match.group(0)
                if name in _LEAN_BUILTIN_WORDS or name == "_":
                    continue
                record(
                    name,
                    line_start + match.start(1) + name_match.start(),
                    line_start + match.start(1) + name_match.end(),
                )
                record(name, scope_start, end)
        for match in rintro_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            end = scope_end(line_index, scope_indent)
            scope_start = same_line_tactic_scope_start(line_index, line, match.end(1))
            alternatives = split_pattern_alternatives(match.group(1))
            if len(alternatives) > 1:
                branch_ranges = tactic_alternative_scope_ranges(
                    line_index,
                    line,
                    scope_indent,
                    match.end(1),
                    alternatives,
                )
                for alt_index, (pattern_text, pattern_offset) in enumerate(alternatives):
                    if alt_index >= len(branch_ranges):
                        continue
                    branch_start, branch_stop = branch_ranges[alt_index]
                    record_pattern_scope(
                        line_start + match.start(1) + pattern_offset,
                        pattern_text,
                        branch_start,
                        branch_stop,
                    )
                continue
            for name_match in binder_pattern_name_matches(match.group(1)):
                name = name_match.group(0)
                if name in _LEAN_BUILTIN_WORDS or name == "_":
                    continue
                record(
                    name,
                    line_start + match.start(1) + name_match.start(),
                    line_start + match.start(1) + name_match.end(),
                )
                record(name, scope_start, end)
        for match in rename_i_re.finditer(line):
            bullet_pos = line.find("·", 0, match.start(1))
            scope_indent = bullet_pos if bullet_pos >= 0 else max(-1, line_indent - 1)
            scope_start = same_line_tactic_scope_start(line_index, line, match.end(1))
            scope_stop = scope_end(line_index, scope_indent)
            for name_match in binder_pattern_name_matches(match.group(1)):
                name = name_match.group(0)
                if name in _LEAN_BUILTIN_WORDS or name == "_":
                    continue
                record(
                    name,
                    line_start + match.start(1) + name_match.start(),
                    line_start + match.start(1) + name_match.end(),
                )
                record(name, scope_start, scope_stop)
        for match in pattern_alt_re.finditer(line):
            scope_indent = max(-1, line_indent)
            target_depth = lean_depth_before(line, match.start(0))
            arrow_index = match.end(0) - 2
            start = line_start + (arrow_index + 2 if arrow_index >= 0 else len(line))
            next_alt = same_line_alternative_end(
                line,
                arrow_index + 2 if arrow_index >= 0 else match.end(1),
                target_depth,
            )
            end = (
                line_start + next_alt
                if next_alt >= 0
                else scope_end(line_index, scope_indent)
            )
            for name, name_start, name_end in pattern_local_name_matches(match.group(1)):
                record(
                    name,
                    line_start + match.start(1) + name_start,
                    line_start + match.start(1) + name_end,
                )
                record(name, start, end)
        for match in case_alt_re.finditer(line):
            scope_indent = max(-1, line_indent)
            arrow_index = line.find("=>", match.end(1))
            start = line_start + (arrow_index + 2 if arrow_index >= 0 else len(line))
            end = scope_end(line_index, scope_indent)
            for name_match in _LEAN_IDENTIFIER_RE.finditer(match.group(1)):
                name = name_match.group(0)
                if name in _LEAN_BUILTIN_WORDS or name == "_":
                    continue
                record(
                    name,
                    line_start + match.start(1) + name_match.start(),
                    line_start + match.start(1) + name_match.end(),
                )
                record(name, start, end)
        for match in fun_re.finditer(line):
            if match.group(1).lstrip().startswith("|"):
                continue
            arrow_index = line.find("=>", match.end(1))
            body_start = arrow_index + 2 if arrow_index >= 0 else match.end(1)
            end = line_start + fun_scope_end(line, match.start(0), body_start)
            for name_match in _LEAN_IDENTIFIER_RE.finditer(match.group(1)):
                name = name_match.group(0)
                if name not in _LEAN_BUILTIN_WORDS:
                    record(name, line_start + match.start(1) + name_match.start(), end)
    return ranges


def lean_referenced_helper_names(
    src: str,
    names: Sequence[str],
    *,
    skip: Optional[str] = None,
    allow_arbitrary_dot_methods: bool = False,
) -> Set[str]:
    name_set = {
        str(name or "").strip()
        for name in list(names or ())
        if str(name or "").strip() and str(name or "").strip() != skip
    }
    if not name_set:
        return set()

    def helper_prefix(raw: str) -> str:
        matches = [
            name
            for name in name_set
            if raw == name
            or (
                raw.startswith(f"{name}.")
                and (
                    allow_arbitrary_dot_methods
                    or raw[len(name) + 1 :].split(".", 1)[0]
                    in _LEAN_KNOWN_DOT_METHOD_SUFFIXES
                )
            )
        ]
        if not matches:
            return ""
        return max(matches, key=len)

    scan_text = _strip_lean_comments_and_strings(str(src or ""))
    local_ranges = _lean_local_binder_ranges_in_proof(str(src or ""))
    lines = scan_text.splitlines(keepends=True)
    line_starts: List[int] = []
    offset = 0
    for line in lines:
        line_starts.append(offset)
        offset += len(line)

    def scoped_line_end(line_index: int, scope_indent: int) -> int:
        for next_index in range(line_index + 1, len(lines)):
            next_line = lines[next_index]
            if not next_line.strip():
                continue
            if _line_indent(next_line) <= scope_indent:
                return line_starts[next_index]
        return len(scan_text)

    open_namespace_ranges: List[Tuple[str, int, int]] = []
    for line_index, line in enumerate(lines):
        for open_match in re.finditer(
            r"(?<![A-Za-z0-9_'.])open\s+(.+?)\s+in\b",
            line,
        ):
            tail = line[open_match.end() :].strip()
            end = (
                line_starts[line_index] + len(line)
                if tail
                else scoped_line_end(line_index, max(-1, _line_indent(line) - 1))
            )
            for namespace in re.findall(
                _LEAN_QUALIFIED_NAME_PATTERN,
                open_match.group(1),
            ):
                open_namespace_ranges.append(
                    (
                        namespace,
                        line_starts[line_index] + open_match.end(),
                        end,
                    )
                )

    refs: Set[str] = set()
    for match in _LEAN_IDENTIFIER_RE.finditer(scan_text):
        raw_token = match.group(0)
        if _lean_identifier_is_record_field_label(scan_text, match.end()):
            continue
        if _lean_identifier_is_projection_field(scan_text, match.start()):
            continue
        token = raw_token
        token_start = match.start()
        if token not in name_set:
            terminal = raw_token.rsplit(".", 1)[-1]
            receiver = helper_prefix(raw_token)
            if raw_token.startswith("_root_."):
                root_name = raw_token[len("_root_.") :]
                rooted_receiver = helper_prefix(root_name)
                if rooted_receiver:
                    token = rooted_receiver
                    token_start = match.start() + len("_root_.")
                elif root_name in name_set:
                    token = root_name
                    token_start = match.start() + len("_root_.")
                elif "." not in root_name and terminal in name_set:
                    token = terminal
                    token_start = match.end() - len(terminal)
                else:
                    continue
            elif receiver in name_set:
                receiver_head = receiver.split(".", 1)[0]
                if any(
                    start <= match.start() < end
                    for start, end in local_ranges.get(receiver_head, ())
                ):
                    continue
                token = receiver
                token_start = match.start()
            else:
                opened = ""
                for namespace, start, end in open_namespace_ranges:
                    candidate = helper_prefix(f"{namespace}.{raw_token}")
                    if start <= match.start() < end and candidate:
                        opened = candidate
                        break
                if opened:
                    token = opened
                    token_start = match.start()
                else:
                    continue
        elif "." in token and not token.startswith("_root_."):
            token_head = token.split(".", 1)[0]
            if any(
                start <= match.start() < end
                for start, end in local_ranges.get(token_head, ())
            ):
                continue
        if token not in name_set:
            continue
        if (
            not _lean_identifier_has_root_qualifier(scan_text, token_start)
            and any(
                start <= token_start < end
                for start, end in local_ranges.get(token, ())
            )
        ):
            continue
        refs.add(token)
    return refs


def _residual_target_needs_continuation(text: str) -> bool:
    rhs = str(text or "").strip()
    if not rhs:
        return False
    balance = 0
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closes = {value: key for key, value in pairs.items()}
    for ch in rhs:
        if ch in pairs:
            balance += 1
        elif ch in closes:
            balance = max(0, balance - 1)
    return balance > 0 or rhs.endswith(_RESIDUAL_TARGET_CONTINUATION_SUFFIXES)


def _is_local_name_char(ch: str) -> bool:
    return ch == "'" or ch == "_" or ch == "✝" or ch.isalnum()


def _has_local_name_boundary(text: str, start: int, end: int) -> bool:
    before_ok = start <= 0 or (
        not _is_local_name_char(text[start - 1]) and text[start - 1] != "."
    )
    after_ok = (
        end >= len(text)
        or not _is_local_name_char(text[end])
        or text[end] == "."
    )
    return before_ok and after_ok


def _replace_local_names_tokenwise_text(
    text: str,
    replacements: Dict[str, str],
) -> str:
    source = str(text or "")
    names = sorted(
        (
            str(old)
            for old, new in replacements.items()
            if old and str(old) != str(new)
        ),
        key=len,
        reverse=True,
    )
    if not source or not names:
        return source
    pieces: List[str] = []
    index = 0
    while index < len(source):
        if source.startswith("«", index):
            end = source.find("»", index + 1)
            if end < 0:
                pieces.append(source[index:])
                break
            quoted = source[index : end + 1]
            replacement = replacements.get(quoted)
            pieces.append(str(replacement) if replacement is not None else quoted)
            index = end + 1
            continue
        lexical_end = _lean_lexical_skip_end(source, index)
        if lexical_end is not None:
            pieces.append(source[index:lexical_end])
            index = lexical_end
            continue
        matched = ""
        for old in names:
            end = index + len(old)
            if (
                source.startswith(old, index)
                and _has_local_name_boundary(source, index, end)
            ):
                matched = old
                break
        if matched:
            pieces.append(str(replacements[matched]))
            index += len(matched)
        else:
            pieces.append(source[index])
            index += 1
    return "".join(pieces)


def _lean_quote_end(text: str, index: int) -> int:
    """Return the end of any non-executable Lean lexical island.

    This historical helper began as quoted-identifier handling, but every
    caller is an operator/depth scanner and therefore must also ignore strings,
    raw strings, character literals, and comments.  Centralizing the complete
    lexical boundary prevents an arrow or binder glyph inside a literal from
    changing proposition identity.
    """

    end = _lean_lexical_skip_end(str(text or ""), index)
    return int(end) if end is not None else -1


def _scan_lean_depth(text: str, index: int, depth: int) -> int:
    ch = text[index]
    if ch in "([{⟨":
        return depth + 1
    if ch in ")]}⟩":
        return max(0, depth - 1)
    return depth


def _balanced_outer_parens(text: str) -> bool:
    if not (text.startswith("(") and text.endswith(")")):
        return False
    depth = 0
    index = 0
    while index < len(text):
        quote_end = _lean_quote_end(text, index)
        if quote_end > index:
            index = quote_end
            continue
        depth = _scan_lean_depth(text, index, depth)
        if depth == 0 and index < len(text) - 1:
            return False
        index += 1
    return depth == 0


def _strip_balanced_outer_parens(text: str) -> str:
    out = str(text or "").strip()
    while _balanced_outer_parens(out):
        out = out[1:-1].strip()
    return out


def _find_top_level_operator(text: str, operator: str) -> int:
    expr = str(text or "")
    op = str(operator or "")
    if not expr or not op:
        return -1
    depth = 0
    index = 0
    while index < len(expr):
        quote_end = _lean_quote_end(expr, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0 and expr.startswith(op, index):
            # ``=`` is also the first character of Lean's lambda/match
            # branch arrow ``=>``.  Treating that arrow as a relation split
            # corrupts pattern lambdas such as ``fun | 0 => a | n => b`` and
            # can manufacture a different durable statement identity.  The
            # longer relation glyphs are handled by their own operator scans;
            # this guard is deliberately lexical and fail-closed.
            if op == "=" and index + 1 < len(expr) and expr[index + 1] == ">":
                index += 2
                continue
            if op == ">" and index > 0 and expr[index - 1] in {"=", "-"}:
                index += 1
                continue
            return index
        depth = _scan_lean_depth(expr, index, depth)
        index += 1
    return -1


def _find_top_level_comma(text: str) -> int:
    raw = str(text or "")
    depth = 0
    index = 0
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0 and raw[index] == ",":
            return index
        depth = _scan_lean_depth(raw, index, depth)
        index += 1
    return -1


def _find_top_level_colon(text: str) -> int:
    raw = str(text or "")
    depth = 0
    index = 0
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0 and raw[index] == ":":
            return index
        depth = _scan_lean_depth(raw, index, depth)
        index += 1
    return -1


def _split_relation_binder_inner(text: str) -> Tuple[str, str, str]:
    raw = str(text or "").strip()
    parts = lean_relation_binder_parts(raw)
    return parts if parts is not None else ("", "", "")


def _relation_binder_prefix_expects_group_rhs(text: str) -> bool:
    raw = str(text or "").strip()
    if not raw:
        return False
    for token in sorted(_LEAN_RELATION_BINDER_TOKENS, key=len, reverse=True):
        if not raw.endswith(token):
            continue
        left = raw[: -len(token)].strip()
        names = _parse_binder_names(left)
        if names and left == " ".join(names):
            return True
    return False


def _has_goal_operator(text: str, symbol: str) -> bool:
    haystack = str(text or "")
    index = 0
    if symbol == "∑":
        while index < len(haystack):
            quote_end = _lean_quote_end(haystack, index)
            if quote_end > index:
                index = quote_end
                continue
            if haystack.startswith("∑", index) and not haystack.startswith("∑'", index):
                return True
            index += 1
        return False
    if symbol == ">":
        while index < len(haystack):
            quote_end = _lean_quote_end(haystack, index)
            if quote_end > index:
                index = quote_end
                continue
            if haystack[index] == ">" and (
                index <= 0 or haystack[index - 1] not in {"-", "="}
            ):
                return True
            index += 1
        return False
    if symbol == "<":
        while index < len(haystack):
            quote_end = _lean_quote_end(haystack, index)
            if quote_end > index:
                index = quote_end
                continue
            if haystack[index] == "<" and (
                index + 1 >= len(haystack) or haystack[index + 1] not in {"-", "="}
            ):
                return True
            index += 1
        return False
    if symbol == "=":
        while index < len(haystack):
            quote_end = _lean_quote_end(haystack, index)
            if quote_end > index:
                index = quote_end
                continue
            if haystack[index] == "=" and (
                (index <= 0 or haystack[index - 1] not in {":", "<", ">", "!", "="})
                and (
                    index + 1 >= len(haystack)
                    or haystack[index + 1] not in {">", "="}
                )
            ):
                return True
            index += 1
        return False
    while index < len(haystack):
        quote_end = _lean_quote_end(haystack, index)
        if quote_end > index:
            index = quote_end
            continue
        if haystack.startswith(symbol, index):
            return True
        index += 1
    return False


def _leading_quantifier_body(
    text: str,
    *,
    quantifiers: Sequence[str],
) -> Tuple[str, str, str]:
    expr = _strip_balanced_outer_parens(str(text or "").strip())
    for keyword in quantifiers:
        if expr == keyword or expr.startswith(keyword + " "):
            rest = expr[len(keyword) :].strip()
            comma = _find_identity_quantifier_comma(rest)
            if comma >= 0:
                quantifier = "∀" if keyword == "forall" else ("∃" if keyword == "exists" else keyword)
                return quantifier, rest[:comma].strip(), rest[comma + 1 :].strip()
    return "", "", expr


def _find_identity_quantifier_comma(text: str) -> int:
    """Find the comma ending a Lean quantifier binder sequence.

    A plain top-level-comma scan is unsound for bounded binders whose bound
    contains binder notation of its own. In ``∀ E ⊆ ⋃ i, f i, P E`` the first
    top-level comma belongs to ``⋃`` and the second closes the outer ``∀``.
    Treating the first as the quantifier separator silently changes scope and
    proposition shape.

    Big-operator binders are right-scoped and each consumes one top-level
    comma. Parenthesized commas are already hidden by the depth tracker;
    nested big operators increment the pending count independently.
    """

    raw = str(text or "")
    depth = 0
    pending_big_operator_commas = 0
    index = 0
    while index < len(raw):
        lexical_end = _lean_lexical_skip_end(raw, index)
        if lexical_end is not None:
            index = lexical_end
            continue
        ch = raw[index]
        if (
            depth == 0
            and ch in {"⋃", "⋂", "∑", "∏", "⨆", "⨅"}
            and not _is_unindexed_set_operator_at(raw, index)
        ):
            pending_big_operator_commas += 1
            # ``∑'`` is a single binder form for identity purposes.
            index += 2 if ch == "∑" and raw.startswith("∑'", index) else 1
            continue
        if depth == 0 and ch == ",":
            if pending_big_operator_commas > 0:
                pending_big_operator_commas -= 1
                index += 1
                continue
            return index
        depth = _scan_lean_depth(raw, index, depth)
        index += 1
    return -1


def _leading_forall_body(text: str) -> Tuple[str, str]:
    _quantifier, binder, body = _leading_quantifier_body(
        text,
        quantifiers=("∀", "forall"),
    )
    return binder, body


def _leading_identity_quantifier_body(text: str) -> Tuple[str, str, str]:
    return _leading_quantifier_body(
        text,
        quantifiers=("∀", "forall", "∃", "exists"),
    )


def _implicit_chained_relation_binder(text: str) -> Tuple[str, str]:
    """Split the next comma-delimited bounded binder from a quantifier body.

    Lean accepts chains such as ``∀ x ∈ s, y ∈ t, P x y``.  The first comma
    closes ``x ∈ s`` but the following ``y ∈ t`` is still governed by the same
    quantifier.  Once the leading quantifier has been split, that second binder
    has no explicit ``∀``/``∃`` token, so ordinary expression recursion would
    leave it (and its occurrences) un-normalized.
    """

    raw = str(text or "").strip()
    # Use the big-operator-aware comma finder: in ``x ∈ ⋃ i, s i → P x`` the
    # first top-level comma belongs to ``⋃``, and treating it as the chained-
    # binder separator fabricates a bounded binder over ``x ∈ ⋃ i`` (the same
    # comma-ownership bug _find_identity_quantifier_comma exists to prevent).
    comma = _find_identity_quantifier_comma(raw)
    if comma < 0:
        return "", raw
    binder = raw[:comma].strip()
    body = raw[comma + 1 :].strip()
    # The IMPLICATION form ``∀ x, x ∈ S → ∀ y, …`` hands this function a body
    # whose first eligible comma belongs to the INNER quantifier, making the
    # candidate binder slice span the arrow (``x ∈ S → ∀ y``). A genuine
    # chained bounded binder slice is a bare relation (``y ∈ t``), possibly
    # with big-operator commas inside the bound, but never with an
    # unparenthesized top-level arrow or quantifier token — reject those
    # slices, or the fabricated binder breaks α-stability of the identity key
    # (b2 digest-pin regression: dangling ``_b`` name + inner variable left
    # un-renamed).
    if _split_top_level_operator_sequence(binder, ("→", "->")) is not None:
        return "", raw
    if _contains_top_level_quantifier_token(binder):
        return "", raw
    left, operator, right = _split_relation_binder_inner(binder)
    names = _parse_binder_names(left)
    if not (
        left
        and operator
        and right
        and body
        and names
        and left == " ".join(names)
    ):
        return "", raw
    return binder, body


def _contains_top_level_quantifier_token(text: str) -> bool:
    expr = str(text or "")
    depth = 0
    index = 0
    while index < len(expr):
        quote_end = _lean_quote_end(expr, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0 and expr[index] in "∀∃":
            return True
        depth = _scan_lean_depth(expr, index, depth)
        index += 1
    return False


def _find_top_level_lambda_arrow(text: str) -> int:
    expr = str(text or "")
    depth = 0
    index = 0
    while index < len(expr):
        quote_end = _lean_quote_end(expr, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0 and expr.startswith("=>", index):
            return index
        depth = _scan_lean_depth(expr, index, depth)
        index += 1
    return -1


def _leading_identity_fun_body(text: str) -> Tuple[str, str, str]:
    expr = _strip_balanced_outer_parens(str(text or "").strip())
    if re.match(r"^fun\b", expr):
        keyword_length = len("fun")
    elif expr.startswith("λ"):
        keyword_length = len("λ")
    else:
        return "", "", expr
    rest = expr[keyword_length:].strip()
    if not rest or rest.startswith("|"):
        return "", "", expr
    arrow = _find_top_level_lambda_arrow(rest)
    if arrow < 0:
        return "", "", expr
    binder_text = rest[:arrow].strip()
    body = rest[arrow + 2 :].strip()
    if not binder_text or not body:
        return "", "", expr
    # Normalize both Lean lambda spellings to one identity representation.
    return "fun", binder_text, body


def _find_lambda_body_end(text: str, start: int) -> int:
    raw = str(text or "")
    depth = 0
    index = max(0, int(start or 0))
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            index = quote_end
            continue
        ch = raw[index]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            if depth == 0:
                return index
            depth -= 1
        index += 1
    return len(raw)


def _parse_lambda_at(text: str, start: int) -> Optional[Dict[str, Any]]:
    raw = str(text or "")
    if _starts_word_at(raw, start, "fun"):
        keyword_length = len("fun")
    elif start < len(raw) and raw[start] == "λ":
        keyword_length = len("λ")
    else:
        return None
    index = start + keyword_length
    while index < len(raw) and raw[index].isspace():
        index += 1
    if index >= len(raw) or raw[index] == "|":
        return None
    arrow = _find_top_level_lambda_arrow(raw[index:])
    if arrow < 0:
        return None
    arrow_index = index + arrow
    binder_text = raw[index:arrow_index].strip()
    body_start = arrow_index + 2
    body_end = _find_lambda_body_end(raw, body_start)
    body = raw[body_start:body_end].strip()
    if not binder_text or not body:
        return None
    return {
        "binder": binder_text,
        "body": body,
        "start": start,
        "end": body_end,
    }


def _canonicalize_lambda_expr(
    expr: str,
    *,
    replacements: Dict[str, str],
    next_index: int,
) -> Tuple[str, int, bool]:
    raw = str(expr or "").strip()
    pieces: List[str] = []
    segment_start = 0
    index = 0
    changed = False
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            index = quote_end
            continue
        parsed = _parse_lambda_at(raw, index)
        if parsed is None:
            index += 1
            continue
        pieces.append(
            _replace_local_names_tokenwise_text(
                raw[segment_start:index],
                replacements,
            )
        )
        scoped_replacements = dict(replacements)
        group_texts = _split_binder_groups(str(parsed["binder"])) or [
            str(parsed["binder"])
        ]
        normalized_groups: List[str] = []
        for group in group_texts:
            normalized_group, next_index, _names = _canonicalize_binder_group(
                group,
                replacements=scoped_replacements,
                next_index=next_index,
            )
            if normalized_group:
                normalized_groups.append(normalized_group)
        body_norm, next_index = _canonicalize_identity_expr(
            str(parsed["body"] or ""),
            replacements=scoped_replacements,
            next_index=next_index,
        )
        prefix = " ".join(normalized_groups)
        pieces.append(f"fun {prefix} => {body_norm}" if prefix else f"fun => {body_norm}")
        index = int(parsed["end"])
        segment_start = index
        changed = True
    if changed:
        pieces.append(
            _replace_local_names_tokenwise_text(raw[segment_start:], replacements)
        )
        return "".join(pieces), next_index, True
    return _replace_local_names_tokenwise_text(raw, replacements), next_index, False


def _lambda_bound_names(text: str) -> List[str]:
    out: List[str] = []
    seen: Set[str] = set()

    def add(name: str) -> None:
        if name not in seen:
            seen.add(name)
            out.append(name)

    def visit(raw_text: str) -> None:
        raw = str(raw_text or "")
        index = 0
        while index < len(raw):
            quote_end = _lean_quote_end(raw, index)
            if quote_end > index:
                index = quote_end
                continue
            parsed = _parse_lambda_at(raw, index)
            if parsed is None:
                index += 1
                continue
            for group in _split_binder_groups(str(parsed["binder"])) or [
                str(parsed["binder"])
            ]:
                item = str(group or "").strip()
                if item[:1] in "({[" and item[-1:] in ")}]":
                    item = item[1:-1].strip()
                colon = _find_top_level_colon(item)
                lhs = item[:colon].strip() if colon >= 0 else item
                for name in _parse_binder_names(lhs):
                    add(name)
            visit(str(parsed.get("body") or ""))
            index = max(index + 1, int(parsed["end"]))

    visit(text)
    return out


def _split_top_level_arrow_conclusion(text: str) -> str:
    expr = str(text or "")
    depth = 0
    last = -1
    last_len = 0
    index = 0
    while index < len(expr):
        quote_end = _lean_quote_end(expr, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0:
            # ``=>`` belongs to lambda/match syntax in Lean 4; it is never a
            # proposition implication.  Treating an embedded lambda arrow as
            # a top-level implication corrupts both its scope and statement
            # identity (for example ``d = fun n => f n``).
            for arrow in ("→", "->"):
                if expr.startswith(arrow, index):
                    last = index
                    last_len = len(arrow)
                    break
        depth = _scan_lean_depth(expr, index, depth)
        index += 1
    if last >= 0:
        return expr[last + last_len :].strip()
    return expr


def _balanced_group_end(text: str, start: int) -> int:
    if start < 0 or start >= len(text) or text[start] not in "({[":
        return -1
    pairs = {"(": ")", "{": "}", "[": "]"}
    close = pairs[text[start]]
    depth = 0
    index = start
    while index < len(text):
        quote_end = _lean_quote_end(text, index)
        if quote_end > index:
            index = quote_end
            continue
        ch = text[index]
        if ch == text[start]:
            depth += 1
        elif ch == close:
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return -1


def _parse_binder_names(lhs: str) -> List[str]:
    out: List[str] = []
    source = str(lhs or "").strip()
    index = 0
    while index < len(source):
        while index < len(source) and source[index].isspace():
            index += 1
        if index >= len(source):
            break
        match = _LEAN_LOCAL_TOKEN_RE.match(source, index)
        if match is None:
            # Binder patterns (for example ``(x, y)``) are not a prefix list
            # of ordinary binders.  Returning a partial prefix here makes the
            # identity normalizer rewrite only ``x`` while accidentally
            # capturing ``y`` from an outer telescope, which can equate
            # different propositions.  Unknown binder syntax must remain
            # layout-sensitive until a complete pattern parser handles it.
            return []
        clean = match.group(0).strip()
        index = match.end()
        if not clean or clean == "_" or clean in _LEAN_RESERVED_LOCAL_NAMES:
            continue
        out.append(clean)
    return out


def _blank_lean_quoted_identifier_contents(text: str) -> str:
    raw = str(text or "")
    pieces: List[str] = []
    index = 0
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            pieces.append(" " * (quote_end - index))
            index = quote_end
            continue
        pieces.append(raw[index])
        index += 1
    return "".join(pieces)


_BIG_OPERATOR_BINDER_RE = re.compile(
    r"(?:∑'|[∑∏⋃⋂⨆⨅])\s*(?P<binder>«[^»]+»|(?:[^\W\d]|_)[\w'✝]*|\([^()\n]*\)|\{[^{}\n]*\}|\[[^\[\]\n]*\])\s*(?:∈|\bin\b|[:,])",
    flags=re.UNICODE,
)


def _is_unindexed_set_operator_at(text: str, index: int) -> bool:
    """Whether ``index`` starts Mathlib's comma-free ``⋃₀``/``⋂₀`` form."""

    raw = str(text or "")
    return raw.startswith("⋃₀", index) or raw.startswith("⋂₀", index)


def _big_operator_bound_names(text: str) -> List[str]:
    out: List[str] = []
    seen: Set[str] = set()

    def add(name: str) -> None:
        if name not in seen:
            seen.add(name)
            out.append(name)

    def visit(raw: str) -> None:
        raw_text = str(raw or "")
        index = 0
        while index < len(raw_text):
            quote_end = _lean_quote_end(raw_text, index)
            if quote_end > index:
                index = quote_end
                continue
            if raw_text[index] not in {"∑", "∏", "⋃", "⋂", "⨆", "⨅"}:
                index += 1
                continue
            if _is_unindexed_set_operator_at(raw_text, index):
                index += 2
                continue
            parsed = _parse_big_operator_at(raw_text, index)
            if parsed is None:
                index += 1
                continue
            _binder_norm, names = _normalize_big_operator_binder_text(
                str(parsed.get("binder") or ""),
                replacements={},
            )
            for name in names:
                add(name)
            visit(str(parsed.get("body") or ""))
            index = max(index + 1, int(parsed.get("end") or index + 1))

    visit(text)
    return out


def _starts_word_at(text: str, index: int, word: str) -> bool:
    if not str(text or "").startswith(word, index):
        return False
    before = text[index - 1] if index > 0 else ""
    after_index = index + len(word)
    after = text[after_index] if after_index < len(text) else ""
    return not (
        (before and re.match(r"[\w'✝]", before, flags=re.UNICODE))
        or (after and re.match(r"[\w'✝]", after, flags=re.UNICODE))
    )


def _find_top_level_comma_from(text: str, start: int) -> int:
    depth = 0
    index = max(0, int(start or 0))
    while index < len(text):
        quote_end = _lean_quote_end(text, index)
        if quote_end > index:
            index = quote_end
            continue
        ch = text[index]
        if ch == "," and depth == 0:
            return index
        depth = _scan_lean_depth(text, index, depth)
        index += 1
    return -1


def _find_big_operator_body_end(text: str, start: int) -> int:
    raw = str(text or "")
    depth = 0
    index = max(0, int(start or 0))
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            index = quote_end
            continue
        ch = raw[index]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            if depth == 0:
                return index
            depth -= 1
        index += 1
    return len(raw)


def _parse_big_operator_at(text: str, start: int) -> Optional[Dict[str, Any]]:
    raw = str(text or "")
    if start < 0 or start >= len(raw) or raw[start] not in {"∑", "∏", "⋃", "⋂", "⨆", "⨅"}:
        return None
    if _is_unindexed_set_operator_at(raw, start):
        return None
    operator = raw[start : start + 2] if raw.startswith("∑'", start) else raw[start]
    index = start + len(operator)
    while index < len(raw) and raw[index].isspace():
        index += 1
    if index >= len(raw):
        return None
    binder_start = index
    parsed_binder = False
    while index < len(raw):
        while index < len(raw) and raw[index].isspace():
            index += 1
        if index >= len(raw):
            break
        if parsed_binder and (
            raw[index] in {"∈", ":", ","} or _starts_word_at(raw, index, "in")
        ):
            break
        if raw[index] in "({[":
            binder_end = _balanced_group_end(raw, index)
            if binder_end < 0:
                return None
            index = binder_end + 1
            parsed_binder = True
            continue
        match = _LEAN_LOCAL_TOKEN_RE.match(raw, index)
        if match is None:
            break
        index = match.end()
        parsed_binder = True
    if not parsed_binder:
        return None
    binder_raw = raw[binder_start:index].strip()
    while index < len(raw) and raw[index].isspace():
        index += 1
    delimiter = ""
    if index < len(raw) and raw[index] == "∈":
        delimiter = "∈"
        payload_start = index + 1
    elif _starts_word_at(raw, index, "in"):
        delimiter = "∈"
        payload_start = index + 2
    elif index < len(raw) and raw[index] == ":":
        delimiter = ":"
        payload_start = index + 1
    elif index < len(raw) and raw[index] == ",":
        delimiter = ","
        payload_start = index + 1
    else:
        return None

    if delimiter == ",":
        payload = ""
        body_start = payload_start
    else:
        comma = _find_top_level_comma_from(raw, payload_start)
        if comma < 0:
            return None
        payload = raw[payload_start:comma].strip()
        body_start = comma + 1
    body_end = _find_big_operator_body_end(raw, body_start)
    body = raw[body_start:body_end].strip()
    if not body:
        return None
    return {
        "operator": operator,
        "binder": binder_raw,
        "delimiter": delimiter,
        "payload": payload,
        "body": body,
        "start": start,
        "end": body_end,
    }


def _normalize_big_operator_binder_text(
    binder_raw: str,
    *,
    replacements: Dict[str, str],
) -> Tuple[str, List[str]]:
    raw = str(binder_raw or "").strip()
    group_texts = _split_binder_groups(raw)
    if len(group_texts) > 1:
        normalized_groups: List[str] = []
        all_names: List[str] = []
        for group in group_texts:
            normalized_group, names = _normalize_big_operator_binder_text(
                group,
                replacements=replacements,
            )
            if normalized_group:
                normalized_groups.append(normalized_group)
            all_names.extend(names)
        return " ".join(normalized_groups), all_names
    opener = raw[0] if raw[:1] in "({[" else ""
    closer = {"(": ")", "{": "}", "[": "]"}.get(opener, "")
    inner = raw[1:-1].strip() if opener and raw.endswith(closer) else raw
    colon = _find_top_level_colon(inner)
    lhs = inner[:colon].strip() if colon >= 0 else inner
    typ = inner[colon + 1 :].strip() if colon >= 0 else ""
    names = _parse_binder_names(lhs)
    if not names:
        return _replace_local_names_tokenwise_text(raw, replacements), []
    lhs_norm = lhs
    if typ:
        typ_norm = _replace_local_names_tokenwise_text(
            _normalize_ascii_arrows_outside_lean_quotes(typ),
            replacements,
        )
        inner_norm = f"{lhs_norm} : {typ_norm}"
    else:
        inner_norm = lhs_norm
    if opener:
        return f"{opener}{inner_norm}{closer}", names
    return inner_norm, names


def _canonicalize_big_operator_binder_sequence(
    binder_raw: str,
    *,
    replacements: Dict[str, str],
    next_index: int,
) -> Tuple[str, List[str], Dict[str, str], int]:
    scoped_replacements = dict(replacements)
    group_texts = _split_binder_groups(str(binder_raw or "").strip()) or [
        str(binder_raw or "").strip()
    ]
    normalized_groups: List[str] = []
    all_names: List[str] = []
    for group in group_texts:
        normalized_group, next_index, names = _canonicalize_binder_group(
            group,
            replacements=scoped_replacements,
            next_index=next_index,
        )
        if normalized_group:
            normalized_groups.append(normalized_group)
        all_names.extend(names)
    return " ".join(normalized_groups), all_names, scoped_replacements, next_index


def _canonicalize_big_operator_expr(
    expr: str,
    *,
    replacements: Dict[str, str],
    next_index: int,
) -> Tuple[str, int, bool]:
    raw = str(expr or "").strip()
    pieces: List[str] = []
    segment_start = 0
    index = 0
    changed = False
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            index = quote_end
            continue
        if raw[index] not in {"∑", "∏", "⋃", "⋂", "⨆", "⨅"}:
            index += 1
            continue
        if _is_unindexed_set_operator_at(raw, index):
            index += 2
            continue
        parsed = _parse_big_operator_at(raw, index)
        if parsed is None:
            index += 1
            continue
        pieces.append(
            _replace_local_names_tokenwise_text(
                raw[segment_start:index],
                replacements,
            )
        )
        binder_norm, names, scoped_replacements, next_index = (
            _canonicalize_big_operator_binder_sequence(
                parsed["binder"],
                replacements=replacements,
                next_index=next_index,
            )
        )
        if not names:
            index += 1
            continue
        payload = str(parsed["payload"] or "")
        if parsed["delimiter"] == ":":
            payload_norm, next_index = _canonicalize_identity_expr(
                _normalize_ascii_arrows_outside_lean_quotes(
                    _replace_local_names_tokenwise_text(payload, replacements)
                ),
                replacements=dict(replacements),
                next_index=next_index,
            )
            head = f"{parsed['operator']} {binder_norm} : {payload_norm}, "
        elif parsed["delimiter"] == "∈":
            payload_norm, next_index = _canonicalize_identity_expr(
                _replace_local_names_tokenwise_text(payload, replacements),
                replacements=dict(replacements),
                next_index=next_index,
            )
            head = f"{parsed['operator']} {binder_norm} ∈ {payload_norm}, "
        else:
            head = f"{parsed['operator']} {binder_norm}, "
        body_norm, next_index = _canonicalize_identity_expr(
            str(parsed["body"] or ""),
            replacements=scoped_replacements,
            next_index=next_index,
        )
        pieces.append(head + body_norm)
        index = int(parsed["end"])
        segment_start = index
        changed = True
    if changed:
        pieces.append(
            _replace_local_names_tokenwise_text(raw[segment_start:], replacements)
        )
        return "".join(pieces), next_index, True
    return _replace_local_names_tokenwise_text(raw, replacements), next_index, False


def _canonicalize_binder_group(
    group_text: str,
    *,
    replacements: Dict[str, str],
    next_index: int,
) -> Tuple[str, int, List[str]]:
    text = str(group_text or "").strip()
    if not text:
        return "", next_index, []
    opener = text[0] if text[:1] in "({[" else ""
    closer = {"(": ")", "{": "}", "[": "]"}.get(opener, "")
    inner = text[1:-1].strip() if opener and text.endswith(closer) else text
    relation_left, relation_op, relation_right = _split_relation_binder_inner(
        inner
    )
    relation_names = _parse_binder_names(relation_left)
    if (
        relation_left
        and relation_op
        and relation_right
        and relation_names
        and relation_left == " ".join(relation_names)
    ):
        name_replacements: Dict[str, str] = {}
        normalized_names: List[str] = []
        for offset, name in enumerate(relation_names):
            name_replacements[name] = f"_b{next_index + offset}"
            normalized_names.append(name_replacements[name])
        next_index += len(relation_names)
        scoped_replacements = dict(replacements)
        scoped_replacements.update(name_replacements)
        right_norm, next_index = _canonicalize_identity_expr(
            _normalize_ascii_arrows_outside_lean_quotes(
                _replace_local_names_tokenwise_text(
                    relation_right,
                    scoped_replacements,
                )
            ),
            replacements=dict(scoped_replacements),
            next_index=next_index,
        )
        replacements.update(name_replacements)
        normalized_inner = f"{' '.join(normalized_names)} {relation_op} {right_norm}"
        return (
            opener + normalized_inner + closer if opener else normalized_inner,
            next_index,
            relation_names,
        )
    colon = _find_top_level_colon(inner)
    if colon < 0:
        if opener == "[":
            normalized_inner = _normalize_ascii_arrows_outside_lean_quotes(
                _replace_local_names_tokenwise_text(inner, replacements)
            )
            return opener + normalized_inner + closer, next_index, []
        names = _parse_binder_names(inner)
        if names:
            new_names: List[str] = []
            for name in names:
                replacements[name] = f"_b{next_index}"
                next_index += 1
                new_names.append(replacements[name])
            normalized_inner = " ".join(new_names)
            return (
                opener + normalized_inner + closer if opener else normalized_inner,
                next_index,
                names,
            )
        return (
            (
                opener
                + _normalize_ascii_arrows_outside_lean_quotes(
                    _replace_local_names_tokenwise_text(inner, replacements)
                )
                + closer
            )
            if opener
            else _normalize_ascii_arrows_outside_lean_quotes(
                _replace_local_names_tokenwise_text(inner, replacements)
            ),
            next_index,
            [],
        )
    lhs = inner[:colon].strip()
    typ = inner[colon + 1 :].strip()
    names = _parse_binder_names(lhs)
    if not names:
        lhs_norm = _replace_local_names_tokenwise_text(lhs, replacements)
        typ_norm, next_index = _canonicalize_identity_expr(
            _normalize_ascii_arrows_outside_lean_quotes(
                _replace_local_names_tokenwise_text(typ, replacements)
            ),
            replacements=dict(replacements),
            next_index=next_index,
        )
        normalized_inner = f"{lhs_norm} : {typ_norm}" if lhs_norm else typ_norm
        return (
            opener + normalized_inner + closer if opener else normalized_inner,
            next_index,
            [],
        )
    new_names: List[str] = []
    name_replacements: Dict[str, str] = {}
    for offset, name in enumerate(names):
        name_replacements[name] = f"_b{next_index + offset}"
        new_names.append(name_replacements[name])
    typ_norm, next_index = _canonicalize_identity_expr(
        _normalize_ascii_arrows_outside_lean_quotes(
            _replace_local_names_tokenwise_text(typ, replacements)
        ),
        replacements=dict(replacements),
        next_index=next_index + len(names),
    )
    replacements.update(name_replacements)
    normalized_inner = f"{' '.join(new_names)} : {typ_norm}"
    if opener:
        return opener + normalized_inner + closer, next_index, names
    return f"({' '.join(new_names)} : {typ_norm})", next_index, names


def _split_binder_groups(binder_text: str) -> List[str]:
    text = str(binder_text or "").strip()
    if not text:
        return []
    groups: List[str] = []
    index = 0
    while index < len(text):
        while index < len(text) and text[index].isspace():
            index += 1
        if index >= len(text):
            break
        # A relation-style bounded binder owns its entire right-hand
        # expression. Keeping the remainder together is essential when that
        # expression contains parenthesized binders of its own, such as
        # ``E ⊆ ⋃ (i : Fin k), ball ...``. The generic group splitter would
        # otherwise mistake ``(i : Fin k)`` for another outer quantifier
        # binder and silently change the proposition.
        relation_left, relation_op, relation_right = _split_relation_binder_inner(
            text[index:]
        )
        relation_names = _parse_binder_names(relation_left)
        if (
            relation_left
            and relation_op
            and relation_right
            and relation_names
            and relation_left == " ".join(relation_names)
        ):
            groups.append(text[index:].strip())
            break
        if text[index] in "({[":
            end = _balanced_group_end(text, index)
            if end < 0:
                groups.append(text[index:].strip())
                break
            groups.append(text[index : end + 1].strip())
            index = end + 1
            continue
        next_group = len(text)
        colon_seen = False
        depth = 0
        scan = index
        while scan < len(text):
            quote_end = _lean_quote_end(text, scan)
            if quote_end > scan:
                scan = quote_end
                continue
            ch = text[scan]
            if depth == 0 and ch == ":":
                colon_seen = True
            if depth == 0 and not colon_seen and ch in "({[":
                if _relation_binder_prefix_expects_group_rhs(text[index:scan]):
                    depth = _scan_lean_depth(text, scan, depth)
                    scan += 1
                    continue
                next_group = scan
                break
            depth = _scan_lean_depth(text, scan, depth)
            scan += 1
        prefix = text[index:next_group].strip()
        if prefix:
            groups.append(prefix)
        if next_group >= len(text):
            break
        index = next_group
    return groups


def _starts_right_scoped_identity_construct(text: str, index: int) -> bool:
    tail = str(text or "")[index:].lstrip()
    if not tail:
        return False
    candidate = (
        _strip_balanced_outer_parens(tail) if tail.startswith("(") else tail
    )
    if not (
        candidate.startswith(("∀ ", "∃ ", "forall ", "exists ", "let "))
        or candidate in {"∀", "∃", "forall", "exists"}
    ):
        return False
    _quantifier, binder, body = _leading_identity_quantifier_body(tail)
    if binder and body:
        return True
    let_head, let_value, let_body = _leading_identity_let_body(tail)
    return bool(let_head and let_value and let_body)


def _split_top_level_operator_sequence(
    text: str,
    operators: Sequence[str],
) -> Optional[Tuple[List[str], List[str]]]:
    expr = _strip_balanced_outer_parens(str(text or "").strip())
    ops = sorted([op for op in operators if op], key=len, reverse=True)
    if not expr or not ops:
        return None
    depth = 0
    parts: List[str] = []
    found_ops: List[str] = []
    start = 0
    index = 0
    while index < len(expr):
        matched = ""
        quote_end = _lean_quote_end(expr, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0:
            if _starts_right_scoped_identity_construct(expr, index):
                break
            for op in ops:
                if expr.startswith(op, index):
                    matched = op
                    break
        if matched:
            left = expr[start:index].strip()
            if not left:
                return None
            parts.append(left)
            found_ops.append(matched)
            index += len(matched)
            start = index
            continue
        depth = _scan_lean_depth(expr, index, depth)
        index += 1
    if not found_ops:
        return None
    tail = expr[start:].strip()
    if not tail:
        return None
    parts.append(tail)
    return parts, found_ops


def _split_let_value_body(text: str, *, let_head: str = "") -> Tuple[str, str]:
    raw = str(text or "").strip()
    if not raw:
        return "", ""
    value_starts_tactic = raw.lstrip().startswith("by")
    depth = 0
    index = 0
    while index < len(raw):
        quote_end = _lean_quote_end(raw, index)
        if quote_end > index:
            index = quote_end
            continue
        if depth == 0 and raw[index] == ";" and not value_starts_tactic:
            return raw[:index].strip(), raw[index + 1 :].strip()
        if (
            depth == 0
            and raw.startswith(" in ", index)
            and raw[:index].strip()
            and raw[index + 4 :].strip()
        ):
            return raw[:index].strip(), raw[index + 4 :].strip()
        depth = _scan_lean_depth(raw, index, depth)
        index += 1
    value, body = _split_layout_let_value_body(raw, let_head=let_head)
    if value and body:
        return value, body
    return raw, ""


def _split_layout_let_value_body(text: str, *, let_head: str = "") -> Tuple[str, str]:
    raw = str(text or "").strip()
    if "\n" not in raw:
        return raw, ""
    lines = raw.splitlines()
    if len(lines) < 2:
        return raw, ""

    def make_prefix(stop: int) -> str:
        value_prefix = "\n".join(lines[:stop]).strip()
        head = str(let_head or "").strip()
        if head and not head.startswith("let "):
            head = f"let {head}"
        if head:
            return f"{head} := {value_prefix}".strip()
        return f"let _x := {value_prefix}".strip()

    seen_blank = False
    for idx in range(1, len(lines)):
        line = lines[idx]
        stripped = line.strip()
        if not stripped:
            seen_blank = True
            continue
        prefix = make_prefix(idx)
        if (
            _layout_local_let_prefix_has_open_rhs(prefix)
            or _layout_local_let_prefix_expects_term_continuation(prefix)
            or _line_ends_with_open_proof_tail(prefix)
        ):
            seen_blank = False
            continue
        first_value_line = next((item.strip() for item in lines[:idx] if item.strip()), "")
        value_is_tactic = first_value_line.startswith("by")
        if value_is_tactic and _looks_like_tactic_proof_continuation_line(stripped):
            seen_blank = False
            continue
        if (
            seen_blank
            or _layout_local_let_trailer_looks_like_body(prefix, stripped)
            or (line[:1] in {" ", "\t"} and not value_is_tactic)
            or (value_is_tactic and not _looks_like_tactic_proof_continuation_line(stripped))
        ):
            value = "\n".join(lines[:idx]).strip()
            body = "\n".join(lines[idx:]).strip()
            if value and body:
                return value, body
        seen_blank = False
    return raw, ""


def _leading_identity_let_body(text: str) -> Tuple[str, str, str]:
    raw = _strip_balanced_outer_parens(str(text or "").strip())
    if not raw.startswith("let "):
        return "", "", ""
    head, tail = split_goal_definition_binding(raw)
    if not head or not tail:
        return "", "", ""
    head = head.strip()
    if not head.startswith("let "):
        return "", "", ""
    value, body = _split_let_value_body(tail, let_head=head[4:].strip())
    if not value or not body:
        return "", "", ""
    return head[4:].strip(), value, body


def _canonicalize_identity_expr(
    text: str,
    *,
    replacements: Dict[str, str],
    next_index: int,
) -> Tuple[str, int]:
    expr = _strip_balanced_outer_parens(str(text or "").strip())
    let_head, let_value, let_body = _leading_identity_let_body(expr)
    if let_head and let_value and let_body:
        scoped_replacements = dict(replacements)
        colon = _find_top_level_colon(let_head)
        lhs = let_head[:colon].strip() if colon >= 0 else let_head.strip()
        typ = let_head[colon + 1 :].strip() if colon >= 0 else ""
        names = _parse_binder_names(lhs)
        if names:
            name = names[0]
            normalized_name = f"_b{next_index}"
            next_index += 1
            typ_norm = ""
            if typ:
                typ_norm, next_index = _canonicalize_identity_expr(
                    _normalize_ascii_arrows_outside_lean_quotes(
                        _replace_local_names_tokenwise_text(typ, replacements)
                    ),
                    replacements=dict(replacements),
                    next_index=next_index,
                )
            value_norm, next_index = _canonicalize_identity_expr(
                let_value,
                replacements=dict(replacements),
                next_index=next_index,
            )
            scoped_replacements[name] = normalized_name
            body_norm, next_index = _canonicalize_identity_expr(
                let_body,
                replacements=scoped_replacements,
                next_index=next_index,
            )
            head_norm = (
                f"{normalized_name} : {typ_norm}" if typ_norm else normalized_name
            )
            return f"let {head_norm} := {value_norm}; {body_norm}", next_index
    lambda_keyword, lambda_binder_text, lambda_body = _leading_identity_fun_body(expr)
    if lambda_binder_text:
        scoped_replacements = dict(replacements)
        group_texts = _split_binder_groups(lambda_binder_text) or [lambda_binder_text]
        normalized_groups: List[str] = []
        for group in group_texts:
            normalized_group, next_index, _names = _canonicalize_binder_group(
                group,
                replacements=scoped_replacements,
                next_index=next_index,
            )
            if normalized_group:
                normalized_groups.append(normalized_group)
        body_norm, next_index = _canonicalize_identity_expr(
            lambda_body,
            replacements=scoped_replacements,
            next_index=next_index,
        )
        prefix = " ".join(normalized_groups)
        if prefix:
            return f"{lambda_keyword} {prefix} => {body_norm}", next_index
        return f"{lambda_keyword} => {body_norm}", next_index
    quantifier, binder_text, body = _leading_identity_quantifier_body(expr)
    if binder_text:
        scoped_replacements = dict(replacements)
        group_texts = _split_binder_groups(binder_text) or [binder_text]
        normalized_groups: List[str] = []
        for group in group_texts:
            normalized_group, next_index, _names = _canonicalize_binder_group(
                group,
                replacements=scoped_replacements,
                next_index=next_index,
            )
            if normalized_group:
                normalized_groups.append(normalized_group)
        chained_binder, _chained_body = _implicit_chained_relation_binder(body)
        recursive_body = f"{quantifier} {body}" if chained_binder else body
        body_norm, next_index = _canonicalize_identity_expr(
            recursive_body,
            replacements=scoped_replacements,
            next_index=next_index,
        )
        prefix = " ".join(normalized_groups)
        if prefix:
            return f"{quantifier} {prefix}, {body_norm}", next_index
        return f"{quantifier} {body_norm}", next_index

    if expr.startswith("¬"):
        raw_tail = expr[1:].strip()
        tail, next_index = _canonicalize_identity_expr(
            raw_tail,
            replacements=dict(replacements),
            next_index=next_index,
        )
        if _balanced_outer_parens(raw_tail):
            if _strip_balanced_outer_parens(tail).startswith("let "):
                tail = f"({tail})"
                return f"¬ {tail}", next_index
            for nested_operator_group in (
                ("↔",),
                ("→", "->"),
                ("∨",),
                ("∧",),
            ):
                if _split_top_level_operator_sequence(
                    tail,
                    nested_operator_group,
                ) is not None:
                    tail = f"({tail})"
                    break
        return f"¬ {tail}", next_index

    # A lambda used as a relation operand extends to the end of its enclosing
    # term.  Lexical connective splitting cannot infer that scope: without
    # handling the relation first, ``f = fun x => P x ∧ Q x`` is wrongly
    # parsed as ``(f = fun x => P x) ∧ Q x``.  Canonicalize the lambda side
    # as one operand and always render it parenthesized.  That makes redundant
    # source parentheses converge while preserving a following connective's
    # actual Lean scope.
    for relation_operator in ("≠", "=", "≤", "≥", "<", ">", "∈", "∉", "∣"):
        relation_index = _find_top_level_operator(expr, relation_operator)
        if relation_index < 0:
            continue
        raw_left = expr[:relation_index].strip()
        raw_right = expr[relation_index + len(relation_operator) :].strip()
        if not raw_left or not raw_right:
            break
        left_core = _strip_balanced_outer_parens(raw_left)
        right_core = _strip_balanced_outer_parens(raw_right)
        left_is_lambda = left_core.startswith("fun ") or left_core.startswith("λ")
        right_is_lambda = right_core.startswith("fun ") or right_core.startswith("λ")
        if not left_is_lambda and not right_is_lambda:
            continue
        left_norm, next_index = _canonicalize_identity_expr(
            raw_left,
            replacements=dict(replacements),
            next_index=next_index,
        )
        right_norm, next_index = _canonicalize_identity_expr(
            raw_right,
            replacements=dict(replacements),
            next_index=next_index,
        )
        if left_is_lambda:
            left_norm = f"({left_norm})"
        if right_is_lambda:
            right_norm = f"({right_norm})"
        return f"{left_norm} {relation_operator} {right_norm}", next_index

    for operator_group in (
        ("↔",),
        ("→", "->"),
        ("∨",),
        ("∧",),
    ):
        split = _split_top_level_operator_sequence(expr, operator_group)
        if split is None:
            continue
        parts, operators = split
        normalized_parts: List[str] = []
        local_next = next_index
        for part_index, part in enumerate(parts):
            raw_part = str(part or "").strip()
            preserve_outer_parens = _balanced_outer_parens(raw_part)
            is_final_part = part_index == len(parts) - 1
            normalized, local_next = _canonicalize_identity_expr(
                part,
                replacements=dict(replacements),
                next_index=local_next,
            )
            # Lean parses ``→`` more tightly than ``↔``. Canonical rendering
            # must therefore parenthesize an implication used as an Iff side;
            # otherwise ``(H → A) ↔ B`` is emitted ambiguously and later
            # reparsed as ``H → (A ↔ B)``, collapsing distinct propositions.
            if (
                tuple(operator_group) == ("↔",)
                and not _balanced_outer_parens(normalized)
                and _split_top_level_operator_sequence(
                    normalized,
                    ("→", "->"),
                )
                is not None
            ):
                normalized = f"({normalized})"
            if preserve_outer_parens:
                if (
                    not is_final_part
                    and normalized.startswith(("∀ ", "∃ ", "forall ", "exists "))
                ):
                    normalized = f"({normalized})"
                    normalized_parts.append(normalized)
                    continue
                if is_final_part and normalized.startswith(
                    ("∀ ", "∃ ", "forall ", "exists ")
                ):
                    normalized_parts.append(normalized)
                    continue
                if normalized.startswith("let "):
                    if not is_final_part:
                        normalized = f"({normalized})"
                    normalized_parts.append(normalized)
                    continue
                if normalized.startswith("¬ "):
                    negated = normalized[2:].strip()
                    negated_tail = negated
                    while negated_tail.startswith("¬ "):
                        negated_tail = negated_tail[2:].strip()
                    negated_core = _strip_balanced_outer_parens(negated_tail)
                    negated_quantifier = negated_tail.startswith(
                        ("∀ ", "∃ ", "forall ", "exists ")
                    )
                    negated_let = negated_core.startswith("let ")
                    should_wrap_negation = bool(
                        (negated_quantifier or negated_let) and not is_final_part
                    )
                    for nested_operator_group in (
                        ("↔",),
                        ("→", "->"),
                        ("∨",),
                        ("∧",),
                    ):
                        if _split_top_level_operator_sequence(
                            negated_tail,
                            nested_operator_group,
                        ) is not None:
                            should_wrap_negation = not is_final_part
                            break
                    if should_wrap_negation:
                        normalized = f"({normalized})"
                        normalized_parts.append(normalized)
                        continue
                    if (negated_quantifier or negated_let) and is_final_part:
                        normalized_parts.append(normalized)
                        continue
                for nested_operator_group in (
                    ("↔",),
                    ("→", "->"),
                    ("∨",),
                    ("∧",),
                ):
                    if _split_top_level_operator_sequence(
                        normalized,
                        nested_operator_group,
                    ) is not None:
                        normalized = f"({normalized})"
                        break
            normalized_parts.append(normalized)
        out = normalized_parts[0]
        for op, normalized in zip(operators, normalized_parts[1:]):
            if op == "->":
                op = "→"
            out = f"{out} {op} {normalized}"
        return out, local_next

    lambda_norm, next_index, lambda_changed = _canonicalize_lambda_expr(
        expr,
        replacements=replacements,
        next_index=next_index,
    )
    if lambda_changed:
        big_operator_norm, next_index, big_operator_changed = _canonicalize_big_operator_expr(
            lambda_norm,
            replacements={},
            next_index=next_index,
        )
        return (big_operator_norm if big_operator_changed else lambda_norm), next_index

    big_operator_norm, next_index, changed = _canonicalize_big_operator_expr(
        expr,
        replacements=replacements,
        next_index=next_index,
    )
    if changed:
        return big_operator_norm, next_index
    return _replace_local_names_tokenwise_text(expr, replacements), next_index


def canonicalize_lean_statement_for_identity(
    statement: str,
    *,
    extra_bound_names: Sequence[str] = (),
) -> str:
    """Syntactically alpha-normalize a Lean proposition for graph/cache identity."""

    text = _identity_source_text(statement)
    text = _replace_type_symbols_capture_safe(text)
    text = _normalize_colon_spacing_outside_lean_quotes(text)
    replacements: Dict[str, str] = {}
    # Reserve fresh-name space: a statement literally containing _bN tokens
    # must not collide with generated alpha names (external review: canon of
    # `∀ x : Nat, x = _b0` equalled canon of `∀ x : Nat, x = x`).
    next_index = _next_free_alpha_index(text)
    for name in extra_bound_names:
        clean = str(name or "").strip()
        if clean and clean not in replacements:
            replacements[clean] = f"_b{next_index}"
            next_index += 1
    body, _next_index = _canonicalize_identity_expr(
        text,
        replacements=replacements,
        next_index=next_index,
    )

    return body


def lean_statement_bound_names(statement: str) -> List[str]:
    """Return names bound by syntactic forall/exists binders in a statement."""

    text = _identity_source_text(statement)
    out: List[str] = []
    def visit(expr: str) -> None:
        expr = _strip_balanced_outer_parens(str(expr or "").strip())
        let_head, let_value, let_body = _leading_identity_let_body(expr)
        if let_head and let_body:
            colon = _find_top_level_colon(let_head)
            lhs = let_head[:colon].strip() if colon >= 0 else let_head
            names = _parse_binder_names(lhs)
            out.extend(names[:1])
            visit(let_value)
            visit(let_body)
            return
        _lambda_keyword, lambda_binder_text, lambda_body = _leading_identity_fun_body(expr)
        if lambda_binder_text:
            scoped_names: List[str] = []
            for group in _split_binder_groups(lambda_binder_text) or [lambda_binder_text]:
                raw = str(group or "").strip()
                if raw[:1] in "({[" and raw[-1:] in ")}]":
                    raw = raw[1:-1].strip()
                colon = _find_top_level_colon(raw)
                lhs = raw[:colon].strip() if colon >= 0 else raw
                scoped_names.extend(_parse_binder_names(lhs))
            out.extend(scoped_names)
            visit(lambda_body)
            return
        _quantifier, binder_text, body = _leading_identity_quantifier_body(expr)
        if binder_text:
            scoped_names: List[str] = []
            for group in _split_binder_groups(binder_text) or [binder_text]:
                raw = str(group or "").strip()
                if raw[:1] in "({[" and raw[-1:] in ")}]":
                    raw = raw[1:-1].strip()
                colon = _find_top_level_colon(raw)
                lhs = raw[:colon].strip() if colon >= 0 else raw
                scoped_names.extend(_parse_binder_names(lhs))
            out.extend(scoped_names)
            visit(body)
            return
        if expr.startswith("¬ "):
            visit(expr[2:].strip())
            return
        for operator_group in (
            ("↔",),
            ("→", "->"),
            ("∨",),
            ("∧",),
        ):
            split = _split_top_level_operator_sequence(expr, operator_group)
            if split is None:
                continue
            parts, _operators = split
            for part in parts:
                visit(part)
            return

    visit(text)
    for name in _big_operator_bound_names(text):
        if name not in out:
            out.append(name)
    for name in _lambda_bound_names(text):
        if name not in out:
            out.append(name)
    return out


def lean_statement_forall_body(statement: str) -> str:
    """Return the body after canonical, scope-aware leading forall parsing."""

    text = _identity_source_text(statement)
    while True:
        _binder, body = _leading_forall_body(text)
        if body == text:
            break
        text = body
        while True:
            _binder, chained_body = _implicit_chained_relation_binder(text)
            if chained_body == text:
                break
            text = chained_body
    return text


def lean_statement_conclusion(statement: str) -> str:
    text = lean_statement_forall_body(statement)
    return _split_top_level_arrow_conclusion(text)


def _split_top_level_binary(text: str, operator: str) -> Optional[Tuple[str, str]]:
    expr = _strip_balanced_outer_parens(text)
    if re.match(r"^(?:∀|forall|fun)\b", expr):
        return None
    if re.match(r"^(?:∀|forall)\s", expr):
        return None
    if any(_find_top_level_operator(expr, item) >= 0 for item in ("→", "->")):
        return None
    if operator == "∧" and _find_top_level_operator(expr, "↔") >= 0:
        return None
    index = _find_top_level_operator(expr, operator)
    if index < 0:
        return None
    left = expr[:index].strip()
    right = expr[index + len(operator) :].strip()
    if not left or not right:
        return None
    return left, right


def _top_level_application_args(text: str, head: str) -> List[str]:
    expr = _strip_balanced_outer_parens(text)
    prefix = str(head or "").strip()
    if not prefix:
        return []
    if not (expr == prefix or expr.startswith(prefix + " ") or expr.startswith(prefix + "\n")):
        return []
    rest = expr[len(prefix) :].strip()
    if not rest:
        return []
    args: List[str] = []
    depth = 0
    start = 0
    index = 0
    while index < len(rest):
        ch = rest[index]
        if depth == 0 and ch.isspace():
            arg = rest[start:index].strip()
            if arg:
                args.append(arg)
            while index < len(rest) and rest[index].isspace():
                index += 1
            start = index
            continue
        depth = _scan_lean_depth(rest, index, depth)
        index += 1
    tail = rest[start:].strip()
    if tail:
        args.append(tail)
    return args


def _structural_decomposition_for_target(
    target: str,
) -> Tuple[str, List[Dict[str, Any]], str]:
    """Return generic proof-shape child goals for compound propositions."""

    expr = _strip_balanced_outer_parens(target)
    for head, bound_head in (
        ("IsLeast", "lowerBounds"),
        ("IsGreatest", "upperBounds"),
    ):
        args = _top_level_application_args(expr, head)
        if len(args) == 2:
            set_expr, point_expr = args
            return (
                "by\n  constructor",
                [
                    {"target": f"({point_expr}) ∈ ({set_expr})", "hypotheses": []},
                    {
                        "target": f"({point_expr}) ∈ {bound_head} ({set_expr})",
                        "hypotheses": [],
                    },
                ],
                head,
            )

    split = _split_top_level_binary(expr, "↔")
    if split is not None:
        left, right = split
        return (
            "by\n  constructor",
            [
                {"target": f"({left}) → ({right})", "hypotheses": []},
                {"target": f"({right}) → ({left})", "hypotheses": []},
            ],
            "iff",
        )

    split = _split_top_level_binary(expr, "∧")
    if split is not None:
        left, right = split
        return (
            "by\n  constructor",
            [
                {"target": left, "hypotheses": []},
                {"target": right, "hypotheses": []},
            ],
            "and",
        )

    return "", [], ""


@dataclass
class NormalizedProofGoal:
    """Stable, retrieval-oriented view of a Lean proof goal."""

    target_expr: str
    local_hypotheses: List[Dict[str, str]] = field(default_factory=list)
    constants_used: List[str] = field(default_factory=list)
    binder_structure: List[str] = field(default_factory=list)
    typeclass_needs: List[str] = field(default_factory=list)
    namespaces: List[str] = field(default_factory=list)
    result_head: str = ""
    normalized_statement: str = ""
    normalized_statement_hash: str = ""
    shape_tags: List[str] = field(default_factory=list)
    source_failure: str = ""

    def to_record(
        self,
        *,
        suppress_solution_placeholders: bool = True,
    ) -> Dict[str, Any]:
        redact_solution_refs = bool(suppress_solution_placeholders)
        return {
            "target_expr": _proof_state_durable_text(
                self.target_expr,
                limit=2000,
                suppress_solution_placeholders=suppress_solution_placeholders,
            ),
            "local_hypotheses": _proof_state_prompt_safe_value(
                [dict(item) for item in self.local_hypotheses],
                limit=1000,
                redact_solution_refs=redact_solution_refs,
            ),
            "constants_used": _proof_state_prompt_safe_value(
                list(self.constants_used),
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "binder_structure": _proof_state_prompt_safe_value(
                list(self.binder_structure),
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "typeclass_needs": _proof_state_prompt_safe_value(
                list(self.typeclass_needs),
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "namespaces": _proof_state_prompt_safe_value(
                list(self.namespaces),
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "result_head": _proof_state_prompt_safe_text(
                self.result_head,
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "normalized_statement": _proof_state_durable_text(
                self.normalized_statement,
                limit=2000,
                suppress_solution_placeholders=suppress_solution_placeholders,
            ),
            "normalized_statement_hash": self.normalized_statement_hash,
            "shape_tags": _proof_state_prompt_safe_value(
                list(self.shape_tags),
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "source_failure": _proof_state_prompt_safe_text(
                self.source_failure,
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
        }

    def to_execution_record(self) -> Dict[str, Any]:
        """Return the private, in-memory form used to resume a live search.

        ``to_record`` is deliberately safe to put in a dossier or graph
        metadata, so it can redact strings and answer-like identifiers.  That
        projection is not valid Lean source, however.  Keep the executable
        form separate and never route it through public serialization.
        """

        return {
            "target_expr": self.target_expr,
            "local_hypotheses": copy.deepcopy(self.local_hypotheses),
            "constants_used": list(self.constants_used),
            "binder_structure": list(self.binder_structure),
            "typeclass_needs": list(self.typeclass_needs),
            "namespaces": list(self.namespaces),
            "result_head": self.result_head,
            "normalized_statement": self.normalized_statement,
            "normalized_statement_hash": self.normalized_statement_hash,
            "shape_tags": list(self.shape_tags),
            "source_failure": self.source_failure,
        }


@dataclass
class ProofStateAssemblyAttempt:
    """One residual-goal group produced by a single tactic/decl proof stub."""

    assembly_id: str
    source: str
    proof_stub: str
    child_node_ids: List[str] = field(default_factory=list)
    # Original ordered residual batch width. Unlike ``child_node_ids``, this
    # survives quarantine/pruning when a legacy or damaged graph loses one of
    # the child projection nodes, allowing verifier replay to restore the
    # complete batch instead of looping under a too-small inferred cap.
    residual_goal_slot_count: int = 0
    # Exact typed-route identity. Assembly ids are only branch-local counters,
    # so they cannot distinguish sibling verifier batches after graph fan-in.
    # Persist the Lean receipt batch/context alongside the route to make
    # collision handling deterministic and authority preserving.
    residual_goal_batch_digest: str = ""
    residual_goal_elaboration_context_hash: str = ""
    attempt_count: int = 0
    status: str = "open"
    # True only when receipt validation (rather than mathematical/executor
    # failure) placed this route in ``blocked``. This makes the inverse
    # transition safe when valid authority is later restored.
    attestation_quarantined: bool = False
    # Exact lifecycle provenance for the inverse transition.  Only an open
    # route may enter attestation quarantine; legacy/inconsistent booleans
    # without this marker remain fail-closed rather than laundering terminal
    # work back to open.
    attestation_quarantine_previous_status: str = ""
    # E4 (2026-05-09): tuple of "<child_node_id>:<proved_helper_name>"
    # strings (sorted) captured at the moment the most recent
    # assembly attempt fired. Lets us distinguish "tried with these
    # exact witnesses before" from "tried, but a child has since been
    # re-proved with a different helper", and re-attempt the latter.
    last_attempt_witness: Tuple[str, ...] = field(default_factory=tuple)

    def to_record(
        self,
        *,
        suppress_solution_placeholders: bool = True,
    ) -> Dict[str, Any]:
        redact_solution_refs = bool(suppress_solution_placeholders)
        safe_proof_stub = _proof_state_prompt_safe_code(
            self.proof_stub,
            limit=4000,
            redact_solution_refs=redact_solution_refs,
        )
        return {
            "assembly_id": _proof_state_prompt_safe_text(
                self.assembly_id,
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "source": _proof_state_prompt_safe_text(
                self.source,
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "proof_stub": safe_proof_stub,
            "proof_stub_preview": safe_proof_stub[:400],
            "child_node_ids": _proof_state_prompt_safe_value(
                list(self.child_node_ids),
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "residual_goal_slot_count": max(
                0, _proof_state_durable_nonnegative_int(
                    self.residual_goal_slot_count
                )
            ),
            "residual_goal_batch_digest": str(
                self.residual_goal_batch_digest or ""
            ),
            "residual_goal_elaboration_context_hash": str(
                self.residual_goal_elaboration_context_hash or ""
            ),
            "attempt_count": _proof_state_durable_nonnegative_int(
                self.attempt_count
            ),
            "status": _proof_state_prompt_safe_text(
                self.status,
                limit=120,
                redact_solution_refs=redact_solution_refs,
            ),
            "attestation_quarantined": bool(self.attestation_quarantined),
            "attestation_quarantine_previous_status": str(
                self.attestation_quarantine_previous_status or ""
            ),
            "last_attempt_witness": _proof_state_prompt_safe_value(
                list(self.last_attempt_witness),
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
        }

    def to_execution_record(self) -> Dict[str, Any]:
        """Return private, executable assembly state for a live graph clone."""

        return {
            "assembly_id": self.assembly_id,
            "source": self.source,
            "proof_stub": self.proof_stub,
            "proof_stub_preview": self.proof_stub[:400],
            "child_node_ids": list(self.child_node_ids),
            "residual_goal_slot_count": max(
                0, _proof_state_durable_nonnegative_int(
                    self.residual_goal_slot_count
                )
            ),
            "residual_goal_batch_digest": str(
                self.residual_goal_batch_digest or ""
            ),
            "residual_goal_elaboration_context_hash": str(
                self.residual_goal_elaboration_context_hash or ""
            ),
            "attempt_count": _proof_state_durable_nonnegative_int(
                self.attempt_count
            ),
            "status": self.status,
            "attestation_quarantined": bool(self.attestation_quarantined),
            "attestation_quarantine_previous_status": str(
                self.attestation_quarantine_previous_status or ""
            ),
            "last_attempt_witness": list(self.last_attempt_witness),
        }


@dataclass
class ProofStateTransition:
    """Typed diagnostic/work transition for an executable proof-state graph."""

    transition_id: str
    node_id: str
    source: str
    error_type: str
    action: str
    blocker: str = ""
    phase: str = ""
    turn_index: int = 0
    payload: Dict[str, Any] = field(default_factory=dict)

    def to_record(
        self,
        *,
        suppress_solution_placeholders: bool = True,
    ) -> Dict[str, Any]:
        redact_solution_refs = bool(suppress_solution_placeholders)
        return {
            "transition_id": self.transition_id,
            "node_id": _proof_state_prompt_safe_text(
                self.node_id, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "source": _proof_state_prompt_safe_text(
                self.source, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "error_type": _proof_state_prompt_safe_text(
                self.error_type, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "action": _proof_state_prompt_safe_text(
                self.action, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "blocker": _proof_state_prompt_safe_text(
                self.blocker, limit=1000, redact_solution_refs=redact_solution_refs
            ),
            "phase": _proof_state_prompt_safe_text(
                self.phase, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "turn_index": self.turn_index,
            "payload": _proof_state_prompt_safe_value(
                self.payload,
                redact_solution_refs=redact_solution_refs,
            ),
        }


@dataclass(frozen=True)
class ProofStateWorkItem:
    """Scheduler-facing executable unit derived from proof-state nodes."""

    node_id: str
    work_type: str
    action: str
    priority: float
    target_hash: str = ""
    blocker: str = ""
    dependencies: Tuple[str, ...] = ()
    source: str = "legacy"
    graph_node_id: str = ""
    assembly_id: str = ""
    child_state_node_ids: Tuple[str, ...] = ()
    unblocked_by_graph: bool = False
    reopened_by_new_evidence: bool = False
    evidence_hash: str = ""
    retrieval_signature: str = ""
    retrieval_context_stamp: str = ""
    retrieved_decl_names_hash: str = ""
    decl_application_pending_hash: str = ""
    helper_acceptance_request_hash: str = ""
    decl_application_signature: str = ""
    residual_attestation_hash: str = ""
    proof_stub_hash: str = ""
    assembly_witness_hash: str = ""
    assembly_group_status: str = ""
    projection_turn_index: int = 0
    target_statement: str = ""
    execution_scope_schema_version: int = 1
    execution_scope_id: str = ""
    execution_scope_digest: str = ""
    execution_target_sha256: str = ""
    execution_target_available: bool = False
    execution_materialization_seed_sha256: str = ""
    execution_target_graph_node_id: str = ""
    execution_environment_hash: str = ""
    execution_contract_identity: str = ""
    execution_proposition_identity: str = ""
    execution_helper_context_hash: str = ""
    execution_currentness_digest: str = ""
    exact_target_statement: str = ""
    consumer_bindings: Tuple[Dict[str, Any], ...] = ()
    primary_consumer_binding: Dict[str, Any] = field(default_factory=dict)
    cognition_scope_digest: str = ""
    cognition_currentness_digest: str = ""
    obligation_reason: str = ""
    source_phase: str = ""
    missing_dependency: str = ""
    formalization_required: bool = False
    graph_record: Dict[str, Any] = field(default_factory=dict)

    def to_record(
        self,
        *,
        suppress_solution_placeholders: bool = True,
        official_answer_visible_to_llm: bool = False,
    ) -> Dict[str, Any]:
        official_answer_visible = bool(official_answer_visible_to_llm)
        redact_solution_refs = bool(
            suppress_solution_placeholders and not official_answer_visible
        )
        exact_target_statement = str(
            self.exact_target_statement or self.target_statement or ""
        )
        target_statement_answer_redacted = bool(
            redact_solution_refs
            and is_answer_unsafe_statement_text(
                exact_target_statement,
                suppress_solution_placeholders=True,
            )
        )
        raw_execution_scope = dict(self.graph_record.get("execution_scope") or {})
        execution_scope = {
            "target_statement": (
                "" if target_statement_answer_redacted else exact_target_statement
            ),
            "statement_identity": str(
                raw_execution_scope.get("statement_identity")
                or self.execution_proposition_identity
                or self.execution_contract_identity
                or ""
            ),
            "environment_hash": str(
                raw_execution_scope.get("environment_hash")
                or self.execution_environment_hash
                or ""
            ),
            "helper_context_hash": str(
                raw_execution_scope.get("helper_context_hash")
                or self.execution_helper_context_hash
                or ""
            ),
            "graph_revision": str(
                raw_execution_scope.get("graph_revision") or ""
            ),
        }
        record = {
            "node_id": _proof_state_prompt_safe_text(
                self.node_id, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "work_type": _proof_state_prompt_safe_text(
                self.work_type, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "action": _proof_state_prompt_safe_text(
                self.action, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "priority": self.priority,
            "target_hash": self.target_hash,
            "blocker": _proof_state_prompt_safe_text(
                self.blocker, limit=1000, redact_solution_refs=redact_solution_refs
            ),
            "dependencies": list(self.dependencies),
            "source": _proof_state_prompt_safe_text(
                self.source, limit=240, redact_solution_refs=redact_solution_refs
            ),
            "graph_node_id": self.graph_node_id,
            "assembly_id": self.assembly_id,
            "child_state_node_ids": list(self.child_state_node_ids),
            "unblocked_by_graph": self.unblocked_by_graph,
            "reopened_by_new_evidence": self.reopened_by_new_evidence,
            "evidence_hash": self.evidence_hash,
            "retrieval_signature": self.retrieval_signature,
            "retrieval_context_stamp": self.retrieval_context_stamp,
            "retrieved_decl_names_hash": self.retrieved_decl_names_hash,
            "decl_application_pending_hash": self.decl_application_pending_hash,
            "helper_acceptance_request_hash": self.helper_acceptance_request_hash,
            "decl_application_signature": self.decl_application_signature,
            "residual_attestation_hash": self.residual_attestation_hash,
            "proof_stub_hash": self.proof_stub_hash,
            "assembly_witness_hash": self.assembly_witness_hash,
            "assembly_group_status": self.assembly_group_status,
            "projection_turn_index": self.projection_turn_index,
            "target_statement": (
                ""
                if target_statement_answer_redacted
                else self.target_statement
            ),
            "execution_scope_schema_version": self.execution_scope_schema_version,
            "execution_scope_id": self.execution_scope_id,
            "execution_scope_digest": self.execution_scope_digest,
            "execution_target_sha256": self.execution_target_sha256,
            "execution_target_available": bool(
                exact_target_statement and not target_statement_answer_redacted
            ),
            "execution_materialization_seed_sha256": (
                self.execution_materialization_seed_sha256
            ),
            "execution_target_graph_node_id": self.execution_target_graph_node_id,
            "execution_environment_hash": self.execution_environment_hash,
            "execution_contract_identity": self.execution_contract_identity,
            "execution_proposition_identity": self.execution_proposition_identity,
            "execution_helper_context_hash": self.execution_helper_context_hash,
            "execution_scope": execution_scope,
            "execution_currentness_digest": self.execution_currentness_digest,
            "exact_target_statement": (
                "" if target_statement_answer_redacted else exact_target_statement
            ),
            "consumer_bindings": [
                copy.deepcopy(dict(item))
                for item in self.consumer_bindings
                if isinstance(item, Mapping)
            ],
            "primary_consumer_binding": copy.deepcopy(
                self.primary_consumer_binding
            ),
            "cognition_scope_digest": self.cognition_scope_digest,
            "cognition_currentness_digest": self.cognition_currentness_digest,
            "official_answer_visible_to_llm": official_answer_visible,
            "target_statement_answer_redacted": (
                target_statement_answer_redacted
            ),
            "obligation_reason": _proof_state_prompt_safe_text(
                self.obligation_reason,
                limit=1000,
                redact_solution_refs=redact_solution_refs,
            ),
            "source_phase": _proof_state_prompt_safe_text(
                self.source_phase,
                limit=240,
                redact_solution_refs=redact_solution_refs,
            ),
            "missing_dependency": _proof_state_prompt_safe_text(
                self.missing_dependency,
                limit=500,
                redact_solution_refs=redact_solution_refs,
            ),
            "formalization_required": self.formalization_required,
        }
        if not record["consumer_bindings"]:
            record.pop("consumer_bindings")
        if not record["primary_consumer_binding"]:
            record.pop("primary_consumer_binding")
        if self.graph_record:
            for key, value in _proof_state_prompt_safe_value(
                self.graph_record,
                redact_solution_refs=redact_solution_refs,
            ).items():
                if key not in record:
                    record[key] = value
        return record


@dataclass
class ProofStateNode:
    """Run-local proof-search node for actionable mini-prover state."""

    node_id: str
    kind: str
    target: str
    # Lean environment in which ``target`` was created/elaborated.  A
    # same-surface falsification certificate may terminalize this node only
    # when the typed invalidation provenance carries this exact stamp.
    statement_environment_hash: str = ""
    # Exact Lean-authoritative residual-goal admission receipt. This private
    # execution evidence is persisted byte-for-byte and never reconstructed
    # from human goal diagnostics.
    residual_goal_attestation: Dict[str, Any] = field(default_factory=dict)
    # Exact open lifecycle saved only while attestation validation has this
    # node quarantined.  Terminal and independently blocked nodes never enter
    # this transition, preventing a later valid receipt from resurrecting
    # them.
    residual_attestation_quarantine_snapshot: Dict[str, Any] = field(
        default_factory=dict
    )
    # Private verifier work saved after a parent proof stub succeeds but typed
    # residual extraction defers. It lives only in exact execution snapshots
    # and checkpoints, never in prompt-facing records.
    pending_residual_goal_extraction: Dict[str, Any] = field(default_factory=dict)
    # Private, durable verifier-frequency state.  A retryable infrastructure
    # failure never destroys the paid candidate; it only makes the exact
    # request/stage identity temporarily ineligible.  This ledger is omitted
    # from prompt-facing records and survives session/process recreation.
    verifier_retry_states: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    # Exact route request identities definitively rejected during verifier-only
    # re-attestation. Context alone is insufficient: distinct proof stubs on
    # one parent can share a Lean environment and must fail independently.
    residual_attestation_rejected_request_hashes: List[str] = field(
        default_factory=list
    )
    # Durable fair-rotation memory for verifier-only re-attestation.  A
    # route-local infrastructure defer must retain its exact retry count, but
    # it must not monopolize the parent's singular pending frame and starve a
    # different stale route that may be immediately replayable.
    residual_attestation_deferred_request_retries: Dict[str, int] = field(
        default_factory=dict
    )
    residual_attestation_last_deferred_request_hash: str = ""
    suppress_solution_placeholders: bool = True
    goal: Optional[NormalizedProofGoal] = None
    local_context: List[str] = field(default_factory=list)
    local_argument_terms: Dict[str, str] = field(default_factory=dict)
    dependencies: List[str] = field(default_factory=list)
    parent_node_id: str = ""
    child_node_ids: List[str] = field(default_factory=list)
    parent_proof_stub: str = ""
    assembly_attempt_groups: List[ProofStateAssemblyAttempt] = field(default_factory=list)
    status: str = "open"
    action: str = "prove"
    blocker: str = ""
    blocked_by_node_ids: List[str] = field(default_factory=list)
    priority: float = 0.0
    failed_attempts: int = 0
    tactic_attempts: int = 0
    # Strict timeout/exhaustion is terminal for the exact child tactic
    # context. Verified-helper context changes clear these keys and grant one
    # fresh attempt without replaying an unchanged 120-second swarm forever.
    tactic_terminal_context_keys: List[str] = field(default_factory=list)
    # Exact tactic contexts that have consumed their single retryable timeout.
    # A second timeout for the same identity is terminal for that context.
    tactic_timeout_retry_context_keys: List[str] = field(default_factory=list)
    # Exact falsification contexts whose advisory infrastructure failed once.
    # The tactic lane bypasses those contexts thereafter; Lean validation of
    # tactic candidates remains authoritative.
    falsification_preflight_transient_context_keys: List[str] = field(
        default_factory=list
    )
    # Exact unexpected child-executor failures which have consumed their one
    # infrastructure retry. These are not mathematical tactic failures.
    child_executor_exception_retry_context_keys: List[str] = field(
        default_factory=list
    )
    decl_application_attempts: int = 0
    assembly_attempts: int = 0
    cache_hits: int = 0
    close_attempts: int = 0
    budget_skips: int = 0
    successful_family: str = ""
    diagnostics: List[Dict[str, Any]] = field(default_factory=list)
    failure_transitions: List[str] = field(default_factory=list)
    typed_transitions: List[ProofStateTransition] = field(default_factory=list)
    retrieved_facts: List[str] = field(default_factory=list)
    retrieved_decl_names: List[str] = field(default_factory=list)
    # Per-declaration execution provenance.  Graph retrieval edges are durable
    # advisory evidence, but only declarations carrying the current policy
    # stamp may be rehydrated into the paid decl-probe page.
    retrieved_decl_provenance: Dict[str, str] = field(default_factory=dict)
    # Signature of the exact retrieval page that authorized each declaration.
    # Restored graph pages may mix edges from distinct retrieval contexts even
    # when all edges carry the current policy version.
    retrieved_decl_signatures: Dict[str, str] = field(default_factory=dict)
    # Legacy/unvalidated graph declarations are retained separately so repeat
    # graph refreshes neither forget them nor append them to executable work.
    graph_retrieved_decl_quarantine_names: List[str] = field(default_factory=list)
    retrieved_decl_execution_policy_version: str = ""
    retrieval_attempted: bool = False
    retrieval_signature: str = ""
    retrieval_hit_count: int = 0
    retrieval_error: str = ""
    retrieval_error_signature: str = ""
    retrieval_error_transient: bool = False
    retrieval_error_attempt_count: int = 0
    retrieval_retry_after_epoch_s: float = 0.0
    rejection_evidence_hash: str = ""
    decl_application_signature: str = ""
    decl_application_tried_decl_names: List[str] = field(default_factory=list)
    # Declaration names rejected before Lean application can meaningfully
    # depend on helpers/preamble (currently invalid sanitized names only).
    # Unlike context-bound misses, these survive every Lean context change.
    decl_application_structural_miss_decl_names: List[str] = field(
        default_factory=list
    )
    # Context-bound misses queued after a verified-helper/preamble change.
    # They remain complete search work, but genuinely new retrieval results
    # are ranked ahead of them and execution admits at most one per turn.
    decl_application_context_replay_decl_names: List[str] = field(
        default_factory=list
    )
    decl_application_last_context_replay_turn: int = -1
    # Exact Lean application context (residual preamble + final helper blocks
    # actually sent to apply_decl_to_goal) the tried memory was recorded
    # under. Stamped at the application boundary; a mismatch there clears the
    # tried set (grant retry) — covering forced-context and preamble drift the
    # dossier-level fingerprint cannot see.
    decl_application_tried_context_hash: str = ""
    decl_application_retry_keys: List[str] = field(default_factory=list)
    # A kernel-facing candidate that has been generated but whose authoritative
    # helper publication could not complete for infrastructure/deadline reasons.
    # This is executable scheduler state, not advisory telemetry: retry
    # acceptance directly instead of paying to rediscover the proof.
    pending_helper_acceptance: Dict[str, Any] = field(default_factory=dict)
    proved_helper_name: str = ""
    # Phase 2 (2026-05-09) — recursive helper prover telemetry.
    # ``recursive_attempts`` increments each time a
    # ``RecursiveHelperProverAction`` runs against this node;
    # ``last_recursive_attempt_iteration`` records the parent session's
    # iteration counter at the time of the most-recent attempt;
    # ``recursive_giveup_cluster`` stores the most-recent cluster id
    # the child sub-conversation triggered (None if no give-up);
    # ``recursive_giveup_counts`` counts give-ups by cluster across
    # attempts (enables "stop retrying nodes that consistently
    # helpers_insufficient" policy).
    recursive_attempts: int = 0
    last_recursive_attempt_iteration: int = -1
    recursive_giveup_cluster: Optional[str] = None
    recursive_giveup_counts: Dict[str, int] = field(default_factory=dict)
    root_exact_rejected_helper_keys: List[str] = field(default_factory=list)
    root_tactic_attempted_context_keys: List[str] = field(default_factory=list)
    root_tactic_deferred_context_keys: List[str] = field(default_factory=list)
    root_tactic_continued_context_keys: List[str] = field(default_factory=list)
    root_tactic_reenabled_context_keys: List[str] = field(default_factory=list)
    # Exact deterministic portfolio cursor yielded between scheduler quanta.
    # This private proof-bearing payload is emitted only by execution records;
    # generic/prompt-safe records omit it and therefore fail closed.
    root_tactic_portfolio_continuation: Dict[str, Any] = field(default_factory=dict)
    # Durable "this child goal is provably FALSE" marker. Set only from a
    # Lean-checked + axiom-audited negation certificate (never an LLM claim), so
    # proving-oriented work (decl_probe / child_llm_prove) can be permanently
    # suppressed on it. Unlike ``status == "rejected"`` this is NOT re-admitted by
    # ``reopened_by_new_evidence``.
    falsified: bool = False
    falsification_reason: str = ""
    # Content hash of the authoritative negation certificate that set
    # ``falsified`` — binds the durable flag to its Lean-checked evidence
    # (enforced by mark_child_goal_falsified; a bare flag cannot be minted).
    falsification_certificate_hash: str = ""
    # Hash of a current Lean-checked counterexample candidate that has not yet
    # produced an axiom-audited proof of the full negation.  This is scheduling
    # advice only: it must never mint ``falsified`` authority or suppress the
    # ordinary proof lanes.
    falsification_advisory_candidate_hash: str = ""
    # Certificate-specific parent routes retired with this child. Stored on
    # the child rather than in the bounded transition ring so quarantine can
    # always fail open by restoring the exact prior group status.
    falsification_retired_assembly_routes: List[Dict[str, str]] = field(
        default_factory=list
    )


def proof_state_decl_application_candidate_names(node: Any) -> List[str]:
    """Return valid retrieved declarations for deterministic goal probing."""

    if (
        bool(getattr(node, "retrieval_attempted", False))
        and list(getattr(node, "retrieved_decl_names", []) or [])
        and str(
            getattr(node, "retrieved_decl_execution_policy_version", "") or ""
        ).strip()
        != PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
    ):
        # Fail closed on pre-policy checkpoint/graph candidates. The empty
        # executable set causes the scheduler to refresh retrieval under the
        # current relevance gate; it does not discard the advisory facts.
        return []
    page_signature = str(getattr(node, "retrieval_signature", "") or "").strip()
    failed_signature = str(
        getattr(node, "retrieval_error_signature", "") or ""
    ).strip()
    if (
        str(getattr(node, "retrieval_error", "") or "").strip()
        and failed_signature
        and failed_signature != page_signature
    ):
        # A failed refresh for a different context makes the prior page
        # advisory-only during cooldown. Its per-declaration signatures still
        # preserve the old evidence for diagnostics and a later successful
        # refresh, but cannot authorize Lean execution in the new context.
        return []
    out: List[str] = []
    seen: Set[str] = set()
    policy_by_name = dict(
        getattr(node, "retrieved_decl_provenance", {}) or {}
    )
    signature_by_name = dict(
        getattr(node, "retrieved_decl_signatures", {}) or {}
    )
    for raw_name in list(getattr(node, "retrieved_decl_names", []) or []):
        name = str(raw_name or "").strip()
        if not name or name in seen:
            continue
        if not _CHECK_TERM_RE.fullmatch(name.lstrip("@")):
            continue
        if is_answer_unsafe_statement_text(
            name,
            suppress_solution_placeholders=bool(
                getattr(node, "suppress_solution_placeholders", True)
            ),
        ):
            continue
        seen.add(name)
        name_policy = str(policy_by_name.get(name) or "").strip()
        name_signature = str(signature_by_name.get(name) or "").strip()
        if (
            name_policy != PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
            or not page_signature
            or name_signature != page_signature
        ):
            # A node-wide stamp cannot authorize one member of a mixed restored
            # page. Preserve the name as advisory evidence, but never pass it
            # to Lean until a current retrieval refresh stamps this exact name.
            continue
        out.append(name)
    return out


def _reconcile_proof_state_decl_application_quarantine(node: Any) -> None:
    """Persist advisory names rejected by the current execution policy.

    This is deliberately separate from the pure candidate/readiness helpers.
    Durable projection is a write boundary; scheduler applicability is not.
    """

    executable = set(proof_state_decl_application_candidate_names(node))
    quarantine = [
        str(item or "").strip()
        for item in list(
            getattr(node, "graph_retrieved_decl_quarantine_names", []) or []
        )
        if str(item or "").strip()
    ]
    for raw_name in list(getattr(node, "retrieved_decl_names", []) or []):
        name = str(raw_name or "").strip()
        if name and name not in executable and name not in quarantine:
            quarantine.append(name)
    if hasattr(node, "graph_retrieved_decl_quarantine_names"):
        node.graph_retrieved_decl_quarantine_names = list(
            dict.fromkeys(quarantine)
        )[-48:]


def proof_state_decl_application_page_is_current(node: Any) -> bool:
    """Whether every executable-shaped declaration has exact current provenance."""

    raw_names: List[str] = []
    for raw_name in list(getattr(node, "retrieved_decl_names", []) or []):
        name = str(raw_name or "").strip()
        if not name or name in raw_names or not _CHECK_TERM_RE.fullmatch(name.lstrip("@")):
            continue
        if is_answer_unsafe_statement_text(
            name,
            suppress_solution_placeholders=bool(
                getattr(node, "suppress_solution_placeholders", True)
            ),
        ):
            continue
        raw_names.append(name)
    if not raw_names:
        return True
    return len(proof_state_decl_application_candidate_names(node)) == len(raw_names)


def proof_state_begin_decl_application_batch(
    node: Any,
    context_hash: str,
) -> bool:
    """Stamp the EXACT application context at the decl-probe boundary.

    ``context_hash`` must be computed from the exact preamble + final helper
    blocks handed to ``apply_decl_to_goal``. On mismatch the tried memory is
    route-attempt bookkeeping from a DIFFERENT Lean context — clear it (one
    retry allowance under the new context) and stamp the new hash. Returns
    True when memory was cleared.
    """

    context_hash = str(context_hash or "").strip()
    previous = str(
        getattr(node, "decl_application_tried_context_hash", "") or ""
    ).strip()
    if previous == context_hash:
        return False
    node.decl_application_tried_context_hash = context_hash
    if not previous:
        # First boundary observation: establish the baseline without a
        # retroactive clear (fresh nodes have empty tried sets; restored
        # nodes keep their memory until the exact context truly moves).
        return False
    tried, retry_keys = _queue_decl_application_context_replays(node)
    node.decl_application_signature = ""
    return bool(tried or retry_keys)


def _queue_decl_application_context_replays(node: Any) -> tuple[List[str], List[str]]:
    """Move context-bound attempt memory into a bounded replay queue."""

    tried = [
        str(item or "").strip()
        for item in list(
            getattr(node, "decl_application_tried_decl_names", []) or []
        )
        if str(item or "").strip()
    ]
    retry_keys = [
        str(item or "").strip()
        for item in list(getattr(node, "decl_application_retry_keys", []) or [])
        if str(item or "").strip()
    ]
    structural = {
        str(item or "").strip()
        for item in list(
            getattr(node, "decl_application_structural_miss_decl_names", []) or []
        )
        if str(item or "").strip()
    }
    replay = [
        str(item or "").strip()
        for item in list(
            getattr(node, "decl_application_context_replay_decl_names", []) or []
        )
        if str(item or "").strip()
    ]
    replay.extend(tried)
    replay.extend(key.partition("\n")[0].strip() for key in retry_keys)
    node.decl_application_context_replay_decl_names = [
        name
        for name in dict.fromkeys(replay)
        if name and name not in structural
    ][-48:]
    node.decl_application_tried_decl_names = []
    node.decl_application_retry_keys = []
    node.decl_application_last_context_replay_turn = -1
    return tried, retry_keys


def proof_state_decl_application_pending_names(
    node: Any,
    *,
    context_hash: str = "",
) -> List[str]:
    """Return valid retrieved declarations not yet tried on this node."""

    requested_context = str(context_hash or "").strip()
    recorded_context = str(
        getattr(node, "decl_application_tried_context_hash", "") or ""
    ).strip()
    context_changed = bool(
        requested_context
        and recorded_context
        and requested_context != recorded_context
    )
    tried = set()
    if not context_changed:
        tried = {
            str(item or "").strip()
            for item in list(
                getattr(node, "decl_application_tried_decl_names", []) or []
            )
            if str(item or "").strip()
        }
    structural = {
        str(item or "").strip()
        for item in list(
            getattr(node, "decl_application_structural_miss_decl_names", []) or []
        )
        if str(item or "").strip()
    }
    replay = {
        str(item or "").strip()
        for item in list(
            getattr(node, "decl_application_context_replay_decl_names", []) or []
        )
        if str(item or "").strip()
    }
    if context_changed:
        replay.update(
            str(item or "").strip()
            for item in list(
                getattr(node, "decl_application_tried_decl_names", []) or []
            )
            if str(item or "").strip()
        )
    pending = [
        name
        for name in proof_state_decl_application_candidate_names(node)
        if name not in structural and name not in tried
    ]
    fresh = [name for name in pending if name not in replay]
    context_replays = [name for name in pending if name in replay]
    return [*fresh, *context_replays]


@dataclass(frozen=True)
class ProofStateCheckpoint:
    """Snapshot of ProofSearchState (+ optional ProofGraph).

    Created by ``ProofSearchState.checkpoint(dossier=...)`` and consumed
    by ``rollback`` / ``commit``. Stored on a LIFO stack on the state.

    Note on "frozen": ``frozen=True`` blocks reassignment of the field
    references. The inner containers (``nodes`` dict, ``plan_hints``
    list, etc.) ARE mutable. Callers that hold a snapshot reference
    must not mutate its containers; the rollback machinery only reads
    them. Rollback always deepcopies on restore so inadvertent post-
    rollback mutation cannot back-propagate into the snapshot anyway.

    Snapshot scope (deliberate choices, see Gap 3 design notes):

    - ``nodes`` (deepcopy) — speculative children + decomposition tasks
      added during the checkpoint window are wiped on rollback.
    - ``next_index`` — the monotonic ID counter rewinds, so the next
      planner pass reuses freed IDs and there is no permanent gap.
    - ``node_by_target`` — the canonical-statement → node-id index.
    - ``plan_hints``, ``graph_frontier_errors`` — derived state.
    - ``proof_graph`` (cloned via ``ProofGraph.clone()``) — only when
      ``dossier`` is supplied to ``checkpoint``. The causal-proof-graph wiring
      requires the graph to roll back with the proof state or scheduling sees
      inconsistent state.
    - ``dossier.proof_state_record`` (refreshed from restored nodes) —
      keeps the serialized debugging view aligned after rollback.

    Explicitly NOT snapshotted (durable on rollback):

    - ``dossier.verified_helpers`` — kernel-verified durable wins.
      Helpers proven during a speculative window survive rollback so
      the next planner pass can reuse them. After rollback, the
      caller is responsible for re-syncing the proof_graph with the
      surviving helpers (via ``dossier._sync_legacy_helpers_to_graph``)
      so the two stores agree. The ``LemmaDagDecomposeAction``
      consumer does this automatically.
    - ``dossier.attempts`` / ``decl_applications`` — audit trails;
      we never rewrite history. Failure traces survive rollback so
      future passes can avoid repeating known-bad attempts.
    - ``recorder`` events — same rationale.
    - lemma-DAG child rejection counters — policy-gate observability is
      durable even when speculative graph mutations roll back.

    Note: per-node ``typed_transitions`` and ``failure_transitions``
    LIVE on the node and ARE rolled back. The cross-call audit trail
    is in ``dossier.attempts`` (which survives); the per-node trail
    is part of the speculative state and gets discarded with it.
    """

    checkpoint_id: str
    label: str
    next_index: int
    nodes: Dict[str, ProofStateNode]
    node_by_target: Dict[str, str]
    statement_environment_hash: str
    plan_hints: List[str]
    graph_frontier_errors: List[Dict[str, Any]]
    # Helper-set fingerprint the decl-application tried memory was recorded
    # under. Captured so a rollback cannot reset it to "" — a helper landing
    # inside the (rolled-back) speculative window survives durably, and the
    # post-rollback sync must still see the OLD fingerprint to grant the
    # context-change retry.
    decl_application_context_fingerprint: str = ""
    proof_graph_snapshot: Optional[Any] = None
    # Strong reference to the dossier whose graph/record projection is owned
    # by this checkpoint. rollback() restores or refreshes onto this same
    # dossier. If the caller swaps session.dossier between checkpoint and
    # rollback, the rollback writes onto the OLD dossier — callers must not
    # swap dossiers across the speculative window.
    dossier_ref: Optional[Any] = None


class ProofSearchState:
    """Actionable proof state layered over the existing dossier ledger.

    ``ProofDossier`` remains the durable source of verified helper text.
    This object is the short-lived scheduler: it remembers failed root
    diagnostics, turns remaining Lean goals into child nodes, and tells the
    next turn which node/action is worth spending search on.
    """

    _DURABLE_METRIC_COUNTER_FIELDS: Tuple[str, ...] = (
        "graph_frontier_errors_total",
        "graph_obligation_child_promotions",
        "graph_obligation_child_promotion_reuses",
        "graph_obligation_child_promotion_skipped_quarantined",
        "graph_obligation_child_promotion_skipped_untrusted",
        "graph_obligation_child_promotion_skipped_formalization_required",
        "graph_obligation_child_promotion_skipped_non_executable",
        "graph_obligation_child_promotion_skipped_root_equivalent",
        "graph_obligation_child_promotion_skipped_rejected",
        "graph_obligation_child_promotion_skipped_cycle",
        "graph_obligation_child_promotion_skipped_terminal_parent",
        "failed_proof_residual_batches_quarantined",
        "failed_proof_residual_goals_quarantined",
        "residual_goal_context_filtered",
        "tactic_pattern_cache_lookups",
        "tactic_pattern_cache_exact_success_hits",
        "tactic_pattern_cache_shape_success_hits",
        "tactic_pattern_cache_failed_filtered",
        "tactic_pattern_cache_all_candidates_pruned",
        "tactic_pattern_cache_cap_preserved_misses",
        "tactic_pattern_cache_failures_recorded",
        "tactic_pattern_cache_failures_not_cached",
        "tactic_pattern_cache_successes_recorded",
        "tactic_pattern_cache_shape_successes_recorded",
        "tactic_pattern_cache_successes_deferred",
        "tactic_pattern_cache_acceptance_vetoes",
        "tactic_pattern_cache_suppressed_filtered",
        "lemma_dag_child_statement_rejections",
        "lemma_dag_child_source_rejections",
        "lemma_dag_decomposition_all_candidates_rejected",
        "lemma_dag_parent_stub_spawns",
        "lemma_dag_parent_stub_rejections",
        "root_tactic_context_attempts",
        "root_tactic_context_skips",
        "root_tactic_transient_deferrals",
        "root_tactic_transient_retries",
        "root_tactic_deferred_skips",
        "root_tactic_reenabled_by_new_evidence",
        "root_tactic_terminal_after_continuation",
        "assembly_selected_stale",
    )
    _MAX_GRAPH_FRONTIER_ERRORS = 8

    def record_graph_frontier_error(self, record: Mapping[str, Any]) -> None:
        """Record one bounded scheduler diagnostic through a single policy."""

        if not isinstance(self.graph_frontier_errors, list):
            self.graph_frontier_errors = []
        self.graph_frontier_errors_total = (
            int(getattr(self, "graph_frontier_errors_total", 0) or 0) + 1
        )
        self.graph_frontier_errors.append(dict(record))
        del self.graph_frontier_errors[: -self._MAX_GRAPH_FRONTIER_ERRORS]

    @staticmethod
    def _target_environment_index_key(
        normalized_statement_hash: str,
        statement_environment_hash: str = "",
    ) -> str:
        statement_hash = str(normalized_statement_hash or "").strip()
        environment_hash = str(statement_environment_hash or "").strip()
        if not environment_hash:
            return statement_hash
        return f"{statement_hash}:environment:{environment_hash}"
    _GRAPH_OBLIGATION_PROMOTION_SKIP_COUNTER_BY_REASON: Mapping[str, str] = {
        "quarantined": "graph_obligation_child_promotion_skipped_quarantined",
        "untrusted": "graph_obligation_child_promotion_skipped_untrusted",
        "formalization_required": (
            "graph_obligation_child_promotion_skipped_formalization_required"
        ),
        "non_executable": "graph_obligation_child_promotion_skipped_non_executable",
        "root_equivalent": "graph_obligation_child_promotion_skipped_root_equivalent",
        "rejected": "graph_obligation_child_promotion_skipped_rejected",
        "cycle": "graph_obligation_child_promotion_skipped_cycle",
        "terminal_parent": "graph_obligation_child_promotion_skipped_terminal_parent",
    }

    def __init__(
        self,
        *,
        theorem_name: str,
        root_statement: str,
        suppress_solution_placeholders: bool = True,
        statement_environment_hash: str = "",
    ) -> None:
        self.theorem_name = str(theorem_name or "mini")
        self.suppress_solution_placeholders = bool(suppress_solution_placeholders)
        self.statement_environment_hash = str(
            statement_environment_hash or ""
        ).strip()
        root = self._normalize_goal_text(root_statement)
        root_goal = self._goal_signature(
            root,
            [],
            source_failure="root",
        )
        self.root_node_id = "root"
        self._next_index = 1
        self._node_by_target: Dict[str, str] = {
            self._target_environment_index_key(
                root_goal.normalized_statement_hash,
                self.statement_environment_hash,
            ): self.root_node_id
        }
        self._graph_state_node_aliases: Dict[str, str] = {}
        self._graph_state_node_alias_hashes: Dict[str, str] = {}
        self.plan_hints = self._plan_hints(root_goal)
        # Fingerprint of the verified-helper set the decl-application tried
        # memory was recorded under; "" = not yet observed (baseline set on
        # first sync without granting a retroactive retry).
        self.decl_application_context_fingerprint = ""
        self.graph_frontier_errors: List[Dict[str, Any]] = []
        self.graph_frontier_errors_total = 0
        self.graph_obligation_child_promotions = 0
        self.graph_obligation_child_promotion_reuses = 0
        self.graph_obligation_child_promotion_skipped_quarantined = 0
        self.graph_obligation_child_promotion_skipped_untrusted = 0
        self.graph_obligation_child_promotion_skipped_formalization_required = 0
        self.graph_obligation_child_promotion_skipped_non_executable = 0
        self.graph_obligation_child_promotion_skipped_root_equivalent = 0
        self.graph_obligation_child_promotion_skipped_rejected = 0
        self.graph_obligation_child_promotion_skipped_cycle = 0
        self.graph_obligation_child_promotion_skipped_terminal_parent = 0
        self.failed_proof_residual_batches_quarantined = 0
        self.failed_proof_residual_goals_quarantined = 0
        self.residual_goal_context_filtered = 0
        self.tactic_pattern_cache_lookups = 0
        self.tactic_pattern_cache_exact_success_hits = 0
        self.tactic_pattern_cache_shape_success_hits = 0
        self.tactic_pattern_cache_failed_filtered = 0
        self.tactic_pattern_cache_all_candidates_pruned = 0
        self.tactic_pattern_cache_cap_preserved_misses = 0
        self.tactic_pattern_cache_failures_recorded = 0
        self.tactic_pattern_cache_failures_not_cached = 0
        self.tactic_pattern_cache_successes_recorded = 0
        self.tactic_pattern_cache_shape_successes_recorded = 0
        self.tactic_pattern_cache_successes_deferred = 0
        self.tactic_pattern_cache_acceptance_vetoes = 0
        self.tactic_pattern_cache_suppressed_filtered = 0
        # Durable observability counters: the node-level transition trail is
        # intentionally rolled back with speculative graph state, but policy
        # gate rejections should remain visible in run-level metrics.
        self.lemma_dag_child_statement_rejections = 0
        self.lemma_dag_child_source_rejections = 0
        self.lemma_dag_decomposition_all_candidates_rejected = 0
        self.lemma_dag_parent_stub_spawns = 0
        self.lemma_dag_parent_stub_rejections = 0
        self.root_tactic_context_attempts = 0
        self.root_tactic_context_skips = 0
        self.root_tactic_transient_deferrals = 0
        self.root_tactic_transient_retries = 0
        self.root_tactic_deferred_skips = 0
        self.root_tactic_reenabled_by_new_evidence = 0
        self.root_tactic_terminal_after_continuation = 0
        self.assembly_selected_stale = 0
        self.nodes: Dict[str, ProofStateNode] = {
            self.root_node_id: ProofStateNode(
                node_id=self.root_node_id,
                kind="root",
                target=root,
                statement_environment_hash=self.statement_environment_hash,
                suppress_solution_placeholders=self.suppress_solution_placeholders,
                goal=root_goal,
                action="prove_or_assemble",
                priority=100.0,
            )
        }
        # Backtracking primitive (Gap 3 fix, 2026-05-08). LIFO stack of
        # snapshots; rollback truncates everything opened after a target id,
        # commit pops a single snapshot. Verified helpers in the dossier are
        # NEVER snapshotted (they are kernel-verified durable wins). The
        # proof_graph IS snapshotted when a dossier is supplied to
        # ``checkpoint`` so the causal-graph state stays consistent.
        # Counter is instance-level so test isolation isn't affected by
        # other instances. The uuid prefix prevents collisions across
        # instances regardless.
        self._checkpoint_id_prefix = uuid.uuid4().hex[:8]
        self._checkpoint_counter: itertools.count = itertools.count(1)
        self._checkpoint_stack: List["ProofStateCheckpoint"] = []
        # E1 inverse index: child_node_id -> set of (parent_node_id, assembly_id)
        # pairs whose assembly group lists that child. Maintained alongside
        # ``parent.assembly_attempt_groups[].child_node_ids`` so a newly proved
        # child can be propagated to its parents in O(parents) instead of an
        # O(n) frontier scan, and so ``_priority`` can compute closure value
        # without enumerating every node's groups (E3).
        self._assembly_parents_by_child: Dict[str, Set[Tuple[str, str]]] = {}

    def _restore_durable_metric_counters(self, metrics: Any) -> None:
        if not isinstance(metrics, dict):
            return
        for field_name in self._DURABLE_METRIC_COUNTER_FIELDS:
            try:
                value = int(metrics.get(field_name, 0) or 0)
            except (TypeError, ValueError):
                continue
            if value <= 0:
                continue
            try:
                current_value = int(getattr(self, field_name, 0) or 0)
            except (TypeError, ValueError):
                current_value = 0
            setattr(self, field_name, max(current_value, value))

    @staticmethod
    def _write_durable_metrics_to_graph_root(dossier: Any, record: Any) -> None:
        if dossier is None or not isinstance(record, dict):
            return
        graph = getattr(dossier, "proof_graph", None)
        if graph is None:
            return
        metrics = record.get("metrics")
        if not isinstance(metrics, dict):
            return
        try:
            root = graph.ensure_root(getattr(graph, "root_statement", ""))
            root.metadata["proof_state_metrics"] = copy.deepcopy(metrics)
        except Exception:
            pass

    @staticmethod
    def _graph_execution_snapshot_fingerprint(graph: Any) -> str:
        """Hash graph state that a private execution snapshot depends on.

        Graph clones preserve this structure exactly.  Any later graph edit
        (for example evidence cleanup or a removed helper edge) invalidates
        the private snapshot and restores the graph-authoritative path.
        """

        nodes = []
        for node_id, node in sorted(
            dict(getattr(graph, "nodes", {}) or {}).items(),
            key=lambda item: str(item[0] or ""),
        ):
            nodes.append(
                {
                    "node_id": str(node_id or ""),
                    "kind": str(getattr(node, "kind", "") or ""),
                    "name": str(getattr(node, "name", "") or ""),
                    "statement": str(getattr(node, "statement", "") or ""),
                    "status": str(getattr(node, "status", "") or ""),
                    "phase": str(getattr(node, "phase", "") or ""),
                    "turn_index": int(getattr(node, "turn_index", 0) or 0),
                    "metadata": dict(getattr(node, "metadata", {}) or {}),
                }
            )
        edges = sorted(
            [
                (
                    str(getattr(edge, "source", "") or ""),
                    str(getattr(edge, "target", "") or ""),
                    str(getattr(edge, "kind", "") or ""),
                )
                for edge in list(getattr(graph, "edges", []) or [])
            ]
        )
        return text_hash(
            json.dumps(
                {"nodes": nodes, "edges": edges},
                sort_keys=True,
                default=str,
            )
        )

    @classmethod
    def from_graph(
        cls,
        *,
        theorem_name: str,
        root_statement: str,
        graph: Any,
        suppress_solution_placeholders: bool = True,
        statement_environment_hash: str = "",
    ) -> "ProofSearchState":
        state = cls(
            theorem_name=theorem_name,
            root_statement=root_statement,
            suppress_solution_placeholders=suppress_solution_placeholders,
            statement_environment_hash=statement_environment_hash,
        )
        graph_nodes = list(getattr(graph, "nodes", {}).values()) if graph is not None else []
        graph_root = (
            getattr(graph, "nodes", {}).get(getattr(graph, "root_node_id", "root"))
            if graph is not None
            else None
        )
        root_metadata = (
            dict(getattr(graph_root, "metadata", {}) or {})
            if graph_root is not None
            else {}
        )
        durable_metrics = root_metadata.get("proof_state_metrics")
        execution_snapshot = getattr(graph, "_proof_state_execution_record", None)
        snapshot_fingerprint = getattr(
            graph,
            "_proof_state_execution_snapshot_fingerprint",
            "",
        )
        snapshot_is_current = bool(
            graph is not None
            and snapshot_fingerprint
            and snapshot_fingerprint
            == cls._graph_execution_snapshot_fingerprint(graph)
        )
        execution_nodes = (
            execution_snapshot.get("nodes")
            if snapshot_is_current and isinstance(execution_snapshot, dict)
            else None
        )
        restoring_execution_snapshot = isinstance(execution_nodes, list)
        live_falsification_authorities = (
            getattr(graph, "_proof_state_falsification_authorities", {})
            if restoring_execution_snapshot
            else {}
        )
        if not isinstance(live_falsification_authorities, dict):
            live_falsification_authorities = {}
        if (
            restoring_execution_snapshot
            and not state.statement_environment_hash
            and isinstance(execution_snapshot, dict)
        ):
            state.statement_environment_hash = str(
                execution_snapshot.get("statement_environment_hash") or ""
            ).strip()
        records: List[Dict[str, Any]] = []
        if restoring_execution_snapshot:
            records = [
                copy.deepcopy(record)
                for record in execution_nodes
                if isinstance(record, dict)
            ]
            snapshot_metrics = execution_snapshot.get("metrics")
            if isinstance(snapshot_metrics, dict):
                durable_metrics = snapshot_metrics
        else:
            for graph_node in graph_nodes:
                metadata = dict(getattr(graph_node, "metadata", {}) or {})
                record = metadata.get("proof_state_node")
                if isinstance(record, dict):
                    merged_record = copy.deepcopy(record)
                    normalized_goal = merged_record.get("normalized_goal")
                    recorded_source = (
                        str(normalized_goal.get("source_failure") or "")
                        if isinstance(normalized_goal, Mapping)
                        else ""
                    )
                    exact_source = str(
                        metadata.get("residual_goal_source") or ""
                    )
                    source_metadata_mismatch = bool(
                        exact_source and recorded_source != exact_source
                    )
                    if "residual_goal_attestation" in metadata:
                        raw_ledger = metadata.get("residual_goal_attestation")
                        try:
                            exact_ledger = (
                                clone_json_value(
                                    dict(raw_ledger),
                                    label="graph residual goal attestation",
                                )
                                if isinstance(raw_ledger, Mapping)
                                else {"__malformed__": None}
                            )
                        except (TypeError, ValueError):
                            exact_ledger = {"__malformed__": None}
                        nested_ledger = merged_record.get(
                            "residual_goal_attestation"
                        )
                        if nested_ledger and nested_ledger != exact_ledger:
                            exact_ledger = {"__malformed__": None}
                        merged_record["residual_goal_attestation"] = exact_ledger
                    elif proof_state_source_requires_residual_goal_attestation(
                        recorded_source
                    ):
                        merged_record["residual_goal_attestation"] = {
                            "__malformed__": None
                        }
                    if source_metadata_mismatch:
                        merged_record["residual_goal_attestation"] = {
                            "__malformed__": None
                        }
                    exact_environment = str(
                        metadata.get("statement_environment_hash") or ""
                    ).strip()
                    nested_environment = str(
                        merged_record.get("statement_environment_hash") or ""
                    ).strip()
                    if nested_environment and nested_environment != exact_environment:
                        merged_record["residual_goal_attestation"] = {
                            "__malformed__": None
                        }
                    merged_record["statement_environment_hash"] = (
                        exact_environment
                    )
                    records.append(merged_record)

        # Public graph metadata is intentionally prompt-safe.  If it contains
        # a lossy redaction in an executable field, it must not become the
        # next Lean input.  A graph clone keeps a private execution snapshot;
        # a JSON/dossier round-trip does not, so that path fails closed to a
        # fresh root instead of running redacted source.
        if (
            not restoring_execution_snapshot
            and cls._records_have_lossy_execution_redaction(records)
        ):
            state._restore_durable_metric_counters(durable_metrics)
            state._rebuild_assembly_index()
            return state

        restored: Dict[str, ProofStateNode] = {}
        max_index = 1
        for record in records:
            node = cls._node_from_record(record)
            if node is None:
                continue
            node.suppress_solution_placeholders = (
                state.suppress_solution_placeholders
            )
            restored[node.node_id] = node
            match = re.fullmatch(r"(?:goal|decompose)_(\d+)", node.node_id)
            if match is not None:
                max_index = max(max_index, int(match.group(1)))
        for graph_node in graph_nodes:
            node = state._node_from_graph_state_node(graph_node)
            if node is None or node.node_id in restored:
                continue
            node.suppress_solution_placeholders = (
                state.suppress_solution_placeholders
            )
            restored[node.node_id] = node
            match = re.fullmatch(r"(?:goal|decompose)_(\d+)", node.node_id)
            if match is not None:
                max_index = max(max_index, int(match.group(1)))
        if not restored:
            state._restore_durable_metric_counters(durable_metrics)
            state._rebuild_assembly_index()
            return state
        if state.root_node_id not in restored:
            restored[state.root_node_id] = state.nodes[state.root_node_id]
        state.nodes = restored
        state._next_index = max_index
        state._restore_graph_edge_state(
            graph,
            merge=restoring_execution_snapshot,
            topology_only=restoring_execution_snapshot,
        )
        state._prune_missing_graph_references()
        state._normalize_unbacked_node_progress(graph)
        state._normalize_unbacked_assembly_progress()
        state._rebuild_assembly_index()
        # Serialized flags/certificates are quarantined until a live dossier
        # replay recreates process-local authority.  The narrow exception is
        # an in-process private snapshot authored by ``sync_to_graph`` after it
        # reconciled every flag against the live dossier.  Its authority map is
        # deliberately not serialized and binds the node, certificate, exact
        # target, and target environment so a mutated snapshot still fails
        # open. Never expose a window in which frontier projection trusts a
        # restored boolean alone.
        for restored_node in state.nodes.values():
            if not bool(getattr(restored_node, "falsified", False)):
                continue
            restored_hash = str(
                getattr(restored_node, "falsification_certificate_hash", "") or ""
            ).strip()
            live_authority = live_falsification_authorities.get(
                restored_node.node_id
            )
            if (
                isinstance(live_authority, dict)
                and str(live_authority.get("certificate_hash") or "").strip()
                == restored_hash
                and str(live_authority.get("target") or "").strip()
                == str(restored_node.target or "").strip()
                and str(
                    live_authority.get("statement_environment_hash") or ""
                ).strip()
                == str(restored_node.statement_environment_hash or "").strip()
            ):
                continue
            state._restore_routes_after_falsification_quarantine(
                restored_node,
                restored_hash,
            )
            restored_node.falsified = False
            restored_node.falsification_reason = ""
            restored_node.falsification_certificate_hash = ""
            state.record_transition(
                node_id=restored_node.node_id,
                source="falsification",
                error_type="serialized_falsification_quarantined",
                action="reconcile",
                blocker="fresh certificate replay required",
            )
        state._node_by_target = {}
        for node in state.nodes.values():
            if node.kind == "decomposition_task":
                continue
            if node.goal is not None and node.goal.normalized_statement_hash:
                state._node_by_target[
                    state._target_environment_index_key(
                        node.goal.normalized_statement_hash,
                        node.statement_environment_hash,
                    )
                ] = node.node_id
        root = state.nodes.get(state.root_node_id)
        if root is not None and root.goal is not None:
            if not state.statement_environment_hash:
                state.statement_environment_hash = str(
                    root.statement_environment_hash or ""
                ).strip()
            state._node_by_target[
                state._target_environment_index_key(
                    root.goal.normalized_statement_hash,
                    root.statement_environment_hash,
                )
            ] = state.root_node_id
            state.plan_hints = state._plan_hints(root.goal)
        state._quarantine_residual_goal_attestation_failures()
        state._restore_durable_metric_counters(durable_metrics)
        return state

    @staticmethod
    def _records_have_lossy_execution_redaction(records: Sequence[Any]) -> bool:
        """Whether public proof-state records can no longer be executed.

        The check intentionally examines only fields that can flow back into
        Lean or route assembly.  Sanitized diagnostics should remain useful
        after persistence and therefore do not invalidate a rehydrate.
        """

        markers = (
            "<string>",
            "solution_ref_hidden_",
            "prompt_control_hidden_",
            "identifier_hidden_",
            "code_hidden_",
            "helper_name_hidden_",
            "key_hidden_",
        )

        def has_marker(value: Any) -> bool:
            if isinstance(value, str):
                return any(marker in value for marker in markers)
            if isinstance(value, Mapping):
                return any(
                    has_marker(key) or has_marker(item)
                    for key, item in value.items()
                )
            if isinstance(value, (list, tuple)):
                return any(has_marker(item) for item in value)
            return False

        for record in records:
            if not isinstance(record, Mapping):
                continue
            goal = record.get("normalized_goal")
            executable_fields = (
                record.get("target"),
                record.get("local_context"),
                record.get("local_argument_terms"),
                record.get("parent_proof_stub"),
                record.get("assembly_attempt_groups"),
                (
                    {
                        "target_expr": goal.get("target_expr"),
                        "local_hypotheses": goal.get("local_hypotheses"),
                        "normalized_statement": goal.get("normalized_statement"),
                    }
                    if isinstance(goal, Mapping)
                    else None
                ),
            )
            if any(has_marker(value) for value in executable_fields):
                return True
        return False

    @staticmethod
    def _goal_from_record(record: Any) -> Optional[NormalizedProofGoal]:
        if not isinstance(record, dict):
            return None
        raw_target_expr = str(record.get("target_expr") or "")
        if "\n" in raw_target_expr and _has_layout_sensitive_local_let(raw_target_expr):
            target_expr = _normalize_rendered_proof_state_target_text(raw_target_expr)
        else:
            target_expr = _normalize_proof_state_goal_text(raw_target_expr)
        stored_normalized_statement = str(
            record.get("normalized_statement") or ""
        ).strip()
        layout_sensitive_target = bool(
            "\n" in target_expr and _has_layout_sensitive_local_let(target_expr)
        )
        target_normalized_statement = (
            canonicalize_lean_statement_for_identity(
                _normalize_proof_state_goal_text(target_expr)
            )
            if target_expr and not layout_sensitive_target
            else ""
        )
        if stored_normalized_statement and layout_sensitive_target:
            normalized_statement = stored_normalized_statement
        elif (
            stored_normalized_statement
            and target_normalized_statement
            and stored_normalized_statement == target_normalized_statement
        ):
            normalized_statement = stored_normalized_statement
        elif target_normalized_statement:
            normalized_statement = target_normalized_statement
        elif stored_normalized_statement:
            normalized_statement = stored_normalized_statement
        else:
            normalized_statement = ""
        if not target_expr and not normalized_statement:
            return None
        normalized_statement_hash = str(
            record.get("normalized_statement_hash") or ""
        ).strip()
        if normalized_statement:
            expected_hash = text_hash(normalized_statement)
            if normalized_statement_hash != expected_hash:
                normalized_statement_hash = expected_hash
        return NormalizedProofGoal(
            target_expr=target_expr,
            local_hypotheses=[
                {
                    **dict(item),
                    "type": _normalize_proof_state_goal_text(
                        dict(item).get("type", "")
                    ),
                }
                for item in _proof_state_durable_sequence(
                    record.get("local_hypotheses")
                )
                if isinstance(item, dict)
            ],
            constants_used=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("constants_used")
                )
            ],
            binder_structure=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("binder_structure")
                )
            ],
            typeclass_needs=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("typeclass_needs")
                )
            ],
            namespaces=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("namespaces")
                )
            ],
            result_head=str(record.get("result_head") or ""),
            normalized_statement=normalized_statement,
            normalized_statement_hash=normalized_statement_hash,
            shape_tags=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("shape_tags")
                )
            ],
            source_failure=str(record.get("source_failure") or ""),
        )

    @staticmethod
    def _transition_from_record(record: Any) -> Optional[ProofStateTransition]:
        if not isinstance(record, dict):
            return None
        node_id = str(record.get("node_id") or "").strip()
        source = str(record.get("source") or record.get("phase") or "unknown").strip()
        error_type = str(record.get("error_type") or "").strip()
        action = str(record.get("action") or "").strip()
        if not node_id or not action:
            return None
        payload = record.get("payload")
        if not isinstance(payload, dict):
            payload = {}
        phase = str(record.get("phase") or "").strip()
        try:
            turn_index = int(record.get("turn_index") or 0)
        except (TypeError, ValueError):
            turn_index = 0
        transition_id = str(record.get("transition_id") or "").strip()
        if not transition_id:
            transition_id = text_hash(
                json.dumps(
                    {
                        "node_id": node_id,
                        "source": source,
                        "error_type": error_type,
                        "action": action,
                        "blocker": str(record.get("blocker") or ""),
                        "phase": phase,
                        "turn_index": turn_index,
                        "payload": payload,
                    },
                    sort_keys=True,
                    default=str,
                )
            )
        return ProofStateTransition(
            transition_id=transition_id,
            node_id=node_id,
            source=source,
            error_type=error_type,
            action=action,
            blocker=str(record.get("blocker") or ""),
            phase=phase,
            turn_index=turn_index,
            payload=dict(payload),
        )

    @classmethod
    def _node_from_record(cls, record: Any) -> Optional[ProofStateNode]:
        if not isinstance(record, dict):
            return None
        node_id = str(record.get("node_id") or "").strip()
        if not node_id:
            return None
        groups: List[ProofStateAssemblyAttempt] = []
        for item in _proof_state_durable_sequence(
            record.get("assembly_attempt_groups")
        ):
            if not isinstance(item, dict):
                continue
            assembly_id = str(item.get("assembly_id") or "").strip()
            if not assembly_id:
                continue
            group_status = str(item.get("status") or "open")
            group_attestation_quarantined = bool(
                group_status == "blocked"
                and item.get("attestation_quarantined") is True
                and item.get("attestation_quarantine_previous_status")
                == "open"
            )
            groups.append(
                ProofStateAssemblyAttempt(
                    assembly_id=assembly_id,
                    source=str(item.get("source") or ""),
                    proof_stub=str(item.get("proof_stub") or ""),
                    child_node_ids=[
                        str(child)
                        for child in _proof_state_durable_sequence(
                            item.get("child_node_ids")
                        )
                        if str(child or "").strip()
                    ],
                    residual_goal_slot_count=(
                        _proof_state_durable_nonnegative_int(
                            item.get("residual_goal_slot_count")
                        )
                    ),
                    residual_goal_batch_digest=str(
                        item.get("residual_goal_batch_digest") or ""
                    ),
                    residual_goal_elaboration_context_hash=str(
                        item.get("residual_goal_elaboration_context_hash") or ""
                    ),
                    attempt_count=_proof_state_durable_nonnegative_int(
                        item.get("attempt_count")
                    ),
                    status=group_status,
                    attestation_quarantined=group_attestation_quarantined,
                    attestation_quarantine_previous_status=(
                        "open" if group_attestation_quarantined else ""
                    ),
                    last_attempt_witness=tuple(
                        str(witness)
                        for witness in _proof_state_durable_sequence(
                            item.get("last_attempt_witness")
                        )
                        if str(witness or "").strip()
                    ),
                )
            )
        raw_residual_attestation = record.get("residual_goal_attestation")
        residual_goal_attestation: Dict[str, Any] = {}
        if isinstance(raw_residual_attestation, Mapping):
            try:
                residual_goal_attestation = clone_json_value(
                    dict(raw_residual_attestation),
                    label=f"proof node {node_id} residual goal attestation",
                )
            except (TypeError, ValueError):
                residual_goal_attestation = {}
        residual_attestation_quarantine_snapshot = (
            _proof_state_residual_attestation_quarantine_snapshot(
                record.get("residual_attestation_quarantine_snapshot"),
                node_status=record.get("status"),
                node_action=record.get("action"),
                node_blocker=record.get("blocker"),
            )
        )
        raw_pending_extraction = record.get("pending_residual_goal_extraction")
        pending_residual_goal_extraction: Dict[str, Any] = {}
        if isinstance(raw_pending_extraction, Mapping):
            try:
                pending_residual_goal_extraction = clone_json_value(
                    dict(raw_pending_extraction),
                    label=(
                        f"proof node {node_id} pending residual extraction"
                    ),
                )
            except (TypeError, ValueError):
                pending_residual_goal_extraction = {}
        pending_helper_acceptance: Dict[str, Any] = {}
        raw_pending_helper = record.get("pending_helper_acceptance")
        if isinstance(raw_pending_helper, Mapping):
            try:
                pending_helper_acceptance = clone_json_value(
                    dict(raw_pending_helper),
                    label=f"proof node {node_id} pending helper acceptance",
                )
            except (TypeError, ValueError):
                pending_helper_acceptance = {}
        verifier_retry_states: Dict[str, Dict[str, Any]] = {}
        raw_verifier_retry_states = _proof_state_durable_mapping(
            record.get("verifier_retry_states")
        )
        # Ordinary/legacy records have no wall-clock verifier state. Avoid a
        # needless clock read during deterministic restore; only cooldown
        # records require epoch validation and clamping.
        restore_now = time.time() if raw_verifier_retry_states else 0.0
        for retry_key, raw_retry in raw_verifier_retry_states.items():
            key = str(retry_key or "").strip()
            if not _proof_state_is_sha256(key) or not isinstance(raw_retry, Mapping):
                continue
            retry = dict(raw_retry)
            request_hash = str(retry.get("request_hash") or "").strip()
            context_hash = str(retry.get("context_hash") or "").strip()
            failure_fingerprint = str(
                retry.get("failure_fingerprint") or ""
            ).strip()
            if (
                retry.get("schema_version")
                != PROOF_STATE_VERIFIER_RETRY_SCHEMA_VERSION
                or not str(retry.get("stage") or "").strip()
                or not _proof_state_is_sha256(request_hash)
                or (context_hash and not _proof_state_is_sha256(context_hash))
                or (
                    failure_fingerprint
                    and not _proof_state_is_sha256(failure_fingerprint)
                )
            ):
                continue
            last_attempt_epoch_s = min(
                restore_now,
                max(
                    0.0,
                    _proof_state_durable_finite_float(
                        retry.get("last_attempt_epoch_s")
                    ),
                ),
            )
            raw_retry_after = max(
                0.0,
                _proof_state_durable_finite_float(
                    retry.get("retry_after_epoch_s")
                ),
            )
            retry_after_epoch_s = (
                min(
                    raw_retry_after,
                    restore_now + PROOF_STATE_VERIFIER_RETRY_MAX_COOLDOWN_S,
                )
                if raw_retry_after >= last_attempt_epoch_s
                else 0.0
            )
            verifier_retry_states[key] = {
                "schema_version": PROOF_STATE_VERIFIER_RETRY_SCHEMA_VERSION,
                "stage": str(retry.get("stage") or "")[:120],
                "request_hash": request_hash,
                "context_hash": context_hash,
                "verifier_generation": str(
                    retry.get("verifier_generation") or ""
                )[:240],
                "failure_kind": str(retry.get("failure_kind") or "")[:160],
                "failure_fingerprint": failure_fingerprint,
                "consecutive_failure_count": min(
                    _PROOF_STATE_MAX_DURABLE_COUNTER,
                    _proof_state_durable_nonnegative_int(
                        retry.get("consecutive_failure_count")
                    ),
                ),
                "same_fingerprint_count": min(
                    _PROOF_STATE_MAX_DURABLE_COUNTER,
                    _proof_state_durable_nonnegative_int(
                        retry.get("same_fingerprint_count")
                    ),
                ),
                "retry_after_epoch_s": retry_after_epoch_s,
                "last_attempt_epoch_s": last_attempt_epoch_s,
            }
        if len(verifier_retry_states) > PROOF_STATE_VERIFIER_RETRY_MAX_STATES_PER_NODE:
            active_keys = {
                str(
                    dict(pending_residual_goal_extraction or {}).get(
                        "verifier_retry_key"
                    )
                    or ""
                ),
                str(
                    dict(pending_helper_acceptance or {}).get(
                        "verifier_retry_key"
                    )
                    or ""
                ),
            }
            active_keys = {
                key for key in active_keys if key in verifier_retry_states
            }
            recent_budget = max(
                0,
                PROOF_STATE_VERIFIER_RETRY_MAX_STATES_PER_NODE
                - len(active_keys),
            )
            recent_keys = [
                key
                for key, _state in sorted(
                    verifier_retry_states.items(),
                    key=lambda item: float(
                        item[1].get("last_attempt_epoch_s") or 0.0
                    ),
                    reverse=True,
                )
                if key not in active_keys
            ][:recent_budget]
            keep_keys = active_keys | set(recent_keys)
            verifier_retry_states = {
                key: state
                for key, state in verifier_retry_states.items()
                if key in keep_keys
            }
        target = (
            str(record.get("target") or "")
            if residual_goal_attestation
            else _normalize_proof_state_goal_text(record.get("target"))
        )
        goal = cls._goal_from_record(record.get("normalized_goal"))
        if not target and goal is not None:
            target = goal.target_expr
        if not target:
            return None
        local_context = [
            normalized
            for normalized in (
                _normalize_proof_state_context_item(item)
                for item in _proof_state_durable_sequence(
                    record.get("local_context")
                )
            )
            if normalized
        ]
        if goal is None:
            normalized_statement = canonicalize_lean_statement_for_identity(target)
            goal = NormalizedProofGoal(
                target_expr=target,
                local_hypotheses=[],
                constants_used=[],
                binder_structure=[],
                typeclass_needs=[],
                namespaces=[],
                result_head="",
                normalized_statement=normalized_statement,
                normalized_statement_hash=text_hash(normalized_statement),
                shape_tags=[],
                source_failure="record_rehydrate",
            )
        elif not goal.target_expr:
            normalized_statement = canonicalize_lean_statement_for_identity(target)
            goal = replace(
                goal,
                target_expr=target,
                normalized_statement=normalized_statement,
                normalized_statement_hash=text_hash(normalized_statement),
            )
        elif not local_context and goal.target_expr != target:
            normalized_statement = canonicalize_lean_statement_for_identity(target)
            goal = replace(
                goal,
                target_expr=target,
                normalized_statement=normalized_statement,
                normalized_statement_hash=text_hash(normalized_statement),
            )
        else:
            residual_target = _contextual_statement_residual_target(
                target,
                local_context,
            )
            if (
                residual_target
                and _normalize_proof_state_goal_text(goal.target_expr)
                != residual_target
            ):
                goal = replace(goal, target_expr=residual_target)
            normalized_statement = canonicalize_lean_statement_for_identity(target)
            normalized_statement_hash = text_hash(normalized_statement)
            if goal.normalized_statement_hash != normalized_statement_hash:
                goal = replace(
                    goal,
                    normalized_statement=normalized_statement,
                    normalized_statement_hash=normalized_statement_hash,
                )
        node = ProofStateNode(
            node_id=node_id,
            kind=str(record.get("kind") or "child_goal"),
            target=target,
            statement_environment_hash=str(
                record.get("statement_environment_hash") or ""
            ).strip(),
            residual_goal_attestation=residual_goal_attestation,
            residual_attestation_quarantine_snapshot=(
                residual_attestation_quarantine_snapshot
            ),
            pending_residual_goal_extraction=(
                pending_residual_goal_extraction
            ),
            verifier_retry_states=verifier_retry_states,
            residual_attestation_rejected_request_hashes=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get(
                        "residual_attestation_rejected_request_hashes"
                    )
                    or record.get("residual_attestation_rejected_context_hashes")
                )
                if _proof_state_is_sha256(item)
            ][:256],
            residual_attestation_deferred_request_retries={
                str(key): int(value)
                for key, value in list(
                    _proof_state_durable_mapping(
                        record.get(
                            "residual_attestation_deferred_request_retries"
                        )
                    ).items()
                )[-256:]
                if _proof_state_is_sha256(key)
                and not isinstance(value, bool)
                and isinstance(value, int)
                and 0 <= int(value) <= 1_000_000
            },
            residual_attestation_last_deferred_request_hash=(
                str(
                    record.get(
                        "residual_attestation_last_deferred_request_hash"
                    )
                    or ""
                )
                if not record.get(
                    "residual_attestation_last_deferred_request_hash"
                )
                or _proof_state_is_sha256(
                    record.get(
                        "residual_attestation_last_deferred_request_hash"
                    )
                )
                else ""
            ),
            goal=goal,
            local_context=local_context,
            local_argument_terms={
                str(key): str(value)
                for key, value in _proof_state_durable_mapping(
                    record.get("local_argument_terms")
                ).items()
                if str(key or "").strip() and str(value or "").strip()
            },
            dependencies=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("dependencies")
                )
                if str(item or "").strip()
            ],
            parent_node_id=str(record.get("parent_node_id") or ""),
            child_node_ids=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("child_node_ids")
                )
                if str(item or "").strip()
            ],
            parent_proof_stub=str(record.get("parent_proof_stub") or ""),
            assembly_attempt_groups=groups,
            status=str(record.get("status") or "open"),
            action=str(record.get("action") or "prove"),
            blocker=str(record.get("blocker") or ""),
            blocked_by_node_ids=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("blocked_by_node_ids")
                )
                if str(item or "").strip()
            ],
            priority=_proof_state_durable_finite_float(
                record.get("priority")
            ),
            failed_attempts=_proof_state_durable_nonnegative_int(
                record.get("failed_attempts")
            ),
            tactic_attempts=_proof_state_durable_nonnegative_int(
                record.get("tactic_attempts")
            ),
            tactic_terminal_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("tactic_terminal_context_keys")
                )
                if str(item or "").strip()
            ],
            tactic_timeout_retry_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("tactic_timeout_retry_context_keys")
                )
                if str(item or "").strip()
            ],
            falsification_preflight_transient_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("falsification_preflight_transient_context_keys")
                )
                if str(item or "").strip()
            ],
            child_executor_exception_retry_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("child_executor_exception_retry_context_keys")
                )
                if str(item or "").strip()
            ],
            decl_application_attempts=(
                _proof_state_durable_nonnegative_int(
                    record.get("decl_application_attempts")
                )
            ),
            assembly_attempts=_proof_state_durable_nonnegative_int(
                record.get("assembly_attempts")
            ),
            cache_hits=_proof_state_durable_nonnegative_int(
                record.get("cache_hits")
            ),
            close_attempts=_proof_state_durable_nonnegative_int(
                record.get("close_attempts")
            ),
            budget_skips=_proof_state_durable_nonnegative_int(
                record.get("budget_skips")
            ),
            successful_family=str(record.get("successful_family") or ""),
            diagnostics=[
                dict(item)
                for item in _proof_state_durable_sequence(
                    record.get("diagnostics")
                )
                if isinstance(item, dict)
            ],
            failure_transitions=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("failure_transitions")
                )
            ],
            typed_transitions=[
                transition
                for transition in (
                    cls._transition_from_record(item)
                    for item in _proof_state_durable_sequence(
                        record.get("typed_transitions")
                    )
                )
                if transition is not None
            ],
            retrieved_facts=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("retrieved_facts")
                )
            ],
            retrieved_decl_names=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("retrieved_decl_names")
                )
            ],
            retrieved_decl_provenance={
                str(key): str(value)
                for key, value in _proof_state_durable_mapping(
                    record.get("retrieved_decl_provenance")
                ).items()
                if str(key or "").strip() and str(value or "").strip()
            },
            retrieved_decl_signatures={
                str(key): str(value)
                for key, value in _proof_state_durable_mapping(
                    record.get("retrieved_decl_signatures")
                ).items()
                if str(key or "").strip() and str(value or "").strip()
            },
            graph_retrieved_decl_quarantine_names=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("graph_retrieved_decl_quarantine_names")
                )
                if str(item or "").strip()
            ],
            retrieved_decl_execution_policy_version=str(
                record.get("retrieved_decl_execution_policy_version") or ""
            ),
            retrieval_attempted=bool(
                record.get(
                    "retrieval_attempted",
                    bool(record.get("retrieved_decl_names")),
                )
                or str(record.get("retrieval_error") or "").strip()
                or str(record.get("retrieval_error_signature") or "").strip()
                or _proof_state_durable_nonnegative_int(
                    record.get("retrieval_error_attempt_count")
                )
            ),
            retrieval_signature=str(record.get("retrieval_signature") or ""),
            retrieval_hit_count=_proof_state_durable_nonnegative_int(
                record.get("retrieval_hit_count")
            ),
            retrieval_error=str(record.get("retrieval_error") or ""),
            retrieval_error_signature=str(
                record.get("retrieval_error_signature") or ""
            ),
            retrieval_error_transient=bool(
                record.get("retrieval_error_transient", False)
            ),
            retrieval_error_attempt_count=(
                _proof_state_durable_nonnegative_int(
                    record.get("retrieval_error_attempt_count")
                )
            ),
            retrieval_retry_after_epoch_s=max(
                0.0,
                _proof_state_durable_finite_float(
                    record.get("retrieval_retry_after_epoch_s")
                ),
            ),
            rejection_evidence_hash=str(record.get("rejection_evidence_hash") or ""),
            decl_application_signature=str(record.get("decl_application_signature") or ""),
            decl_application_tried_context_hash=str(
                record.get("decl_application_tried_context_hash") or ""
            ),
            decl_application_tried_decl_names=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("decl_application_tried_decl_names")
                )
                if str(item or "").strip()
            ],
            decl_application_structural_miss_decl_names=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("decl_application_structural_miss_decl_names")
                )
                if str(item or "").strip()
            ],
            decl_application_context_replay_decl_names=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("decl_application_context_replay_decl_names")
                )
                if str(item or "").strip()
            ],
            decl_application_last_context_replay_turn=max(
                -1,
                _proof_state_durable_int(
                    record.get("decl_application_last_context_replay_turn"),
                    default=-1,
                ),
            ),
            decl_application_retry_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("decl_application_retry_keys")
                )
                if str(item or "").strip()
            ],
            pending_helper_acceptance=pending_helper_acceptance,
            proved_helper_name=str(record.get("proved_helper_name") or ""),
            falsified=bool(record.get("falsified") or False),
            falsification_reason=str(record.get("falsification_reason") or ""),
            falsification_certificate_hash=str(
                record.get("falsification_certificate_hash") or ""
            ),
            falsification_advisory_candidate_hash=str(
                record.get("falsification_advisory_candidate_hash") or ""
            ),
            falsification_retired_assembly_routes=[
                {
                    "parent_node_id": str(item.get("parent_node_id") or ""),
                    "assembly_id": str(item.get("assembly_id") or ""),
                    "previous_status": str(item.get("previous_status") or "open"),
                    "certificate_hash": str(item.get("certificate_hash") or ""),
                }
                for item in _proof_state_durable_sequence(
                    record.get("falsification_retired_assembly_routes")
                )
                if isinstance(item, dict)
            ],
            # F1 fix (2026-05-11): see to_record companion. Rehydrate
            # Phase 2 recursive helper prover counters from the record
            # so B8's attempt + giveup caps survive parallel-sample
            # cloning. Defaults match the dataclass init.
            recursive_attempts=_proof_state_durable_nonnegative_int(
                record.get("recursive_attempts")
            ),
            last_recursive_attempt_iteration=_proof_state_durable_int(
                record.get("last_recursive_attempt_iteration"),
                default=-1,
            ),
            recursive_giveup_cluster=(
                str(record.get("recursive_giveup_cluster"))
                if record.get("recursive_giveup_cluster") is not None
                else None
            ),
            recursive_giveup_counts={
                str(k): _proof_state_durable_nonnegative_int(v)
                for k, v in _proof_state_durable_mapping(
                    record.get("recursive_giveup_counts")
                ).items()
            },
            root_exact_rejected_helper_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("root_exact_rejected_helper_keys")
                )
                if str(item or "").strip()
            ],
            root_tactic_attempted_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("root_tactic_attempted_context_keys")
                )
                if str(item or "").strip()
            ],
            root_tactic_deferred_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("root_tactic_deferred_context_keys")
                )
                if str(item or "").strip()
            ],
            root_tactic_reenabled_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("root_tactic_reenabled_context_keys")
                )
                if str(item or "").strip()
            ],
            root_tactic_continued_context_keys=[
                str(item)
                for item in _proof_state_durable_sequence(
                    record.get("root_tactic_continued_context_keys")
                )
                if str(item or "").strip()
            ],
            root_tactic_portfolio_continuation=(
                validated_root_tactic_portfolio_continuation(
                    record.get("root_tactic_portfolio_continuation")
                )
            ),
        )
        cls._trim_typed_transitions(node)
        return node

    @staticmethod
    def _graph_node_id(node_id: str) -> str:
        return f"proof_state:{str(node_id or '').strip()}"

    @staticmethod
    def _state_node_id_from_graph_id(graph_node_id: str) -> str:
        text = str(graph_node_id or "").strip()
        if text.startswith("proof_state:"):
            return text.split(":", 1)[1].strip()
        return ""

    @classmethod
    def _blocker_graph_node_id(cls, blocker_id: str) -> str:
        text = str(blocker_id or "").strip()
        if not text:
            return ""
        if text == "root" or ":" in text:
            return text
        return cls._graph_node_id(text)

    @classmethod
    def _canonical_blocker_ids(cls, blocker_ids: Sequence[str]) -> List[str]:
        out: List[str] = []
        for raw in list(blocker_ids or ()):
            blocker_id = cls._blocker_graph_node_id(str(raw or ""))
            if blocker_id and blocker_id not in out:
                out.append(blocker_id)
        return out

    @staticmethod
    def _is_search_state_graph_kind(kind: str) -> bool:
        text = str(kind or "")
        return text.startswith("proof_state_") and text not in {
            "proof_state_transition",
            "proof_state_attempt",
            "proof_state_retrieval",
            "proof_state_assembly",
        }

    def _node_from_graph_state_node(self, graph_node: Any) -> Optional[ProofStateNode]:
        kind_text = str(getattr(graph_node, "kind", "") or "")
        if not self._is_search_state_graph_kind(kind_text):
            return None
        metadata = dict(getattr(graph_node, "metadata", {}) or {})
        node_id = (
            str(metadata.get("proof_state_node_id") or "").strip()
            or self._state_node_id_from_graph_id(getattr(graph_node, "node_id", ""))
        )
        if not node_id:
            return None
        node_kind = kind_text.removeprefix("proof_state_") or (
            "root" if node_id == self.root_node_id else "child_goal"
        )
        raw_ledger = metadata.get("residual_goal_attestation")
        ledger: Dict[str, Any] = {}
        if isinstance(raw_ledger, Mapping):
            try:
                ledger = clone_json_value(
                    dict(raw_ledger),
                    label=f"proof node {node_id} graph residual attestation",
                )
            except (TypeError, ValueError):
                ledger = {"__malformed__": None}
        elif "residual_goal_attestation" in metadata:
            ledger = {"__malformed__": None}
        authorities = _residual_goal_attestation_authorities(ledger)
        authority_statements = {
            str(authority.get("statement") or "") for authority in authorities
        }
        target = (
            next(iter(authority_statements))
            if len(authority_statements) == 1
            else self._normalize_goal_text(getattr(graph_node, "statement", ""))
        )
        if not target and node_id == self.root_node_id:
            target = self.nodes[self.root_node_id].target
        authority_sources = {
            str(authority.get("source") or "") for authority in authorities
        }
        source_failure = (
            next(iter(authority_sources))
            if len(authority_sources) == 1
            else str(metadata.get("residual_goal_source") or "graph_rehydrate")
        )
        goal = (
            self._goal_signature(target, [], source_failure=source_failure)
            if target
            else None
        )
        priority_raw = metadata.get("priority")
        try:
            priority = float(priority_raw)
        except (TypeError, ValueError):
            priority = 100.0 if node_kind == "root" else 82.0
        node = ProofStateNode(
            node_id=node_id,
            kind=node_kind,
            target=target,
            statement_environment_hash=str(
                metadata.get("statement_environment_hash") or ""
            ).strip(),
            residual_goal_attestation=ledger,
            suppress_solution_placeholders=self.suppress_solution_placeholders,
            goal=goal,
            local_context=[
                f"{item['name']} : {item['type']}"
                for item in (goal.local_hypotheses if goal is not None else [])
            ],
            status=str(getattr(graph_node, "status", "") or "open"),
            action=str(
                metadata.get("action")
                or ("prove_or_assemble" if node_kind == "root" else "prove_child_helper")
            ),
            blocker=str(metadata.get("blocker") or ""),
            blocked_by_node_ids=[
                str(item)
                for item in list(metadata.get("blocked_by_node_ids") or [])
                if str(item or "").strip()
            ],
            priority=priority,
        )
        return node

    def hydrate_graph_state_nodes(self, graph: Any) -> int:
        """Import missing graph-owned proof-state nodes before frontier projection."""

        graph_nodes = getattr(graph, "nodes", {}) if graph is not None else {}
        if not isinstance(graph_nodes, dict):
            return 0
        imported = 0
        max_numeric_index = int(getattr(self, "_next_index", 1) or 1)

        def merge_exact_residual_ledger(
            existing_node: ProofStateNode,
            incoming_node: ProofStateNode,
        ) -> None:
            """Union exact receipt authorities when graph nodes coalesce."""

            if not incoming_node.residual_goal_attestation:
                return
            if (
                not self._residual_targets_are_equivalent(
                    incoming_node.target,
                    existing_node.target,
                )
                or incoming_node.statement_environment_hash
                != existing_node.statement_environment_hash
            ):
                return
            incoming_authorities = _residual_goal_attestation_authorities(
                incoming_node.residual_goal_attestation
            )
            if not incoming_authorities:
                # A corrupt/missing incoming route remains quarantined by its
                # declared batch identity below. It must not destroy an
                # unrelated valid local authority merely because the graph
                # child coalesces onto the same statement.
                return
            existing_authorities = _residual_goal_attestation_authorities(
                existing_node.residual_goal_attestation
            )
            incoming_identities = {
                str(authority.get("structural_identity") or "")
                for authority in incoming_authorities
            }
            existing_identities = {
                str(authority.get("structural_identity") or "")
                for authority in existing_authorities
            }
            if (
                incoming_authorities
                and (
                    not existing_node.residual_goal_attestation
                    or existing_authorities
                )
                and (
                    not existing_identities
                    or incoming_identities == existing_identities
                )
            ):
                for authority in incoming_authorities:
                    authority_key = _residual_goal_attestation_authority_key(
                        authority
                    )
                    if authority_key:
                        existing_authority = (
                            existing_node.residual_goal_attestation.get(
                                authority_key
                            )
                        )
                        if existing_authority is not None:
                            # One batch/slot key names exactly one immutable
                            # Lean receipt.  A conflicting graph projection is
                            # corruption, not an update: never let it replace
                            # live local authority.  Equal records are the
                            # idempotent same-route case and require no write.
                            continue
                        existing_node.residual_goal_attestation[authority_key] = (
                            clone_json_value(
                                authority,
                                label=(
                                    "aliased graph residual goal attestation"
                                ),
                            )
                        )
                return
            # Conflicting or already-malformed local authority remains as-is.
            # The incoming assembly route cannot validate without its receipt.

        for graph_node in list(graph_nodes.values()):
            kind_text = str(getattr(graph_node, "kind", "") or "")
            if not self._is_search_state_graph_kind(kind_text):
                continue
            metadata = dict(getattr(graph_node, "metadata", {}) or {})
            record = metadata.get("proof_state_node")
            node = self._node_from_record(record) if isinstance(record, dict) else None
            if node is None:
                node = self._node_from_graph_state_node(graph_node)
            elif "residual_goal_attestation" in metadata:
                raw_ledger = metadata.get("residual_goal_attestation")
                try:
                    exact_ledger = (
                        clone_json_value(
                            dict(raw_ledger),
                            label=(
                                f"proof node {node.node_id} graph residual "
                                "attestation"
                            ),
                        )
                        if isinstance(raw_ledger, Mapping)
                        else {"__malformed__": None}
                    )
                except (TypeError, ValueError):
                    exact_ledger = {"__malformed__": None}
                if (
                    node.residual_goal_attestation
                    and node.residual_goal_attestation != exact_ledger
                ):
                    node.residual_goal_attestation = {"__malformed__": None}
                else:
                    node.residual_goal_attestation = exact_ledger
                exact_environment = str(
                    metadata.get("statement_environment_hash") or ""
                ).strip()
                if (
                    node.statement_environment_hash
                    and node.statement_environment_hash != exact_environment
                ):
                    node.residual_goal_attestation = {"__malformed__": None}
                node.statement_environment_hash = exact_environment
                exact_source = str(
                    metadata.get("residual_goal_source") or ""
                )
                if exact_source:
                    recorded_source = str(
                        node.goal.source_failure if node.goal is not None else ""
                    )
                    if recorded_source != exact_source:
                        node.residual_goal_attestation = {"__malformed__": None}
                    if node.goal is not None:
                        node.goal = replace(
                            node.goal,
                            source_failure=exact_source,
                        )
            elif node is not None:
                recorded_source = str(
                    node.goal.source_failure if node.goal is not None else ""
                )
                exact_source = str(
                    metadata.get("residual_goal_source") or recorded_source
                )
                if proof_state_source_requires_residual_goal_attestation(
                    exact_source
                ):
                    node.residual_goal_attestation = {"__malformed__": None}
                    if node.goal is not None:
                        node.goal = replace(
                            node.goal,
                            source_failure=exact_source,
                        )
            if node is None or not node.node_id:
                continue
            graph_node_id = str(getattr(graph_node, "node_id", "") or "").strip()
            node_hash = (
                node.goal.normalized_statement_hash if node.goal is not None else ""
            )
            for alias_key in (graph_node_id, node.node_id):
                if not alias_key:
                    continue
                alias_hash = str(
                    self._graph_state_node_alias_hashes.get(alias_key) or ""
                )
                if alias_hash and alias_hash != node_hash:
                    self._graph_state_node_aliases.pop(alias_key, None)
                    self._graph_state_node_alias_hashes.pop(alias_key, None)
            if node.node_id in self.nodes:
                existing_node = self.nodes[node.node_id]
                merge_exact_residual_ledger(existing_node, node)
                if graph_node_id:
                    self._graph_state_node_aliases[graph_node_id] = node.node_id
                    self._graph_state_node_alias_hashes[graph_node_id] = node_hash
                self._graph_state_node_aliases[node.node_id] = node.node_id
                self._graph_state_node_alias_hashes[node.node_id] = node_hash
                continue
            if node.goal is not None:
                existing_id = self._node_by_target.get(
                    self._target_environment_index_key(
                        node.goal.normalized_statement_hash,
                        node.statement_environment_hash,
                    )
                )
                existing_node = self.nodes.get(existing_id or "")
                if (
                    existing_id
                    and existing_id != node.node_id
                    and existing_node is not None
                    and existing_node.status not in {
                        "proved",
                        "obsolete",
                        "rejected",
                        "failed",
                    }
                ):
                    # A branch/public-graph node may coalesce onto an existing
                    # local statement node. Preserve exact Lean receipt
                    # authority only when the executable statement bytes and
                    # environment are identical; normalized-only aliases keep
                    # no authority and will be quarantined by their imported
                    # residual assembly route below.
                    merge_exact_residual_ledger(existing_node, node)
                    if graph_node_id:
                        self._graph_state_node_aliases[graph_node_id] = existing_id
                        self._graph_state_node_alias_hashes[graph_node_id] = node_hash
                    self._graph_state_node_aliases[node.node_id] = existing_id
                    self._graph_state_node_alias_hashes[node.node_id] = node_hash
                    continue
            self.nodes[node.node_id] = node
            if node.goal is not None and node.kind != "decomposition_task":
                self._node_by_target.setdefault(
                    self._target_environment_index_key(
                        node.goal.normalized_statement_hash,
                        node.statement_environment_hash,
                    ),
                    node.node_id,
                )
            match = re.match(r"^(?:goal|decompose)_(\d+)$", node.node_id)
            if match:
                try:
                    max_numeric_index = max(max_numeric_index, int(match.group(1)))
                except ValueError:
                    pass
            imported += 1
        if imported:
            self._next_index = max(
                int(getattr(self, "_next_index", 1) or 1),
                max_numeric_index,
            )
        self._restore_graph_edge_state(graph, merge=True, topology_only=True)
        if imported:
            self._prune_missing_graph_references()
        self._normalize_unbacked_assembly_progress()
        self._rebuild_assembly_index()
        self._quarantine_residual_goal_attestation_failures()
        return imported

    @staticmethod
    def _graph_transition_node_id(node_id: str, payload: Any) -> str:
        return f"proof_state_transition:{node_id}:{text_hash(json.dumps(payload, sort_keys=True, default=str))}"

    @staticmethod
    def _graph_attempt_node_id(node_id: str, payload: Any) -> str:
        return f"proof_state_attempt:{node_id}:{text_hash(json.dumps(payload, sort_keys=True, default=str))}"

    @staticmethod
    def _graph_retrieval_node_id(node_id: str, payload: str) -> str:
        return f"proof_state_retrieval:{node_id}:{text_hash(payload)}"

    @staticmethod
    def _graph_assembly_node_id(assembly_id: str) -> str:
        return f"proof_state_assembly:{text_hash(assembly_id)}"

    def sync_to_graph(
        self,
        dossier: Optional[ProofDossier],
        *,
        phase: str = "",
        turn_index: int = 0,
        refresh_target_node_ids: Optional[Sequence[str]] = None,
        refresh_graph_readiness: bool = False,
    ) -> None:
        """Mirror scheduler state into the durable proof graph.

        Sync is a local-state-authoritative write. Call
        ``refresh_graph_readiness`` explicitly before sync when a caller wants
        to ingest graph evidence; otherwise stale proof-state projection nodes
        can re-poison reopened local work before the projection is pruned.
        """

        if dossier is None:
            return
        # Decl-application "tried" memory is ROUTE-ATTEMPT memory bound to the
        # Lean context the application ran under (residual preamble + verified
        # helper blocks), not a mathematical negative: a declaration that
        # failed before a helper existed can succeed after it lands. When the
        # verified-helper set changes, grant every child goal one fresh
        # retry allowance by clearing its tried set (same-context re-retrieval
        # still never replays — the original anti-replay win is preserved).
        self._invalidate_decl_tried_on_context_change(dossier)
        self._reconcile_falsified_flags(dossier)
        graph = getattr(dossier, "proof_graph", None)
        if graph is None:
            return
        refresher = getattr(self, "refresh_graph_readiness", None)
        if refresh_graph_readiness and callable(refresher):
            try:
                refresher(
                    graph,
                    phase=phase or "proof_state_sync",
                    turn_index=turn_index,
                    target_node_ids=refresh_target_node_ids,
                )
            except Exception:
                pass
        graph_root = getattr(graph, "nodes", {}).get(
            getattr(graph, "root_node_id", "")
        )
        durable_final_proof = bool(
            str(getattr(dossier, "final_proof", "") or "").strip()
            or str(getattr(dossier, "final_proof_hash", "") or "").strip()
        )
        if (
            durable_final_proof
            and graph_root is not None
            and str(getattr(graph_root, "status", "") or "").strip() == "proved"
            and str(self.nodes[self.root_node_id].status or "").strip() != "proved"
        ):
            self.mark_root_solved()
        target_graph_ids = {
            self._graph_node_id(str(item or "").strip())
            for item in list(refresh_target_node_ids or ())
            if str(item or "").strip()
        }
        preserved_nodes: Dict[str, Any] = {}
        preserved_edges: List[Any] = []
        if target_graph_ids:
            graph_nodes = getattr(graph, "nodes", {}) or {}
            for edge in list(getattr(graph, "edges", []) or []):
                kind = str(getattr(edge, "kind", "") or "")
                if kind not in {"retrieved_declaration", "retrieved_fact", "blocked_by"}:
                    continue
                source = str(getattr(edge, "source", "") or "")
                if source in target_graph_ids:
                    continue
                source_state_id = self._state_node_id_from_graph_id(source)
                if source_state_id not in self.nodes:
                    continue
                source_node = graph_nodes.get(source)
                if source_node is not None and source.startswith("proof_state:"):
                    preserved_nodes[source] = source_node
                target = str(getattr(edge, "target", "") or "")
                target_node = graph_nodes.get(target)
                if target_node is not None and str(target or "").startswith("proof_state"):
                    preserved_nodes[target] = target_node
                preserved_edges.append(edge)
        for node in self.nodes.values():
            _reconcile_proof_state_decl_application_quarantine(node)
        record = self.to_record()
        setattr(dossier, "proof_state_record", record)
        self._write_durable_metrics_to_graph_root(dossier, record)
        if hasattr(graph, "prune_proof_state_projection"):
            graph.prune_proof_state_projection()
        by_id = {
            str(item.get("node_id") or ""): item
            for item in list(record.get("nodes") or [])
            if isinstance(item, dict)
        }
        for node in self.nodes.values():
            node.blocked_by_node_ids = self._canonical_blocker_ids(node.blocked_by_node_ids)
            node_record = by_id.get(node.node_id, {})
            safe_node_action = str(node_record.get("action") or node.action or "")
            safe_node_blocker = str(node_record.get("blocker") or node.blocker or "")
            safe_node_target = _proof_state_durable_text(node.target, limit=2000)
            graph_node_id = self._graph_node_id(node.node_id)
            graph.ensure_state_node(
                graph_node_id,
                kind=f"proof_state_{node.kind}",
                name=node.node_id,
                statement=safe_node_target,
                status=node.status,
                phase=phase or node.successful_family or safe_node_action,
                turn_index=turn_index,
                metadata={
                    "proof_state_node": node_record,
                    "proof_state_node_id": node.node_id,
                    "statement_environment_hash": str(
                        node.statement_environment_hash or ""
                    ),
                    "residual_goal_attestation": clone_json_value(
                        node.residual_goal_attestation,
                        label=(
                            f"proof node {node.node_id} residual goal "
                            "attestation"
                        ),
                    ),
                    "residual_goal_source": str(
                        node.goal.source_failure if node.goal is not None else ""
                    ),
                    "action": safe_node_action,
                    "blocker": safe_node_blocker,
                    "blocked_by_node_ids": list(node.blocked_by_node_ids),
                    "last_rejection_evidence_hash": node.rejection_evidence_hash,
                    "priority": node.priority,
                },
            )
            if node.node_id == self.root_node_id:
                graph_root = graph.nodes.get(graph.root_node_id)
                if graph_root is not None:
                    root_status = str(node.status or "").strip()
                    graph_root_status = str(getattr(graph_root, "status", "") or "")
                    if (
                        root_status
                        and (
                            root_status == "proved"
                            or graph_root_status != "proved"
                            or not durable_final_proof
                        )
                    ):
                        graph_root.status = root_status or graph_root.status
                        graph_root.metadata.setdefault(
                            "proof_state_root_status",
                            graph_root.status,
                        )
                        graph_root.metadata["proof_state_root_status"] = graph_root.status
                graph.add_edge(graph.root_node_id, graph_node_id, "proof_state_root")
            helper_name = str(node.proved_helper_name or "").strip()
            if helper_name and node.status == "proved":
                graph.add_edge(
                    graph_node_id,
                    graph.helper_node_id(helper_name),
                    "proved_by_helper",
                )
            if node.parent_node_id:
                parent_graph_id = self._graph_node_id(node.parent_node_id)
                graph.add_edge(parent_graph_id, graph_node_id, "proof_state_child")
            for dependency in node.dependencies:
                dependency_id = str(dependency or "").strip()
                if dependency_id:
                    graph.add_edge(
                        self._graph_node_id(dependency_id),
                        graph_node_id,
                        "proof_state_dependency",
                    )
            for blocker_id in node.blocked_by_node_ids:
                blocker_graph_id = self._blocker_graph_node_id(blocker_id)
                if blocker_graph_id:
                    graph.add_edge(graph_node_id, blocker_graph_id, "blocked_by")
            for child_id in node.child_node_ids:
                graph.add_edge(
                    graph_node_id,
                    self._graph_node_id(child_id),
                    "proof_state_child",
                )
            if node.typed_transitions:
                for typed_transition in node.typed_transitions:
                    transition_record = typed_transition.to_record()
                    safe_transition_action = str(
                        transition_record.get("action") or ""
                    )
                    safe_transition_error = str(
                        transition_record.get("error_type") or ""
                    )
                    safe_transition_blocker = str(
                        transition_record.get("blocker") or ""
                    )
                    transition_name = (
                        f"{safe_transition_error}->{safe_transition_action}"
                        if safe_transition_error
                        else safe_transition_action
                    )
                    transition_payload = {
                        "node_id": node.node_id,
                        "transition": transition_name,
                        "action": safe_transition_action,
                        "blocker": safe_transition_blocker,
                        "typed_transition": transition_record,
                    }
                    transition_id = self._graph_transition_node_id(
                        node.node_id,
                        transition_payload,
                    )
                    graph.ensure_state_node(
                        transition_id,
                        kind="proof_state_transition",
                        name=transition_name,
                        statement=safe_transition_blocker[:1000],
                        status="open",
                        phase=str(transition_record.get("phase") or phase or "proof_state_transition"),
                        turn_index=int(transition_record.get("turn_index") or turn_index or 0),
                        metadata=transition_payload,
                    )
                    graph.add_edge(graph_node_id, transition_id, "diagnostic_transition")
            else:
                for transition in node.failure_transitions[-4:]:
                    safe_transition = _proof_state_prompt_safe_text(
                        transition,
                        limit=240,
                    )
                    transition_payload = {
                        "node_id": node.node_id,
                        "transition": safe_transition,
                        "action": safe_node_action,
                        "blocker": safe_node_blocker,
                    }
                    transition_id = self._graph_transition_node_id(
                        node.node_id,
                        transition_payload,
                    )
                    graph.ensure_state_node(
                        transition_id,
                        kind="proof_state_transition",
                        name=safe_transition,
                        statement=safe_node_blocker[:1000],
                        status="open",
                        phase=phase or "proof_state_transition",
                        turn_index=turn_index,
                        metadata=transition_payload,
                    )
                    graph.add_edge(graph_node_id, transition_id, "diagnostic_transition")
            safe_diagnostics = [
                item
                for item in _proof_state_prompt_safe_value(node.diagnostics[-4:])
                if isinstance(item, dict)
            ]
            for diagnostic in safe_diagnostics:
                attempt_id = self._graph_attempt_node_id(node.node_id, diagnostic)
                graph.ensure_state_node(
                    attempt_id,
                    kind="proof_state_attempt",
                    name=str(diagnostic.get("error_type") or "lean_rejected"),
                    statement=str(diagnostic.get("blocker") or safe_node_blocker)[:1000],
                    status="rejected",
                    phase=str(diagnostic.get("phase") or phase or "proof_state_attempt"),
                    turn_index=int(diagnostic.get("turn_index") or turn_index or 0),
                    metadata={
                        "proof_state_node_id": node.node_id,
                        "diagnostic": dict(diagnostic),
                    },
                )
                graph.add_edge(graph_node_id, attempt_id, "failed_attempt")
                transition_id = self._graph_transition_node_id(
                    node.node_id,
                    diagnostic,
                )
                graph.ensure_state_node(
                    transition_id,
                    kind="proof_state_transition",
                    name=str(diagnostic.get("action") or safe_node_action),
                    statement=str(diagnostic.get("blocker") or safe_node_blocker)[:1000],
                    status="open",
                    phase=str(diagnostic.get("phase") or phase or "proof_state_transition"),
                    turn_index=int(diagnostic.get("turn_index") or turn_index or 0),
                    metadata={
                        "proof_state_node_id": node.node_id,
                        "diagnostic": dict(diagnostic),
                    },
                )
                graph.add_edge(graph_node_id, transition_id, "diagnostic_transition")
            for decl_name in node.retrieved_decl_names[-12:]:
                safe_decl_name = _proof_state_prompt_safe_text(decl_name, limit=240)
                retrieval_id = self._graph_retrieval_node_id(node.node_id, decl_name)
                decl_policy_version = str(
                    node.retrieved_decl_provenance.get(decl_name, "") or ""
                ).strip()
                decl_retrieval_signature = str(
                    node.retrieved_decl_signatures.get(decl_name, "") or ""
                ).strip()
                graph.ensure_state_node(
                    retrieval_id,
                    kind="proof_state_retrieval",
                    name=safe_decl_name,
                    statement=safe_decl_name,
                    status="open",
                    phase=phase or "proof_state_retrieval",
                    turn_index=turn_index,
                    metadata={
                        "proof_state_node_id": node.node_id,
                        "decl_name": safe_decl_name,
                        "decl_execution_policy_version": decl_policy_version,
                        "retrieval_signature": decl_retrieval_signature,
                    },
                )
                graph.add_edge(graph_node_id, retrieval_id, "retrieved_declaration")
            for fact in node.retrieved_facts[-3:]:
                safe_fact = _proof_state_prompt_safe_text(fact, limit=2000)
                retrieval_id = self._graph_retrieval_node_id(node.node_id, fact)
                graph.ensure_state_node(
                    retrieval_id,
                    kind="proof_state_retrieval",
                    name=_compact_search_text(safe_fact, limit=80),
                    statement=safe_fact[:2000],
                    status="open",
                    phase=phase or "proof_state_retrieval",
                    turn_index=turn_index,
                    metadata={
                        "proof_state_node_id": node.node_id,
                        "retrieved_fact": safe_fact[:2000],
                    },
                )
                graph.add_edge(graph_node_id, retrieval_id, "retrieved_fact")
            for group in node.assembly_attempt_groups:
                assembly_id = self._graph_assembly_node_id(group.assembly_id)
                group_record = group.to_record()
                safe_group_proof_stub = str(group_record.get("proof_stub") or "")
                graph.ensure_state_node(
                    assembly_id,
                    kind="proof_state_assembly",
                    name=str(group_record.get("assembly_id") or group.assembly_id),
                    statement=safe_group_proof_stub[:2000],
                    status=group.status,
                    phase=phase or "proof_state_assembly",
                    turn_index=turn_index,
                    metadata={
                        "proof_state_parent_node_id": node.node_id,
                        "proof_state_assembly": group_record,
                    },
                )
                graph.add_edge(graph_node_id, assembly_id, "proof_state_assembly")
                for slot_index, child_id in enumerate(group.child_node_ids):
                    graph.add_edge(
                        assembly_id,
                        self._graph_node_id(child_id),
                        f"assembly_requires_slot:{slot_index}",
                    )
                    graph.add_edge(
                        assembly_id,
                        self._graph_node_id(child_id),
                        "assembly_requires",
                    )
        for preserved_node in preserved_nodes.values():
            node_id = str(getattr(preserved_node, "node_id", "") or "")
            if not node_id:
                continue
            graph.ensure_state_node(
                node_id,
                kind=str(getattr(preserved_node, "kind", "") or "proof_state"),
                name=str(getattr(preserved_node, "name", "") or node_id),
                statement=str(getattr(preserved_node, "statement", "") or ""),
                status=str(getattr(preserved_node, "status", "") or "open"),
                phase=str(getattr(preserved_node, "phase", "") or phase),
                turn_index=int(getattr(preserved_node, "turn_index", 0) or turn_index),
                metadata=dict(getattr(preserved_node, "metadata", {}) or {}),
            )
        for edge in preserved_edges:
            source = str(getattr(edge, "source", "") or "")
            target = str(getattr(edge, "target", "") or "")
            kind = str(getattr(edge, "kind", "") or "")
            target_ready = target in graph.nodes or kind == "blocked_by"
            if source and target and kind and source in graph.nodes and target_ready:
                graph.add_edge(source, target, kind)

        # This deliberately stays on the live graph object rather than in
        # graph/dossier records.  The public projection above is prompt-safe
        # and may redact Lean literals or answer-like identifiers; only an
        # in-process clone may resume the exact executable state.
        graph._proof_state_execution_record = self.to_execution_record()
        graph._proof_state_execution_snapshot_fingerprint = (
            self._graph_execution_snapshot_fingerprint(graph)
        )
        # Process-local authority only.  This map is intentionally absent from
        # every public/durable record; a checkpoint restored in another process
        # must replay its Lean certificate before suppressing work again.
        graph._proof_state_falsification_authorities = {
            node.node_id: {
                "certificate_hash": str(
                    node.falsification_certificate_hash or ""
                ).strip(),
                "target": str(node.target or "").strip(),
                "statement_environment_hash": str(
                    node.statement_environment_hash or ""
                ).strip(),
            }
            for node in self.nodes.values()
            if node.kind == "child_goal"
            and node.falsified
            and str(node.falsification_certificate_hash or "").strip()
        }

    def _local_state_node_id_from_graph_id(self, graph_node_id: str) -> str:
        text = str(graph_node_id or "").strip()
        aliases = getattr(self, "_graph_state_node_aliases", {}) or {}
        if text in aliases:
            return str(aliases[text] or "").strip()
        state_id = self._state_node_id_from_graph_id(text)
        if state_id in aliases:
            return str(aliases[state_id] or "").strip()
        return state_id

    def _restore_graph_edge_state(
        self,
        graph: Any,
        *,
        merge: bool = False,
        topology_only: bool = False,
    ) -> None:
        graph_nodes = dict(getattr(graph, "nodes", {}) or {})
        graph_edges = list(getattr(graph, "edges", []) or [])
        if not graph_edges:
            return
        has_child_edges = any(
            getattr(edge, "kind", "") in {"proof_state_child", "proof_state_dependency"}
            for edge in graph_edges
        )
        has_attempt_edges = any(
            getattr(edge, "kind", "") == "failed_attempt" for edge in graph_edges
        )
        has_transition_edges = any(
            getattr(edge, "kind", "") == "diagnostic_transition"
            for edge in graph_edges
        )
        has_retrieval_edges = any(
            getattr(edge, "kind", "") in {"retrieved_declaration", "retrieved_fact"}
            for edge in graph_edges
        )
        has_blocker_edges = any(
            getattr(edge, "kind", "") == "blocked_by" for edge in graph_edges
        )
        has_assembly_edges = any(
            getattr(edge, "kind", "") == "proof_state_assembly"
            for edge in graph_edges
        )
        if (has_child_edges or has_assembly_edges) and not merge:
            for node in self.nodes.values():
                node.parent_node_id = ""
                node.dependencies = []
                node.child_node_ids = []
                node.assembly_attempt_groups = []
                if node.action == "assemble_from_children":
                    node.action = (
                        "prove_or_assemble"
                        if node.node_id == self.root_node_id
                        else "prove_child_helper"
                    )
        if has_attempt_edges and not merge:
            for node in self.nodes.values():
                node.diagnostics = []
        if has_transition_edges and not merge:
            for node in self.nodes.values():
                node.failure_transitions = []
                node.typed_transitions = []
        if has_retrieval_edges and not merge:
            for node in self.nodes.values():
                node.retrieved_decl_names = []
                node.retrieved_decl_provenance = {}
                node.retrieved_decl_signatures = {}
                node.graph_retrieved_decl_quarantine_names = []
                node.retrieved_facts = []
                node.retrieval_attempted = False
                node.retrieval_hit_count = 0
                node.decl_application_retry_keys = []
        if has_blocker_edges and not merge:
            for node in self.nodes.values():
                node.blocked_by_node_ids = []

        graph_decl_signatures: Dict[str, Set[str]] = {}
        if has_retrieval_edges and not topology_only:
            for edge in graph_edges:
                if str(getattr(edge, "kind", "") or "") != "retrieved_declaration":
                    continue
                node_id = self._local_state_node_id_from_graph_id(
                    str(getattr(edge, "source", "") or "")
                )
                retrieval_node = graph_nodes.get(
                    str(getattr(edge, "target", "") or "")
                )
                metadata = (
                    dict(getattr(retrieval_node, "metadata", {}) or {})
                    if retrieval_node is not None
                    else {}
                )
                if (
                    str(metadata.get("decl_execution_policy_version") or "").strip()
                    != PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                ):
                    continue
                signature = str(metadata.get("retrieval_signature") or "").strip()
                if node_id and signature:
                    graph_decl_signatures.setdefault(node_id, set()).add(signature)
        authoritative_graph_decl_signatures: Dict[str, str] = {}
        for node_id, signatures in graph_decl_signatures.items():
            node = self.nodes.get(node_id)
            existing = str(
                getattr(node, "retrieval_signature", "") or ""
            ).strip()
            if existing.startswith("graph_quarantine:"):
                existing = ""
            if existing:
                authoritative_graph_decl_signatures[node_id] = existing
            elif len(signatures) == 1:
                authoritative_graph_decl_signatures[node_id] = next(iter(signatures))

        assembly_groups: Dict[str, Tuple[str, ProofStateAssemblyAttempt]] = {}
        legacy_children: Dict[str, List[str]] = {}
        slot_children: Dict[str, List[Tuple[int, str]]] = {}

        def assembly_route_fingerprint(
            parent: ProofStateNode,
            group: ProofStateAssemblyAttempt,
        ) -> Tuple[str, bool]:
            """Return exact route identity and whether it carries authority.

            Branch-local assembly counters are not route identities. For a
            typed residual route, require one complete valid Lean receipt
            batch and bind the identity to its batch/context. Legacy groups
            may recover those fields only when exactly one valid batch fits.
            """

            child_ids = list(group.child_node_ids or ())
            child_payload = [
                {
                    "target_sha256": _proof_state_exact_sha256(
                        self.nodes[child_id].target
                    ),
                    "statement_environment_hash": str(
                        self.nodes[child_id].statement_environment_hash or ""
                    ),
                }
                for child_id in child_ids
                if child_id in self.nodes
            ]
            base_payload = {
                "parent_node_id": parent.node_id,
                "source": str(group.source or ""),
                "proof_stub_sha256": _proof_state_exact_sha256(group.proof_stub),
                "slot_count": max(
                    len(child_ids),
                    _proof_state_durable_nonnegative_int(
                        group.residual_goal_slot_count
                    ),
                ),
                "children": child_payload,
            }
            if not proof_state_source_requires_residual_goal_attestation(
                group.source
            ):
                valid = bool(
                    group.source
                    and group.proof_stub
                    and child_ids
                    and len(child_payload) == len(child_ids)
                )
                return (
                    text_hash(json.dumps(base_payload, sort_keys=True)),
                    valid,
                )

            if not child_ids or len(child_payload) != len(child_ids):
                invalid_payload = {
                    **base_payload,
                    "declared_batch_digest": str(
                        group.residual_goal_batch_digest or ""
                    ),
                    "declared_context_hash": str(
                        group.residual_goal_elaboration_context_hash or ""
                    ),
                    "typed_authority_valid": False,
                }
                return (
                    text_hash(json.dumps(invalid_payload, sort_keys=True)),
                    False,
                )

            declared_batch = str(group.residual_goal_batch_digest or "")
            declared_context = str(
                group.residual_goal_elaboration_context_hash or ""
            )
            first_authorities = _residual_goal_attestation_authorities(
                self.nodes[child_ids[0]].residual_goal_attestation
            )
            candidates = {
                (
                    str(authority.get("batch_digest") or ""),
                    str(authority.get("elaboration_context_hash") or ""),
                )
                for authority in first_authorities
                if authority.get("slot_index") == 0
                and authority.get("slot_count") == len(child_ids)
                and str(authority.get("source") or "") == group.source
                and str(authority.get("parent_node_id") or "") == parent.node_id
                and (
                    not declared_batch
                    or str(authority.get("batch_digest") or "")
                    == declared_batch
                )
                and (
                    not declared_context
                    or str(authority.get("elaboration_context_hash") or "")
                    == declared_context
                )
            }
            valid_batches: List[Tuple[str, str]] = []
            for batch_digest, context_hash in sorted(candidates):
                records: List[Dict[str, Any]] = []
                statements: List[str] = []
                for slot_index, child_id in enumerate(child_ids):
                    child = self.nodes[child_id]
                    authority = child.residual_goal_attestation.get(
                        f"{batch_digest}:{slot_index}"
                    )
                    if not isinstance(authority, Mapping):
                        records = []
                        break
                    records.append(dict(authority))
                    statements.append(child.target)
                if records and _validate_bound_residual_goal_attestation_batch(
                    records,
                    statements=statements,
                    source=group.source,
                    parent_node_id=parent.node_id,
                    parent_statement=parent.target,
                    parent_proof_stub=group.proof_stub,
                    statement_environment_hash=self.statement_environment_hash,
                    elaboration_context_hash=context_hash,
                ):
                    valid_batches.append((batch_digest, context_hash))
            if len(valid_batches) == 1:
                batch_digest, context_hash = valid_batches[0]
                group.residual_goal_batch_digest = batch_digest
                group.residual_goal_elaboration_context_hash = context_hash
                group.residual_goal_slot_count = len(child_ids)
                exact_payload = {
                    **base_payload,
                    "batch_digest": batch_digest,
                    "elaboration_context_hash": context_hash,
                    "typed_authority_valid": True,
                }
                return (
                    text_hash(json.dumps(exact_payload, sort_keys=True)),
                    True,
                )
            invalid_payload = {
                **base_payload,
                "declared_batch_digest": declared_batch,
                "declared_context_hash": declared_context,
                "candidate_batches": sorted(candidates),
                "typed_authority_valid": False,
            }
            return (
                text_hash(json.dumps(invalid_payload, sort_keys=True)),
                False,
            )

        def merge_same_route_progress(
            existing: ProofStateAssemblyAttempt,
            incoming: ProofStateAssemblyAttempt,
        ) -> ProofStateAssemblyAttempt:
            """Merge route identity, never an unbacked parent-closure verdict."""

            existing.residual_goal_slot_count = max(
                _proof_state_durable_nonnegative_int(
                    existing.residual_goal_slot_count
                ),
                _proof_state_durable_nonnegative_int(
                    incoming.residual_goal_slot_count
                ),
            )
            existing.residual_goal_batch_digest = (
                existing.residual_goal_batch_digest
                or incoming.residual_goal_batch_digest
            )
            existing.residual_goal_elaboration_context_hash = (
                existing.residual_goal_elaboration_context_hash
                or incoming.residual_goal_elaboration_context_hash
            )
            # The graph projection carries child helper-name witnesses, but
            # not the destination's kernel-checked parent helper/certificate.
            # Importing ``proved`` would suppress a valid assembly forever;
            # importing ``failed``/attempt_count can likewise strand a route.
            # Preserve only destination-owned progress and deterministically
            # replay this cheap parent assembly under the local Lean context.
            return existing

        def remap_colliding_assembly_id(
            parent: ProofStateNode,
            group: ProofStateAssemblyAttempt,
            graph_assembly_id: str,
        ) -> ProofStateAssemblyAttempt:
            """Preserve both routes when branch-local assembly ids collide."""

            incoming_fingerprint, incoming_authoritative = (
                assembly_route_fingerprint(parent, group)
            )
            collision = next(
                (
                    existing
                    for existing in parent.assembly_attempt_groups
                    if existing.assembly_id == group.assembly_id
                ),
                None,
            )
            if collision is None:
                return group
            collision_fingerprint, collision_authoritative = (
                assembly_route_fingerprint(parent, collision)
            )
            if (
                incoming_authoritative
                and collision_authoritative
                and incoming_fingerprint == collision_fingerprint
            ):
                return merge_same_route_progress(collision, group)
            if (
                not incoming_authoritative
                and not collision_authoritative
                and str(group.residual_goal_batch_digest or "")
                and group.residual_goal_batch_digest
                == collision.residual_goal_batch_digest
                and group.residual_goal_elaboration_context_hash
                == collision.residual_goal_elaboration_context_hash
                and str(group.source or "") == str(collision.source or "")
                and str(group.proof_stub or "")
                == str(collision.proof_stub or "")
                and _proof_state_durable_nonnegative_int(
                    group.residual_goal_slot_count
                )
                == _proof_state_durable_nonnegative_int(
                    collision.residual_goal_slot_count
                )
            ):
                # The same damaged receipt-bound route may appear in both the
                # execution record and its graph projection. Coalesce that
                # exact quarantine record without importing any progress.
                return collision
            suffix = text_hash(
                json.dumps(
                    {
                        "graph_assembly_id": str(graph_assembly_id or ""),
                        "parent_node_id": parent.node_id,
                        "route_fingerprint": incoming_fingerprint,
                    },
                    sort_keys=True,
                    ensure_ascii=True,
                )
            )[:16]
            base_id = f"{parent.node_id}:asm_import_{suffix}"
            candidate_id = base_id
            collision_index = 1
            while True:
                existing = next(
                    (
                        item
                        for item in parent.assembly_attempt_groups
                        if item.assembly_id == candidate_id
                    ),
                    None,
                )
                if existing is None:
                    group.assembly_id = candidate_id
                    return group
                existing_fingerprint, existing_authoritative = (
                    assembly_route_fingerprint(parent, existing)
                )
                if existing_fingerprint == incoming_fingerprint and (
                    incoming_authoritative == existing_authoritative
                ):
                    if incoming_authoritative:
                        return merge_same_route_progress(existing, group)
                    # Repeated hydration of the same quarantined route is
                    # idempotent, but never upgrades its status/authority.
                    return existing
                candidate_id = f"{base_id}_{collision_index}"
                collision_index += 1

        for edge in graph_edges:
            kind = str(getattr(edge, "kind", "") or "")
            source = str(getattr(edge, "source", "") or "")
            target = str(getattr(edge, "target", "") or "")
            if topology_only and not (
                kind
                in {
                    "proof_state_child",
                    "proof_state_dependency",
                    "proof_state_assembly",
                    "assembly_requires",
                }
                or kind.startswith("assembly_requires_slot:")
            ):
                continue
            if kind == "proof_state_child":
                parent_id = self._local_state_node_id_from_graph_id(source)
                child_id = self._local_state_node_id_from_graph_id(target)
                parent = self.nodes.get(parent_id)
                child = self.nodes.get(child_id)
                if parent is None or child is None:
                    continue
                if self._would_create_cycle(parent_id, child_id):
                    continue
                if child_id not in parent.child_node_ids:
                    parent.child_node_ids.append(child_id)
                child.parent_node_id = child.parent_node_id or parent_id
                if parent_id not in child.dependencies:
                    child.dependencies.append(parent_id)
            elif kind == "proof_state_dependency":
                dependency_id = self._local_state_node_id_from_graph_id(source)
                node_id = self._local_state_node_id_from_graph_id(target)
                node = self.nodes.get(node_id)
                if (
                    node is not None
                    and dependency_id
                    and not self._would_create_dependency_cycle(dependency_id, node_id)
                    and dependency_id not in node.dependencies
                ):
                    node.dependencies.append(dependency_id)
            elif kind == "blocked_by":
                node_id = self._local_state_node_id_from_graph_id(source)
                node = self.nodes.get(node_id)
                if node is None:
                    continue
                blocker_id = str(target or "").strip()
                if blocker_id and blocker_id not in node.blocked_by_node_ids:
                    node.blocked_by_node_ids.append(blocker_id)
            elif kind == "proved_by_helper":
                node_id = self._local_state_node_id_from_graph_id(source)
                node = self.nodes.get(node_id)
                helper_node = graph_nodes.get(target)
                if node is None:
                    continue
                helper_name = (
                    str(getattr(helper_node, "name", "") or "").strip()
                    if helper_node is not None
                    else str(target).removeprefix("helper:").strip()
                )
                if helper_name:
                    node.proved_helper_name = helper_name
                    node.successful_family = node.successful_family or "graph_helper"
            elif kind == "proof_state_assembly":
                parent_id = self._local_state_node_id_from_graph_id(source)
                parent = self.nodes.get(parent_id)
                assembly_node = graph_nodes.get(target)
                if parent is None or assembly_node is None:
                    continue
                group = self._assembly_group_from_graph_node(assembly_node)
                if group is None:
                    continue
                # Resolve branch-local assembly-id collisions only after all
                # ordered child-slot edges have been mapped. The attested
                # batch/context is part of route identity.
                assembly_groups[target] = (parent_id, group)
            elif kind == "assembly_requires" or kind.startswith("assembly_requires_slot:"):
                child_id = self._local_state_node_id_from_graph_id(target)
                if not child_id:
                    continue
                if kind.startswith("assembly_requires_slot:"):
                    try:
                        slot = int(kind.split(":", 1)[1])
                    except (IndexError, ValueError):
                        slot = len(slot_children.get(source, []))
                    slot_children.setdefault(source, []).append((slot, child_id))
                else:
                    legacy_children.setdefault(source, []).append(child_id)
            elif kind in {"retrieved_declaration", "retrieved_fact"}:
                node_id = self._local_state_node_id_from_graph_id(source)
                node = self.nodes.get(node_id)
                retrieval_node = graph_nodes.get(target)
                if node is None or retrieval_node is None:
                    continue
                metadata = dict(getattr(retrieval_node, "metadata", {}) or {})
                node.retrieval_attempted = True
                if kind == "retrieved_declaration":
                    decl_name = str(
                        metadata.get("decl_name")
                        or getattr(retrieval_node, "name", "")
                        or getattr(retrieval_node, "statement", "")
                        or ""
                    ).strip()
                    policy_version = str(
                        metadata.get("decl_execution_policy_version") or ""
                    ).strip()
                    edge_signature = str(
                        metadata.get("retrieval_signature") or ""
                    ).strip()
                    authoritative_signature = (
                        authoritative_graph_decl_signatures.get(node_id, "")
                    )
                    if (
                        decl_name
                        and policy_version
                        == PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                        and authoritative_signature
                        and edge_signature == authoritative_signature
                    ):
                        if decl_name not in node.retrieved_decl_names:
                            node.retrieved_decl_names.append(decl_name)
                        node.retrieved_decl_provenance[decl_name] = policy_version
                        node.retrieved_decl_execution_policy_version = policy_version
                        node.retrieved_decl_signatures[decl_name] = edge_signature
                        node.retrieval_signature = authoritative_signature
                    elif (
                        decl_name
                        and decl_name
                        not in node.graph_retrieved_decl_quarantine_names
                    ):
                        node.graph_retrieved_decl_quarantine_names.append(decl_name)
                else:
                    fact = str(
                        metadata.get("retrieved_fact")
                        or getattr(retrieval_node, "statement", "")
                        or getattr(retrieval_node, "name", "")
                        or ""
                    ).strip()
                    if fact and fact not in node.retrieved_facts:
                        node.retrieved_facts.append(fact[:1000])
                node.retrieval_hit_count = max(
                    node.retrieval_hit_count,
                    len(node.retrieved_decl_names)
                    + len(node.graph_retrieved_decl_quarantine_names)
                    + len(node.retrieved_facts),
                )
            elif kind == "failed_attempt":
                node_id = self._local_state_node_id_from_graph_id(source)
                node = self.nodes.get(node_id)
                attempt_node = graph_nodes.get(target)
                if node is None or attempt_node is None:
                    continue
                metadata = dict(getattr(attempt_node, "metadata", {}) or {})
                diagnostic = metadata.get("diagnostic")
                if not isinstance(diagnostic, dict):
                    diagnostic = {
                        "phase": str(getattr(attempt_node, "phase", "") or ""),
                        "turn_index": int(getattr(attempt_node, "turn_index", 0) or 0),
                        "error_type": str(getattr(attempt_node, "name", "") or ""),
                        "action": node.action,
                        "blocker": str(getattr(attempt_node, "statement", "") or ""),
                    }
                if diagnostic not in node.diagnostics:
                    node.diagnostics.append(dict(diagnostic))
            elif kind == "diagnostic_transition":
                node_id = self._local_state_node_id_from_graph_id(source)
                node = self.nodes.get(node_id)
                transition_node = graph_nodes.get(target)
                if node is None or transition_node is None:
                    continue
                metadata = dict(getattr(transition_node, "metadata", {}) or {})
                typed_record = (
                    metadata.get("typed_transition")
                    if isinstance(metadata.get("typed_transition"), dict)
                    else None
                )
                if typed_record is not None:
                    transition_obj = self._transition_from_record(typed_record)
                    if transition_obj is not None and all(
                        item.transition_id != transition_obj.transition_id
                        for item in node.typed_transitions
                    ):
                        node.typed_transitions.append(transition_obj)
                        self._trim_typed_transitions(node)
                transition = str(
                    getattr(transition_node, "name", "")
                    or metadata.get("transition")
                    or ""
                ).strip()
                if transition and transition not in node.failure_transitions:
                    node.failure_transitions.append(transition)

        for assembly_graph_id, (parent_id, group) in assembly_groups.items():
            parent = self.nodes.get(parent_id)
            if parent is None:
                continue
            slotted = slot_children.get(assembly_graph_id, [])
            if slotted:
                child_ids = [child_id for _, child_id in sorted(slotted)]
            else:
                child_ids = legacy_children.get(assembly_graph_id, group.child_node_ids)
            group.child_node_ids = [
                child_id
                for child_id in child_ids
                if child_id in self.nodes and not self._would_create_cycle(parent_id, child_id)
            ]
            mapped_witness: List[str] = []
            for raw_witness in group.last_attempt_witness:
                raw_child_id, separator, helper_name = str(raw_witness).partition(":")
                mapped_child_id = self._local_state_node_id_from_graph_id(
                    raw_child_id
                )
                if separator and mapped_child_id:
                    mapped_witness.append(f"{mapped_child_id}:{helper_name}")
            group.last_attempt_witness = tuple(sorted(set(mapped_witness)))
            effective_group = remap_colliding_assembly_id(
                parent,
                group,
                assembly_graph_id,
            )
            if effective_group not in parent.assembly_attempt_groups:
                parent.assembly_attempt_groups.append(effective_group)
            parent.action = "assemble_from_children"
            for child_id in effective_group.child_node_ids:
                child = self.nodes.get(child_id)
                if child is None:
                    continue
                if child_id not in parent.child_node_ids:
                    parent.child_node_ids.append(child_id)
                child.parent_node_id = child.parent_node_id or parent_id
                if parent_id not in child.dependencies:
                    child.dependencies.append(parent_id)
                if effective_group.proof_stub and not child.parent_proof_stub:
                    child.parent_proof_stub = effective_group.proof_stub
            if not effective_group.child_node_ids and effective_group.status == "open":
                effective_group.status = "failed"

    def _assembly_group_from_graph_node(
        self,
        graph_node: Any,
    ) -> Optional[ProofStateAssemblyAttempt]:
        metadata = dict(getattr(graph_node, "metadata", {}) or {})
        record = metadata.get("proof_state_assembly")
        if isinstance(record, dict):
            assembly_id = str(record.get("assembly_id") or "").strip()
            if not assembly_id:
                assembly_id = str(getattr(graph_node, "name", "") or "").strip()
            if not assembly_id:
                return None
            group_status = str(
                record.get("status")
                or getattr(graph_node, "status", "")
                or "open"
            )
            group_attestation_quarantined = bool(
                group_status == "blocked"
                and record.get("attestation_quarantined") is True
                and record.get("attestation_quarantine_previous_status")
                == "open"
            )
            return ProofStateAssemblyAttempt(
                assembly_id=assembly_id,
                source=str(record.get("source") or ""),
                proof_stub=str(record.get("proof_stub") or getattr(graph_node, "statement", "") or ""),
                child_node_ids=[
                    str(child)
                    for child in _proof_state_durable_sequence(
                        record.get("child_node_ids")
                    )
                    if str(child or "").strip()
                ],
                residual_goal_slot_count=(
                    _proof_state_durable_nonnegative_int(
                        record.get("residual_goal_slot_count")
                    )
                ),
                residual_goal_batch_digest=str(
                    record.get("residual_goal_batch_digest") or ""
                ),
                residual_goal_elaboration_context_hash=str(
                    record.get("residual_goal_elaboration_context_hash") or ""
                ),
                attempt_count=_proof_state_durable_nonnegative_int(
                    record.get("attempt_count")
                ),
                status=group_status,
                attestation_quarantined=group_attestation_quarantined,
                attestation_quarantine_previous_status=(
                    "open" if group_attestation_quarantined else ""
                ),
                last_attempt_witness=tuple(
                    str(witness)
                    for witness in _proof_state_durable_sequence(
                        record.get("last_attempt_witness")
                    )
                    if str(witness or "").strip()
                ),
            )
        assembly_id = str(getattr(graph_node, "name", "") or "").strip()
        if not assembly_id:
            return None
        return ProofStateAssemblyAttempt(
            assembly_id=assembly_id,
            source=str(metadata.get("source") or ""),
            proof_stub=str(getattr(graph_node, "statement", "") or ""),
            status=str(getattr(graph_node, "status", "") or "open"),
        )

    def _prune_missing_graph_references(self) -> None:
        valid_ids = set(self.nodes)
        for node in self.nodes.values():
            if node.parent_node_id and (
                node.parent_node_id not in valid_ids
                or self._would_create_cycle(node.parent_node_id, node.node_id)
            ):
                node.parent_node_id = ""
            node.dependencies = [
                item
                for item in node.dependencies
                if item in valid_ids
                and item != node.node_id
                and not self._would_create_dependency_cycle(item, node.node_id)
            ]
            node.blocked_by_node_ids = [
                item
                for item in node.blocked_by_node_ids
                if not str(item or "").startswith("proof_state:")
                or self._state_node_id_from_graph_id(item) in valid_ids
            ]
            node.child_node_ids = [
                item
                for item in node.child_node_ids
                if item in valid_ids and not self._would_create_cycle(node.node_id, item)
            ]
            for group in node.assembly_attempt_groups:
                group.child_node_ids = [
                    item
                    for item in group.child_node_ids
                    if item in valid_ids and not self._would_create_cycle(node.node_id, item)
                ]
                if not group.child_node_ids and group.status == "open":
                    group.status = "failed"
            if (
                node.action == "assemble_from_children"
                and not node.child_node_ids
                and not any(group.child_node_ids for group in node.assembly_attempt_groups)
            ):
                node.action = (
                    "prove_or_assemble"
                    if node.node_id == self.root_node_id
                    else "needs_llm_or_split"
                )
                node.priority = self._priority(node)
        # Adversarial review fix 2026-05-09: this method bulk-mutates
        # ``group.child_node_ids`` without going through
        # ``_attach_child_to_parent``. Rebuild the inverse index here so
        # any future caller that doesn't pair this with a separate
        # rebuild (only ``from_graph`` does today) cannot leave stale
        # entries. Defensive coupling — the call is idempotent.
        self._rebuild_assembly_index()

    def _normalize_unbacked_assembly_progress(self) -> None:
        """Discard terminal route progress lacking a local parent certificate."""

        valid_statuses = {"open", "proved", "failed", "blocked", "obsolete"}
        for parent in self.nodes.values():
            for group in parent.assembly_attempt_groups:
                if group.status not in valid_statuses:
                    group.status = "open"
                    group.attempt_count = 0
                    group.last_attempt_witness = ()
                if group.status == "proved" and parent.status != "proved":
                    # Child helper-name witnesses do not carry the checked
                    # parent helper/certificate from another runtime. Reopen
                    # deterministic assembly so local Lean recreates it.
                    group.status = "open"
                    group.attempt_count = 0
                    group.last_attempt_witness = ()

    def _normalize_unbacked_node_progress(self, graph: Any) -> None:
        """Reopen restored proved nodes lacking graph-owned proof authority.

        The private proof-state snapshot is an execution cache, not an
        independent certificate store.  Root closure is corroborated by the
        graph's exact final proof/hash.  Non-root closure is corroborated by a
        replayable verified-helper node that certifies the exact proof-state
        target and environment.  A mutated/stale status bit must never retire
        work by itself.
        """

        graph_nodes = getattr(graph, "nodes", {}) if graph is not None else {}
        if not isinstance(graph_nodes, dict):
            graph_nodes = {}
        graph_root = graph_nodes.get(
            str(getattr(graph, "root_node_id", "") or "")
        )
        helper_ids = getattr(graph, "helper_name_to_node_id", {}) or {}
        helper_certifies = getattr(graph, "_helper_certifies_node", None)

        for node in self.nodes.values():
            if node.status != "proved" or node.kind == "decomposition_task":
                continue
            backed = False
            if node.node_id == self.root_node_id:
                root_metadata = (
                    dict(getattr(graph_root, "metadata", {}) or {})
                    if graph_root is not None
                    else {}
                )
                final_proof = str(root_metadata.get("final_proof") or "")
                proof_hash = str(
                    getattr(graph_root, "proof_hash", "") or ""
                ).strip()
                backed = bool(
                    graph_root is not None
                    and str(getattr(graph_root, "status", "") or "")
                    == "proved"
                    and final_proof
                    and proof_hash == text_hash(final_proof)
                )
            else:
                helper_name = str(node.proved_helper_name or "").strip()
                graph_node = graph_nodes.get(self._graph_node_id(node.node_id))
                helper_node = graph_nodes.get(
                    str(helper_ids.get(helper_name) or "")
                )
                if helper_name and callable(helper_certifies):
                    try:
                        backed = bool(helper_certifies(helper_node, graph_node))
                    except Exception:
                        backed = False
            if backed:
                continue
            node.status = "open"
            node.action = (
                "prove_or_assemble"
                if node.node_id == self.root_node_id
                else "prove_child_helper"
            )
            node.proved_helper_name = ""
            node.successful_family = ""
            node.blocker = (
                "restored proved state lacked an exact graph proof certificate"
            )
            node.priority = self._priority(node)

    def reconcile_helpers_to_dossier(
        self,
        dossier: Optional[ProofDossier],
        *,
        source: str = "rollback_resync",
        phase: str = "reconcile_helpers_to_dossier",
        turn_index: int = 0,
        target_node_id: str = "",
    ) -> List[Dict[str, Any]]:
        """Re-promote OPEN proof_state child_goals matching durable dossier helpers.

        B2 fix (2026-05-11): the rollback contract restores
        ``proof_state.nodes`` from a deep-copied snapshot (terminal
        statuses such as ``"proved"`` revert to ``"open"``), but
        ``dossier.verified_helpers`` is preserved as durable wins. The
        existing ``_resync_graph_from_dossier`` helper re-syncs only
        ``dossier.proof_graph`` from those surviving helpers — it
        never touches ``proof_state.nodes``. Three-way drift: dossier
        + graph agree the helper is proved; proof_state child_goal
        whose target matches the helper is back to ``"open"``; the
        assembly fixpoint can't consume the helper.

        This method closes the gap by re-marking matching child_goal
        nodes as ``status="proved"`` with ``proved_helper_name`` set.

        Eligibility (F2 hardening, 2026-05-11): ONLY nodes currently
        in ``status="open"`` are promoted. The first cut of B2 reused
        ``record_verified_helper_matches``, which also accepts
        ``rejected``/``failed``/``blocked`` — that would resurrect
        intentionally-failed nodes from old durable helpers and cascade
        sibling obsolete-cancellations. Post-rollback semantics: the
        only drift we want to close is "rollback reset proved → open
        for a node whose helper survived in the dossier." Other
        terminal statuses are intentional close states the rollback
        should NOT undo. (``proved``, ``obsolete`` are already skipped
        by record_verified_helper_matches; here we additionally skip
        ``rejected``, ``failed``, ``blocked``.)

        Companion to ``reconcile_with_dossier`` (which handles the
        opposite drift: proof_state thinks proved, dossier disagrees).
        """

        if dossier is None:
            return []
        helpers = getattr(dossier, "verified_helpers", None)
        if not isinstance(helpers, dict) or not helpers:
            return []

        helper_records: List[Tuple[str, str, str]] = []
        for helper_name, helper in helpers.items():
            name = str(helper_name or "").strip()
            if not name:
                continue
            helper_source = str(getattr(helper, "source", "") or "")
            helper_statement = helper_decl_statement(helper_source)
            if not helper_statement:
                continue
            helper_records.append(
                (
                    name,
                    helper_statement,
                    canonicalize_lean_statement_for_identity(helper_statement),
                )
            )
        if not helper_records:
            return []

        requested_target_id = str(target_node_id or "").strip()
        candidate_nodes = (
            [self.nodes[requested_target_id]]
            if requested_target_id in self.nodes
            else ([] if requested_target_id else list(self.nodes.values()))
        )
        matched: List[Dict[str, Any]] = []
        for node in candidate_nodes:
            if node.node_id == self.root_node_id:
                continue
            if node.kind != "child_goal":
                continue
            # Keep authoritative falsification orthogonal to status/reopen
            # policy, but never manufacture the contradictory state
            # ``status=proved`` plus ``falsified=True`` during recovery.
            if node.falsified:
                continue
            # F2 hardening: only re-promote OPEN nodes. Other terminal
            # statuses are deliberate close states that rollback should
            # not undo.
            if node.status != "open":
                continue
            target_key = canonicalize_lean_statement_for_identity(node.target)
            if not target_key:
                continue
            for helper_name, helper_statement, helper_key in helper_records:
                if not self._verified_helper_match_allowed_for_node(node, helper_name):
                    continue
                if helper_key != target_key:
                    continue
                node.status = "proved"
                node.action = "available_for_assembly"
                node.proved_helper_name = helper_name
                node.successful_family = source
                node.blocker = (
                    "post-rollback reconcile: durable helper matched "
                    f"open child target: {helper_name}"
                )
                node.priority = self._priority(node)
                self._clear_terminal_node_verifier_work(node)
                self.record_transition(
                    node_id=node.node_id,
                    source=source,
                    error_type="reconcile_helper_to_dossier",
                    action=node.action,
                    blocker=node.blocker,
                    payload={
                        "helper_name": helper_name,
                        "helper_statement_preview": helper_statement[:200],
                        "turn_index": int(turn_index or 0),
                    },
                )
                self._reconcile_unverified_lemma_dag_parent_for_child(
                    node.node_id,
                    source=source,
                    turn_index=turn_index,
                )
                self._refresh_priorities_for_neighbors(node.node_id)
                matched.append(
                    {
                        "node_id": node.node_id,
                        "helper_name": helper_name,
                        "target": node.target[:200],
                    }
                )
                break
        return matched

    def reconcile_with_dossier(self, dossier: Optional[ProofDossier]) -> None:
        """Reopen graph-restored proved nodes without matching dossier certificates."""

        if dossier is None:
            return

        def reopen_proved_assembly_groups(
            node: ProofStateNode,
            *,
            source: str,
            error_type: str,
        ) -> None:
            reopened: List[str] = []
            for group in node.assembly_attempt_groups:
                if group.status != "proved":
                    continue
                group.status = "open"
                group.attempt_count = 0
                group.last_attempt_witness = ()
                reopened.append(group.assembly_id)
            if reopened:
                self.record_transition(
                    node_id=node.node_id,
                    source=source,
                    error_type=error_type,
                    action=node.action,
                    blocker=node.blocker,
                    payload={"assembly_ids": reopened},
                )

        for node in self.nodes.values():
            if node.node_id == self.root_node_id and node.status == "proved":
                if str(getattr(dossier, "final_proof_hash", "") or ""):
                    continue
                node.status = "open"
                node.action = "prove_or_assemble"
                node.proved_helper_name = ""
                node.successful_family = ""
                node.blocker = "graph root solved state missing final dossier proof"
                self.record_transition(
                    node_id=node.node_id,
                    source="graph_rehydrate",
                    error_type="missing_root_proof",
                    action=node.action,
                    blocker=node.blocker,
                    payload={"final_proof_hash": ""},
                )
                reopen_proved_assembly_groups(
                    node,
                    source="graph_rehydrate",
                    error_type="root_assembly_group_reopened_missing_final_proof",
                )
                node.priority = self._priority(node)
                continue
            helper_name = str(node.proved_helper_name or "").strip()
            if node.status != "proved":
                continue
            if node.kind == "decomposition_task":
                continue
            if not helper_name:
                node.status = "open"
                node.action = (
                    "prove_child_helper"
                    if node.kind != "root"
                    else "prove_or_assemble"
                )
                node.proved_helper_name = ""
                node.successful_family = ""
                node.blocker = "graph proved node missing helper certificate"
                self.record_transition(
                    node_id=node.node_id,
                    source="graph_rehydrate",
                    error_type="missing_helper_edge",
                    action=node.action,
                    blocker=node.blocker,
                )
                reopen_proved_assembly_groups(
                    node,
                    source="graph_rehydrate",
                    error_type="assembly_group_reopened_missing_helper_edge",
                )
                node.priority = self._priority(node)
                continue
            helper_record = getattr(dossier, "verified_helpers", {}).get(helper_name)
            helper_source = str(getattr(helper_record, "source", "") or "")
            helper_statement = helper_decl_statement(helper_source)
            if helper_record is not None and (
                canonicalize_lean_statement_for_identity(helper_statement)
                == canonicalize_lean_statement_for_identity(node.target)
            ):
                continue
            node.status = "open"
            node.action = "prove_child_helper" if node.kind != "root" else "prove_or_assemble"
            node.proved_helper_name = ""
            node.successful_family = ""
            if helper_record is None:
                node.blocker = "graph proved helper missing from verified dossier"
                self.record_transition(
                    node_id=node.node_id,
                    source="graph_rehydrate",
                    error_type="missing_helper",
                    action=node.action,
                    blocker=node.blocker,
                    payload={"helper_name": helper_name},
                )
                reopen_proved_assembly_groups(
                    node,
                    source="graph_rehydrate",
                    error_type="assembly_group_reopened_missing_helper",
                )
            else:
                node.blocker = "graph proved helper statement mismatches node target"
                self.record_transition(
                    node_id=node.node_id,
                    source="graph_rehydrate",
                    error_type="helper_statement_mismatch",
                    action=node.action,
                    blocker=node.blocker,
                    payload={"helper_name": helper_name},
                )
                reopen_proved_assembly_groups(
                    node,
                    source="graph_rehydrate",
                    error_type="assembly_group_reopened_helper_statement_mismatch",
                )
            node.priority = self._priority(node)

    def invalidate_assembly_contracts_for_helpers(
        self,
        helper_names: Sequence[str],
        *,
        phase: str = "",
        turn_index: int = 0,
        source: str = "helper_replacement",
        conservative: bool = False,
    ) -> int:
        names = {
            str(name or "").strip()
            for name in list(helper_names or ())
            if str(name or "").strip()
        }
        if not names:
            return 0
        invalidated = 0
        for node in self.nodes.values():
            invalidated_groups: List[Dict[str, Any]] = []
            for group in node.assembly_attempt_groups:
                if group.status == "obsolete":
                    continue
                refs = (
                    set(names)
                    if conservative
                    else lean_referenced_helper_names(group.proof_stub, sorted(names))
                )
                if not refs:
                    continue
                group.status = "open" if conservative else "obsolete"
                if conservative:
                    group.attempt_count = 0
                group.last_attempt_witness = ()
                invalidated += 1
                invalidated_groups.append(
                    {
                        "assembly_id": group.assembly_id,
                        "referenced_helpers": sorted(refs),
                        "conservative": bool(conservative),
                    }
                )
            if not invalidated_groups:
                continue
            if conservative or node.status not in {"proved", "obsolete"}:
                node.status = "open"
                node.action = (
                    "prove_or_assemble"
                    if node.node_id == self.root_node_id
                    else "assemble_from_children"
                )
                node.blocker = "assembly contract invalidated by helper replacement"
                node.priority = self._priority(node)
            self.record_transition(
                node_id=node.node_id,
                source=source,
                error_type="assembly_contract_invalidated_by_helper_replacement",
                action=node.action,
                blocker=node.blocker,
                phase=phase,
                turn_index=turn_index,
                payload={
                    "invalidated_helpers": sorted(names),
                    "conservative": bool(conservative),
                    "assembly_groups": invalidated_groups,
                },
            )
        return invalidated

    def _goal_signature(
        self,
        target: str,
        context: Sequence[str],
        *,
        source_failure: str = "",
    ) -> NormalizedProofGoal:
        """Build the stable, type-shaped representation used by the scheduler.

        This is deliberately syntactic.  We do not ask Lean for elaborated
        expressions here, but we normalize local binder names, extract theorem
        constants, and hash the resulting proposition so equivalent residual
        goals do not fork the search graph under cosmetic Lean-printing drift.
        """

        if "\n" in str(target or "") and _has_layout_sensitive_local_let(str(target)):
            clean_target = _normalize_rendered_proof_state_target_text(target)
        else:
            clean_target = self._normalize_goal_text(target)
        sanitized_target, sanitized_context = self._sanitize_context_for_statement(
            clean_target,
            context,
        )
        local_hypotheses: List[Dict[str, str]] = []
        bound_names: Set[str] = set()
        bound_order: List[str] = []
        binder_structure: List[str] = []
        for hyp in sanitized_context:
            if self._is_local_definition_context(hyp):
                for name in self._split_local_definition_names(hyp):
                    bound_names.add(name)
                    bound_order.append(name)
                continue
            names, typ = self._split_hypothesis_binder(hyp)
            if not names or not typ:
                continue
            typ_norm = self._normalize_goal_text(typ)
            for name in names:
                bound_names.add(name)
                bound_order.append(name)
                local_hypotheses.append({"name": name, "type": typ_norm})
            head = self._goal_result_head(typ_norm) or self._first_constant(typ_norm)
            binder_structure.append(
                f"{len(names)}:{head or _compact_search_text(typ_norm, limit=60)}"
            )

        statement = self._statement_from_context(sanitized_target, sanitized_context)
        statement_bound_names = lean_statement_bound_names(statement)
        all_bound_names = set(bound_names).union(statement_bound_names)
        hash_bound_names = [
            name for name in bound_order if name not in statement_bound_names
        ]
        normalized_statement = self._normalize_statement_for_hash(
            statement,
            bound_names=hash_bound_names,
        )
        constants = self._extract_goal_constants(statement, bound_names=all_bound_names)
        typeclass_needs = self._typeclass_needs(statement)
        namespaces = self._namespace_list(constants)
        result_head = self._goal_result_head(sanitized_target, bound_names=all_bound_names)
        shape_tags = self._goal_shape_tags(
            constants=constants,
            target=sanitized_target,
            typeclass_needs=typeclass_needs,
            binder_structure=binder_structure,
        )
        return NormalizedProofGoal(
            target_expr=sanitized_target,
            local_hypotheses=local_hypotheses,
            constants_used=constants,
            binder_structure=binder_structure,
            typeclass_needs=typeclass_needs,
            namespaces=namespaces,
            result_head=result_head,
            normalized_statement=normalized_statement,
            normalized_statement_hash=text_hash(normalized_statement),
            shape_tags=shape_tags,
            source_failure=str(source_failure or ""),
        )

    def record_failure(
        self,
        *,
        phase: str,
        turn_index: int,
        analysis: Dict[str, Any],
        repair_retrieval: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        root = self.nodes[self.root_node_id]
        raw_remaining_goals = list(analysis.get("remaining_goals") or [])
        remaining_goals = raw_remaining_goals[:4]
        routed_action, routed_blocker = self._route_failure(analysis)
        root.failed_attempts += 1
        root.status = "open"
        if routed_action == "spawn_child_goals" and remaining_goals:
            root.action = "repair_failed_proof_residue"
            root.blocker = (
                f"quarantined {len(remaining_goals)} unvalidated remaining goal(s)"
            )
        else:
            root.action, root.blocker = routed_action, routed_blocker
        self.record_transition(
            node_id=self.root_node_id,
            source="lean_failure",
            error_type=str(analysis.get("error_type") or "lean_rejected"),
            action=root.action,
            blocker=root.blocker,
            phase=phase,
            turn_index=turn_index,
            payload={
                "details": dict(analysis.get("details") or {}),
                "remaining_goal_count": len(raw_remaining_goals),
                "routed_action": routed_action,
                "routed_blocker": routed_blocker,
            },
        )
        root.priority = self._priority(root)
        root.diagnostics.append(
            {
                "phase": str(phase or ""),
                "turn_index": int(turn_index or 0),
                "error_type": str(analysis.get("error_type") or ""),
                "action": root.action,
                "blocker": root.blocker,
            }
        )
        del root.diagnostics[:-8]

        if repair_retrieval:
            rendered = str(repair_retrieval.get("rendered", "") or "").strip()
            if rendered:
                self.record_retrieved_facts(
                    self.root_node_id,
                    rendered,
                    hit_count=int(repair_retrieval.get("result_count", 0) or 0),
                )

        quarantined = self._quarantine_failed_proof_residual_goals(
            remaining_goals,
            total_goal_count=len(raw_remaining_goals),
            phase=phase,
            turn_index=turn_index,
            action=root.action,
            blocker=root.blocker,
        )
        spawned: List[str] = []
        return {
            "root_action": root.action,
            "root_blocker": root.blocker,
            "spawned_nodes": spawned,
            "quarantined_remaining_goal_count": len(quarantined),
            "quarantined_remaining_goals": quarantined,
            "frontier": [node.node_id for node in self.frontier(max_nodes=6)],
        }

    def _quarantine_failed_proof_residual_goals(
        self,
        goals: Sequence[Any],
        *,
        total_goal_count: int = 0,
        phase: str,
        turn_index: int,
        action: str,
        blocker: str,
    ) -> List[Dict[str, Any]]:
        """Record unvalidated failed-proof residuals without scheduling them.

        Residual goals from a failed complete proof are evidence about that
        proof script, not automatically mathematical sublemmas. Validated
        reduction paths still call ``spawn_remaining_goals`` directly with a
        checked ``parent_proof_stub``; this gate covers only the low-trust
        ``record_failure`` path.
        """

        quarantined: List[Dict[str, Any]] = []
        for index, goal in enumerate(list(goals or []), 1):
            if not isinstance(goal, dict):
                continue
            target = self._normalize_goal_text(goal.get("target"))
            if not target:
                continue
            raw_context = (
                goal.get("hypotheses")
                or goal.get("context")
                or goal.get("local_context")
                or []
            )
            if isinstance(raw_context, str):
                raw_context = [line for line in raw_context.splitlines() if line.strip()]
            context = [
                self._normalize_hypothesis(item)
                for item in list(raw_context or [])[:10]
            ]
            context = [item for item in context if item]
            try:
                goal_index = int(goal.get("index") or index)
            except (TypeError, ValueError):
                goal_index = index
            quarantined.append(
                {
                    "index": goal_index,
                    "target": target,
                    "hypotheses": list(context),
                    "hypothesis_count": len(context),
                    "reason": "unvalidated_failed_proof_residue",
                }
            )
        if not quarantined:
            return []
        total_quarantined = max(len(quarantined), int(total_goal_count or 0))
        self.failed_proof_residual_batches_quarantined += 1
        self.failed_proof_residual_goals_quarantined += total_quarantined
        root = self.nodes.get(self.root_node_id)
        if root is not None:
            self.record_transition(
                node_id=root.node_id,
                source="failed_proof_residual_gate",
                error_type="failed_proof_residuals_quarantined",
                action=action,
                blocker=blocker,
                phase=phase,
                turn_index=turn_index,
                payload={
                    "quarantined_count": total_quarantined,
                    "quarantined_detail_count": len(quarantined),
                    "goals": [dict(item) for item in quarantined],
                },
            )
        return quarantined

    def _invalidate_decl_tried_on_context_change(self, dossier: Any) -> None:
        """Clear per-node decl-application tried memory when the Lean
        application context (verified-helper set) changes.

        The fingerprint is cheap (sorted helper source hashes) and stable
        across handoffs/re-retrievals that do NOT change the context, so the
        anti-replay behavior for unchanged contexts is untouched.
        """

        helpers = getattr(dossier, "verified_helpers", None)
        if not isinstance(helpers, dict):
            return
        hasher = hashlib.sha256()
        for source_hash in sorted(
            str(getattr(helper, "source_hash", "") or "")
            for helper in helpers.values()
        ):
            hasher.update(source_hash.encode("utf-8", "replace"))
            hasher.update(b"\0")
        fingerprint = hasher.hexdigest()
        previous = str(
            getattr(self, "decl_application_context_fingerprint", "") or ""
        )
        if previous == fingerprint:
            return
        self.decl_application_context_fingerprint = fingerprint
        if not previous:
            # First observation: establish the baseline without granting a
            # retro-active retry (fresh states have empty tried sets anyway;
            # restored states keep their memory until the context truly moves).
            return
        for node in self.nodes.values():
            if getattr(node, "kind", "") != "child_goal":
                continue
            terminal_tactic_keys = list(
                getattr(node, "tactic_terminal_context_keys", []) or []
            )
            retry_tactic_keys = list(
                getattr(node, "tactic_timeout_retry_context_keys", []) or []
            )
            if terminal_tactic_keys or retry_tactic_keys:
                node.tactic_terminal_context_keys = []
                node.tactic_timeout_retry_context_keys = []
                self.record_transition(
                    node_id=node.node_id,
                    source="tactic",
                    error_type="tactic_terminal_context_reset_context_change",
                    action=node.action,
                    blocker=(
                        "helper_context_changed:"
                        f"{len(terminal_tactic_keys) + len(retry_tactic_keys)}_retriable"
                    ),
                )
            tried = list(getattr(node, "decl_application_tried_decl_names", []) or [])
            retry_keys = list(getattr(node, "decl_application_retry_keys", []) or [])
            if not tried and not retry_keys:
                continue
            _queue_decl_application_context_replays(node)
            node.decl_application_signature = ""
            self.record_transition(
                node_id=node.node_id,
                source="decl_application",
                error_type="decl_tried_reset_context_change",
                action="reset",
                blocker=(
                    "helper_context_changed:"
                    f"{len(tried) + len(retry_keys)}_retriable"
                ),
            )

    @staticmethod
    def _authoritative_falsification_certificates(
        dossier: Any,
    ) -> Dict[str, Tuple[str, str]]:
        """Map certificate hash to statement + target environment.

        Only AUTHORITATIVE refutation certificates with fresh process-local
        authority are included.

        The immutable ledger survives checkpoints for audit and replay, but a
        serialized certificate is quarantined on restore.  Only a typed
        process-local authority receipt recreated by a live replay may
        continue suppressing proof-state work.
        """

        out: Dict[str, Tuple[str, str]] = {}
        active_certificates = {
            str(authority.get("certificate_hash") or "").strip(): (
                str(authority.get("target_environment_hash") or "").strip()
            )
            for authority in dict(
                getattr(dossier, "mini_authoritative_negations", {}) or {}
            ).values()
            if isinstance(authority, dict)
            and str(authority.get("certificate_hash") or "").strip()
            and str(authority.get("target_environment_hash") or "").strip()
        }
        if not active_certificates:
            return out
        for report in list(getattr(dossier, "mini_falsification_ledger", []) or []):
            if not isinstance(report, dict):
                continue
            for finding in list(report.get("findings") or []):
                if not isinstance(finding, dict):
                    continue
                cert = finding.get("certificate")
                if not isinstance(cert, dict) or not cert.get("authoritative"):
                    continue
                cert_hash = str(cert.get("certificate_hash") or "").strip()
                target_environment_hash = active_certificates.get(cert_hash, "")
                if target_environment_hash:
                    out[cert_hash] = (
                        str(cert.get("statement") or ""),
                        target_environment_hash,
                    )
        return out

    def _falsified_linkage_ok(
        self,
        node: Any,
        certificate_hash: str,
        certificates: Dict[str, Tuple[str, str]],
    ) -> bool:
        certificate = certificates.get(str(certificate_hash or "").strip())
        if certificate is None:
            return False
        statement, target_environment_hash = certificate
        node_environment_hash = str(
            getattr(node, "statement_environment_hash", "") or ""
        ).strip()
        if (
            not node_environment_hash
            or node_environment_hash != target_environment_hash
        ):
            return False
        # Exact trimmed equality: production certifies the node's target
        # STRING verbatim, and canonical keys sit in the identity-
        # collision blast radius (external review: a certificate for a false
        # statement was accepted for a true one via a canonical-key merge).
        return str(statement).strip() == str(
            getattr(node, "target", "") or ""
        ).strip()

    def _restore_routes_after_falsification_quarantine(
        self,
        node: ProofStateNode,
        certificate_hash: str,
    ) -> None:
        """Undo only assembly retirements caused by this certificate."""

        wanted_hash = str(certificate_hash or "").strip()
        durable_routes = [
            dict(item)
            for item in list(
                getattr(node, "falsification_retired_assembly_routes", []) or []
            )
            if isinstance(item, dict)
            and (
                not wanted_hash
                or str(item.get("certificate_hash") or "") == wanted_hash[:128]
            )
        ]
        for parent_id, assembly_id in self.parent_groups_for_child(node.node_id):
            parent = self.nodes.get(parent_id)
            if parent is None:
                continue
            previous_status = ""
            for route in durable_routes:
                if (
                    str(route.get("parent_node_id") or "") == parent_id
                    and str(route.get("assembly_id") or "") == assembly_id
                ):
                    previous_status = str(route.get("previous_status") or "open")
                    break
            for transition in reversed(list(parent.typed_transitions or [])):
                if previous_status:
                    break
                if (
                    transition.source != "falsification"
                    or transition.error_type
                    != "assembly_route_invalidated_by_falsified_child"
                ):
                    continue
                payload = dict(transition.payload or {})
                if (
                    str(payload.get("child_node_id") or "") != node.node_id
                    or str(payload.get("assembly_id") or "") != assembly_id
                    or (
                        wanted_hash
                        and str(payload.get("certificate_hash") or "")
                        != wanted_hash[:128]
                    )
                ):
                    continue
                previous_status = str(payload.get("previous_status") or "open")
                break
            if not previous_status:
                continue
            for group in parent.assembly_attempt_groups:
                if group.assembly_id == assembly_id and group.status == "obsolete":
                    group.status = (
                        previous_status
                        if previous_status in {"open", "failed"}
                        else "open"
                    )
                    parent.blocker = "falsification authority quarantined; route reopened"
                    parent.priority = self._priority(parent)
                    break
        node.falsification_retired_assembly_routes = []

    def _reconcile_falsified_flags(self, dossier: Any) -> None:
        """Fail-open enforcement of the certificate linkage.

        Durable suppression may only survive while its certificate hash names
        an AUTHORITATIVE ledger refutation of this exact node statement. A
        flag without that linkage (fabricated in-memory, or a corrupted /
        foreign record) is CLEARED — re-probing a false goal costs budget;
        suppressing a provable one is catastrophic. Legacy flags (recorded
        before the hash field existed) adopt the matching ledger hash.
        """

        falsified_nodes = [
            node
            for node in self.nodes.values()
            if getattr(node, "kind", "") == "child_goal"
            and getattr(node, "falsified", False)
        ]
        if not falsified_nodes:
            return
        certificates = self._authoritative_falsification_certificates(dossier)
        statement_to_hash = {
            (str(statement).strip(), target_environment_hash): cert_hash
            for cert_hash, (statement, target_environment_hash) in certificates.items()
        }
        for node in falsified_nodes:
            cert_hash = str(
                getattr(node, "falsification_certificate_hash", "") or ""
            ).strip()
            if cert_hash and self._falsified_linkage_ok(
                node, cert_hash, certificates
            ):
                continue
            if not cert_hash:
                adopted = statement_to_hash.get(
                    (
                        str(getattr(node, "target", "") or "").strip(),
                        str(
                            getattr(node, "statement_environment_hash", "") or ""
                        ).strip(),
                    )
                )
                if adopted:
                    node.falsification_certificate_hash = adopted[:128]
                    continue
            self._restore_routes_after_falsification_quarantine(node, cert_hash)
            node.falsified = False
            node.falsification_reason = ""
            node.falsification_certificate_hash = ""
            self.record_transition(
                node_id=node.node_id,
                source="falsification",
                error_type="falsified_flag_unverifiable_cleared",
                action="reconcile",
                blocker="no authoritative ledger certificate for this statement",
            )

    def mark_child_goal_falsified(
        self,
        node_id: str,
        *,
        certificate_hash: str,
        dossier: Any = None,
        reason: str = "",
        phase: str = "",
        turn_index: int = 0,
    ) -> bool:
        """Durably mark a child goal as Lean-falsified (proven FALSE).

        SOUNDNESS: the caller MUST already hold an axiom-audited negation
        certificate for this node's statement (e.g. from
        ``certify_negation_proof_result``); this method does not itself verify
        falsity. Marking a genuinely-provable goal falsified would permanently
        suppress the only path to the root, so the certificate gate is
        non-negotiable. Suppresses all further proving-oriented work on the node
        via ``work_frontier``; the flag is durable across checkpoint/graph
        round-trips and the status-reopen machinery.
        """

        certificate_hash = str(certificate_hash or "").strip()
        if not certificate_hash:
            # A falsified flag can only exist bound to certificate evidence.
            return False
        node = self.nodes.get(str(node_id or "").strip())
        if node is None or getattr(node, "kind", "") != "child_goal":
            return False
        if dossier is None:
            # A hash-shaped token is not authority. Every caller must supply
            # the live dossier so exact statement/environment linkage can be
            # verified before even transient in-process suppression.
            return False
        if not self._falsified_linkage_ok(
            node,
            certificate_hash,
            self._authoritative_falsification_certificates(dossier),
        ):
            # Structural enforcement: when the caller supplies the dossier,
            # the hash must name an authoritative ledger refutation of this
            # exact statement. (Flags minted without a dossier are reconciled
            # away at the next sync against a ledger lacking the certificate.)
            return False
        if node.falsified:
            return False
        node.falsified = True
        node.falsification_reason = str(reason or "")[:240]
        node.falsification_certificate_hash = certificate_hash[:128]
        node.falsification_advisory_candidate_hash = ""
        invalidated_groups: List[Dict[str, str]] = []
        for parent_id, assembly_id in self.parent_groups_for_child(node.node_id):
            parent = self.nodes.get(parent_id)
            if parent is None:
                continue
            for group in parent.assembly_attempt_groups:
                if group.assembly_id != assembly_id or group.status not in {
                    "open",
                    "failed",
                }:
                    continue
                previous_status = group.status
                group.status = "obsolete"
                invalidated_groups.append(
                    {
                        "parent_node_id": parent_id,
                        "assembly_id": assembly_id,
                        "previous_status": previous_status,
                        "certificate_hash": certificate_hash[:128],
                    }
                )
                parent.blocker = "assembly route invalidated by falsified child"
                parent.priority = self._priority(parent)
                self.record_transition(
                    node_id=parent.node_id,
                    source="falsification",
                    error_type="assembly_route_invalidated_by_falsified_child",
                    action=parent.action,
                    blocker=parent.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={
                        "child_node_id": node.node_id,
                        "assembly_id": assembly_id,
                        "certificate_hash": certificate_hash[:128],
                        "previous_status": previous_status,
                    },
                )
        node.falsification_retired_assembly_routes = [
            dict(item) for item in invalidated_groups
        ]
        self.record_transition(
            node_id=node.node_id,
            source="falsification",
            error_type="child_goal_lean_falsified",
            action="falsify",
            blocker=str(reason or "")[:120],
            phase=phase,
            turn_index=turn_index,
            payload={"invalidated_assembly_groups": invalidated_groups},
        )
        self._refresh_priorities_for_neighbors(node.node_id)
        return True

    def record_transition(
        self,
        *,
        node_id: str,
        source: str,
        error_type: str,
        action: str,
        blocker: str = "",
        phase: str = "",
        turn_index: int = 0,
        payload: Optional[Dict[str, Any]] = None,
    ) -> None:
        node = self.nodes.get(str(node_id or ""))
        if node is None:
            return
        error = str(error_type or "").strip()
        transition = f"{error}->{action}" if error else str(action or "").strip()
        if transition and transition not in node.failure_transitions:
            node.failure_transitions.append(transition)
            del node.failure_transitions[:-12]
        record_payload = _proof_state_prompt_safe_value(dict(payload or {}))
        transition_record = {
            "node_id": _proof_state_prompt_safe_text(node.node_id, limit=240),
            "source": _proof_state_prompt_safe_text(source or "unknown", limit=240),
            "error_type": _proof_state_prompt_safe_text(error, limit=240),
            "action": _proof_state_prompt_safe_text(action or node.action or "", limit=240),
            "blocker": _proof_state_prompt_safe_text(
                blocker or node.blocker or "",
                limit=1000,
            ),
            "phase": _proof_state_prompt_safe_text(phase or "", limit=240),
            "turn_index": int(turn_index or 0),
            "payload": record_payload,
        }
        transition_id = text_hash(
            json.dumps(transition_record, sort_keys=True, default=str)
        )
        if any(item.transition_id == transition_id for item in node.typed_transitions):
            return
        typed = ProofStateTransition(
            transition_id=transition_id,
            node_id=node.node_id,
            source=transition_record["source"],
            error_type=transition_record["error_type"],
            action=transition_record["action"],
            blocker=transition_record["blocker"],
            phase=transition_record["phase"],
            turn_index=transition_record["turn_index"],
            payload=record_payload,
        )
        node.typed_transitions.append(typed)
        self._trim_typed_transitions(node)

    @staticmethod
    def _trim_typed_transitions(node: ProofStateNode) -> None:
        """Bound ordinary transitions without dropping control-flow markers."""

        transitions = list(node.typed_transitions or [])
        if len(transitions) <= _TYPED_TRANSITION_RING:
            return
        keep_indices = set(
            range(len(transitions) - _TYPED_TRANSITION_RING, len(transitions))
        )
        for index, transition in enumerate(transitions):
            error_type = str(getattr(transition, "error_type", "") or "")
            source = str(getattr(transition, "source", "") or "")
            if (
                error_type in _TYPED_TRANSITION_POLICY_MARKERS
                or source in _TYPED_TRANSITION_POLICY_SOURCES
            ):
                keep_indices.add(index)
        node.typed_transitions = [
            transition
            for index, transition in enumerate(transitions)
            if index in keep_indices
        ]

    def _residual_targets_are_equivalent(self, left: str, right: str) -> bool:
        left_text = str(left or "")
        right_text = str(right or "")
        if left_text == right_text:
            return True
        return canonicalize_lean_statement_for_identity(
            left_text
        ) == canonicalize_lean_statement_for_identity(right_text)

    def _lemma_dag_live_child_ids(self, task: ProofStateNode) -> List[str]:
        out: List[str] = []
        for child_id in task.child_node_ids or ():
            child = self.nodes.get(str(child_id or ""))
            if child is None:
                continue
            if child.kind != "child_goal" or child.status == "obsolete":
                continue
            out.append(child.node_id)
        return out

    def _lemma_dag_child_progress(
        self,
        task: ProofStateNode,
    ) -> Tuple[List[str], List[str], List[str]]:
        live_children = self._lemma_dag_live_child_ids(task)
        proved_children = [
            child_id
            for child_id in live_children
            if self.nodes.get(child_id) is not None
            and self.nodes[child_id].status == "proved"
        ]
        unproved_children = [
            child_id
            for child_id in live_children
            if self.nodes.get(child_id) is not None
            and self.nodes[child_id].status != "proved"
        ]
        return live_children, proved_children, unproved_children

    def _reconcile_unverified_lemma_dag_parent_for_child(
        self,
        child_node_id: str,
        *,
        source: str,
        phase: str = "",
        turn_index: int = 0,
    ) -> List[str]:
        child_id = str(child_node_id or "").strip()
        child = self.nodes.get(child_id)
        if child is None or child.status != "proved":
            return []

        parent_ids: Set[str] = set()
        if child.parent_node_id:
            parent_ids.add(child.parent_node_id)
        for candidate in self.nodes.values():
            if child_id in (candidate.child_node_ids or ()):
                parent_ids.add(candidate.node_id)

        reconciled: List[str] = []
        for parent_id in sorted(parent_ids):
            task = self.nodes.get(parent_id)
            if task is None or task.kind != "decomposition_task":
                continue
            recoverable_blocked = task.status == "blocked" and task.action in {
                "llm_lemma_dag_spawned_unverified",
                "llm_lemma_dag_spawned_partial_verified",
                "assemble_from_children",
            }
            prior_all_rejected_batch = any(
                transition.error_type
                == "llm_lemma_dag_decomposition_all_candidates_rejected"
                for transition in task.typed_transitions
            )
            recoverable_retry = (
                task.status == "open"
                and (
                    task.action == "lemma_dag_decomposition"
                    or (
                        task.action == "assemble_from_children"
                        and prior_all_rejected_batch
                    )
                )
                and child_id in (task.child_node_ids or ())
            )
            if not (recoverable_blocked or recoverable_retry):
                continue
            live_children, proved_children, unproved_children = (
                self._lemma_dag_child_progress(task)
            )
            if not proved_children:
                continue
            previous_status = task.status
            previous_action = task.action
            if unproved_children:
                task.status = "blocked"
                task.action = "llm_lemma_dag_spawned_partial_verified"
                task.blocker = (
                    "waiting on LLM lemma-DAG child helper verification "
                    f"({len(proved_children)}/{len(live_children)} proved; "
                    f"{len(unproved_children)} unverified)"
                )
                task.priority = self._priority(task)
                error_type = "llm_lemma_dag_decomposition_partial_verified"
            else:
                task.status = "proved"
                task.action = "llm_lemma_dag_spawned"
                task.blocker = (
                    "closed after all LLM lemma-DAG child helpers verified "
                    f"({len(proved_children)}/{len(live_children)} proved)"
                )
                task.priority = 0.0
                self._clear_terminal_node_verifier_work(task)
                error_type = "llm_lemma_dag_decomposition_recovered"
            self.record_transition(
                node_id=task.node_id,
                source=str(source or "proof_state"),
                error_type=error_type,
                action=task.action,
                blocker=task.blocker,
                phase=phase,
                turn_index=turn_index,
                payload={
                    "previous_status": previous_status,
                    "previous_action": previous_action,
                    "child_node_id": child_id,
                    "proved_child_node_ids": list(proved_children),
                    "unproved_child_node_ids": list(unproved_children),
                },
            )
            self._refresh_priorities_for_neighbors(task.node_id)
            if not unproved_children:
                reconciled.append(task.node_id)
        return reconciled

    def positive_close_blocked_by_falsification(
        self,
        node: ProofStateNode,
        *,
        source: str,
        phase: str = "",
        turn_index: int = 0,
        error_type: str = "positive_close_skipped_falsified",
        helper_name: str = "",
    ) -> bool:
        """Reject stale positive completions after authoritative refutation."""

        if not node.falsified:
            return False
        self.record_transition(
            node_id=node.node_id,
            source=str(source or "proof_state"),
            error_type=str(error_type or "positive_close_skipped_falsified"),
            action=node.action,
            blocker=(
                "authoritative falsification already terminalized this child goal"
            ),
            phase=phase,
            turn_index=turn_index,
            payload={
                "helper_name": str(helper_name or ""),
                "certificate_hash": str(
                    node.falsification_certificate_hash or ""
                ),
            },
        )
        return True

    def record_tactic_result(
        self,
        *,
        node_id: str,
        ok: bool,
        attempt_count: int,
        exit_reason: str,
        helper_name: str = "",
        terminal_context_key: str = "",
        terminal_for_context: bool = False,
    ) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        if ok and self.positive_close_blocked_by_falsification(
            node,
            source="tactic",
            helper_name=helper_name,
        ):
            return
        # E6 fix (adversarial review 2026-05-09): obsolete is a sticky
        # terminal status. Re-proving an obsolete node would cancel
        # its assembly groups again and resurrect orphaned subtrees.
        # Refuse the close.
        if node.status == "obsolete":
            return
        attempts = max(0, int(attempt_count or 0))
        node.tactic_attempts += attempts
        node.close_attempts += attempts
        node.blocker = str(exit_reason or "")
        if ok:
            node.status = "proved"
            node.action = "available_for_assembly"
            node.proved_helper_name = str(helper_name or "")
            node.successful_family = "tactic"
            node.priority = 0.0
            self._clear_terminal_node_verifier_work(node)
            # E6 (2026-05-09): tactic-close cannot use any of node's
            # assembly groups, so all open/retryable sibling groups are
            # obsolete.
            self._cancel_obsolete_or_siblings(node.node_id)
            self._refresh_priorities_for_neighbors(node.node_id)
            self._reconcile_unverified_lemma_dag_parent_for_child(
                node.node_id,
                source="tactic",
            )
        else:
            node.failed_attempts += 1
            context_key = str(terminal_context_key or "").strip()
            if (
                terminal_for_context
                and context_key
                and context_key not in node.tactic_terminal_context_keys
            ):
                node.tactic_terminal_context_keys.append(context_key)
                node.tactic_terminal_context_keys = node.tactic_terminal_context_keys[-16:]
            node.action = (
                "assemble_from_children" if node.child_node_ids else "needs_llm_or_split"
            )
            if exit_reason:
                self.record_transition(
                    node_id=node.node_id,
                    source="tactic",
                    error_type="tactic_failed",
                    action=node.action,
                    blocker=str(exit_reason),
                    payload={
                        "exit_reason": str(exit_reason),
                        "attempt_count": attempts,
                        "terminal_context_key": context_key,
                        "terminal_for_context": bool(terminal_for_context),
                    },
                )
            node.priority = self._priority(node)

    def record_assembly_result(
        self,
        *,
        node_id: str,
        ok: bool,
        attempt_count: int,
        exit_reason: str,
        helper_name: str = "",
    ) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        if ok and self.positive_close_blocked_by_falsification(
            node,
            source="assembly",
            helper_name=helper_name,
        ):
            return
        # E6 fix: obsolete nodes are sticky terminal — see
        # ``record_tactic_result`` for the rationale.
        if node.status == "obsolete":
            return
        attempts = max(0, int(attempt_count or 0))
        node.close_attempts += attempts
        node.assembly_attempts += attempts
        node.blocker = str(exit_reason or "")
        if ok:
            node.status = "proved"
            node.action = "available_for_assembly"
            node.proved_helper_name = str(helper_name or "")
            node.successful_family = "assembler"
            node.priority = 0.0
            self._clear_terminal_node_verifier_work(node)
            # E6 (2026-05-09): the caller mutated exactly one group to
            # status="proved" before this method ran. That group is
            # the winner; sibling groups (still "open") are obsolete.
            winning_assembly_id = ""
            for group in node.assembly_attempt_groups:
                if group.status == "proved":
                    winning_assembly_id = group.assembly_id
                    break
            self._cancel_obsolete_or_siblings(
                node.node_id, winning_assembly_id=winning_assembly_id
            )
            self._refresh_priorities_for_neighbors(node.node_id)
            self._reconcile_unverified_lemma_dag_parent_for_child(
                node.node_id,
                source="assembler",
            )
        else:
            node.failed_attempts += 1
            node.action = (
                "assemble_from_children" if node.child_node_ids else "needs_llm_or_split"
            )
            if exit_reason:
                self.record_transition(
                    node_id=node.node_id,
                    source="assembler",
                    error_type="assembly_failed",
                    action=node.action,
                    blocker=str(exit_reason),
                    payload={"exit_reason": str(exit_reason), "attempt_count": attempts},
                )
            node.priority = self._priority(node)

    def record_retrieved_facts(
        self,
        node_id: str,
        rendered: str,
        *,
        decl_names: Sequence[str] = (),
        hit_count: Optional[int] = None,
        retrieval_signature: str = "",
        decl_execution_policy_version: str = (
            PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
        ),
    ) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        old_signature = str(node.retrieval_signature or "").strip()
        new_signature = str(retrieval_signature or "").strip()
        if new_signature and old_signature != new_signature:
            # A new RETRIEVAL signature refreshes the retrieved fact set, but must
            # NOT wipe the PERMANENTLY-failed decl set. A child node's goal
            # statement never changes (a refinement makes a new node) and decl
            # applicability is determined solely by that goal statement, so a decl
            # that already permanently failed to apply here will fail again.
            # Clearing decl_application_tried_decl_names re-marked every such decl
            # "pending" after a handoff / session-reset re-retrieval (a new
            # retrieval signature for the SAME decls), replaying an identical,
            # multi-hundred-second decl_probe on the same (often unprovable) goal.
            # The transient retry_keys / decl-content signature still refresh so
            # transient failures can be retried when the context genuinely changes.
            node.retrieved_decl_names = []
            node.retrieved_decl_provenance = {}
            node.retrieved_decl_signatures = {}
            node.retrieved_facts = []
            node.retrieval_hit_count = 0
            node.decl_application_retry_keys = []
            node.decl_application_signature = ""
        node.retrieval_attempted = True
        node.retrieved_decl_execution_policy_version = str(
            decl_execution_policy_version or ""
        ).strip()
        if new_signature:
            node.retrieval_signature = new_signature
        node.retrieval_error = ""
        node.retrieval_error_signature = ""
        node.retrieval_error_transient = False
        node.retrieval_error_attempt_count = 0
        node.retrieval_retry_after_epoch_s = 0.0
        seen = set(node.retrieved_decl_names)
        new_decl_count = 0
        for name in decl_names:
            decl = str(name or "").strip()
            if not decl:
                continue
            node.retrieved_decl_provenance[decl] = str(
                decl_execution_policy_version or ""
            ).strip()
            node.retrieved_decl_signatures[decl] = new_signature
            if decl in seen:
                node.graph_retrieved_decl_quarantine_names = [
                    name
                    for name in node.graph_retrieved_decl_quarantine_names
                    if name != decl
                ]
                continue
            seen.add(decl)
            node.retrieved_decl_names.append(decl)
            node.graph_retrieved_decl_quarantine_names = [
                name
                for name in node.graph_retrieved_decl_quarantine_names
                if name != decl
            ]
            new_decl_count += 1
        del node.retrieved_decl_names[:-12]
        retained_decls = set(node.retrieved_decl_names)
        node.retrieved_decl_provenance = {
            name: version
            for name, version in node.retrieved_decl_provenance.items()
            if name in retained_decls
        }
        node.retrieved_decl_signatures = {
            name: signature
            for name, signature in node.retrieved_decl_signatures.items()
            if name in retained_decls
        }
        if hit_count is None:
            counted_hits = new_decl_count
        else:
            counted_hits = max(new_decl_count, max(0, int(hit_count or 0)))
        if old_signature and new_signature and old_signature == new_signature:
            node.retrieval_hit_count += new_decl_count
        else:
            node.retrieval_hit_count += counted_hits
        node.priority = self._priority(node)
        text = str(rendered or "").strip()
        if not text or text == "No matches.":
            return
        node.retrieved_facts.append(text[:1000])
        del node.retrieved_facts[:-3]

    def _retain_current_page_retrieved_decls(self, node: ProofStateNode) -> None:
        """Keep only decls stamped for the current page; quarantine the rest."""

        page_signature = str(node.retrieval_signature or "").strip()
        policy_by_name = dict(node.retrieved_decl_provenance or {})
        signature_by_name = dict(node.retrieved_decl_signatures or {})
        keep: List[str] = []
        dropped: List[str] = []
        seen: Set[str] = set()
        for raw_name in list(node.retrieved_decl_names or []):
            name = str(raw_name or "").strip()
            if not name or name in seen:
                continue
            seen.add(name)
            name_policy = str(policy_by_name.get(name) or "").strip()
            name_signature = str(signature_by_name.get(name) or "").strip()
            if (
                page_signature
                and name_policy == PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                and name_signature == page_signature
            ):
                keep.append(name)
            else:
                dropped.append(name)
        if not dropped:
            return
        node.retrieved_decl_names = keep
        node.retrieved_decl_provenance = {
            name: policy
            for name, policy in policy_by_name.items()
            if name in keep
        }
        node.retrieved_decl_signatures = {
            name: item_signature
            for name, item_signature in signature_by_name.items()
            if name in keep
        }
        quarantine = [
            str(item or "").strip()
            for item in list(node.graph_retrieved_decl_quarantine_names or [])
            if str(item or "").strip()
        ]
        quarantine.extend(dropped)
        node.graph_retrieved_decl_quarantine_names = list(
            dict.fromkeys(quarantine)
        )[-48:]

    def record_retrieval_failure(
        self,
        node_id: str,
        error: str,
        *,
        retrieval_signature: str = "",
        transient: bool = False,
    ) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        # A failed backend call is still a completed retrieval attempt.  Keep
        # the base frontier closed while the signature-specific retry policy
        # below decides whether and when to reopen it.
        node.retrieval_attempted = True
        signature = str(retrieval_signature or "").strip()
        same_failure = bool(signature and node.retrieval_error_signature == signature)
        node.retrieval_error_attempt_count = (
            int(node.retrieval_error_attempt_count or 0) + 1
            if same_failure
            else 1
        )
        node.retrieval_error = str(error or "").strip()[:500]
        node.retrieval_error_signature = signature
        node.retrieval_error_transient = bool(transient)
        if node.retrieval_error_transient:
            error_name = node.retrieval_error.split(":", 1)[0]
            base_delay = (
                1.0 if error_name == "RetrievalWorkerCapacityError" else 5.0
            )
            exponent = min(6, max(0, node.retrieval_error_attempt_count - 1))
            node.retrieval_retry_after_epoch_s = time.time() + min(
                300.0,
                base_delay * (2**exponent),
            )
        else:
            node.retrieval_retry_after_epoch_s = 0.0
            page_signature = str(node.retrieval_signature or "").strip()
            if signature and signature == page_signature:
                # A matching terminal error must not freeze a mixed page, but
                # retrying the same invalid query forever is also forbidden.
                # Drop only decls that are not current-page executable; keep
                # already-stamped current decls so proving is not reduced.
                self._retain_current_page_retrieved_decls(node)
                node.retrieved_decl_execution_policy_version = (
                    PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                )

    def record_decl_application_result(
        self,
        *,
        node_id: str,
        ok: bool,
        attempt_count: int,
        exit_reason: str,
        helper_name: str = "",
        decl_application_signature: str = "",
    ) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        if ok and self.positive_close_blocked_by_falsification(
            node,
            source="decl_application",
            helper_name=helper_name,
        ):
            return
        # E6 fix: obsolete nodes are sticky terminal.
        if node.status == "obsolete":
            return
        if str(decl_application_signature or "").strip():
            node.decl_application_signature = str(decl_application_signature or "").strip()
        attempts = max(0, int(attempt_count or 0))
        node.decl_application_attempts += attempts
        node.close_attempts += attempts
        if exit_reason:
            node.blocker = str(exit_reason)
        if ok:
            node.status = "proved"
            node.action = "available_for_assembly"
            node.proved_helper_name = str(helper_name or "")
            node.successful_family = "decl_application"
            node.priority = 0.0
            self._clear_terminal_node_verifier_work(node)
            # E6: decl-application closed the node directly; all
            # assembly groups are obsolete.
            self._cancel_obsolete_or_siblings(node.node_id)
            self._refresh_priorities_for_neighbors(node.node_id)
            self._reconcile_unverified_lemma_dag_parent_for_child(
                node.node_id,
                source="decl_application",
            )
        elif exit_reason:
            node.failed_attempts += 1
            node.action = (
                "assemble_from_children" if node.child_node_ids else node.action
            )
            self.record_transition(
                node_id=node.node_id,
                source="decl_application",
                error_type="decl_application_failed",
                action=node.action,
                blocker=str(exit_reason),
                payload={
                    "exit_reason": str(exit_reason),
                    "attempt_count": attempts,
                    "decl_application_signature": str(decl_application_signature or ""),
                },
            )
            node.priority = self._priority(node)

    def record_cache_hit(self, *, node_id: str, helper_name: str) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        if self.positive_close_blocked_by_falsification(
            node,
            source="persistent_cache",
            helper_name=helper_name,
        ):
            return
        # E6 fix: obsolete nodes are sticky terminal.
        if node.status == "obsolete":
            return
        node.cache_hits += 1
        node.status = "proved"
        node.action = "available_for_assembly"
        node.proved_helper_name = str(helper_name or "")
        node.successful_family = "persistent_cache"
        node.priority = 0.0
        self._clear_terminal_node_verifier_work(node)
        # E6: cache hit closed the node directly; assembly groups are
        # obsolete.
        self._cancel_obsolete_or_siblings(node.node_id)
        self._refresh_priorities_for_neighbors(node.node_id)
        self._reconcile_unverified_lemma_dag_parent_for_child(
            node.node_id,
            source="persistent_cache",
        )

    def record_tactic_pattern_cache_metrics(
        self,
        metadata: Optional[Dict[str, Any]],
    ) -> None:
        if not isinstance(metadata, dict) or not bool(metadata.get("enabled")):
            return
        mapping = {
            "lookups": "tactic_pattern_cache_lookups",
            "exact_success_hits": "tactic_pattern_cache_exact_success_hits",
            "shape_success_hits": "tactic_pattern_cache_shape_success_hits",
            "failed_filtered": "tactic_pattern_cache_failed_filtered",
            "all_candidates_pruned": "tactic_pattern_cache_all_candidates_pruned",
            "cap_preserved_misses": "tactic_pattern_cache_cap_preserved_misses",
            "failures_recorded": "tactic_pattern_cache_failures_recorded",
            "failures_not_cached": "tactic_pattern_cache_failures_not_cached",
            "successes_recorded": "tactic_pattern_cache_successes_recorded",
            "shape_successes_recorded": (
                "tactic_pattern_cache_shape_successes_recorded"
            ),
            "successes_deferred": "tactic_pattern_cache_successes_deferred",
            "acceptance_vetoes": "tactic_pattern_cache_acceptance_vetoes",
            "suppressed_filtered": "tactic_pattern_cache_suppressed_filtered",
        }
        for key, attr in mapping.items():
            try:
                amount = max(0, int(metadata.get(key, 0) or 0))
            except Exception:
                amount = 0
            if amount <= 0:
                continue
            setattr(self, attr, int(getattr(self, attr, 0) or 0) + amount)

    def record_verified_helper_matches(
        self,
        *,
        dossier: ProofDossier,
        helper_names: Sequence[str],
        source: str,
        phase: str,
        turn_index: int,
    ) -> List[Dict[str, Any]]:
        """Mark open child nodes proved when newly verified helpers match them.

        Helper salvage and lemma-DAG verification update the dossier first.
        This method reconnects those verified declarations to the executable
        proof-state graph so deterministic assembly can consume them in the
        same controller turn.
        """

        if dossier is None:
            return []
        helper_records: List[Tuple[str, str, str]] = []
        seen_helpers: Set[str] = set()
        for raw_name in helper_names:
            helper_name = str(raw_name or "").strip()
            if not helper_name or helper_name in seen_helpers:
                continue
            seen_helpers.add(helper_name)
            helper_record = getattr(dossier, "verified_helpers", {}).get(helper_name)
            helper_source = str(getattr(helper_record, "source", "") or "")
            helper_statement = helper_decl_statement(helper_source)
            if not helper_statement:
                continue
            helper_records.append(
                (
                    helper_name,
                    helper_statement,
                    canonicalize_lean_statement_for_identity(helper_statement),
                )
            )
        if not helper_records:
            return []

        matched: List[Dict[str, Any]] = []
        for node in self.nodes.values():
            if node.node_id == self.root_node_id:
                continue
            if node.kind != "child_goal" or node.status == "proved":
                continue
            if node.falsified:
                continue
            # E6 fix: obsolete is sticky terminal — a verified helper
            # match for an already-cancelled node would resurrect it
            # into orphaned ghost work without informing scheduling.
            if node.status == "obsolete":
                continue
            target_key = canonicalize_lean_statement_for_identity(node.target)
            if not target_key:
                continue
            for helper_name, helper_statement, helper_key in helper_records:
                if not self._verified_helper_match_allowed_for_node(node, helper_name):
                    continue
                if helper_key != target_key:
                    continue
                node.status = "proved"
                node.action = "available_for_assembly"
                node.proved_helper_name = helper_name
                node.successful_family = str(source or "verified_helper_match")
                node.blocker = (
                    "verified helper matched proof-state child target: "
                    f"{helper_name}"
                )
                node.priority = 0.0
                self._clear_terminal_node_verifier_work(node)
                # E6: helper match closed the node directly; assembly
                # groups are obsolete.
                self._cancel_obsolete_or_siblings(node.node_id)
                self._refresh_priorities_for_neighbors(node.node_id)
                self._reconcile_unverified_lemma_dag_parent_for_child(
                    node.node_id,
                    source=str(source or "verified_helper_match"),
                    phase=phase,
                    turn_index=turn_index,
                )
                self.record_transition(
                    node_id=node.node_id,
                    source=str(source or "verified_helper_match"),
                    error_type="verified_helper_matched_child",
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={
                        "helper_name": helper_name,
                        "helper_statement": helper_statement,
                    },
                )
                matched.append(
                    {
                        "phase": "proof_state_verified_helper_match",
                        "turn_in_phase": int(turn_index or 0),
                        "node_id": node.node_id,
                        "target": node.target,
                        "helper_name": helper_name,
                        "source": str(source or "verified_helper_match"),
                        "verdict": "child_marked_proved",
                    }
                )
                break
        return matched

    def _statement_identity_helper_match_allowed(self, node: ProofStateNode) -> bool:
        """Allow global statement matches only for context-free child goals."""

        if node.local_context:
            return False
        if node.local_argument_terms:
            return False
        goal = getattr(node, "goal", None)
        if goal is not None and getattr(goal, "local_hypotheses", None):
            return False
        return True

    @staticmethod
    def _node_specific_helper_names(node: ProofStateNode) -> Set[str]:
        names: Set[str] = set()
        proved_name = str(getattr(node, "proved_helper_name", "") or "").strip()
        if proved_name:
            names.add(proved_name)
        node_id = str(getattr(node, "node_id", "") or "").strip()
        if node_id:
            names.add(f"helper_{node_id}")
        return names

    def _verified_helper_match_allowed_for_node(
        self,
        node: ProofStateNode,
        helper_name: str,
    ) -> bool:
        """Allow broad matches only for context-free nodes, exact node matches otherwise."""

        if self._statement_identity_helper_match_allowed(node):
            return True
        name = str(helper_name or "").strip()
        return bool(name and name in self._node_specific_helper_names(node))

    def record_budget_skip(self, *, node_id: str, reason: str) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        node.budget_skips += 1
        node.blocker = str(reason or "budget_disabled")
        self.record_transition(
            node_id=node.node_id,
            source="budget",
            error_type="budget_skip",
            action=node.action,
            blocker=node.blocker,
            payload={"reason": node.blocker},
        )
        node.priority = self._priority(node)

    def reopen_node(
        self,
        node_id: str,
        *,
        reason: str = "explicit_replan",
        phase: str = "",
        turn_index: int = 0,
    ) -> bool:
        """Explicitly reopen a non-proved node.

        Failed nodes never reopen implicitly through graph frontier queries;
        this method is the intentional replan/reset primitive.
        """

        node = self.nodes.get(str(node_id or "").strip())
        if node is None or node.status == "proved":
            return False
        # E6 fix (adversarial review 2026-05-09): refuse to reopen
        # obsolete nodes. Their assembly groups are also obsolete; a
        # naive reopen would set status="open" but leave every group
        # locked, producing a "looks alive in frontier, makes zero
        # progress" zombie. Either someone needs to explicitly reset
        # the groups too OR the reopen is unintended; the safe default
        # is to refuse. ``rejected`` / ``failed`` reopens still work.
        if node.status == "obsolete":
            return False
        node.status = "open"
        node.blocker = str(reason or "explicit_replan")
        node.action = (
            "assemble_from_children"
            if node.child_node_ids or node.assembly_attempt_groups
            else node.action
        )
        self.record_transition(
            node_id=node.node_id,
            source="proof_state",
            error_type="explicit_reopen",
            action=node.action,
            blocker=node.blocker,
            phase=phase,
            turn_index=turn_index,
            payload={"reason": node.blocker},
        )
        node.priority = self._priority(node)
        return True

    def record_construction_collapse(
        self,
        *,
        phase: str,
        turn_index: int,
        reason: str,
        proof_preview: str = "",
        response_preview: str = "",
    ) -> Dict[str, Any]:
        root = self.nodes[self.root_node_id]
        root.failed_attempts += 1
        root.status = "open"
        root.action = "force_graph_decomposition"
        root.blocker = str(reason or "known-answer/no-construction collapse detected")
        self.record_transition(
            node_id=self.root_node_id,
            source="controller_policy",
            error_type="known_answer_no_construction_collapse",
            action=root.action,
            blocker=root.blocker,
            phase=phase,
            turn_index=turn_index,
            payload={
                "proof_preview": _compact_search_text(proof_preview, limit=400),
                "response_preview": _compact_search_text(response_preview, limit=400),
            },
        )
        root.priority = self._priority(root)
        task_id = self._ensure_decomposition_task(
            source=f"{phase}:{turn_index}:construction_collapse",
            blocker=root.blocker,
        )
        structural_nodes = self.spawn_structural_decomposition(
            node_id=self.root_node_id,
            source=f"{phase}:{turn_index}:construction_collapse",
            max_goals=4,
        )
        if structural_nodes:
            root.action = "assemble_from_children"
            root.blocker = (
                "structural decomposition available with "
                f"{len(structural_nodes)} child goal(s)"
            )
            root.priority = self._priority(root)
            task = self.nodes.get(task_id)
            if task is not None:
                task.status = "proved"
                task.action = "structural_decomposition_spawned"
                task.blocker = (
                    "closed after deterministic structural decomposition "
                    f"spawned {len(structural_nodes)} child goal(s)"
                )
                task.priority = 0.0
                self._clear_terminal_node_verifier_work(task)
                self._refresh_priorities_for_neighbors(task.node_id)
        return {
            "root_action": self.nodes[self.root_node_id].action,
            "root_blocker": root.blocker,
            "decomposition_node": task_id,
            "structural_child_nodes": structural_nodes,
            "frontier": [node.node_id for node in self.frontier(max_nodes=6)],
        }

    def ensure_decomposition_task_open(
        self,
        *,
        source: str,
        blocker: str = "LLM emitted sorry-stub helpers as decomposition request",
        reuse_closed_structural: bool = False,
        reuse_closed_lemma_dag: bool = True,
    ) -> str:
        """Public, idempotent decomposition-task opener.

        D2 fix (2026-05-09): the lemma-DAG path
        (``_try_proof_state_lemma_dag_helpers``) early-returns when
        ``has_open_decomposition_task()`` is False, which silently
        drops sorry-stub helpers the LLM emits in response to the
        Phase 1 give-up gate's decomposition nudge. The previous
        only-trigger was inside ``record_construction_collapse`` —
        too narrow.

        This wrapper is the public entry point for Phase 2's helper
        decomposition pipeline: any caller that detects the LLM has
        explicitly requested decomposition (sorry-stub helpers, or
        any cluster of the give-up gate firing) can call this to
        ensure the lemma-DAG path will accept the helpers and
        materialize them as ``child_goal`` nodes that
        ``RecursiveHelperProverAction`` can then attack.

        Idempotent: returns the existing open task id if one exists.
        Returns the new task id otherwise. Closed structural tasks do
        not satisfy this public "open" contract unless a caller opts
        into legacy reuse explicitly. Closed LLM lemma-DAG tasks are
        reopened by default so repeated sorry-stub turns aggregate under
        the same decomposition task instead of proliferating root tasks.
        """

        return self._ensure_decomposition_task(
            source=source,
            blocker=blocker,
            reuse_closed_structural=reuse_closed_structural,
            reuse_closed_lemma_dag=reuse_closed_lemma_dag,
        )

    def _ensure_decomposition_task(
        self,
        *,
        source: str,
        blocker: str,
        reuse_closed_structural: bool = True,
        reuse_closed_lemma_dag: bool = False,
    ) -> str:
        # B9 fix (2026-05-11): refuse to open or surface ANY decomposition
        # task when the root is already in a terminal status. Late callers
        # (sorry-stub detector at conversation_turn.py, construction-collapse
        # handler at mini_prover.py, helper-only salvage cascade) may still
        # invoke this entry after ``mark_root_solved`` ran, or after the
        # root has been marked obsolete/rejected/failed by an earlier
        # cascade in the same turn. Without this guard, the function below
        # force-appends a fresh ``decomposition_task`` via
        # ``root.child_node_ids.append`` (line ~2727), BYPASSING the
        # ``_attach_child_to_parent`` closed-parent guard at line ~4147.
        # The phantom task then surfaces in ``decomposition_frontier`` and
        # ``work_frontier``, causing downstream actions to dispatch helper-
        # verification work against a problem that's already proved (or
        # against a root the search has otherwise abandoned).
        #
        # Returning ``""`` matches the contract used elsewhere: callers
        # treat empty as "no task open" and short-circuit their cascades.
        root = self.nodes.get(self.root_node_id)
        if root is not None and root.status in (
            "proved",
            "obsolete",
            "rejected",
            "failed",
        ):
            return ""
        for node in self.nodes.values():
            if node.kind != "decomposition_task":
                continue
            if node.parent_node_id != self.root_node_id:
                continue
            if node.status != "open":
                continue
            node.blocker = str(blocker or node.blocker)
            node.priority = self._priority(node)
            return node.node_id
        for node in self.nodes.values():
            if node.kind != "decomposition_task":
                continue
            if node.parent_node_id != self.root_node_id:
                continue
            if (
                reuse_closed_structural
                and node.status == "proved"
                and node.action == "structural_decomposition_spawned"
            ):
                return node.node_id
            if (
                reuse_closed_lemma_dag
                and (
                    (
                        node.status == "proved"
                        and node.action == "llm_lemma_dag_spawned"
                    )
                    or (
                        node.status == "blocked"
                        and node.action
                        in {
                            "llm_lemma_dag_spawned_unverified",
                            "llm_lemma_dag_spawned_partial_verified",
                        }
                    )
                )
            ):
                previous_action = node.action
                previous_status = node.status
                node.status = "open"
                node.action = "plan_lemma_dag"
                node.blocker = str(blocker or node.blocker)
                node.priority = self._priority(node)
                self.record_transition(
                    node_id=node.node_id,
                    source=str(source or "proof_state"),
                    error_type="lemma_dag_decomposition_reopened",
                    action=node.action,
                    blocker=node.blocker,
                    payload={
                        "previous_action": previous_action,
                        "previous_status": previous_status,
                    },
                )
                self._refresh_priorities_for_neighbors(node.node_id)
                return node.node_id
        root = self.nodes[self.root_node_id]
        self._next_index += 1
        node_id = f"decompose_{self._next_index}"
        node = ProofStateNode(
            node_id=node_id,
            kind="decomposition_task",
            target=root.target,
            suppress_solution_placeholders=self.suppress_solution_placeholders,
            goal=root.goal,
            local_context=list(root.local_context),
            dependencies=[self.root_node_id],
            parent_node_id=self.root_node_id,
            action="plan_lemma_dag",
            blocker=str(blocker or "force durable lemma-DAG decomposition"),
            priority=98.0,
        )
        node.priority = self._priority(node)
        self.nodes[node_id] = node
        if node_id not in root.child_node_ids:
            root.child_node_ids.append(node_id)
        return node_id

    def spawn_structural_decomposition(
        self,
        *,
        node_id: str,
        source: str,
        max_goals: int = 4,
    ) -> List[str]:
        node = self.nodes.get(str(node_id or ""))
        if node is None:
            return []
        proof_stub, goals, kind = _structural_decomposition_for_target(node.target)
        if not proof_stub or not goals:
            return []
        for group in node.assembly_attempt_groups:
            if group.source.startswith(f"structural:{kind}:") and group.child_node_ids:
                return list(dict.fromkeys(group.child_node_ids))
        spawned = self.spawn_remaining_goals(
            goals[: max(0, int(max_goals or 0))],
            source=f"structural:{kind}:{source}",
            parent_node_id=node.node_id,
            parent_proof_stub=proof_stub,
            max_goals=max_goals,
        )
        if not spawned:
            return []
        node.action = "assemble_from_children"
        node.blocker = f"structural {kind} decomposition spawned {len(spawned)} child goal(s)"
        self.record_transition(
            node_id=node.node_id,
            source="structural_decomposition",
            error_type="structural_decomposition",
            action=node.action,
            blocker=node.blocker,
            payload={
                "kind": kind,
                "spawned_nodes": list(spawned),
                "goal_targets": [str(item.get("target") or "") for item in goals],
            },
        )
        node.priority = self._priority(node)
        return spawned

    def _lemma_dag_child_statement_rejection(self, target: str) -> str:
        compact = _compact_search_text(target, limit=0)
        unwrapped = _strip_balanced_outer_parens(compact)
        if unwrapped in {"False", "false"}:
            return "false_statement"
        if is_answer_unsafe_statement_text(
            compact,
            suppress_solution_placeholders=self.suppress_solution_placeholders,
        ):
            return "answer_placeholder_statement"
        return ""

    def _record_lemma_dag_child_statement_rejection(
        self,
        *,
        parent_id: str,
        helper_name: str,
        target: str,
        accepted: bool,
        source: str,
        phase: str,
        turn_index: int,
        reason: str,
    ) -> None:
        anchor = self.nodes.get(str(parent_id or "")) or self.nodes[self.root_node_id]
        blocker = f"rejected LLM lemma-DAG child statement: {reason}"
        self.lemma_dag_child_statement_rejections += 1
        self.record_transition(
            node_id=anchor.node_id,
            source="llm_lemma_dag",
            error_type="llm_lemma_dag_child_statement_rejected",
            action=anchor.action,
            blocker=blocker,
            phase=phase,
            turn_index=turn_index,
            payload={
                "helper_name": str(helper_name or "").strip(),
                "target": str(target or ""),
                "accepted": bool(accepted),
                "source": str(source or ""),
                "reason": str(reason or ""),
            },
        )
        anchor.blocker = blocker
        anchor.priority = self._priority(anchor)

    def _record_lemma_dag_child_source_rejection(
        self,
        *,
        parent_id: str,
        helper_name: str,
        target: str,
        accepted: bool,
        source: str,
        phase: str,
        turn_index: int,
        reason: str,
    ) -> None:
        anchor = self.nodes.get(str(parent_id or "")) or self.nodes[self.root_node_id]
        blocker = f"rejected LLM lemma-DAG helper source: {reason}"
        self.lemma_dag_child_source_rejections += 1
        self.record_transition(
            node_id=anchor.node_id,
            source="llm_lemma_dag",
            error_type="llm_lemma_dag_child_source_rejected",
            action=anchor.action,
            blocker=blocker,
            phase=phase,
            turn_index=turn_index,
            payload={
                "helper_name": str(helper_name or "").strip(),
                "target": str(target or ""),
                "accepted": bool(accepted),
                "source": str(source or ""),
                "reason": str(reason or ""),
            },
        )
        anchor.blocker = blocker
        anchor.priority = self._priority(anchor)

    def record_lemma_dag_source_rejection(
        self,
        *,
        helper_name: str = "",
        target: str = "",
        accepted: bool = False,
        source: str = "",
        phase: str = "",
        turn_index: int = 0,
        parent_node_id: str = "",
        reason: str = "",
    ) -> None:
        """Record a helper-source policy rejection without admitting a child.

        This is the executor-facing path for malformed helper blocks that
        cannot supply a valid theorem/lemma statement and therefore cannot use
        ``record_lemma_dag_candidate``'s child-goal admission path.
        """

        rejection = str(reason or "").strip()
        if not rejection:
            return
        requested_parent_id = str(parent_node_id or "").strip()
        requested_parent = self.nodes.get(requested_parent_id)
        parent_id = (
            requested_parent.node_id
            if requested_parent is not None
            else self.root_node_id
        )
        normalized_target = self._normalize_goal_text(target)
        if not normalized_target or normalized_target == "(target unavailable)":
            normalized_target = "(target unavailable)"
        self._record_lemma_dag_child_source_rejection(
            parent_id=parent_id,
            helper_name=helper_name,
            target=normalized_target,
            accepted=bool(accepted),
            source=source,
            phase=phase,
            turn_index=turn_index,
            reason=rejection,
        )

    def record_lemma_dag_parent_stub_spawned(
        self,
        *,
        task_id: str,
        parent_node_id: str,
        helper_name: str,
        proof_stub: str,
        spawned_node_ids: Sequence[str],
        residual_goal_count: int,
        phase: str,
        turn_index: int,
        source: str,
    ) -> None:
        """Record a Lean-validated parent proof stub from lemma-DAG output."""

        task = self.nodes.get(str(task_id or ""))
        parent = self.nodes.get(str(parent_node_id or "")) or self.nodes.get(
            self.root_node_id
        )
        anchor = task or parent
        if anchor is None:
            return
        self.lemma_dag_parent_stub_spawns += 1
        blocker = (
            "validated LLM lemma-DAG parent proof stub spawned "
            f"{len(list(spawned_node_ids or ()))}/{int(residual_goal_count or 0)} "
            "residual goal(s)"
        )
        self.record_transition(
            node_id=anchor.node_id,
            source="llm_lemma_dag",
            error_type="llm_lemma_dag_parent_stub_spawned",
            action=anchor.action,
            blocker=blocker,
            phase=phase,
            turn_index=turn_index,
            payload={
                "helper_name": str(helper_name or "").strip(),
                "parent_node_id": str(parent_node_id or "").strip(),
                "task_id": str(task_id or "").strip(),
                "source": str(source or ""),
                "proof_stub": str(proof_stub or "")[:400],
                "spawned_node_ids": list(spawned_node_ids or ()),
                "residual_goal_count": int(residual_goal_count or 0),
            },
        )
        if task is not None:
            task.blocker = blocker
            task.priority = self._priority(task)
        if parent is not None:
            parent.priority = self._priority(parent)

    def record_lemma_dag_parent_stub_rejection(
        self,
        *,
        task_id: str,
        parent_node_id: str,
        helper_name: str,
        proof_stub: str,
        phase: str,
        turn_index: int,
        source: str,
        reason: str,
    ) -> None:
        """Record a root/parent-shaped lemma-DAG proof stub that could not spawn."""

        task = self.nodes.get(str(task_id or ""))
        parent = self.nodes.get(str(parent_node_id or "")) or self.nodes.get(
            self.root_node_id
        )
        anchor = task or parent
        if anchor is None:
            return
        self.lemma_dag_parent_stub_rejections += 1
        rejection = str(reason or "parent_stub_rejected").strip()
        blocker = f"rejected LLM lemma-DAG parent proof stub: {rejection}"
        self.record_transition(
            node_id=anchor.node_id,
            source="llm_lemma_dag",
            error_type="llm_lemma_dag_parent_stub_rejected",
            action=anchor.action,
            blocker=blocker,
            phase=phase,
            turn_index=turn_index,
            payload={
                "helper_name": str(helper_name or "").strip(),
                "parent_node_id": str(parent_node_id or "").strip(),
                "task_id": str(task_id or "").strip(),
                "source": str(source or ""),
                "proof_stub": str(proof_stub or "")[:400],
                "reason": rejection,
            },
        )
        anchor.blocker = blocker
        anchor.priority = self._priority(anchor)

    def _apply_lemma_dag_task_child_progress(
        self,
        task: ProofStateNode,
        *,
        proposed_count: int,
        accepted_count: int,
        node_ids: Sequence[str],
        empty_retry: bool = False,
    ) -> bool:
        live_children, proved_children, unproved_children = (
            self._lemma_dag_child_progress(task)
        )
        if not live_children:
            return False
        proved_child_count = len(proved_children)
        verified_progress = proved_child_count > 0
        all_live_children_verified = not unproved_children
        if all_live_children_verified:
            task.status = "proved"
            task.action = "llm_lemma_dag_spawned"
            task.blocker = (
                f"closed after LLM lemma-DAG proposed {proposed_count} helper "
                f"node(s), {accepted_count} verified in this batch, "
                f"{proved_child_count}/{len(live_children)} total child node(s) verified"
            )
            error_type = (
                "llm_lemma_dag_decomposition_empty_existing_complete"
                if empty_retry
                else "llm_lemma_dag_decomposition_spawned"
            )
            self._clear_terminal_node_verifier_work(task)
        elif verified_progress:
            task.status = "blocked"
            task.action = "llm_lemma_dag_spawned_partial_verified"
            task.blocker = (
                f"waiting on {len(unproved_children)} LLM lemma-DAG child helper "
                f"node(s); {proved_child_count}/{len(live_children)} verified"
            )
            error_type = (
                "llm_lemma_dag_decomposition_empty_existing_partial_verified"
                if empty_retry
                else "llm_lemma_dag_decomposition_spawned_partial_verified"
            )
        else:
            task.status = "blocked"
            task.action = "llm_lemma_dag_spawned_unverified"
            task.blocker = (
                f"waiting on {len(unproved_children)} LLM lemma-DAG child helper "
                "node(s); no helper verified yet"
            )
            error_type = (
                "llm_lemma_dag_decomposition_empty_existing_unverified"
                if empty_retry
                else "llm_lemma_dag_decomposition_spawned_unverified"
            )
        task.priority = 0.0
        self._refresh_priorities_for_neighbors(task.node_id)
        self.record_transition(
            node_id=task.node_id,
            source="llm_lemma_dag",
            error_type=error_type,
            action=task.action,
            blocker=task.blocker,
            payload={
                "proposed_count": int(proposed_count or 0),
                "accepted_count": int(accepted_count or 0),
                "proved_child_count": int(proved_child_count),
                "unproved_child_count": len(unproved_children),
                "node_ids": list(node_ids),
                "live_child_node_ids": list(live_children),
                "unproved_child_node_ids": list(unproved_children),
                "verified_progress": verified_progress,
                "all_live_children_verified": all_live_children_verified,
                "empty_retry": bool(empty_retry),
            },
        )
        return True

    def record_lemma_dag_candidate(
        self,
        *,
        helper_name: str,
        statement: str,
        accepted: bool,
        source: str,
        phase: str,
        turn_index: int,
        parent_node_id: str = "",
        target_node_id: str = "",
        rejection: str = "",
        is_sorry_stub_body: bool = False,
    ) -> str:
        """Record an LLM-proposed lemma-DAG candidate as a graph node.

        ``is_sorry_stub_body`` (Phase 2, 2026-05-09): when True, the
        helper's body was just ``by sorry`` / ``by admit`` — i.e., the
        LLM was explicitly REQUESTING decomposition rather than
        attempting a proof. The rejection is structurally expected
        (Lean rejects every sorry under ``warning_as_error=True``), so
        the ``failed_attempts`` bump is suppressed. Without this, a
        sorry-stub helper would arrive in the graph with
        ``failed_attempts=1`` even though no real proof attempt was
        made, which would degrade the node's priority unfairly when
        downstream actions (Phase 2 RecursiveHelperProverAction,
        ChildClosureAction) try to attack it.
        """

        target = self._normalize_goal_text(statement)
        if not target or target == "(target unavailable)":
            return ""
        helper = str(helper_name or "").strip()
        requested_parent_id = str(parent_node_id or "").strip()
        parent_id = self.root_node_id
        requested_parent = self.nodes.get(requested_parent_id)
        if requested_parent_id:
            blocked_recovery_parent = (
                requested_parent is not None
                and requested_parent.kind == "decomposition_task"
                and bool(accepted)
                and requested_parent.status == "blocked"
                and requested_parent.action
                in {
                    "llm_lemma_dag_spawned_unverified",
                    "llm_lemma_dag_spawned_partial_verified",
                }
            )
            if (
                requested_parent is not None
                and requested_parent.kind == "decomposition_task"
                and (requested_parent.status == "open" or blocked_recovery_parent)
            ):
                parent_id = requested_parent.node_id
            else:
                anchor = requested_parent or self.nodes[self.root_node_id]
                blocker = "rejected stale LLM lemma-DAG candidate for non-open parent"
                self.record_transition(
                    node_id=anchor.node_id,
                    source="llm_lemma_dag",
                    error_type="llm_lemma_dag_candidate_rejected_closed_parent",
                    action=anchor.action,
                    blocker=blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={
                        "helper_name": helper,
                        "target": target,
                        "accepted": bool(accepted),
                        "requested_parent_node_id": requested_parent_id,
                        "requested_parent_status": (
                            requested_parent.status if requested_parent is not None else ""
                        ),
                        "requested_parent_action": (
                            requested_parent.action if requested_parent is not None else ""
                        ),
                        "source": str(source or ""),
                    },
                )
                anchor.blocker = blocker
                anchor.priority = self._priority(anchor)
                return ""
        source_rejection = str(rejection or "").strip()
        if not accepted and lemma_dag_rejection_is_terminal_policy(source_rejection):
            self._record_lemma_dag_child_source_rejection(
                parent_id=parent_id,
                helper_name=helper,
                target=target,
                accepted=bool(accepted),
                source=source,
                phase=phase,
                turn_index=turn_index,
                reason=source_rejection,
            )
            return ""
        dependencies = [self.root_node_id]
        if parent_id != self.root_node_id:
            dependencies.append(parent_id)
        signature = self._goal_signature(
            target,
            [],
            source_failure=(
                f"lemma_dag_verified:{source}"
                if accepted
                else f"lemma_dag_unverified:{source}"
            ),
        )
        requested_target_id = str(target_node_id or "").strip()
        requested_target = self.nodes.get(requested_target_id)
        if requested_target_id and (
            requested_target is None
            or requested_target.node_id == self.root_node_id
            or self._normalize_goal_text(requested_target.target) != target
        ):
            anchor = requested_target or self.nodes[self.root_node_id]
            self.record_transition(
                node_id=anchor.node_id,
                source="llm_lemma_dag",
                error_type="llm_lemma_dag_candidate_target_binding_rejected",
                action=anchor.action,
                blocker=(
                    "verified helper completion did not match its selected "
                    "proof-state obligation"
                ),
                phase=phase,
                turn_index=turn_index,
                payload={
                    "helper_name": helper,
                    "target": target,
                    "requested_target_node_id": requested_target_id,
                    "requested_target_statement": (
                        requested_target.target if requested_target is not None else ""
                    ),
                    "source": str(source or ""),
                },
            )
            return ""
        target_environment_hash = (
            str(requested_target.statement_environment_hash or "").strip()
            if requested_target is not None
            else self.statement_environment_hash
        )
        target_index_key = self._target_environment_index_key(
            signature.normalized_statement_hash,
            target_environment_hash,
        )
        existing = (
            requested_target.node_id
            if requested_target is not None
            else self._node_by_target.get(target_index_key)
        )
        if existing == self.root_node_id:
            root = self.nodes[self.root_node_id]
            self.record_transition(
                node_id=self.root_node_id,
                source="llm_lemma_dag",
                error_type="llm_lemma_dag_root_equivalent_rejected",
                action=root.action,
                blocker="LLM lemma-DAG candidate restated the root instead of decomposing it",
                phase=phase,
                turn_index=turn_index,
                payload={
                    "helper_name": helper,
                    "accepted": bool(accepted),
                    "source": str(source or ""),
                },
            )
            root.blocker = "LLM lemma-DAG candidate restated the root"
            root.priority = self._priority(root)
            return ""
        parent_node = self.nodes.get(parent_id)
        if parent_node is not None:
            try:
                candidate_key = canonicalize_lean_statement_for_identity(target)
                parent_key = canonicalize_lean_statement_for_identity(
                    str(getattr(parent_node, "target", "") or "")
                )
            except Exception:
                candidate_key = " ".join(str(target or "").split())
                parent_key = " ".join(
                    str(getattr(parent_node, "target", "") or "").split()
                )
            if candidate_key and parent_key and candidate_key == parent_key:
                self.record_transition(
                    node_id=parent_node.node_id,
                    source="llm_lemma_dag",
                    error_type="llm_lemma_dag_parent_equivalent_rejected",
                    action=parent_node.action,
                    blocker=(
                        "LLM lemma-DAG candidate restated the active parent "
                        "goal instead of decomposing it"
                    ),
                    phase=phase,
                    turn_index=turn_index,
                    payload={
                        "helper_name": helper,
                        "accepted": bool(accepted),
                        "source": str(source or ""),
                        "parent_node_id": parent_node.node_id,
                    },
                )
                parent_node.blocker = (
                    "LLM lemma-DAG candidate restated the active parent goal"
                )
                parent_node.priority = self._priority(parent_node)
                return ""
        statement_rejection = self._lemma_dag_child_statement_rejection(target)
        if statement_rejection:
            self._record_lemma_dag_child_statement_rejection(
                parent_id=parent_id,
                helper_name=helper,
                target=target,
                accepted=bool(accepted),
                source=source,
                phase=phase,
                turn_index=turn_index,
                reason=statement_rejection,
            )
            return ""
        if existing and existing != self.root_node_id:
            node = self.nodes[existing]
            # E6: obsolete is sticky terminal. Refuse before mutating
            # dependencies/root children so stale lemma-DAG completions
            # cannot pollute the live graph with a cancelled node.
            if node.status == "obsolete":
                self.record_transition(
                    node_id=node.node_id,
                    source="llm_lemma_dag",
                    error_type="llm_lemma_dag_helper_skipped_obsolete",
                    action=node.action,
                    blocker="node was cancelled (obsolete) before this helper landed",
                    phase=phase,
                    turn_index=turn_index,
                    payload={"helper_name": helper, "accepted": bool(accepted)},
                )
                return ""
            if node.falsified:
                self.record_transition(
                    node_id=node.node_id,
                    source="llm_lemma_dag",
                    error_type="llm_lemma_dag_helper_skipped_falsified",
                    action=node.action,
                    blocker=(
                        "authoritative falsification already terminalized this "
                        "child goal"
                    ),
                    phase=phase,
                    turn_index=turn_index,
                    payload={"helper_name": helper, "accepted": bool(accepted)},
                )
                return ""
            if parent_id != self.root_node_id:
                attached = self._attach_child_to_parent(
                    parent_node_id=parent_id,
                    child_node_id=node.node_id,
                )
                if attached:
                    self._move_primary_parent_if_rootish(
                        child_node_id=node.node_id,
                        parent_node_id=parent_id,
                    )
                    for dependency in dependencies:
                        if (
                            dependency not in node.dependencies
                            and not self._would_create_dependency_cycle(
                                dependency,
                                node.node_id,
                            )
                        ):
                            node.dependencies.append(dependency)
            elif not node.parent_node_id or node.parent_node_id == self.root_node_id:
                attached = self._attach_child_to_parent(
                    parent_node_id=self.root_node_id,
                    child_node_id=node.node_id,
                )
                if attached:
                    self._move_primary_parent_if_rootish(
                        child_node_id=node.node_id,
                        parent_node_id=self.root_node_id,
                    )
                    for dependency in dependencies:
                        if (
                            dependency not in node.dependencies
                            and not self._would_create_dependency_cycle(
                                dependency,
                                node.node_id,
                            )
                        ):
                            node.dependencies.append(dependency)
        else:
            self._next_index += 1
            node_id = f"goal_{self._next_index}"
            node = ProofStateNode(
                node_id=node_id,
                kind="child_goal",
                target=target,
                statement_environment_hash=target_environment_hash,
                suppress_solution_placeholders=self.suppress_solution_placeholders,
                goal=signature,
                local_context=[],
                dependencies=dependencies,
                parent_node_id=parent_id,
                action="prove_child_helper",
                blocker=f"proposed by LLM lemma-DAG decomposition ({source})",
                priority=84.0,
            )
            self.nodes[node_id] = node
            if existing != self.root_node_id:
                self._node_by_target[target_index_key] = node_id
            self._attach_child_to_parent(
                parent_node_id=parent_id,
                child_node_id=node_id,
            )
        if accepted:
            # E6 fix: obsolete is sticky terminal — refuse the close.
            if node.status == "obsolete":
                self.record_transition(
                    node_id=node.node_id,
                    source="llm_lemma_dag",
                    error_type="llm_lemma_dag_helper_skipped_obsolete",
                    action=node.action,
                    blocker="node was cancelled (obsolete) before this helper landed",
                    phase=phase,
                    turn_index=turn_index,
                    payload={"helper_name": helper, "accepted": True},
                )
                return ""
            node.status = "proved"
            node.action = "available_for_assembly"
            node.proved_helper_name = helper
            node.successful_family = "llm_lemma_dag"
            node.blocker = "verified LLM lemma-DAG helper"
            node.priority = 0.0
            self._clear_terminal_node_verifier_work(node)
            # E6: lemma-DAG-verified helper closed the node directly;
            # assembly groups are obsolete.
            self._cancel_obsolete_or_siblings(node.node_id)
            self._refresh_priorities_for_neighbors(node.node_id)
            self._reconcile_unverified_lemma_dag_parent_for_child(
                node.node_id,
                source="llm_lemma_dag",
                phase=phase,
                turn_index=turn_index,
            )
            transition_error = "llm_lemma_dag_helper_accepted"
        else:
            if node.status == "proved":
                transition_error = "llm_lemma_dag_helper_rejected_existing_proved"
                self.record_transition(
                    node_id=node.node_id,
                    source="llm_lemma_dag",
                    error_type=transition_error,
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={
                        "helper_name": helper,
                        "accepted": False,
                        "rejection": str(rejection or ""),
                        "source": str(source or ""),
                        "proved_helper_name": node.proved_helper_name,
                    },
                )
                return node.node_id
            node.status = "open"
            # Phase 2 fix (2026-05-09): suppress the failed_attempts bump
            # for sorry-stub bodies. The LLM's `:= by sorry` is a
            # decomposition REQUEST, not a meaningful proof attempt;
            # bumping would mis-calibrate the node's priority for
            # subsequent actions (RecursiveHelperProverAction reads this
            # to decide retry order).
            if not is_sorry_stub_body:
                node.failed_attempts += 1
            node.action = "prove_child_helper"
            node.blocker = str(rejection or "LLM lemma-DAG helper proof rejected")
            node.priority = self._priority(node)
            transition_error = "llm_lemma_dag_helper_rejected"
        self.record_transition(
            node_id=node.node_id,
            source="llm_lemma_dag",
            error_type=transition_error,
            action=node.action,
            blocker=node.blocker,
            phase=phase,
            turn_index=turn_index,
            payload={
                "helper_name": helper,
                "accepted": bool(accepted),
                "rejection": str(rejection or ""),
                "source": str(source or ""),
            },
        )
        return node.node_id

    def close_decomposition_task_from_lemma_dag(
        self,
        *,
        task_id: str,
        proposed_count: int,
        accepted_count: int,
        node_ids: Sequence[str],
    ) -> None:
        task = self.nodes.get(str(task_id or ""))
        if task is None or task.kind != "decomposition_task":
            return
        if task.status != "open":
            return
        if proposed_count <= 0:
            live_children, proved_children, _unproved_children = (
                self._lemma_dag_child_progress(task)
            )
            if accepted_count <= 0 and live_children and not proved_children:
                self.lemma_dag_decomposition_all_candidates_rejected += 1
                task.failed_attempts += 1
                task.status = "open"
                task.action = "lemma_dag_decomposition"
                task.blocker = (
                    "LLM lemma-DAG retry produced no usable helper statements; "
                    "existing unverified child helper node(s) remain open and "
                    "the decomposition task remains retryable."
                )
                task.priority = self._priority(task)
                self.record_transition(
                    node_id=task.node_id,
                    source="llm_lemma_dag",
                    error_type="llm_lemma_dag_decomposition_empty_all_unverified_retry",
                    action=task.action,
                    blocker=task.blocker,
                    payload={
                        "proposed_count": int(proposed_count or 0),
                        "accepted_count": int(accepted_count or 0),
                        "node_ids": list(node_ids),
                        "live_child_node_ids": list(live_children),
                    },
                )
                self._refresh_priorities_for_neighbors(task.node_id)
                return
            if self._apply_lemma_dag_task_child_progress(
                task,
                proposed_count=proposed_count,
                accepted_count=accepted_count,
                node_ids=node_ids,
                empty_retry=True,
            ):
                return
            task.status = "failed"
            task.action = "lemma_dag_decomposition_failed"
            task.blocker = "LLM lemma-DAG decomposition produced no usable helper statements"
            task.priority = self._priority(task)
            self._clear_terminal_node_verifier_work(task)
            self.record_transition(
                node_id=task.node_id,
                source="llm_lemma_dag",
                error_type="llm_lemma_dag_decomposition_empty",
                action=task.action,
                blocker=task.blocker,
                payload={"proposed_count": int(proposed_count or 0)},
            )
            return
        for child_id in list(node_ids or ()):
            child = self.nodes.get(str(child_id or ""))
            if child is None or child.node_id == self.root_node_id:
                continue
            if child.kind != "child_goal" or child.status == "obsolete":
                continue
            if self._would_create_dependency_cycle(task.node_id, child.node_id):
                continue
            attached = self._attach_child_to_parent(
                parent_node_id=task.node_id,
                child_node_id=child.node_id,
            )
            if not attached:
                continue
            if task.node_id not in child.dependencies:
                child.dependencies.append(task.node_id)
            self._move_primary_parent_if_rootish(
                child_node_id=child.node_id,
                parent_node_id=task.node_id,
            )
        if accepted_count <= 0:
            self.lemma_dag_decomposition_all_candidates_rejected += 1
            task.failed_attempts += 1
            task_was_opened_for_inline_sorry_stubs = (
                "ad_hoc:sorry_stub_helpers_volunteered:executor_inline"
                in str(task.blocker or "")
            )
            if (
                task_was_opened_for_inline_sorry_stubs
                and self._apply_lemma_dag_task_child_progress(
                    task,
                    proposed_count=proposed_count,
                    accepted_count=accepted_count,
                    node_ids=node_ids,
                )
            ):
                return
            task.status = "open"
            task.action = "lemma_dag_decomposition"
            task.blocker = (
                "LLM lemma-DAG decomposition proposed helper node(s), but no "
                "candidate proof passed verification; task remains open for a "
                "fresh decomposition attempt."
            )
            task.priority = self._priority(task)
            self.record_transition(
                node_id=task.node_id,
                source="llm_lemma_dag",
                error_type="llm_lemma_dag_decomposition_all_candidates_rejected",
                action=task.action,
                blocker=task.blocker,
                payload={
                    "proposed_count": int(proposed_count or 0),
                    "accepted_count": int(accepted_count or 0),
                    "node_ids": list(node_ids),
                },
            )
            self._refresh_priorities_for_neighbors(task.node_id)
            return
        if not self._apply_lemma_dag_task_child_progress(
            task,
            proposed_count=proposed_count,
            accepted_count=accepted_count,
            node_ids=node_ids,
        ):
            task.status = "failed"
            task.action = "lemma_dag_decomposition_failed"
            task.blocker = "LLM lemma-DAG decomposition produced no live child helper nodes"
            task.priority = self._priority(task)
            self._clear_terminal_node_verifier_work(task)
            self.record_transition(
                node_id=task.node_id,
                source="llm_lemma_dag",
                error_type="llm_lemma_dag_decomposition_no_live_children",
                action=task.action,
                blocker=task.blocker,
                payload={
                    "proposed_count": int(proposed_count or 0),
                    "accepted_count": int(accepted_count or 0),
                    "node_ids": list(node_ids),
                },
            )

    # ------------------------------------------------------------------
    # Backtracking primitive — Gap 3 fix (2026-05-08).
    # ------------------------------------------------------------------

    def checkpoint(
        self,
        *,
        dossier: Optional[ProofDossier] = None,
        label: str = "",
    ) -> str:
        """Snapshot the current proof_state (and optionally proof_graph).

        Returns a CheckpointId string the caller passes back to
        ``rollback`` or ``commit``. Checkpoints stack — opening N
        before resolving the previous one is allowed; rollback to an
        earlier id discards everything stacked above it.

        When ``dossier`` is supplied (and has a ``proof_graph``), the
        graph is cloned via ``ProofGraph.clone()`` and restored to the
        same dossier on rollback. Verified helpers and attempts are
        NEVER snapshotted — they are durable wins / audit trail.
        """

        seq = next(self._checkpoint_counter)
        checkpoint_id = f"ckpt_{self._checkpoint_id_prefix}_{seq}"
        graph_snapshot: Optional[Any] = None
        dossier_owner: Optional[Any] = None
        if dossier is not None:
            dossier_owner = dossier
            graph = getattr(dossier, "proof_graph", None)
            if graph is not None and callable(getattr(graph, "clone", None)):
                try:
                    graph_snapshot = graph.clone()
                except Exception:
                    graph_snapshot = None
        snapshot = ProofStateCheckpoint(
            checkpoint_id=checkpoint_id,
            label=str(label or ""),
            next_index=self._next_index,
            nodes=copy.deepcopy(self.nodes),
            node_by_target=dict(self._node_by_target),
            statement_environment_hash=str(
                self.statement_environment_hash or ""
            ),
            plan_hints=list(self.plan_hints),
            graph_frontier_errors=copy.deepcopy(self.graph_frontier_errors),
            decl_application_context_fingerprint=str(
                getattr(self, "decl_application_context_fingerprint", "") or ""
            ),
            proof_graph_snapshot=graph_snapshot,
            dossier_ref=dossier_owner,
        )
        self._checkpoint_stack.append(snapshot)
        return checkpoint_id

    def commit(self, checkpoint_id: str) -> bool:
        """Discard the named snapshot and any newer (more-recently-opened)
        snapshots stacked above it.

        Use after a speculative window succeeded — we keep the current
        state and free the snapshot memory. Idempotent: a second call
        with the same id returns False.

        Stack semantics: the stack grows by appending newer snapshots
        on top of older ones. ``commit(id)`` deletes the entry at ``id``
        and everything stacked above (= newer than) it. Older
        (more-deeply-nested) checkpoints continue to live. Conversely,
        committing an OUTER checkpoint while inner ones remain open
        also drops the inner ones, because they live on top of the
        outer in the stack.
        """

        index = self._checkpoint_index(checkpoint_id)
        if index < 0:
            return False
        # Drop the named snapshot and everything stacked above (newer than) it.
        del self._checkpoint_stack[index:]
        return True

    def capture_checkpoint(self, checkpoint_id: str) -> Optional[ProofStateCheckpoint]:
        """Retain a live checkpoint payload across an irreversible commit.

        ``commit`` normally drops its stack entry.  A deadline-aware outer
        transaction needs to check the elapsed budget *after* that release,
        so it holds this already-isolated payload and can restore it if the
        deadline wins inside ``commit`` itself.  The payload is not copied:
        ``checkpoint`` created all mutable graph/node members as snapshots,
        and preserving its dossier reference is required to restore the
        original graph object rather than a cloned dossier.
        """

        index = self._checkpoint_index(checkpoint_id)
        if index < 0:
            return None
        return self._checkpoint_stack[index]

    def restore_checkpoint(self, snapshot: Optional[ProofStateCheckpoint]) -> bool:
        """Restore a checkpoint payload retained by ``capture_checkpoint``."""

        if snapshot is None:
            return False
        self.nodes = copy.deepcopy(snapshot.nodes)
        self._node_by_target = dict(snapshot.node_by_target)
        self.statement_environment_hash = str(
            snapshot.statement_environment_hash or ""
        )
        self._next_index = snapshot.next_index
        self.plan_hints = list(snapshot.plan_hints)
        self.decl_application_context_fingerprint = str(
            getattr(snapshot, "decl_application_context_fingerprint", "") or ""
        )
        self.graph_frontier_errors = copy.deepcopy(snapshot.graph_frontier_errors)
        # E1: rollback restored ``self.nodes`` from a deepcopy; rebuild the
        # inverse index from the restored assembly groups so newly proved
        # children find their (parent, group) pairs again.
        self._rebuild_assembly_index()
        if (
            snapshot.proof_graph_snapshot is not None
            and snapshot.dossier_ref is not None
        ):
            try:
                snapshot.dossier_ref.proof_graph = snapshot.proof_graph_snapshot.clone()
            except Exception:
                # Keep the current graph if cloning a recovery snapshot fails;
                # the durable dossier restore in the outer transaction still
                # leaves it in a coherent, non-aliased state.
                pass
        if snapshot.dossier_ref is not None:
            try:
                record = self.to_record()
                setattr(snapshot.dossier_ref, "proof_state_record", record)
                self._write_durable_metrics_to_graph_root(
                    snapshot.dossier_ref,
                    record,
                )
            except Exception:
                pass
        return True

    def rollback(self, checkpoint_id: str) -> bool:
        """Restore the named snapshot and discard those stacked above.

        Use after a speculative window failed — wipes children/decomp
        tasks/index gains made during the window, restores proof_graph
        if it was snapshotted. Verified helpers are NOT restored.

        Idempotent: a second call with the same id returns False.
        """

        index = self._checkpoint_index(checkpoint_id)
        if index < 0:
            return False
        snapshot = self._checkpoint_stack[index]
        self.restore_checkpoint(snapshot)
        # Drop this snapshot and everything stacked above (no longer valid).
        del self._checkpoint_stack[index:]
        return True

    def active_checkpoints(self) -> List[str]:
        """Return the ids of currently open checkpoints (oldest first)."""

        return [snap.checkpoint_id for snap in self._checkpoint_stack]

    def _checkpoint_index(self, checkpoint_id: str) -> int:
        target = str(checkpoint_id or "")
        if not target:
            return -1
        for index, snap in enumerate(self._checkpoint_stack):
            if snap.checkpoint_id == target:
                return index
        return -1

    def mark_root_solved(self) -> None:
        root = self.nodes[self.root_node_id]
        root.status = "proved"
        root.action = "root_solved"
        root.priority = 0.0
        self._clear_terminal_node_verifier_work(root)
        # E6 (2026-05-09): when root is solved via a top-level path
        # (not via the assembly fixpoint), all of root's open assembly
        # groups become obsolete and their unique children should be
        # cancelled. If root was proved via assembly, the winning
        # group is already status="proved" and ``record_assembly_result``
        # already handled the cancellation; this call is a no-op then
        # because no open groups remain.
        self._cancel_obsolete_or_siblings(self.root_node_id)
        for node in list(self.nodes.values()):
            if node.kind != "decomposition_task" or node.status != "open":
                continue
            node.status = "obsolete"
            node.action = "root_solved_obsolete"
            node.blocker = "root solved; decomposition task no longer schedulable"
            node.priority = self._priority(node)
            self._clear_terminal_node_verifier_work(node)
            self.record_transition(
                node_id=node.node_id,
                source="root_solved",
                error_type="decomposition_task_obsolete_after_root_solved",
                action=node.action,
                blocker=node.blocker,
            )
        # Adversarial review fix 2026-05-09: this is the 9th
        # status="proved" close site (the 8 in record_* methods plus
        # this one). Without this refresh, any open child of the root
        # carrying a closure-bonus credit for closing the now-proved
        # root retains its stale priority. Currently benign because
        # ``mark_root_solved`` typically ends the search, but
        # ``reconcile_with_dossier`` can reopen the root and the open
        # children would then use stale ranks. Refresh is cheap.
        self._refresh_priorities_for_neighbors(self.root_node_id)

    def _residual_goal_attestation_validation(
        self,
        *,
        elaboration_context_hash: str = "",
        elaboration_context_hashes: Optional[Sequence[str]] = None,
        route_elaboration_context_hashes: Optional[
            Mapping[Tuple[str, str], str]
        ] = None,
    ) -> Tuple[Set[str], Set[str], Dict[Tuple[str, str], bool]]:
        """Return required nodes, authorized nodes, and route validity."""

        expected_context_hashes = {
            str(item or "").strip()
            for item in list(elaboration_context_hashes or ())
            if str(item or "").strip()
        }
        if str(elaboration_context_hash or "").strip():
            expected_context_hashes.add(
                str(elaboration_context_hash or "").strip()
            )
        exact_route_contexts = {
            (str(key[0] or ""), str(key[1] or "")): str(value or "").strip()
            for key, value in dict(route_elaboration_context_hashes or {}).items()
            if isinstance(key, tuple)
            and len(key) == 2
            and str(value or "").strip()
        }
        required: Set[str] = set()
        authorized: Set[str] = set()
        route_validity: Dict[Tuple[str, str], bool] = {}
        for node in self.nodes.values():
            node_source = (
                node.goal.source_failure if node.goal is not None else ""
            )
            if proof_state_source_requires_residual_goal_attestation(
                node_source
            ):
                required.add(node.node_id)
        bound_parent_identities: Dict[str, Set[str]] = {}
        for child in self.nodes.values():
            for authority in _residual_goal_attestation_authorities(
                child.residual_goal_attestation
            ):
                parent_id = str(authority.get("parent_node_id") or "")
                parent = self.nodes.get(parent_id)
                identity = str(
                    authority.get("parent_structural_identity") or ""
                )
                if (
                    parent is not None
                    and str(authority.get("parent_target_sha256") or "")
                    == _proof_state_exact_sha256(parent.target)
                    and str(authority.get("statement_environment_hash") or "")
                    == self.statement_environment_hash
                    and has_current_lean_contract_identity(identity)
                ):
                    bound_parent_identities.setdefault(parent_id, set()).add(
                        identity
                    )
        structurally_residual_node_ids = {
            child_id
            for candidate in self.nodes.values()
            for group in candidate.assembly_attempt_groups
            if proof_state_source_requires_residual_goal_attestation(
                group.source
            )
            for child_id in group.child_node_ids
        }
        for parent in self.nodes.values():
            parent_requires_attestation = (
                self._parent_residual_attestation_ledger_is_authoritative(
                    parent,
                    structurally_residual_node_ids=(
                        structurally_residual_node_ids
                    ),
                )
            )
            parent_authorities = (
                _residual_goal_attestation_authorities(
                    parent.residual_goal_attestation
                )
                if parent_requires_attestation
                else []
            )
            parent_ledger_valid = (
                not parent_requires_attestation
                or bool(parent_authorities)
                or not bool(parent.residual_goal_attestation)
            )
            parent_identities = {
                str(authority.get("structural_identity") or "")
                for authority in parent_authorities
            }
            parent_identities.update(
                bound_parent_identities.get(parent.node_id, set())
            )
            expected_parent_identity = (
                next(iter(parent_identities))
                if len(parent_identities) == 1
                else ""
            )
            for group in parent.assembly_attempt_groups:
                if not proof_state_source_requires_residual_goal_attestation(
                    group.source
                ):
                    continue
                route_key = (parent.node_id, group.assembly_id)
                child_ids = list(group.child_node_ids)
                required.update(child_ids)
                route_validity[route_key] = False
                if (
                    not child_ids
                    or (
                        _proof_state_durable_nonnegative_int(
                            group.residual_goal_slot_count
                        )
                        > 0
                        and _proof_state_durable_nonnegative_int(
                            group.residual_goal_slot_count
                        )
                        != len(child_ids)
                    )
                    or not parent_ledger_valid
                    or len(parent_identities) > 1
                    or any(child_id not in self.nodes for child_id in child_ids)
                    or any(
                        self.nodes[child_id].statement_environment_hash
                        != self.statement_environment_hash
                        for child_id in child_ids
                        if child_id in self.nodes
                    )
                ):
                    continue
                first_child = self.nodes[child_ids[0]]
                first_authorities = _residual_goal_attestation_authorities(
                    first_child.residual_goal_attestation
                )
                candidate_digests = {
                    str(authority.get("batch_digest") or "")
                    for authority in first_authorities
                    if authority.get("slot_index") == 0
                    and authority.get("slot_count") == len(child_ids)
                    and str(authority.get("source") or "") == group.source
                    and str(authority.get("parent_node_id") or "")
                    == parent.node_id
                    and (
                        not str(group.residual_goal_batch_digest or "")
                        or str(authority.get("batch_digest") or "")
                        == str(group.residual_goal_batch_digest or "")
                    )
                    and (
                        not str(
                            group.residual_goal_elaboration_context_hash or ""
                        )
                        or str(
                            authority.get("elaboration_context_hash") or ""
                        )
                        == str(
                            group.residual_goal_elaboration_context_hash or ""
                        )
                    )
                }
                for batch_digest in candidate_digests:
                    records: List[Dict[str, Any]] = []
                    statements: List[str] = []
                    for slot_index, child_id in enumerate(child_ids):
                        child = self.nodes[child_id]
                        authority_key = f"{batch_digest}:{slot_index}"
                        authority = child.residual_goal_attestation.get(
                            authority_key
                        )
                        if not isinstance(authority, Mapping):
                            records = []
                            break
                        records.append(dict(authority))
                        statements.append(child.target)
                    if not records:
                        continue
                    context_hash = str(
                        records[0].get("elaboration_context_hash") or ""
                    )
                    route_expected_context = exact_route_contexts.get(route_key)
                    if route_expected_context and (
                        context_hash != route_expected_context
                    ):
                        continue
                    if (
                        not route_expected_context
                        and expected_context_hashes
                        and context_hash not in expected_context_hashes
                    ):
                        continue
                    if _validate_bound_residual_goal_attestation_batch(
                        records,
                        statements=statements,
                        source=group.source,
                        parent_node_id=parent.node_id,
                        parent_statement=parent.target,
                        parent_proof_stub=group.proof_stub,
                        statement_environment_hash=self.statement_environment_hash,
                        elaboration_context_hash=context_hash,
                        expected_parent_structural_identity=(
                            expected_parent_identity
                        ),
                    ):
                        route_validity[route_key] = True
                        authorized.update(child_ids)
                        break
        return required, authorized, route_validity

    def _parent_residual_attestation_ledger_is_authoritative(
        self,
        parent: ProofStateNode,
        *,
        structurally_residual_node_ids: Optional[Set[str]] = None,
    ) -> bool:
        """Whether a parent's residual ledger is child-admission authority.

        The theorem root is intrinsically a non-residual boundary.  For every
        other node, fail closed when durable state is ambiguous: source text
        is mutable during restoration, while membership in a typed residual
        assembly is structural evidence that cannot be downgraded by changing
        that text alone.
        """

        if parent.node_id == self.root_node_id:
            return False
        source = parent.goal.source_failure if parent.goal is not None else ""
        if proof_state_source_requires_residual_goal_attestation(source):
            return True
        if structurally_residual_node_ids is None:
            structurally_residual_node_ids = {
                child_id
                for candidate in self.nodes.values()
                for group in candidate.assembly_attempt_groups
                if proof_state_source_requires_residual_goal_attestation(
                    group.source
                )
                for child_id in group.child_node_ids
            }
        if parent.node_id in structurally_residual_node_ids:
            return True
        # A non-root durable ledger with no surviving topology is ambiguous,
        # not irrelevant. Preserve the established fail-closed behavior.
        return bool(parent.residual_goal_attestation)

    def _residual_parent_bound_structural_identities(
        self,
        parent: ProofStateNode,
    ) -> Set[str]:
        """Typed parent identities already bound by any admitted child batch."""

        parent_target_sha256 = _proof_state_exact_sha256(parent.target)
        identities: Set[str] = set()
        for node in self.nodes.values():
            for authority in _residual_goal_attestation_authorities(
                node.residual_goal_attestation
            ):
                identity = str(
                    authority.get("parent_structural_identity") or ""
                )
                if (
                    str(authority.get("parent_node_id") or "")
                    == parent.node_id
                    and str(authority.get("parent_target_sha256") or "")
                    == parent_target_sha256
                    and str(authority.get("statement_environment_hash") or "")
                    == self.statement_environment_hash
                    and has_current_lean_contract_identity(identity)
                ):
                    identities.add(identity)
        return identities

    def residual_goal_attestation_status(
        self,
        node_or_id: Any,
        *,
        elaboration_context_hash: str = "",
        elaboration_context_hashes: Optional[Sequence[str]] = None,
        route_elaboration_context_hashes: Optional[
            Mapping[Tuple[str, str], str]
        ] = None,
    ) -> str:
        """Return the residual-admission status used by every dispatcher."""

        node_id = (
            node_or_id.node_id
            if isinstance(node_or_id, ProofStateNode)
            else str(node_or_id or "")
        )
        required, authorized, _route_validity = (
            self._residual_goal_attestation_validation(
                elaboration_context_hash=str(
                    elaboration_context_hash or ""
                ).strip(),
                elaboration_context_hashes=elaboration_context_hashes,
                route_elaboration_context_hashes=(
                    route_elaboration_context_hashes
                ),
            )
        )
        if node_id not in required:
            return "not_required"
        if node_id in authorized:
            return "attested"
        return "residual_elaboration_attestation_required"

    def residual_goal_node_is_executable_attested(
        self,
        node_or_id: Any,
        *,
        elaboration_context_hash: str = "",
        elaboration_context_hashes: Optional[Sequence[str]] = None,
        route_elaboration_context_hashes: Optional[
            Mapping[Tuple[str, str], str]
        ] = None,
    ) -> bool:
        """Whether a node may enter any recursive/conversation dispatcher."""

        return self.residual_goal_attestation_status(
            node_or_id,
            elaboration_context_hash=elaboration_context_hash,
            elaboration_context_hashes=elaboration_context_hashes,
            route_elaboration_context_hashes=route_elaboration_context_hashes,
        ) != (
            "residual_elaboration_attestation_required"
        )

    def _quarantine_residual_goal_attestation_failures(self) -> None:
        required, authorized, route_validity = (
            self._residual_goal_attestation_validation()
        )
        for parent in self.nodes.values():
            for group in parent.assembly_attempt_groups:
                route_key = (parent.node_id, group.assembly_id)
                if group.status != "blocked" and (
                    group.attestation_quarantined
                    or group.attestation_quarantine_previous_status
                ):
                    group.attestation_quarantined = False
                    group.attestation_quarantine_previous_status = ""
                elif group.status == "blocked" and (
                    group.attestation_quarantined
                    or group.attestation_quarantine_previous_status
                ) and not (
                    group.attestation_quarantined
                    and group.attestation_quarantine_previous_status == "open"
                ):
                    group.attestation_quarantined = False
                    group.attestation_quarantine_previous_status = ""
                if route_key in route_validity and not route_validity[route_key]:
                    if group.status == "open":
                        group.attestation_quarantine_previous_status = "open"
                        group.status = "blocked"
                        group.attestation_quarantined = True
                elif (
                    route_validity.get(route_key)
                    and group.status == "blocked"
                    and group.attestation_quarantined
                    and group.attestation_quarantine_previous_status == "open"
                ):
                    group.status = "open"
                    group.attestation_quarantined = False
                    group.attestation_quarantine_previous_status = ""
        for node in self.nodes.values():
            if not node.residual_attestation_quarantine_snapshot:
                continue
            node.residual_attestation_quarantine_snapshot = (
                _proof_state_residual_attestation_quarantine_snapshot(
                    node.residual_attestation_quarantine_snapshot,
                    node_status=node.status,
                    node_action=node.action,
                    node_blocker=node.blocker,
                )
            )
        for node_id in required - authorized:
            node = self.nodes.get(node_id)
            if node is None or node.status != "open":
                continue
            node.residual_attestation_quarantine_snapshot = {
                "schema_version": (
                    _RESIDUAL_ATTESTATION_QUARANTINE_SCHEMA_VERSION
                ),
                "status": "open",
                "action": node.action,
                "blocker": node.blocker,
                "priority": node.priority,
            }
            node.status = "blocked"
            node.action = "residual_elaboration_attestation_required"
            node.blocker = "residual_elaboration_attestation_required"
            node.priority = 0.0
        for node_id in required & authorized:
            node = self.nodes.get(node_id)
            if (
                node is None
                or node.status != "blocked"
                or node.action != "residual_elaboration_attestation_required"
                or node.blocker != "residual_elaboration_attestation_required"
            ):
                continue
            snapshot = node.residual_attestation_quarantine_snapshot
            if str(snapshot.get("status") or "") != "open":
                continue
            node.status = "open"
            node.action = str(snapshot.get("action") or "prove_child_helper")
            node.blocker = str(snapshot.get("blocker") or "")
            node.priority = _proof_state_durable_finite_float(
                snapshot.get("priority"),
                default=self._priority(node),
            )
            node.residual_attestation_quarantine_snapshot = {}
            self._refresh_priorities_for_neighbors(node.node_id)

    def record_pending_residual_goal_extraction(
        self,
        *,
        parent_node_id: str,
        source: str,
        parent_proof_stub: str,
        max_goals: int,
        request_context_hash: str,
        elaboration_context_hash: str = "",
        origin_metadata: Optional[Mapping[str, Any]] = None,
        action_metadata: Optional[Mapping[str, Any]] = None,
        retry_count: int = 0,
        verifier_retry_key: str = "",
        verifier_failure: Optional[Mapping[str, Any]] = None,
    ) -> bool:
        """Persist one exact verifier-only typed-extraction retry request."""

        parent_id = str(parent_node_id or self.root_node_id)
        parent = self.nodes.get(parent_id)
        exact_source = str(source or "").strip()
        exact_stub = str(parent_proof_stub or "").strip()
        request_hash = str(request_context_hash or "").strip()
        context_hash = str(elaboration_context_hash or "").strip()
        exact_retry_key = str(verifier_retry_key or "").strip()
        if (
            parent is None
            or parent.status in {"proved", "obsolete", "rejected", "failed"}
            or not proof_state_source_requires_residual_goal_attestation(
                exact_source
            )
            or not exact_stub
            or max(0, int(max_goals or 0)) <= 0
            or not _proof_state_is_sha256(request_hash)
            or (context_hash and not _proof_state_is_sha256(context_hash))
            or isinstance(retry_count, bool)
            or int(retry_count or 0) < 0
            or (exact_retry_key and not _proof_state_is_sha256(exact_retry_key))
        ):
            return False
        try:
            origin = clone_json_value(
                dict(origin_metadata or {}),
                label="pending residual extraction origin metadata",
            )
            action = clone_json_value(
                dict(action_metadata or {}),
                label="pending residual extraction action metadata",
            )
            failure = clone_json_value(
                dict(verifier_failure or {}),
                label="pending residual extraction verifier failure",
            )
        except (TypeError, ValueError):
            return False
        parent.pending_residual_goal_extraction = {
            "schema_version": (
                PROOF_STATE_PENDING_RESIDUAL_EXTRACTION_SCHEMA_VERSION
            ),
            "source": exact_source,
            "parent_node_id": parent_id,
            "parent_target_sha256": _proof_state_exact_sha256(parent.target),
            "parent_proof_stub": exact_stub,
            "parent_proof_stub_sha256": _proof_state_exact_sha256(exact_stub),
            "max_goals": max(1, int(max_goals or 0)),
            "statement_environment_hash": self.statement_environment_hash,
            "elaboration_context_hash": context_hash,
            "request_context_hash": request_hash,
            "origin_metadata": origin,
            "action_metadata": action,
            "retry_count": int(retry_count or 0),
            "verifier_retry_key": exact_retry_key,
            "verifier_failure": failure,
        }
        return True

    def verifier_retry_status(
        self,
        node_or_id: Any,
        retry_key: str,
        *,
        now_epoch_s: Optional[float] = None,
    ) -> str:
        """Return ``ready`` or ``cooling`` for one exact verifier identity.

        Missing/malformed records fail open for capability: the authoritative
        verifier still decides the proof, while a valid persisted cooldown
        only controls how often infrastructure is retried.
        """

        node_id = (
            node_or_id.node_id
            if isinstance(node_or_id, ProofStateNode)
            else str(node_or_id or "")
        )
        node = self.nodes.get(node_id)
        exact_key = str(retry_key or "").strip()
        if node is None or not _proof_state_is_sha256(exact_key):
            return "ready"
        record = dict(node.verifier_retry_states.get(exact_key) or {})
        if (
            record.get("schema_version")
            != PROOF_STATE_VERIFIER_RETRY_SCHEMA_VERSION
        ):
            return "ready"
        now = time.time() if now_epoch_s is None else max(0.0, float(now_epoch_s))
        retry_after = max(
            0.0,
            _proof_state_durable_finite_float(
                record.get("retry_after_epoch_s")
            ),
        )
        return "cooling" if retry_after > now else "ready"

    def verifier_retry_next_eligible_at(
        self,
        node_or_id: Any,
        retry_key: str,
    ) -> float:
        """Return the durable wall-clock wake time for a cooling identity."""

        node_id = (
            node_or_id.node_id
            if isinstance(node_or_id, ProofStateNode)
            else str(node_or_id or "")
        )
        node = self.nodes.get(node_id)
        exact_key = str(retry_key or "").strip()
        if node is None or not _proof_state_is_sha256(exact_key):
            return 0.0
        if self.verifier_retry_status(node, exact_key) != "cooling":
            return 0.0
        return max(
            0.0,
            _proof_state_durable_finite_float(
                dict(node.verifier_retry_states.get(exact_key) or {}).get(
                    "retry_after_epoch_s"
                )
            ),
        )

    def record_verifier_retry_failure(
        self,
        node_or_id: Any,
        *,
        retry_key: str,
        stage: str,
        request_hash: str,
        context_hash: str,
        verifier_generation: str,
        failure_kind: str,
        failure_fingerprint: str,
        now_epoch_s: Optional[float] = None,
        immediate_retry_count: int = 1,
        base_cooldown_s: float = 30.0,
        max_cooldown_s: float = 1800.0,
    ) -> Dict[str, Any]:
        """Persist a non-terminal retry-frequency transition.

        The first infrastructure failure remains immediately retryable.  Every
        later consecutive failure cools exponentially, including alternating
        fingerprints.  No count ever deletes or semantically rejects the paid
        proof candidate.
        """

        node_id = (
            node_or_id.node_id
            if isinstance(node_or_id, ProofStateNode)
            else str(node_or_id or "")
        )
        node = self.nodes.get(node_id)
        key = str(retry_key or "").strip()
        request = str(request_hash or "").strip()
        context = str(context_hash or "").strip()
        fingerprint = str(failure_fingerprint or "").strip()
        if (
            node is None
            or not _proof_state_is_sha256(key)
            or not _proof_state_is_sha256(request)
            or (context and not _proof_state_is_sha256(context))
            or (fingerprint and not _proof_state_is_sha256(fingerprint))
        ):
            return {}
        prior = dict(node.verifier_retry_states.get(key) or {})
        prior_count = _proof_state_durable_nonnegative_int(
            prior.get("consecutive_failure_count")
        )
        total_count = min(_PROOF_STATE_MAX_DURABLE_COUNTER, prior_count + 1)
        same_count = (
            min(
                _PROOF_STATE_MAX_DURABLE_COUNTER,
                _proof_state_durable_nonnegative_int(
                    prior.get("same_fingerprint_count")
                )
                + 1,
            )
            if fingerprint
            and fingerprint == str(prior.get("failure_fingerprint") or "")
            else 1
        )
        immediate = max(0, int(immediate_retry_count or 0))
        cooldown_index = max(0, total_count - immediate - 1)
        cooldown_s = 0.0
        if total_count > immediate:
            cooldown_s = min(
                max(0.0, float(max_cooldown_s or 0.0)),
                max(0.0, float(base_cooldown_s or 0.0))
                * (2.0 ** min(cooldown_index, 20)),
            )
        now = time.time() if now_epoch_s is None else max(0.0, float(now_epoch_s))
        record = {
            "schema_version": PROOF_STATE_VERIFIER_RETRY_SCHEMA_VERSION,
            "stage": str(stage or "")[:120],
            "request_hash": request,
            "context_hash": context,
            "verifier_generation": str(verifier_generation or "")[:240],
            "failure_kind": str(failure_kind or "")[:160],
            "failure_fingerprint": fingerprint,
            "consecutive_failure_count": total_count,
            "same_fingerprint_count": same_count,
            "retry_after_epoch_s": now + cooldown_s if cooldown_s > 0.0 else 0.0,
            "last_attempt_epoch_s": now,
        }
        node.verifier_retry_states[key] = record
        active_keys = {
            str(
                dict(node.pending_residual_goal_extraction or {}).get(
                    "verifier_retry_key"
                )
                or ""
            ),
            str(
                dict(node.pending_helper_acceptance or {}).get(
                    "verifier_retry_key"
                )
                or ""
            ),
            key,
        }
        if len(node.verifier_retry_states) > PROOF_STATE_VERIFIER_RETRY_MAX_STATES_PER_NODE:
            active_keys = {
                active_key
                for active_key in active_keys
                if active_key in node.verifier_retry_states
            }
            recent_budget = max(
                0,
                PROOF_STATE_VERIFIER_RETRY_MAX_STATES_PER_NODE
                - len(active_keys),
            )
            recent_keys = [
                retry_state_key
                for retry_state_key, _retry_state in sorted(
                    node.verifier_retry_states.items(),
                    key=lambda item: float(
                        item[1].get("last_attempt_epoch_s") or 0.0
                    ),
                    reverse=True,
                )
                if retry_state_key not in active_keys
            ][:recent_budget]
            keep_keys = active_keys | set(recent_keys)
            node.verifier_retry_states = {
                retry_state_key: retry_state
                for retry_state_key, retry_state in node.verifier_retry_states.items()
                if retry_state_key in keep_keys
            }
        return dict(record)

    def clear_verifier_retry_state(
        self,
        node_or_id: Any,
        retry_key: str,
    ) -> bool:
        node_id = (
            node_or_id.node_id
            if isinstance(node_or_id, ProofStateNode)
            else str(node_or_id or "")
        )
        node = self.nodes.get(node_id)
        key = str(retry_key or "").strip()
        if node is None or key not in node.verifier_retry_states:
            return False
        node.verifier_retry_states.pop(key, None)
        return True

    @staticmethod
    def _clear_terminal_node_verifier_work(node: ProofStateNode) -> None:
        """Retire private verifier work after an authoritative node close."""

        node.pending_residual_goal_extraction = {}
        node.pending_helper_acceptance = {}
        node.verifier_retry_states = {}

    def pending_residual_goal_extraction_status(
        self,
        node_or_id: Any,
        *,
        request_context_hash: str = "",
        elaboration_context_hash: str = "",
    ) -> str:
        """Read-only currentness status for a verifier-only retry request."""

        node_id = (
            node_or_id.node_id
            if isinstance(node_or_id, ProofStateNode)
            else str(node_or_id or "")
        )
        node = self.nodes.get(node_id)
        if node is None or not node.pending_residual_goal_extraction:
            return "none"
        if node.status in {"proved", "obsolete", "rejected", "failed"}:
            return "terminal"
        record = node.pending_residual_goal_extraction
        expected_request_hash = str(request_context_hash or "").strip()
        expected_context_hash = str(elaboration_context_hash or "").strip()
        stored_stub = str(record.get("parent_proof_stub") or "").strip()
        stored_context_hash = str(
            record.get("elaboration_context_hash") or ""
        )
        immutable_stale = bool(
            record.get("schema_version")
            != PROOF_STATE_PENDING_RESIDUAL_EXTRACTION_SCHEMA_VERSION
            or str(record.get("parent_node_id") or "") != node.node_id
            or str(record.get("parent_target_sha256") or "")
            != _proof_state_exact_sha256(node.target)
            or str(record.get("parent_proof_stub_sha256") or "")
            != _proof_state_exact_sha256(stored_stub)
            or not stored_stub
            or not proof_state_source_requires_residual_goal_attestation(
                record.get("source")
            )
            or not _proof_state_is_sha256(record.get("request_context_hash"))
            or (stored_context_hash and not _proof_state_is_sha256(stored_context_hash))
            or isinstance(record.get("max_goals"), bool)
            or not isinstance(record.get("max_goals"), int)
            or int(record.get("max_goals") or 0) <= 0
            or not isinstance(record.get("origin_metadata"), Mapping)
            or not isinstance(record.get("action_metadata"), Mapping)
            or not isinstance(record.get("verifier_failure", {}), Mapping)
            or (
                str(record.get("verifier_retry_key") or "")
                and not _proof_state_is_sha256(record.get("verifier_retry_key"))
            )
        )
        if immutable_stale:
            return "stale"
        if (
            str(record.get("statement_environment_hash") or "")
            != self.statement_environment_hash
            or (
                expected_request_hash
                and str(record.get("request_context_hash") or "")
                != expected_request_hash
            )
            or (
                expected_context_hash
                and str(record.get("elaboration_context_hash") or "")
                != expected_context_hash
            )
        ):
            # The exact stub/source/target is intact. A helper, preamble, or
            # environment change requires verifier-only rematerialization;
            # it is not corruption and must not discard the paid proof frame.
            return "rematerialize"
        return "pending"

    def clear_pending_residual_goal_extraction(
        self,
        node_or_id: Any,
    ) -> bool:
        node_id = (
            node_or_id.node_id
            if isinstance(node_or_id, ProofStateNode)
            else str(node_or_id or "")
        )
        node = self.nodes.get(node_id)
        if node is None or not node.pending_residual_goal_extraction:
            return False
        node.pending_residual_goal_extraction = {}
        return True

    def frontier(self, *, max_nodes: int = 6) -> List[ProofStateNode]:
        # A Lean-falsified child goal is dead work: exclude it here so the
        # auxiliary frontier consumers (child_frontier, retrieval static-priority
        # fallback, helper-salvage relevance targets, and the LLM prompt surface)
        # never re-surface it — mirroring the work_frontier.add() suppression.
        residual_required, residual_authorized, _route_validity = (
            self._residual_goal_attestation_validation()
        )
        nodes = [
            node
            for node in self.nodes.values()
            if (
                node.status == "open"
                and not getattr(node, "falsified", False)
                and (
                    node.node_id not in residual_required
                    or node.node_id in residual_authorized
                )
            )
        ]
        nodes.sort(key=lambda node: (-node.priority, node.node_id))
        return nodes[: max(0, int(max_nodes or 0))]

    def child_frontier(self, *, max_nodes: int = 3) -> List[ProofStateNode]:
        nodes = [
            node
            for node in self.frontier(max_nodes=max(8, int(max_nodes or 0) * 3))
            if node.kind == "child_goal"
        ]
        return nodes[: max(0, int(max_nodes or 0))]

    def decomposition_frontier(self, *, max_nodes: int = 2) -> List[ProofStateNode]:
        nodes = [
            node
            for node in self.frontier(max_nodes=max(4, int(max_nodes or 0) * 4))
            if node.kind == "decomposition_task"
        ]
        return nodes[: max(0, int(max_nodes or 0))]

    def has_open_decomposition_task(self) -> bool:
        return bool(self.decomposition_frontier(max_nodes=1))

    def record_decomposition_task_prompted(
        self,
        *,
        task_id: str,
        phase: str,
        turn_index: int,
    ) -> bool:
        task = self.nodes.get(str(task_id or ""))
        if task is None or task.kind != "decomposition_task" or task.status != "open":
            return False
        scheduled_indices = [
            index
            for index, transition in enumerate(task.typed_transitions)
            if transition.error_type == "lemma_dag_decomposition_scheduled"
        ]
        if scheduled_indices:
            retry_epoch_opened = any(
                transition.error_type
                in {
                    "llm_lemma_dag_decomposition_all_candidates_rejected",
                    "llm_lemma_dag_decomposition_empty_all_unverified_retry",
                }
                for transition in task.typed_transitions[scheduled_indices[-1] + 1 :]
            )
            if not retry_epoch_opened:
                return False
        task.action = "await_llm_lemma_dag"
        task.blocker = (
            "awaiting named theorem/lemma declarations that decompose the root "
            "into durable child goals"
        )
        self.record_transition(
            node_id=task.node_id,
            source="proof_state_executor",
            error_type="lemma_dag_decomposition_scheduled",
            action=task.action,
            blocker=task.blocker,
            phase=phase,
            turn_index=turn_index,
            payload={"target_hash": task.goal.normalized_statement_hash if task.goal else ""},
        )
        task.priority = self._priority(task)
        return True

    def _graph_frontier_records(
        self,
        graph: Any,
        *,
        max_items: int,
        mutate: bool = True,
        record_errors: Optional[bool] = None,
    ) -> List[Dict[str, Any]]:
        if graph is None:
            return []
        getter = getattr(graph, "work_frontier", None)
        if not callable(getter):
            return []
        may_record_errors = mutate if record_errors is None else bool(record_errors)
        try:
            records = getter(max_items=max_items, mutate=mutate)
        except TypeError:
            if not mutate:
                return []
            try:
                records = getter()
            except Exception:
                if may_record_errors:
                    self.record_graph_frontier_error(
                        {
                            "error": "graph_work_frontier_failed",
                            "call": "getter()",
                        }
                    )
                return []
        except Exception:
            if may_record_errors:
                self.record_graph_frontier_error(
                    {
                        "error": "graph_work_frontier_failed",
                        "call": "getter(max_items=...)",
                    }
                )
            return []
        out: List[Dict[str, Any]] = []
        for record in list(records or []):
            if isinstance(record, dict):
                out.append(dict(record))
        return out

    def _graph_status_for_local_node(self, graph: Any, node_id: str) -> str:
        if graph is None:
            return ""
        nodes = getattr(graph, "nodes", {}) or {}
        graph_node = nodes.get(self._graph_node_id(str(node_id or "")))
        if graph_node is None:
            return ""
        return str(getattr(graph_node, "status", "") or "").strip()

    def _graph_status_suppresses_local_work(self, graph: Any, node_id: str) -> bool:
        return self._graph_status_for_local_node(graph, node_id) in {
            "blocked",
            "rejected",
            "failed",
        }

    def promote_trusted_graph_obligations(
        self,
        graph: Any,
        *,
        phase: str = "graph_obligation_promotion",
        turn_index: int = 0,
        max_promotions: int = 8,
    ) -> Dict[str, Any]:
        """Materialize trusted executable graph obligations as child goals.

        Graph-native ``missing_obligation`` work is useful for route repair,
        but the recursive/micro-lemma prover only sees first-class
        ``ProofSearchState`` child goals. This bridge promotes only obligations
        that already crossed the graph trust/executability boundary, and stamps
        the source graph node so its native scheduler does not race the local
        child-goal scheduler.
        """

        result: Dict[str, Any] = {
            "promoted_count": 0,
            "reused_count": 0,
            "reconciled_count": 0,
            "skip_changed_count": 0,
            "promoted": [],
            "reused": [],
            "skipped": [],
        }
        for reason in self._GRAPH_OBLIGATION_PROMOTION_SKIP_COUNTER_BY_REASON:
            result[f"skipped_{reason}_count"] = 0
        if graph is None:
            return result
        try:
            promotion_cap = max(0, int(max_promotions or 0))
        except (TypeError, ValueError):
            promotion_cap = 0
        if promotion_cap <= 0:
            return result
        root = self.nodes.get(self.root_node_id)
        if root is None:
            return result

        def obligation_metadata(obligation: Any) -> Dict[str, Any]:
            metadata = getattr(obligation, "metadata", None)
            if isinstance(metadata, dict):
                return metadata
            metadata = {}
            try:
                obligation.metadata = metadata
            except Exception:
                pass
            return metadata

        def increment_skip_metric(reason: str) -> None:
            metric_field = self._GRAPH_OBLIGATION_PROMOTION_SKIP_COUNTER_BY_REASON.get(
                reason
            )
            if not metric_field:
                return
            try:
                current = int(getattr(self, metric_field, 0) or 0)
            except (TypeError, ValueError):
                current = 0
            setattr(self, metric_field, current + 1)

        def note_skip(
            obligation: Any,
            reason: str,
            *,
            details: Optional[Dict[str, Any]] = None,
        ) -> None:
            clean_reason = str(reason or "rejected").strip() or "rejected"
            result_key = f"skipped_{clean_reason}_count"
            result[result_key] = int(result.get(result_key, 0) or 0) + 1
            metadata = obligation_metadata(obligation)
            previous = str(
                metadata.get("proof_state_promotion_skip_reason") or ""
            ).strip()
            clean_details = dict(details or {})
            previous_details = metadata.get(
                "proof_state_promotion_skip_details"
            )
            previous_details = (
                dict(previous_details)
                if isinstance(previous_details, Mapping)
                else {}
            )
            skip_changed = bool(
                previous != clean_reason
                or previous_details != clean_details
            )
            if previous != clean_reason:
                increment_skip_metric(clean_reason)
            if skip_changed:
                result["skip_changed_count"] = int(
                    result.get("skip_changed_count", 0) or 0
                ) + 1
                metadata["proof_state_promotion_skip_reason"] = clean_reason
                if clean_details:
                    metadata["proof_state_promotion_skip_details"] = clean_details
                else:
                    metadata.pop("proof_state_promotion_skip_details", None)
            result["skipped"].append(
                {
                    "obligation_id": str(getattr(obligation, "node_id", "") or ""),
                    "reason": clean_reason,
                    **clean_details,
                }
            )

        def graph_child_id_for(node: ProofStateNode) -> str:
            return self._graph_node_id(node.node_id)

        def promoted_child_id_from_metadata(obligation: Any) -> str:
            metadata = obligation_metadata(obligation)
            child_id = str(metadata.get("proof_state_child_node_id") or "").strip()
            if child_id:
                return child_id
            child_graph_id = str(
                metadata.get("proof_state_child_graph_node_id") or ""
            ).strip()
            return self._state_node_id_from_graph_id(child_graph_id)

        def detach_promoted_child(
            obligation: Any,
            *,
            child_id: str = "",
        ) -> None:
            """Remove one persisted promotion link and its topology index."""

            metadata = obligation_metadata(obligation)
            reconciliation_changed = False
            child_graph_id = str(
                metadata.get("proof_state_child_graph_node_id") or ""
            ).strip()
            if not child_graph_id and child_id:
                child_graph_id = self._graph_node_id(child_id)
            for key in (
                "promoted_to_proof_state",
                "proof_state_child_node_id",
                "proof_state_child_graph_node_id",
                "proof_state_promotion_phase",
                "proof_state_promotion_turn_index",
                "proof_state_promotion_reused_existing",
            ):
                if key in metadata:
                    reconciliation_changed = True
                    metadata.pop(key, None)
            obligation_id = str(
                getattr(obligation, "node_id", "") or ""
            ).strip()
            if not obligation_id or not child_graph_id or not hasattr(graph, "edges"):
                if reconciliation_changed:
                    result["reconciled_count"] = int(
                        result.get("reconciled_count", 0) or 0
                    ) + 1
                return
            prior_edge_count = len(graph.edges)
            graph.edges = [
                edge
                for edge in list(graph.edges)
                if not (
                    str(getattr(edge, "source", "") or "") == obligation_id
                    and str(getattr(edge, "target", "") or "") == child_graph_id
                    and str(getattr(edge, "kind", "") or "")
                    == "obligation_promoted_to_proof_state"
                )
            ]
            if len(graph.edges) != prior_edge_count:
                reconciliation_changed = True
                rebuild_edge_index = getattr(graph, "_rebuild_edge_index", None)
                if callable(rebuild_edge_index):
                    rebuild_edge_index()
            if reconciliation_changed:
                result["reconciled_count"] = int(
                    result.get("reconciled_count", 0) or 0
                ) + 1

        def promoted_child_from_metadata(
            obligation: Any,
        ) -> Optional[ProofStateNode]:
            metadata = obligation_metadata(obligation)
            child_id = promoted_child_id_from_metadata(obligation)
            if not child_id:
                return None
            child = self.nodes.get(child_id)
            if child is None:
                detach_promoted_child(obligation, child_id=child_id)
                return None
            obligation_statement = self._normalize_goal_text(
                str(getattr(obligation, "statement", "") or "")
            )
            child_statement = self._normalize_goal_text(child.target)
            obligation_environment_hash = str(
                metadata.get("statement_environment_hash") or ""
            ).strip()
            child_environment_hash = str(
                child.statement_environment_hash or ""
            ).strip()
            if (
                obligation_statement != child_statement
                or obligation_environment_hash != child_environment_hash
            ):
                # The same graph obligation ID may be re-recorded after a
                # preamble extension because its durable mathematical/work
                # identity intentionally excludes the environment. Never let
                # that metadata update retain an old-environment proof-state
                # child. Detach the stale projection and allow normal
                # environment-qualified promotion below to create/reuse the
                # correct child.
                detach_promoted_child(obligation, child_id=child.node_id)
                still_referenced = any(
                    promoted_child_id_from_metadata(other) == child.node_id
                    and self._normalize_goal_text(
                        str(getattr(other, "statement", "") or "")
                    )
                    == child_statement
                    and str(
                        obligation_metadata(other).get(
                            "statement_environment_hash"
                        )
                        or ""
                    ).strip()
                    == child_environment_hash
                    and str(getattr(other, "status", "") or "").strip()
                    in {"open", "blocked"}
                    for other in list(
                        getattr(graph, "nodes_by_kind", lambda _kind: [])(
                            "missing_obligation"
                        )
                        or []
                    )
                    if other is not obligation
                )
                if not still_referenced and child.status in {"open", "blocked"}:
                    child.status = "obsolete"
                    child.action = "environment_superseded"
                    child.blocker = (
                        "graph obligation was re-recorded in a different "
                        "Lean environment"
                    )
                    child.priority = 0.0
                return None
            if child.status in {"failed", "rejected", "obsolete"}:
                # Promotion metadata is an ownership link to actionable
                # proof-state work, not a permanent tombstone. A terminal
                # child must not hide an otherwise-live graph obligation.
                detach_promoted_child(obligation, child_id=child.node_id)
                stale_index_key = self._target_environment_index_key(
                    child.goal.normalized_statement_hash,
                    child_environment_hash,
                )
                if self._node_by_target.get(stale_index_key) == child.node_id:
                    self._node_by_target.pop(stale_index_key, None)
                return None
            repaired_projection = bool(
                metadata.get("promoted_to_proof_state") is not True
                or str(metadata.get("proof_state_child_node_id") or "")
                != child.node_id
                or str(metadata.get("proof_state_child_graph_node_id") or "")
                != graph_child_id_for(child)
            )
            metadata["promoted_to_proof_state"] = True
            metadata["proof_state_child_node_id"] = child.node_id
            metadata["proof_state_child_graph_node_id"] = graph_child_id_for(child)
            if repaired_projection:
                result["reconciled_count"] = int(
                    result.get("reconciled_count", 0) or 0
                ) + 1
            return child

        def stamp_promotion(
            obligation: Any,
            child: ProofStateNode,
            *,
            reused: bool,
        ) -> Dict[str, Any]:
            metadata = obligation_metadata(obligation)
            metadata["promoted_to_proof_state"] = True
            metadata["proof_state_child_node_id"] = child.node_id
            metadata["proof_state_child_graph_node_id"] = graph_child_id_for(child)
            metadata["proof_state_promotion_phase"] = str(phase or "")
            metadata["proof_state_promotion_turn_index"] = int(turn_index or 0)
            metadata["proof_state_promotion_reused_existing"] = bool(reused)
            metadata.pop("proof_state_promotion_skip_reason", None)
            metadata.pop("proof_state_promotion_skip_details", None)
            obligation_id = str(getattr(obligation, "node_id", "") or "")
            add_edge = getattr(graph, "add_edge", None)
            if callable(add_edge) and obligation_id:
                try:
                    add_edge(
                        obligation_id,
                        graph_child_id_for(child),
                        "obligation_promoted_to_proof_state",
                    )
                except Exception:
                    pass
            record = {
                "obligation_id": obligation_id,
                "proof_state_child_node_id": child.node_id,
                "proof_state_child_graph_node_id": graph_child_id_for(child),
                "target": child.target,
                "reused": bool(reused),
            }
            return record

        getter = getattr(graph, "nodes_by_kind", None)
        if callable(getter):
            try:
                obligations = list(getter("missing_obligation") or [])
            except Exception:
                obligations = []
        else:
            obligations = [
                node
                for node in list((getattr(graph, "nodes", {}) or {}).values())
                if getattr(node, "kind", "") == "missing_obligation"
            ]

        for obligation in obligations:
            if (
                int(result["promoted_count"]) + int(result["reused_count"])
                >= promotion_cap
            ):
                break
            if getattr(obligation, "kind", "") != "missing_obligation":
                continue
            if str(getattr(obligation, "status", "") or "open") != "open":
                continue

            existing_promoted_child = promoted_child_from_metadata(obligation)
            if existing_promoted_child is not None:
                continue

            metadata = obligation_metadata(obligation)
            statement = str(getattr(obligation, "statement", "") or "").strip()
            obligation_environment_hash = str(
                metadata.get("statement_environment_hash") or ""
            ).strip()
            if root.status in {"proved", "obsolete", "rejected", "failed"}:
                note_skip(
                    obligation,
                    "terminal_parent",
                    details={"parent_status": root.status},
                )
                continue
            if graph_node_frontier_quarantined(obligation):
                note_skip(obligation, "quarantined")
                continue
            source = str(metadata.get("source") or "").strip()
            trust = str(metadata.get("obligation_trust") or "").strip()
            bridge_trust_validator = getattr(
                graph,
                "formalization_bridge_open_premise_is_trusted",
                None,
            )
            bridge_premise_trusted = bool(
                source == "formalization_bridge_open_premise"
                and callable(bridge_trust_validator)
                and bridge_trust_validator(obligation)
            )
            if (
                metadata.get("certified_fact") is False
                or trust == "untrusted_failed_proof_residual"
                or (
                    source == "formalization_bridge_open_premise"
                    and (
                        trust != FORMALIZATION_BRIDGE_OPEN_PREMISE_TRUST
                        or not bridge_premise_trusted
                    )
                )
                or source
                in {
                    "post_failure_residual_work_item",
                    "failed_proof_residual_work_item",
                }
            ):
                note_skip(
                    obligation,
                    "untrusted",
                    details={"source": source, "obligation_trust": trust},
                )
                continue
            if metadata.get("formalization_required"):
                note_skip(obligation, "formalization_required")
                continue
            if not graph_statement_is_executable(statement):
                note_skip(obligation, "non_executable")
                continue
            route_id = str(metadata.get("route_id") or "").strip()
            root_suppression = graph_root_equivalent_suppression_decision(
                statement,
                str(getattr(graph, "root_statement", "") or root.target or ""),
                active_target_statements=(),
                route_backed_work=bool(route_id),
                allow_route_backed_work=True,
                reopened_after_superseded_spawn=bool(
                    metadata.get("spawned_claim_superseded_reopen_ids")
                ),
            )
            if root_suppression.suppress:
                metadata["root_equivalent_work_suppressed"] = True
                note_skip(
                    obligation,
                    "root_equivalent",
                    details={
                        "exact_root_statement": root_suppression.exact_root_statement,
                        "active_root_statement": root_suppression.active_root_statement,
                    },
                )
                continue
            goal_item = {"target": statement, "hypotheses": []}
            rejection = self._remaining_goal_item_rejection(
                goal_item,
                parent_proof_stub="",
                source="graph_obligation_promotion",
            )
            if rejection:
                note_skip(obligation, "rejected", details={"rejection": rejection})
                continue

            signature = self._goal_signature(
                self._normalize_goal_text(statement),
                [],
                source_failure="graph_obligation_promotion",
            )
            target_index_key = self._target_environment_index_key(
                signature.normalized_statement_hash,
                obligation_environment_hash,
            )
            existing_id = self._node_by_target.get(target_index_key)
            if existing_id:
                existing = self.nodes.get(existing_id)
                if existing is None:
                    self._node_by_target.pop(target_index_key, None)
                elif existing.status in {"obsolete", "failed", "rejected"}:
                    # A live trusted obligation is fresh authority to retry.
                    # Retire this environment-qualified index entry so normal
                    # spawning below creates a new actionable child.
                    self._node_by_target.pop(target_index_key, None)
                elif self._would_create_cycle(self.root_node_id, existing.node_id):
                    note_skip(
                        obligation,
                        "cycle",
                        details={"existing_node_id": existing.node_id},
                    )
                    continue
                else:
                    if self.root_node_id not in existing.dependencies:
                        existing.dependencies.append(self.root_node_id)
                    self._attach_child_to_parent(
                        parent_node_id=self.root_node_id,
                        child_node_id=existing.node_id,
                    )
                    record = stamp_promotion(obligation, existing, reused=True)
                    self.graph_obligation_child_promotion_reuses += 1
                    result["reused_count"] = int(result["reused_count"]) + 1
                    result["reused"].append(record)
                    continue

            child = self._spawn_remaining_goal(
                goal_item,
                source="graph_obligation_promotion",
                parent_node_id=self.root_node_id,
                parent_proof_stub="",
                statement_environment_hash=obligation_environment_hash,
            )
            if child is None:
                note_skip(obligation, "rejected", details={"rejection": "spawn_failed"})
                continue
            child.action = "prove_child_helper"
            child.blocker = (
                "promoted from trusted graph obligation "
                f"({str(metadata.get('reason') or getattr(obligation, 'node_id', '') or '').strip()})"
            )
            child.priority = self._priority(child)
            child.diagnostics.append(
                {
                    "phase": str(phase or ""),
                    "turn_index": int(turn_index or 0),
                    "error_type": "trusted_graph_obligation_promoted",
                    "action": child.action,
                    "blocker": child.blocker,
                    "obligation_id": str(getattr(obligation, "node_id", "") or ""),
                    "route_id": route_id,
                }
            )
            del child.diagnostics[:-8]
            self.record_transition(
                node_id=child.node_id,
                source="graph_obligation_promotion",
                error_type="trusted_graph_obligation_promoted",
                action=child.action,
                blocker=child.blocker,
                phase=phase,
                turn_index=turn_index,
                payload={
                    "obligation_id": str(getattr(obligation, "node_id", "") or ""),
                    "route_id": route_id,
                    "target": statement,
                },
            )
            record = stamp_promotion(obligation, child, reused=False)
            self.graph_obligation_child_promotions += 1
            result["promoted_count"] = int(result["promoted_count"]) + 1
            result["promoted"].append(record)
        return result

    def refresh_graph_readiness(
        self,
        graph: Any,
        *,
        phase: str = "graph_readiness_refresh",
        turn_index: int = 0,
        target_node_ids: Optional[Sequence[str]] = None,
    ) -> List[Dict[str, Any]]:
        """Apply safe graph-derived readiness facts to local proof state.

        This is the explicit mutation companion to the read-only
        ``work_frontier`` query.  It may reopen blocked/rejected nodes when
        graph evidence justifies retrying them, and it may hydrate retrieval
        evidence.  It never marks nodes proved.
        """

        if graph is None:
            return []
        terminal_blockers_by_graph_node: Dict[str, List[str]] = {}
        repair_terminal_blockers = getattr(graph, "repair_terminal_blockers", None)
        if callable(repair_terminal_blockers):
            terminal_blockers_by_graph_node = dict(
                repair_terminal_blockers() or {}
            )
        graph_nodes = dict(getattr(graph, "nodes", {}) or {})
        graph_edges = list(getattr(graph, "edges", []) or [])
        if not graph_nodes:
            return []
        target_ids = {
            str(item or "").strip()
            for item in list(target_node_ids or ())
            if str(item or "").strip()
        }
        records: List[Dict[str, Any]] = []
        outgoing_by_node: Dict[str, List[Any]] = {}
        for edge in graph_edges:
            outgoing_by_node.setdefault(str(getattr(edge, "source", "") or ""), []).append(edge)

        def graph_id_for(node: ProofStateNode) -> str:
            return self._graph_node_id(node.node_id)

        def retrieval_evidence(
            graph_node_id: str,
        ) -> Tuple[List[Tuple[str, str, str]], List[str]]:
            """Return graph declarations with their executable provenance.

            The graph's convenience getter intentionally exposes only names,
            which is insufficient for execution.  Read the edge/node metadata
            directly so legacy evidence is quarantined instead of inheriting a
            node-wide current stamp.
            """

            decl_records: List[Tuple[str, str, str]] = []
            facts: List[str] = []
            for edge in outgoing_by_node.get(graph_node_id, []):
                kind = str(getattr(edge, "kind", "") or "")
                if kind not in {"retrieved_declaration", "retrieved_fact"}:
                    continue
                retrieval_node = graph_nodes.get(str(getattr(edge, "target", "") or ""))
                if retrieval_node is None:
                    continue
                metadata = dict(getattr(retrieval_node, "metadata", {}) or {})
                if kind == "retrieved_declaration":
                    decl = str(
                        metadata.get("decl_name")
                        or getattr(retrieval_node, "name", "")
                        or getattr(retrieval_node, "statement", "")
                        or ""
                    ).strip()
                    if decl:
                        decl_records.append(
                            (
                                decl,
                                str(
                                    metadata.get(
                                        "decl_execution_policy_version"
                                    )
                                    or ""
                                ).strip(),
                                str(metadata.get("retrieval_signature") or "").strip(),
                            )
                        )
                else:
                    fact = str(
                        metadata.get("retrieved_fact")
                        or getattr(retrieval_node, "statement", "")
                        or getattr(retrieval_node, "name", "")
                        or ""
                    ).strip()
                    if fact:
                        facts.append(fact[:1000])
            graph_node = graph_nodes.get(graph_node_id)
            metadata = dict(getattr(graph_node, "metadata", {}) or {}) if graph_node is not None else {}
            node_record = metadata.get("proof_state_node")
            if isinstance(node_record, dict):
                record_provenance = {
                    str(key): str(value)
                    for key, value in dict(
                        node_record.get("retrieved_decl_provenance") or {}
                    ).items()
                }
                record_signatures = {
                    str(key): str(value)
                    for key, value in dict(
                        node_record.get("retrieved_decl_signatures") or {}
                    ).items()
                }
                for decl in list(node_record.get("retrieved_decl_names") or []):
                    clean = str(decl or "").strip()
                    if clean:
                        decl_records.append(
                            (
                                clean,
                                str(record_provenance.get(clean) or "").strip(),
                                str(record_signatures.get(clean) or "").strip(),
                            )
                        )
                for decl in list(
                    node_record.get("graph_retrieved_decl_quarantine_names") or []
                ):
                    clean = str(decl or "").strip()
                    if clean:
                        decl_records.append((clean, "", ""))
                for fact in list(node_record.get("retrieved_facts") or []):
                    clean = str(fact or "").strip()
                    if clean:
                        facts.append(clean[:1000])
            by_name: Dict[str, Tuple[str, str, str]] = {}
            for record in decl_records:
                name, policy_version, signature = record
                current = by_name.get(name)
                if current is None or (
                    policy_version == PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                    and current[1] != PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                ):
                    by_name[name] = (name, policy_version, signature)
            return list(by_name.values()), list(dict.fromkeys(facts))

        def evidence_hash(node: ProofStateNode, graph_node_id: str) -> str:
            graph_hash_getter = getattr(graph, "evidence_hash_for_node", None)
            if callable(graph_hash_getter):
                try:
                    graph_hash = str(graph_hash_getter(graph_node_id) or "").strip()
                    if graph_hash:
                        return graph_hash
                except Exception:
                    pass
            decl_records, facts = retrieval_evidence(graph_node_id)
            decls = [name for name, _policy, _signature in decl_records]
            proved_blockers = [
                blocker_id
                for blocker_id in self._canonical_blocker_ids(node.blocked_by_node_ids)
                if graph_nodes.get(blocker_id) is not None
                and getattr(graph_nodes[blocker_id], "status", "") == "proved"
            ]
            if not decls and not facts and not proved_blockers:
                return ""
            return text_hash(
                json.dumps(
                    {
                        "retrieved_decl_names": sorted(decls),
                        "retrieved_facts": sorted(facts),
                        "proved_blockers": sorted(proved_blockers),
                    },
                    sort_keys=True,
                )
            )

        def blockers_resolved(node: ProofStateNode) -> bool:
            blockers = self._canonical_blocker_ids(node.blocked_by_node_ids)
            if not blockers:
                return False
            for blocker_id in blockers:
                blocker = graph_nodes.get(blocker_id)
                if blocker is None or getattr(blocker, "status", "") != "proved":
                    return False
            return True

        for node in self.nodes.values():
            if target_ids and node.node_id not in target_ids:
                continue
            graph_node_id = graph_id_for(node)
            graph_node = graph_nodes.get(graph_node_id)
            detached_terminal_blockers = self._canonical_blocker_ids(
                terminal_blockers_by_graph_node.get(graph_node_id, [])
            )
            if detached_terminal_blockers:
                detached_set = set(detached_terminal_blockers)
                node.blocked_by_node_ids = [
                    blocker_id
                    for blocker_id in self._canonical_blocker_ids(
                        node.blocked_by_node_ids
                    )
                    if blocker_id not in detached_set
                ]
                if node.status == "blocked" and not node.blocked_by_node_ids:
                    node.status = "open"
                    node.blocker = "terminal graph blocker detached"
                    node.priority = self._priority(node)
                    self._refresh_priorities_for_neighbors(node.node_id)
                self.record_transition(
                    node_id=node.node_id,
                    source="proof_graph",
                    error_type="graph_terminal_blocker_detached",
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={"blocker_node_ids": detached_terminal_blockers},
                )
                records.append(
                    {
                        "node_id": node.node_id,
                        "verdict": "terminal_blocker_detached",
                        "blocker_node_ids": detached_terminal_blockers,
                    }
                )
            if graph_node is not None:
                metadata = dict(getattr(graph_node, "metadata", {}) or {})
                raw_blockers = metadata.get("blocked_by_node_ids")
                if isinstance(raw_blockers, list):
                    for raw in raw_blockers:
                        blocker_id = self._blocker_graph_node_id(str(raw or ""))
                        if blocker_id and blocker_id not in node.blocked_by_node_ids:
                            node.blocked_by_node_ids.append(blocker_id)
            for edge in outgoing_by_node.get(graph_node_id, []):
                if str(getattr(edge, "kind", "") or "") != "blocked_by":
                    continue
                blocker_id = self._blocker_graph_node_id(
                    str(getattr(edge, "target", "") or "")
                )
                if blocker_id and blocker_id not in node.blocked_by_node_ids:
                    node.blocked_by_node_ids.append(blocker_id)
            node.blocked_by_node_ids = self._canonical_blocker_ids(node.blocked_by_node_ids)

            decl_records, facts = retrieval_evidence(graph_node_id)
            graph_current_signatures = {
                signature
                for _decl, policy_version, signature in decl_records
                if policy_version == PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                and signature
            }
            authoritative_signature = str(node.retrieval_signature or "").strip()
            if authoritative_signature.startswith("graph_quarantine:"):
                authoritative_signature = ""
            if not authoritative_signature and len(graph_current_signatures) == 1:
                authoritative_signature = next(iter(graph_current_signatures))
            accepted_graph_decls = [
                (decl, signature)
                for decl, policy_version, signature in decl_records
                if decl
                and policy_version == PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                and authoritative_signature
                and signature == authoritative_signature
            ]
            quarantined_graph_decls = [
                decl
                for decl, policy_version, signature in decl_records
                if decl
                and (
                    policy_version != PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                    or not authoritative_signature
                    or signature != authoritative_signature
                )
            ]
            new_decls = [
                decl
                for decl, _signature in accepted_graph_decls
                if decl not in node.retrieved_decl_names
            ]
            new_quarantined_decls = [
                decl
                for decl in quarantined_graph_decls
                if decl not in node.graph_retrieved_decl_quarantine_names
                and decl not in node.retrieved_decl_names
            ]
            new_facts = [
                fact for fact in facts if fact and fact not in node.retrieved_facts
            ]
            if new_decls or new_quarantined_decls or new_facts:
                node.retrieval_attempted = True
                if new_decls:
                    node.retrieved_decl_execution_policy_version = (
                        PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                    )
                for decl, signature in accepted_graph_decls:
                    node.retrieved_decl_provenance[decl] = (
                        PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                    )
                    node.retrieved_decl_signatures[decl] = signature
                    if decl in new_decls:
                        node.retrieved_decl_names.append(decl)
                    if authoritative_signature and (
                        not node.retrieval_signature
                        or node.retrieval_signature.startswith("graph_quarantine:")
                    ):
                        node.retrieval_signature = authoritative_signature
                node.retrieved_decl_names = list(dict.fromkeys(node.retrieved_decl_names))[-12:]
                retained_decl_names = set(node.retrieved_decl_names)
                node.retrieved_decl_provenance = {
                    name: value
                    for name, value in node.retrieved_decl_provenance.items()
                    if name in retained_decl_names
                }
                node.retrieved_decl_signatures = {
                    name: value
                    for name, value in node.retrieved_decl_signatures.items()
                    if name in retained_decl_names
                }
                node.graph_retrieved_decl_quarantine_names = [
                    decl
                    for decl in node.graph_retrieved_decl_quarantine_names
                    if decl not in new_decls
                ]
                node.graph_retrieved_decl_quarantine_names.extend(
                    new_quarantined_decls
                )
                node.graph_retrieved_decl_quarantine_names = list(
                    dict.fromkeys(node.graph_retrieved_decl_quarantine_names)
                )[-48:]
                # A graph-only legacy page has been fully reconciled: it is an
                # attempted advisory scan with zero executable declarations.
                # Keep a current node stamp and a distinct signature so no
                # backend means no endless retrieval/decl-probe debt, while a
                # later real searcher still changes the desired signature and
                # refreshes normally.
                if (
                    new_quarantined_decls
                    and not node.retrieved_decl_names
                    and not node.retrieval_signature
                ):
                    node.retrieved_decl_execution_policy_version = (
                        PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
                    )
                    node.retrieval_signature = "graph_quarantine:" + text_hash(
                        "\n".join(node.graph_retrieved_decl_quarantine_names)
                    )
                node.retrieved_facts.extend(new_facts)
                node.retrieved_facts = list(dict.fromkeys(node.retrieved_facts))[-3:]
                node.retrieval_hit_count = max(
                    node.retrieval_hit_count,
                    len(node.retrieved_decl_names)
                    + len(node.graph_retrieved_decl_quarantine_names)
                    + len(node.retrieved_facts),
                )
                self.record_transition(
                    node_id=node.node_id,
                    source="proof_graph",
                    error_type="graph_retrieval_evidence_hydrated",
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={
                        "decl_names": list(new_decls),
                        "quarantined_decl_names": list(new_quarantined_decls),
                        "fact_count": len(new_facts),
                    },
                )
                records.append(
                    {
                        "node_id": node.node_id,
                        "verdict": "retrieval_evidence_hydrated",
                        "decl_names": list(new_decls),
                        "quarantined_decl_names": list(new_quarantined_decls),
                        "fact_count": len(new_facts),
                    }
                )

            current_evidence_hash = evidence_hash(node, graph_node_id)
            graph_status = (
                str(getattr(graph_node, "status", "") or "").strip()
                if graph_node is not None
                else ""
            )
            graph_status_blocks_local = (
                graph_status in {"blocked", "rejected", "failed"}
                and node.status != "proved"
            )
            rejected_has_new_evidence = (
                graph_status == "rejected"
                and bool(current_evidence_hash)
                and current_evidence_hash != node.rejection_evidence_hash
                and node.status != "failed"
            )
            if (
                graph_status == "blocked"
                and not blockers_resolved(node)
                and node.status != "blocked"
                and node.status != "proved"
            ):
                graph_metadata = (
                    dict(getattr(graph_node, "metadata", {}) or {})
                    if graph_node is not None
                    else {}
                )
                node.status = "blocked"
                node.blocker = (
                    str(graph_metadata.get("blocker") or "").strip()
                    or node.blocker
                    or "blocked by proof graph"
                )
                node.priority = self._priority(node)
                self._refresh_priorities_for_neighbors(node.node_id)
                self.record_transition(
                    node_id=node.node_id,
                    source="proof_graph",
                    error_type="graph_status_blocked_hydrated",
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={"graph_status": graph_status},
                )
                records.append(
                    {"node_id": node.node_id, "verdict": "graph_status_blocked"}
                )
            elif graph_status == "failed" and node.status not in {"failed", "proved"}:
                node.status = "failed"
                node.blocker = node.blocker or "failed in proof graph"
                node.priority = self._priority(node)
                self._refresh_priorities_for_neighbors(node.node_id)
                self.record_transition(
                    node_id=node.node_id,
                    source="proof_graph",
                    error_type="graph_status_failed_hydrated",
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={"graph_status": graph_status},
                )
                records.append(
                    {"node_id": node.node_id, "verdict": "graph_status_failed"}
                )
            elif (
                graph_status == "rejected"
                and not rejected_has_new_evidence
                and node.status not in {"failed", "rejected", "proved"}
            ):
                node.status = "rejected"
                if current_evidence_hash and not node.rejection_evidence_hash:
                    node.rejection_evidence_hash = current_evidence_hash
                node.blocker = node.blocker or "rejected in proof graph"
                node.priority = self._priority(node)
                self._refresh_priorities_for_neighbors(node.node_id)
                self.record_transition(
                    node_id=node.node_id,
                    source="proof_graph",
                    error_type="graph_status_rejected_hydrated",
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={"graph_status": graph_status},
                )
                records.append(
                    {"node_id": node.node_id, "verdict": "graph_status_rejected"}
                )

            if node.status == "blocked" and blockers_resolved(node):
                node.status = "open"
                node.blocker = "graph blocked_by dependencies resolved"
                node.priority = self._priority(node)
                self._refresh_priorities_for_neighbors(node.node_id)
                self.record_transition(
                    node_id=node.node_id,
                    source="proof_graph",
                    error_type="graph_blocked_by_resolved",
                    action=node.action,
                    blocker=node.blocker,
                    phase=phase,
                    turn_index=turn_index,
                    payload={"blocked_by_node_ids": list(node.blocked_by_node_ids)},
                )
                records.append(
                    {"node_id": node.node_id, "verdict": "blocked_by_resolved"}
                )
            elif (node.status == "rejected" or rejected_has_new_evidence) and current_evidence_hash:
                if current_evidence_hash != node.rejection_evidence_hash:
                    old_hash = node.rejection_evidence_hash
                    node.status = "open"
                    node.blocker = "new graph evidence after rejection"
                    node.rejection_evidence_hash = current_evidence_hash
                    node.priority = self._priority(node)
                    self._refresh_priorities_for_neighbors(node.node_id)
                    self.record_transition(
                        node_id=node.node_id,
                        source="proof_graph",
                        error_type="graph_rejected_new_evidence",
                        action=node.action,
                        blocker=node.blocker,
                        phase=phase,
                        turn_index=turn_index,
                        payload={
                            "old_evidence_hash": old_hash,
                            "new_evidence_hash": current_evidence_hash,
                        },
                    )
                    records.append(
                        {"node_id": node.node_id, "verdict": "rejected_reopened"}
                    )
            elif (
                current_evidence_hash
                and not node.rejection_evidence_hash
                and not graph_status_blocks_local
            ):
                node.rejection_evidence_hash = current_evidence_hash
        return records

    def _node_ready_for_assembly(self, node: ProofStateNode) -> bool:
        if (
            node.status != "open"
            or node.falsified
            or not node.assembly_attempt_groups
        ):
            return False
        return bool(self.ready_assembly_groups(node))

    def assembly_targets(
        self,
        target_node_ids: Sequence[str],
    ) -> List[ProofStateNode]:
        """Validate explicit assembly targets without capped frontier truncation."""

        out: List[ProofStateNode] = []
        seen: Set[str] = set()
        for raw_id in list(target_node_ids or ()):
            node_id = str(raw_id or "").strip()
            if not node_id or node_id in seen:
                continue
            seen.add(node_id)
            node = self.nodes.get(node_id)
            if node is not None and self._node_ready_for_assembly(node):
                out.append(node)
        return out

    def assembly_frontier(
        self,
        *,
        max_nodes: int = 3,
        graph: Any = None,
        mutate: bool = True,
        graph_records: Optional[Sequence[Dict[str, Any]]] = None,
    ) -> List[ProofStateNode]:
        """Return open parent nodes whose recorded proof stubs can be assembled.

        Child-goal proving and parent assembly are separate pieces of work.  A
        previous turn may have already proved all children, or graph
        rehydration may restore a ready assembly group before any new child is
        probed.  This frontier lets the executor spend search on those parent
        nodes directly instead of waiting for another child helper to be
        accepted in the same batch.
        """

        ready: List[ProofStateNode] = []
        seen: Set[str] = set()

        effective_graph_records = (
            list(graph_records)
            if graph_records is not None
            else None
        )
        if effective_graph_records is None:
            graph_frontier_getter = self._graph_frontier_records
            try:
                supports_mutate = (
                    "mutate" in inspect.signature(graph_frontier_getter).parameters
                )
            except (TypeError, ValueError):
                supports_mutate = False
            if supports_mutate:
                effective_graph_records = graph_frontier_getter(
                    graph,
                    max_items=max(4, int(max_nodes or 0) * 4),
                    mutate=mutate,
                )
            elif mutate:
                effective_graph_records = graph_frontier_getter(
                    graph,
                    max_items=max(4, int(max_nodes or 0) * 4),
                )
            else:
                effective_graph_records = []
        for record in effective_graph_records:
            if str(record.get("work_type") or "") != "assembly":
                continue
            node_id = str(record.get("node_id") or "").strip()
            node = self.nodes.get(node_id)
            if node is None or node.node_id in seen:
                continue
            if self._node_ready_for_assembly(node):
                ready.append(node)
                seen.add(node.node_id)

        for node in self.nodes.values():
            if node.node_id in seen:
                continue
            if self._graph_status_suppresses_local_work(graph, node.node_id):
                continue
            if self._node_ready_for_assembly(node):
                ready.append(node)
                seen.add(node.node_id)
        ready.sort(
            key=lambda node: (
                0 if node.node_id == self.root_node_id else 1,
                -node.priority,
                node.node_id,
            )
        )
        return ready[: max(0, int(max_nodes or 0))]

    def work_frontier(
        self,
        *,
        max_items: int = 8,
        offset: int = 0,
        graph: Any = None,
        source_filter: str = "",
        include_child_llm_prove: bool = False,
        max_recursive_attempts_per_node: int = 0,
        max_recursive_giveups_per_cluster_per_node: int = 0,
        retrieval_needed_node_ids: Optional[Sequence[str]] = None,
        retrieval_context_stamps: Optional[Mapping[str, str]] = None,
        retrieval_available: bool = False,
        decl_application_context_hashes: Optional[Mapping[str, str]] = None,
        mutate: bool = True,
    ) -> List[ProofStateWorkItem]:
        """Return executable work derived from the current graph frontier.

        This is a typed scheduler view over the graph state: parents ready for
        deterministic assembly are separate from child-goal retrieval/probing,
        and root failures remain explicit repair work instead of transcript text.
        """

        start = max(0, int(offset or 0))
        limit = max(0, int(max_items or 0))
        if limit <= 0:
            return []
        if graph is not None and mutate:
            self.hydrate_graph_state_nodes(graph)
        source_limit = start + limit
        graph_node_count = len(getattr(graph, "nodes", {}) or {}) if graph is not None else 0
        local_scan_limit = max(
            source_limit,
            len(getattr(self, "nodes", {}) or {}),
            graph_node_count,
        )
        items: List[ProofStateWorkItem] = []
        seen: Set[Tuple[str, str, str]] = set()
        retrieval_refresh_ids = {
            str(node_id or "").strip()
            for node_id in list(retrieval_needed_node_ids or ())
            if str(node_id or "").strip()
        }
        retrieval_refresh_stamps = {
            str(node_id or "").strip(): str(stamp or "").strip()
            for node_id, stamp in dict(retrieval_context_stamps or {}).items()
            if str(node_id or "").strip() and str(stamp or "").strip()
        }
        retrieval_refresh_ids.update(retrieval_refresh_stamps)
        decl_context_hashes = {
            str(node_id or "").strip(): str(context_hash or "").strip()
            for node_id, context_hash in dict(
                decl_application_context_hashes or {}
            ).items()
            if str(node_id or "").strip() and str(context_hash or "").strip()
        }
        residual_required, residual_authorized, _residual_route_validity = (
            self._residual_goal_attestation_validation()
        )

        if mutate and decl_context_hashes:
            for node_id, context_hash in decl_context_hashes.items():
                node = self.nodes.get(node_id)
                if node is None or node.kind != "child_goal":
                    continue
                proof_state_begin_decl_application_batch(node, context_hash)

        def _pending_decl_names_for_node(node: ProofStateNode) -> List[str]:
            return proof_state_decl_application_pending_names(
                node,
                context_hash=decl_context_hashes.get(node.node_id, ""),
            )

        def _decl_probe_ready(node: ProofStateNode) -> bool:
            pending_acceptance = dict(
                getattr(node, "pending_helper_acceptance", {}) or {}
            )
            return bool(
                str(pending_acceptance.get("source") or "").startswith(
                    "decl_application:"
                )
                or _pending_decl_names_for_node(node)
            )

        def add(
            node: ProofStateNode,
            work_type: str,
            *,
            source: str = "legacy",
            graph_record: Optional[Dict[str, Any]] = None,
        ) -> None:
            # A child goal proven FALSE (Lean-checked + axiom-audited negation)
            # can never be closed; suppress ALL proving-oriented work on it
            # (decl_probe, child_llm_prove, retrieval, tactic_swarm,
            # formal_state_expand) across both the local and graph frontier lanes,
            # durably (independent of the status/reopen machinery).
            if (
                getattr(node, "kind", "") == "child_goal"
                and getattr(node, "falsified", False)
            ):
                return
            if (
                getattr(node, "kind", "") == "child_goal"
                and node.node_id in residual_required
                and node.node_id not in residual_authorized
            ):
                return
            if source != "graph" and self._graph_status_suppresses_local_work(
                graph,
                node.node_id,
            ):
                return
            graph_record = dict(graph_record or {})
            assembly_id = str(graph_record.get("assembly_id") or "").strip()
            key = (
                node.node_id,
                work_type,
                assembly_id if work_type == "assembly" else "",
            )
            if key in seen:
                return
            if source != "graph" and (node.node_id, work_type, "") in seen:
                return
            seen.add(key)
            if source == "graph" and work_type == "assembly":
                seen.add((node.node_id, work_type, ""))
            target_hash = (
                node.goal.normalized_statement_hash
                if node.goal is not None
                else text_hash(node.target)
            )
            priority = float(getattr(node, "priority", 0.0) or 0.0)
            if source == "graph" and "priority" in graph_record:
                try:
                    priority = float(graph_record.get("priority") or 0.0)
                except (TypeError, ValueError):
                    priority = float(getattr(node, "priority", 0.0) or 0.0)
            assembly_version: Dict[str, Any] = {}
            if work_type == "assembly":
                assembly_version = self.assembly_work_version(
                    node,
                    assembly_id=assembly_id,
                )
            pending_decl_names = _pending_decl_names_for_node(node)
            pending_decl_identity_parts = list(pending_decl_names)
            pending_acceptance = dict(
                getattr(node, "pending_helper_acceptance", {}) or {}
            )
            if str(pending_acceptance.get("source") or "").startswith(
                "decl_application:"
            ):
                pending_decl_identity_parts.append(
                    "acceptance:"
                    + text_hash(
                        json.dumps(
                            pending_acceptance,
                            sort_keys=True,
                            default=str,
                        )
                    )
                )
            items.append(
                ProofStateWorkItem(
                    node_id=node.node_id,
                    work_type=work_type,
                    action=node.action,
                    priority=priority,
                    target_hash=target_hash,
                    blocker=node.blocker,
                    dependencies=tuple(node.dependencies),
                    source=str(source or "legacy"),
                    graph_node_id=str(graph_record.get("graph_node_id") or ""),
                    assembly_id=assembly_id,
                    child_state_node_ids=tuple(
                        str(item or "").strip()
                        for item in list(graph_record.get("child_state_node_ids") or ())
                        if str(item or "").strip()
                    ),
                    unblocked_by_graph=bool(graph_record.get("unblocked_by_graph")),
                    reopened_by_new_evidence=bool(
                        graph_record.get("reopened_by_new_evidence")
                    ),
                    evidence_hash=str(
                        graph_record.get("evidence_hash")
                        or getattr(node, "rejection_evidence_hash", "")
                        or ""
                    ),
                    retrieval_signature=str(
                        getattr(node, "retrieval_signature", "") or ""
                    ),
                    retrieval_context_stamp=(
                        retrieval_refresh_stamps.get(node.node_id, "")
                        if work_type == "retrieval"
                        else ""
                    ),
                    retrieved_decl_names_hash=(
                        text_hash("\n".join(node.retrieved_decl_names))
                        if getattr(node, "retrieved_decl_names", None)
                        else ""
                    ),
                    decl_application_pending_hash=(
                        text_hash("\n".join(pending_decl_identity_parts))
                        if pending_decl_identity_parts
                        else ""
                    ),
                    helper_acceptance_request_hash=(
                        str(
                            pending_acceptance.get("acceptance_request_hash")
                            or pending_acceptance.get("verifier_retry_key")
                            or ""
                        )
                        if work_type == "helper_acceptance"
                        else ""
                    ),
                    decl_application_signature=str(
                        getattr(node, "decl_application_signature", "") or ""
                    ),
                    residual_attestation_hash=(
                        str(
                            dict(
                                node.pending_residual_goal_extraction or {}
                            ).get("request_context_hash")
                            or ""
                        )
                        if work_type == "residual_goal_extraction"
                        else (
                            text_hash(
                                json.dumps(
                                    node.residual_goal_attestation,
                                    sort_keys=True,
                                    separators=(",", ":"),
                                    ensure_ascii=True,
                                )
                            )
                            if node.residual_goal_attestation
                            else ""
                        )
                    ),
                    proof_stub_hash=str(graph_record.get("proof_stub_hash") or ""),
                    assembly_witness_hash=str(
                        assembly_version.get("assembly_witness_hash") or ""
                    ),
                    assembly_group_status=str(
                        assembly_version.get("assembly_group_status") or ""
                    ),
                    projection_turn_index=(
                        _proof_state_durable_nonnegative_int(
                            graph_record.get("projection_turn_index")
                        )
                    ),
                    target_statement=str(graph_record.get("target_statement") or ""),
                    execution_scope_schema_version=max(
                        1,
                        _proof_state_durable_nonnegative_int(
                            graph_record.get("execution_scope_schema_version")
                        ),
                    ),
                    execution_scope_id=str(
                        graph_record.get("execution_scope_id") or ""
                    ),
                    execution_scope_digest=str(
                        graph_record.get("execution_scope_digest") or ""
                    ),
                    execution_target_sha256=str(
                        graph_record.get("execution_target_sha256") or ""
                    ),
                    execution_target_available=bool(
                        graph_record.get("execution_target_available")
                    ),
                    execution_materialization_seed_sha256=str(
                        graph_record.get("execution_materialization_seed_sha256")
                        or ""
                    ),
                    execution_target_graph_node_id=str(
                        graph_record.get("execution_target_graph_node_id") or ""
                    ),
                    execution_environment_hash=str(
                        graph_record.get("execution_environment_hash") or ""
                    ),
                    execution_contract_identity=str(
                        graph_record.get("execution_contract_identity") or ""
                    ),
                    execution_proposition_identity=str(
                        graph_record.get("execution_proposition_identity") or ""
                    ),
                    execution_helper_context_hash=str(
                        graph_record.get("execution_helper_context_hash") or ""
                    ),
                    execution_currentness_digest=str(
                        graph_record.get("execution_currentness_digest") or ""
                    ),
                    exact_target_statement=str(
                        graph_record.get("exact_target_statement")
                        or graph_record.get("target_statement")
                        or ""
                    ),
                    consumer_bindings=tuple(
                        dict(item)
                        for item in list(graph_record.get("consumer_bindings") or [])
                        if isinstance(item, Mapping)
                    ),
                    primary_consumer_binding=dict(
                        graph_record.get("primary_consumer_binding") or {}
                    ),
                    cognition_scope_digest=str(
                        graph_record.get("cognition_scope_digest") or ""
                    ),
                    cognition_currentness_digest=str(
                        graph_record.get("cognition_currentness_digest") or ""
                    ),
                    obligation_reason=str(
                        graph_record.get("obligation_reason") or ""
                    ),
                    source_phase=str(graph_record.get("source_phase") or ""),
                    missing_dependency=str(
                        graph_record.get("missing_dependency") or ""
                    ),
                    formalization_required=bool(
                        graph_record.get("formalization_required")
                    ),
                    graph_record={
                        **dict(graph_record),
                        **assembly_version,
                    },
                )
            )

        def add_graph_record(record: Dict[str, Any]) -> None:
            work_type = str(record.get("work_type") or "").strip()
            node_id = str(record.get("node_id") or "").strip()
            if not work_type or not node_id:
                return
            local_node_id = node_id
            if local_node_id == "proof_state:root":
                local_node_id = self.root_node_id
            elif local_node_id.startswith("proof_state:"):
                local_node_id = local_node_id.removeprefix("proof_state:")
            graph_node_id = str(record.get("graph_node_id") or node_id).strip()
            aliases = getattr(self, "_graph_state_node_aliases", {}) or {}
            aliased_node_id = str(
                aliases.get(graph_node_id) or aliases.get(local_node_id) or ""
            ).strip()
            if aliased_node_id and aliased_node_id in self.nodes:
                record = dict(record)
                record.setdefault("graph_node_id", graph_node_id)
                record["aliased_graph_state_node_id"] = local_node_id
                record["node_id"] = aliased_node_id
                node_id = aliased_node_id
                local_node_id = aliased_node_id
            if local_node_id != node_id and local_node_id in self.nodes:
                record = dict(record)
                record.setdefault("graph_node_id", node_id)
                record["node_id"] = local_node_id
                node_id = local_node_id
            node = self.nodes.get(node_id)
            if node is None:
                graph_native_work = {
                    "formalize_claim",
                    "formalize_missing_obligation",
                    "prove_claim_variant",
                    "mine_missing_obligation",
                    "route_replan",
                    "assemble_route",
                    "materialize_replay_source",
                    "target_integrity_adjudication",
                }
                if work_type not in graph_native_work:
                    return
                graph_node_id = str(record.get("graph_node_id") or node_id).strip()
                key = (graph_node_id, work_type, str(record.get("target_hash") or ""))
                if key in seen:
                    return
                seen.add(key)
                items.append(
                    ProofStateWorkItem(
                        node_id=graph_node_id,
                        work_type=work_type,
                        action=str(record.get("action") or work_type),
                        priority=_proof_state_durable_finite_float(
                            record.get("priority")
                        ),
                        target_hash=str(record.get("target_hash") or ""),
                        blocker=str(record.get("blocker") or ""),
                        dependencies=tuple(
                            str(item or "").strip()
                            for item in list(record.get("dependencies") or ())
                            if str(item or "").strip()
                        ),
                        source="graph",
                        graph_node_id=graph_node_id,
                        evidence_hash=str(record.get("evidence_hash") or ""),
                        projection_turn_index=(
                            _proof_state_durable_nonnegative_int(
                                record.get("projection_turn_index")
                            )
                        ),
                        target_statement=str(record.get("target_statement") or ""),
                        execution_scope_schema_version=max(
                            1,
                            _proof_state_durable_nonnegative_int(
                                record.get("execution_scope_schema_version")
                            ),
                        ),
                        execution_scope_id=str(
                            record.get("execution_scope_id") or ""
                        ),
                        execution_scope_digest=str(
                            record.get("execution_scope_digest") or ""
                        ),
                        execution_target_sha256=str(
                            record.get("execution_target_sha256") or ""
                        ),
                        execution_target_available=bool(
                            record.get("execution_target_available")
                        ),
                        execution_materialization_seed_sha256=str(
                            record.get("execution_materialization_seed_sha256")
                            or ""
                        ),
                        execution_target_graph_node_id=str(
                            record.get("execution_target_graph_node_id") or ""
                        ),
                        execution_environment_hash=str(
                            record.get("execution_environment_hash") or ""
                        ),
                        execution_contract_identity=str(
                            record.get("execution_contract_identity") or ""
                        ),
                        execution_proposition_identity=str(
                            record.get("execution_proposition_identity") or ""
                        ),
                        execution_helper_context_hash=str(
                            record.get("execution_helper_context_hash") or ""
                        ),
                        execution_currentness_digest=str(
                            record.get("execution_currentness_digest") or ""
                        ),
                        exact_target_statement=str(
                            record.get("exact_target_statement")
                            or record.get("target_statement")
                            or ""
                        ),
                        consumer_bindings=tuple(
                            dict(item)
                            for item in list(record.get("consumer_bindings") or [])
                            if isinstance(item, Mapping)
                        ),
                        primary_consumer_binding=dict(
                            record.get("primary_consumer_binding") or {}
                        ),
                        cognition_scope_digest=str(
                            record.get("cognition_scope_digest") or ""
                        ),
                        cognition_currentness_digest=str(
                            record.get("cognition_currentness_digest") or ""
                        ),
                        obligation_reason=str(
                            record.get("obligation_reason") or ""
                        ),
                        source_phase=str(record.get("source_phase") or ""),
                        missing_dependency=str(
                            record.get("missing_dependency") or ""
                        ),
                        formalization_required=bool(
                            record.get("formalization_required")
                        ),
                        graph_record=dict(record),
                    )
                )
                return
            # B6 fix (2026-05-11): the graph emits work records with
            # ``unblocked_by_graph=True`` for nodes whose graph status
            # is ``blocked`` but whose blocker has been resolved (the
            # graph's causal readiness signal). ``refresh_graph_readiness``
            # normally reconciles local status before ``work_frontier``
            # runs, but the session's call site at session.py:725-748
            # silently swallows refresh exceptions. When that happens,
            # local node.status stays ``blocked`` while the graph
            # correctly says the work is ready — and the per-work_type
            # local-status re-gate below would silently drop the work.
            # Honor the graph signal: when ``unblocked_by_graph`` is
            # carried in the record, treat ``blocked`` local status as
            # acceptable so the work flows through. Downstream actions
            # reconcile the local state; the scheduler must not be the
            # only mechanism that blocks the unblock path. Terminal
            # statuses (rejected/failed/proved/obsolete) remain
            # respected — the graph's unblock claim does not override
            # a definitive local close.
            unblocked = bool(record.get("unblocked_by_graph"))
            reopened = bool(record.get("reopened_by_new_evidence"))
            acceptable_local_statuses = {"open"}
            if unblocked:
                acceptable_local_statuses.add("blocked")
            if reopened:
                acceptable_local_statuses.add("rejected")
            if work_type == "assembly":
                selected_assembly_id = str(record.get("assembly_id") or "").strip()
                if node.status in acceptable_local_statuses and self.ready_assembly_groups(
                    node,
                    assembly_id=selected_assembly_id,
                ):
                    add(node, "assembly", source="graph", graph_record=record)
            elif work_type == "lemma_dag_decomposition":
                if (
                    node.kind == "decomposition_task"
                    and node.status in acceptable_local_statuses
                ):
                    add(node, "lemma_dag_decomposition", source="graph", graph_record=record)
            elif work_type == "retrieval":
                if (
                    retrieval_available
                    and node.kind == "child_goal"
                    and node.status in acceptable_local_statuses
                    and (
                        not node.retrieval_attempted
                        or node.node_id in retrieval_refresh_ids
                    )
                ):
                    add(node, "retrieval", source="graph", graph_record=record)
            elif work_type == "decl_probe":
                if (
                    node.kind == "child_goal"
                    and node.status in acceptable_local_statuses
                    and node.node_id not in retrieval_refresh_ids
                    and _decl_probe_ready(node)
                ):
                    add(node, "decl_probe", source="graph", graph_record=record)
            elif work_type == "tactic_swarm":
                if (
                    node.kind == "child_goal"
                    and node.status in acceptable_local_statuses
                ):
                    add(node, "tactic_swarm", source="graph", graph_record=record)
            elif work_type == "formal_state_expand":
                if (
                    node.kind == "child_goal"
                    and node.status in acceptable_local_statuses
                    and int(getattr(node, "tactic_attempts", 0) or 0) > 0
                ):
                    add(
                        node,
                        "formal_state_expand",
                        source="graph",
                        graph_record=record,
                    )
            elif work_type == "child_llm_prove":
                # B8 fix (2026-05-11): consume the graph-source
                # ``child_llm_prove`` work_type. Mirrors the legacy
                # local-path cap check at the unified frontier loop
                # (attempt cap + per-cluster giveup cap). Without this
                # branch, child_llm_prove records emitted by the graph
                # would be silently dropped — defeating the B8 emission
                # fix. Caller-driven gating: only fires when
                # ``include_child_llm_prove`` is True AND the per-node
                # attempt/giveup budgets are not yet exhausted. Ordering
                # below keeps this expensive LLM lane behind retrieval,
                # decl-probe, and tactic-swarm work for the same child.
                if not include_child_llm_prove:
                    return
                if (
                    node.kind != "child_goal"
                    or node.status not in acceptable_local_statuses
                ):
                    return
                attempts = int(getattr(node, "recursive_attempts", 0) or 0)
                cap = int(max_recursive_attempts_per_node or 0)
                giveup_cap = int(max_recursive_giveups_per_cluster_per_node or 0)
                giveup_counts = (
                    getattr(node, "recursive_giveup_counts", None) or {}
                )
                giveup_blocked = giveup_cap > 0 and any(
                    int(count or 0) >= giveup_cap for count in giveup_counts.values()
                )
                if (cap <= 0 or attempts < cap) and not giveup_blocked:
                    add(node, "child_llm_prove", source="graph", graph_record=record)
            elif work_type == "root_repair":
                if (
                    node.node_id == self.root_node_id
                    and node.status in acceptable_local_statuses
                ):
                    # B7 fix extension (2026-05-11): the original B7
                    # guard only suppressed the LEGACY root_repair
                    # emission site. The graph-source path here can
                    # ALSO emit root_repair concurrently with the
                    # legacy assembly emission, producing the same
                    # duplicate-dispatch hazard. The structural check
                    # ``_node_ready_for_assembly(root)`` is independent
                    # of emission order; if assembly is viable, the
                    # repair lane is moot regardless of which side
                    # emits first.
                    if not self._node_ready_for_assembly(node):
                        add(node, "root_repair", source="graph", graph_record=record)

        # A successful parent stub whose typed residual extraction deferred is
        # verifier-only continuation work. Surface it before any provider,
        # retrieval, declaration, or tactic lane so the paid attempt is never
        # consumed a second time. Internal target/environment staleness clears
        # the request; helper/preamble currentness is checked by the extractor
        # against ``request_context_hash``.
        for pending_node in self.nodes.values():
            pending_helper = dict(
                getattr(pending_node, "pending_helper_acceptance", {}) or {}
            )
            helper_retry_key = str(
                pending_helper.get("verifier_retry_key") or ""
            ).strip()
            if (
                pending_node.status == "open"
                and
                str(pending_helper.get("helper_block") or "").strip()
                and str(pending_helper.get("target_hash") or "")
                == text_hash(str(pending_node.target or ""))
                and (
                    not helper_retry_key
                    or self.verifier_retry_status(
                        pending_node,
                        helper_retry_key,
                    )
                    != "cooling"
                )
            ):
                add(pending_node, "helper_acceptance")

        for pending_node in self.nodes.values():
            if pending_node.status != "open":
                continue
            pending_status = self.pending_residual_goal_extraction_status(
                pending_node
            )
            if pending_status in {"pending", "rematerialize"}:
                pending_record = dict(
                    pending_node.pending_residual_goal_extraction or {}
                )
                retry_key = str(
                    pending_record.get("verifier_retry_key") or ""
                ).strip()
                if (
                    pending_status == "rematerialize"
                    or not retry_key
                    or self.verifier_retry_status(pending_node, retry_key)
                    != "cooling"
                ):
                    add(pending_node, "residual_goal_extraction")
            elif mutate and pending_status in {"stale", "terminal"}:
                self.clear_pending_residual_goal_extraction(pending_node)

        graph_frontier_getter = self._graph_frontier_records
        try:
            graph_frontier_parameters = inspect.signature(
                graph_frontier_getter
            ).parameters
            graph_frontier_supports_mutate = "mutate" in graph_frontier_parameters
            graph_frontier_supports_record_errors = (
                "record_errors" in graph_frontier_parameters
            )
        except (TypeError, ValueError):
            graph_frontier_supports_mutate = False
            graph_frontier_supports_record_errors = False
        graph_frontier_mutate = bool(mutate)
        if graph_frontier_supports_mutate and graph_frontier_supports_record_errors:
            graph_frontier_records = self._graph_frontier_records(
                graph,
                max_items=max(8, int(local_scan_limit or 0) * 4),
                mutate=graph_frontier_mutate,
                record_errors=mutate,
            )
        elif graph_frontier_supports_mutate:
            # Older overrides cannot separate snapshot reconciliation from
            # diagnostic writes. Keep observational calls non-mutating.
            graph_frontier_records = self._graph_frontier_records(
                graph,
                max_items=max(8, int(local_scan_limit or 0) * 4),
                mutate=mutate,
            )
        elif not mutate:
            graph_frontier_records = []
        else:
            # Preserve compatibility with extension overrides from before the
            # observational keyword was introduced. Dispatch mode retains its
            # historical write authority; read-only mode above fails closed.
            graph_frontier_records = self._graph_frontier_records(
                graph,
                max_items=max(8, int(local_scan_limit or 0) * 4),
            )
        for record in graph_frontier_records:
            add_graph_record(record)

        for node in self.assembly_frontier(
            max_nodes=local_scan_limit,
            graph=graph,
            mutate=mutate,
            graph_records=graph_frontier_records,
        ):
            add(node, "assembly")
        for node in self.frontier(max_nodes=local_scan_limit):
            if node.kind == "decomposition_task":
                add(node, "lemma_dag_decomposition")
        for node in self.child_frontier(max_nodes=local_scan_limit):
            if include_child_llm_prove:
                attempts = int(getattr(node, "recursive_attempts", 0) or 0)
                cap = int(max_recursive_attempts_per_node or 0)
                giveup_cap = int(max_recursive_giveups_per_cluster_per_node or 0)
                giveup_counts = getattr(node, "recursive_giveup_counts", None) or {}
                giveup_blocked = (
                    giveup_cap > 0
                    and any(int(count or 0) >= giveup_cap for count in giveup_counts.values())
                )
                if (cap <= 0 or attempts < cap) and not giveup_blocked:
                    add(node, "child_llm_prove")
            if (
                retrieval_available
                and (
                    not node.retrieval_attempted
                    or node.node_id in retrieval_refresh_ids
                )
            ):
                add(node, "retrieval")
            if (
                node.node_id not in retrieval_refresh_ids
                and _decl_probe_ready(node)
            ):
                add(node, "decl_probe")
            add(node, "tactic_swarm")
            if int(getattr(node, "tactic_attempts", 0) or 0) > 0:
                # Goal-conditioned search is a typed executable lane, not a
                # narrative/static afterthought.  It follows the cheap tactic
                # swarm and precedes another unconstrained recursive LLM turn.
                add(node, "formal_state_expand")
        root = self.nodes.get(self.root_node_id)
        if root is not None and root.status == "open":
            # B7 fix (2026-05-11): suppress root_repair emission when
            # the same node has already emitted ``assembly`` work this
            # turn. Both work items target the root with different
            # work_types — the per-node ``seen`` tuple
            # ``(node_id, work_type, assembly_id)`` makes them distinct,
            # so without this guard the LLM-repair lane and the
            # deterministic-assembly lane would BOTH receive the same
            # node. Currently latent because the dispatcher maps
            # ``root_repair`` to None, but a future root_repair action
            # would dispatch the root twice per turn against the same
            # state — wasted Lean spend. Repair work is structurally
            # only meaningful when assembly is NOT a viable closure
            # path; if assembly is ready, defer to it.
            assembly_already_emitted_for_root = any(
                key[0] == root.node_id and key[1] == "assembly"
                for key in seen
            )
            if not assembly_already_emitted_for_root:
                add(root, "root_repair")
        alternate_to_pending_exists = any(
            item.work_type not in {"residual_goal_extraction", "root_repair"}
            for item in items
        )

        def durable_retry_count(value: Any) -> int:
            if isinstance(value, bool):
                return 0
            try:
                return max(0, int(value or 0))
            except (TypeError, ValueError):
                return 0

        def work_order(item: ProofStateWorkItem) -> int:
            pending_node = self.nodes.get(item.node_id)
            if (
                item.work_type == "child_llm_prove"
                and pending_node is not None
                and str(
                    getattr(
                        pending_node,
                        "falsification_advisory_candidate_hash",
                        "",
                    )
                    or ""
                ).strip()
            ):
                # A checked-but-uncertified counterexample should steer the
                # next LLM quantum toward completing the negation certificate.
                # Keep decl/tactic work in the frontier as a fallback.
                return 4
            if item.work_type == "residual_goal_extraction":
                pending_record = dict(
                    getattr(
                        pending_node,
                        "pending_residual_goal_extraction",
                        {},
                    )
                    or {}
                )
                # The first verifier replay remains immediate. If that exact
                # durable request has already deferred, rotate one dispatch to
                # other executable work instead of starving every frontier
                # family. With no alternative it remains the first route.
                if (
                    alternate_to_pending_exists
                    and durable_retry_count(pending_record.get("retry_count")) > 0
                ):
                    return 9
                return -2
            if item.work_type == "helper_acceptance":
                return -2
            if item.work_type in {"decl_probe", "tactic_swarm"}:
                pending_acceptance = dict(
                    getattr(pending_node, "pending_helper_acceptance", {}) or {}
                )
                pending_target_hash = text_hash(
                    str(getattr(pending_node, "target", "") or "")
                )
                if (
                    str(pending_acceptance.get("helper_block") or "").strip()
                    and str(pending_acceptance.get("target_hash") or "")
                    == pending_target_hash
                    and durable_retry_count(
                        pending_acceptance.get("attempt_count")
                    )
                    > 0
                ):
                    # A paid helper verification is immediate once. Repeated
                    # infrastructure deferrals rotate behind other work rather
                    # than monopolizing the deterministic closure action.
                    return 9
            if (
                item.work_type == "formalize_missing_obligation"
                and bool((item.graph_record or {}).get("formalization_statement_pending"))
                and not str(item.target_statement or "").strip()
            ):
                return 6
            return {
                    "materialize_replay_source": -1,
                    "helper_acceptance": -1,
                    "assembly": 0,
                    "assemble_route": 0,
                    "lemma_dag_decomposition": 1,
                    "route_replan": 2,
                    "mine_missing_obligation": 2,
                    "prove_claim_variant": 3,
                    "formalize_claim": 3,
                    "formalize_missing_obligation": 3,
                    "retrieval": 5,
                    "decl_probe": 5,
                    "tactic_swarm": 5,
                    "formal_state_expand": 6,
                    "child_llm_prove": 7,
                    "root_repair": 8,
                }.get(item.work_type, 4)

        items.sort(
            key=lambda item: (
                work_order(item),
                -item.priority,
                item.node_id,
                item.work_type,
            )
        )
        if str(source_filter or "").strip():
            wanted_source = str(source_filter or "").strip()
            items = [item for item in items if item.source == wanted_source]
        return items[start : start + limit]

    def helper_name_for_node(self, node: ProofStateNode, dossier: ProofDossier) -> str:
        base = re.sub(r"[^A-Za-z0-9_'.]", "_", self.theorem_name)
        base = re.sub(r"_+", "_", base).strip("_") or "mini"
        kind_part = re.sub(r"[^A-Za-z0-9_'.]", "_", str(node.kind or "node"))
        kind_part = re.sub(r"_+", "_", kind_part).strip("_") or "node"
        node_part = f"{kind_part}_{text_hash(node.node_id)[:10]}"
        candidate = f"mini_{base}_ps_{node_part}"[:96].rstrip("_")
        if not candidate or candidate[0].isdigit():
            candidate = f"mini_{candidate}"
        out = candidate
        suffix = 2
        while dossier.has_helper(out):
            tail = f"_{suffix}"
            out = candidate[: max(1, 96 - len(tail))].rstrip("_") + tail
            suffix += 1
        return out

    def _prompt_node_label(
        self,
        node: ProofStateNode,
        index: int,
        *,
        session_scope: str = "problem",
    ) -> str:
        if node.node_id == self.root_node_id:
            if str(session_scope or "problem").strip() in {"subgoal", "branch"}:
                return "local child target"
            return "root theorem"
        kind = str(node.kind or "work item").replace("_", " ")
        if int(index or 0) <= 0:
            return kind
        return f"{kind} #{max(1, int(index or 1))}"

    def _sanitize_internal_node_ids_for_prompt(
        self,
        text: str,
        label_by_node_id: Dict[str, str],
        *,
        preserve_code_spans: bool = False,
    ) -> str:
        def sanitize_segment(segment: str) -> str:
            out = str(segment or "")
            for node_id, label in sorted(
                label_by_node_id.items(),
                key=lambda item: len(item[0]),
                reverse=True,
            ):
                if not node_id or node_id == self.root_node_id:
                    continue
                out = re.sub(
                    r"(?<![A-Za-z0-9_'.])"
                    + re.escape(node_id)
                    + r"(?![A-Za-z0-9_'])",
                    label,
                    out,
                )
            return out

        raw = str(text or "")
        if not raw:
            return ""
        if not preserve_code_spans:
            return sanitize_segment(raw)
        spans = re.split(
            r"(```.*?```|`[^`\n]*`|'[^'\n]*'|\"[^\"\n]*\")",
            raw,
            flags=re.DOTALL,
        )
        if len(spans) <= 1:
            return sanitize_segment(raw)
        out_parts: List[str] = []
        for index, part in enumerate(spans):
            if index % 2 == 1:
                out_parts.append(part)
            else:
                out_parts.append(sanitize_segment(part))
        return "".join(out_parts)

    def render_context(
        self,
        *,
        max_nodes: int = 5,
        active_root_targets: Sequence[Mapping[str, Any]] = (),
        graph: Any = None,
        session_scope: str = "problem",
    ) -> str:
        normalized_session_scope = str(session_scope or "problem").strip() or "problem"
        local_child_scope = normalized_session_scope in {"subgoal", "branch"}

        def localize_authority_language(text: str) -> str:
            rendered = str(text or "")
            if not local_child_scope:
                return rendered
            replacements = (
                (r"\bparent/root theorem\b", "local child target"),
                (r"\broot theorem\b", "local child target"),
                (r"\broot assembly\b", "local child target assembly"),
                (r"\broot repair\b", "local target repair"),
                (r"\broot node\b", "local target node"),
                (r"\bassemble the root\b", "assemble the local child target"),
                (r"\bretry the root\b", "retry the local child target"),
            )
            for pattern, replacement in replacements:
                rendered = re.sub(pattern, replacement, rendered, flags=re.IGNORECASE)
            return rendered
        frontier = self.frontier(max_nodes=max_nodes)
        graph_work = (
            self.work_frontier(
                max_items=max_nodes,
                graph=graph,
                source_filter="graph",
            )
            if graph is not None
            else []
        )
        if not frontier and not graph_work:
            return ""
        graph_work_records = []
        for item in graph_work:
            try:
                graph_work_records.append(
                    item.to_record(
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                        official_answer_visible_to_llm=(
                            not self.suppress_solution_placeholders
                        ),
                    )
                )
            except Exception:
                graph_work_records.append({})
        scoped_formalization_active = any(
            str(record.get("work_type") or "") == "formalize_missing_obligation"
            and bool(record.get("formalization_required"))
            for record in graph_work_records
            if isinstance(record, Mapping)
        )
        active_root_target = ""
        active_items = [
            item
            for item in list(active_root_targets or ())
            if isinstance(item, Mapping)
            and str(item.get("working_target") or item.get("target") or "").strip()
        ]
        if len(active_items) == 1:
            active_item = active_items[0]
            target_text = str(
                active_item.get("working_target")
                or active_item.get("target")
                or ""
            ).strip()
            active_hypotheses = [
                str(hyp or "").strip()
                for hyp in list(active_item.get("hypotheses") or ())
                if str(hyp or "").strip()
            ]
            if active_hypotheses:
                target_text = self._statement_from_context(
                    target_text,
                    active_hypotheses,
                )
            active_root_target = " ".join(target_text.split()).strip()
        label_by_node_id = {
            node.node_id: self._prompt_node_label(
                node,
                0,
                session_scope=normalized_session_scope,
            )
            for node in self.nodes.values()
            if node.node_id
        }
        label_by_node_id.update({
            node.node_id: self._prompt_node_label(
                node,
                index,
                session_scope=normalized_session_scope,
            )
            for index, node in enumerate(frontier, start=1)
            if node.node_id
        })
        if local_child_scope:
            lines = [
                "Proof-state scheduler:",
                "- This is a local child session. Its `local child target` is not the parent theorem.",
                "- Work the highest-priority open node. Treat each open node as a local-theory obligation: prove smaller child nodes as reusable named helpers, manufacture smaller child obligations when Lean exposes them, then assemble the local child target from verified helpers.",
                "- A successful local `try_lean` check closes only this child target and authorizes returning its checked proof to the caller as a verified helper. It does not solve or finalize the parent theorem.",
            ]
        else:
            lines = [
                "Proof-state scheduler:",
                "- Work the highest-priority open node. Treat each open node as a local-theory obligation: prove child nodes as reusable named helpers, manufacture smaller child obligations when Lean exposes them, then assemble the root from verified helpers.",
            ]
        if active_root_target:
            if local_child_scope:
                lines.append(
                    "- Active-local-target override: for the local child target, "
                    "the current mathematical target is the active target after "
                    "`_solution` shell reduction; the original child shell is "
                    "retained only for returning a checked helper."
                )
            else:
                lines.append(
                    "- Active-root override: for the root node, the current "
                    "mathematical target is the active target after `_solution` "
                    "shell reduction; the original shell is retained only for "
                    "final Lean stitching."
                )
        if self.plan_hints:
            lines.append(
                "- candidate decomposition routes: "
                + _proof_state_model_prompt_text(
                    self._sanitize_internal_node_ids_for_prompt(
                        localize_authority_language("; ".join(self.plan_hints[:4])),
                        label_by_node_id,
                    ),
                    limit=1000,
                    suppress_solution_placeholders=(
                        self.suppress_solution_placeholders
                    ),
                )
            )
        for index, node in enumerate(frontier, start=1):
            label = label_by_node_id.get(
                node.node_id,
                self._prompt_node_label(
                    node,
                    index,
                    session_scope=normalized_session_scope,
                ),
            )
            prompt_kind = (
                "local_target"
                if local_child_scope and node.node_id == self.root_node_id
                else node.kind
            )
            target = _proof_state_model_prompt_text(
                (
                    active_root_target
                    if node.node_id == self.root_node_id and active_root_target
                    else node.target
                ),
                limit=360,
                suppress_solution_placeholders=self.suppress_solution_placeholders,
                statement=True,
            )
            original_root_note = ""
            if node.node_id == self.root_node_id and active_root_target:
                if (
                    self.suppress_solution_placeholders
                    and is_answer_unsafe_statement_text(
                        node.target,
                        suppress_solution_placeholders=True,
                    )
                ):
                    original_root_note = (
                        (
                            "; original_local_child_shell: "
                            if local_child_scope
                            else "; original_root_shell: "
                        )
                        + f"{_OFFICIAL_ANSWER_REFERENCE_HIDDEN}"
                    )
                else:
                    original_root = _proof_state_model_prompt_text(
                        node.target,
                        limit=220,
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                        statement=True,
                    )
                    if original_root and original_root != target:
                        original_root_note = (
                            f"; original_local_child_shell: `{original_root}`"
                            if local_child_scope
                            else f"; original_root_shell: `{original_root}`"
                        )
            if scoped_formalization_active and node.node_id == self.root_node_id:
                scoped_context_role = (
                    "local target context"
                    if local_child_scope
                    else "parent context"
                )
                lines.append(
                    f"- {label} [{prompt_kind}/{node.status}] {scoped_context_role} only while scoped graph formalization is active; "
                    f"target: `{target}`{original_root_note}"
                )
                continue
            context = ""
            if node.local_context:
                context = "; context: " + "; ".join(
                    _proof_state_model_prompt_text(
                        item,
                        limit=120,
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                    )
                    for item in node.local_context[:4]
                )
            goal_bits = ""
            if node.goal is not None:
                safe_consts = [
                    _proof_state_model_prompt_text(
                        item,
                        limit=80,
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                    )
                    for item in list(node.goal.constants_used[:5])
                    if not (
                        self.suppress_solution_placeholders
                        and is_answer_unsafe_statement_text(
                            item,
                            suppress_solution_placeholders=True,
                        )
                    )
                ]
                safe_tags = [
                    _proof_state_model_prompt_text(
                        item,
                        limit=80,
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                    )
                    for item in list(node.goal.shape_tags[:5])
                ]
                goal_parts = [
                    f"hash={node.goal.normalized_statement_hash}",
                    "consts=" + ",".join(item for item in safe_consts if item),
                    "tags=" + ",".join(item for item in safe_tags if item),
                ]
                goal_bits = "; " + "; ".join(part for part in goal_parts if part)
            children = ""
            if node.child_node_ids:
                proved = sum(
                    1
                    for child_id in node.child_node_ids
                    if self.nodes.get(child_id) is not None
                    and self.nodes[child_id].status == "proved"
                )
                children = f"; children={proved}/{len(node.child_node_ids)}"
            assembly = ""
            if node.assembly_attempt_groups:
                open_groups = sum(
                    1 for group in node.assembly_attempt_groups if group.status == "open"
                )
                assembly = f"; assembly_groups={open_groups}/{len(node.assembly_attempt_groups)}"
            lines.append(
                f"- {label} [{prompt_kind}/{node.status}] "
                f"priority={node.priority:.1f}; action={node.action}; "
                f"blocker={_proof_state_model_prompt_text(self._sanitize_internal_node_ids_for_prompt(localize_authority_language(node.blocker), label_by_node_id, preserve_code_spans=False), limit=180, suppress_solution_placeholders=self.suppress_solution_placeholders)}; "
                f"target: `{target}`{original_root_note}{context}{goal_bits}{children}{assembly}"
            )
            if node.retrieved_facts:
                lines.append(f"  retrieved candidates for {label}:")
                for fact_line in node.retrieved_facts[-1].splitlines()[:7]:
                    fact = _proof_state_model_prompt_text(
                        self._sanitize_internal_node_ids_for_prompt(
                            fact_line,
                            label_by_node_id,
                        ),
                        limit=220,
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                    )
                    if fact:
                        lines.append(f"  {fact}")
            if node.kind == "decomposition_task":
                if local_child_scope:
                    lines.append(
                        "  required move: create durable named helper lemmas or "
                        "definitions plus a local child proof body that Lean "
                        "reduces to those subgoals; do not retry the local child "
                        "target with a no-op tactic."
                    )
                else:
                    lines.append(
                        "  required move: create durable named helper lemmas or "
                        "definitions plus a parent/root theorem body that Lean "
                        "reduces to those subgoals; do not retry the root with a "
                        "no-op tactic."
                    )
        if graph_work:
            lines.append(
                "- graph-native frontier work (not facts; prove, formalize, or replace before citing):"
            )
            for record in graph_work_records[: max(0, int(max_nodes or 0))]:
                work_type = _proof_state_model_prompt_text(
                    str(record.get("work_type") or ""),
                    limit=80,
                    suppress_solution_placeholders=(
                        self.suppress_solution_placeholders
                    ),
                )
                graph_work_type = work_type
                if local_child_scope and work_type == "root_repair":
                    work_type = "local_target_repair"
                node_id = _proof_state_model_prompt_text(
                    str(record.get("graph_node_id") or record.get("node_id") or ""),
                    limit=80,
                    suppress_solution_placeholders=(
                        self.suppress_solution_placeholders
                    ),
                )
                raw_node_ids = {
                    str(record.get("node_id") or "").strip(),
                    str(record.get("graph_node_id") or "").strip(),
                }
                rootish_ids = {
                    str(self.root_node_id or "").strip(),
                    "root",
                    "proof_state:root",
                }
                if local_child_scope and str(node_id or "").strip() in rootish_ids:
                    node_id = "local_child_target"
                raw_target = str(record.get("target_statement") or "")
                target_source = raw_target
                if (
                    graph_work_type == "root_repair"
                    and active_root_target
                    and bool(raw_node_ids & rootish_ids)
                ):
                    target_source = active_root_target
                target = _proof_state_model_prompt_text(
                    target_source,
                    limit=360,
                    suppress_solution_placeholders=(
                        self.suppress_solution_placeholders
                    ),
                    statement=True,
                )
                original_root_note = ""
                if (
                    graph_work_type == "root_repair"
                    and active_root_target
                    and (
                        (
                            raw_target
                            and raw_target != target_source
                        )
                        or bool(
                            record.get("target_statement_answer_redacted")
                        )
                    )
                ):
                    if bool(record.get("target_statement_answer_redacted")):
                        original_root_note = (
                            (
                                "; original_local_child_shell: "
                                if local_child_scope
                                else "; original_root_shell: "
                            )
                            + f"{_OFFICIAL_ANSWER_REFERENCE_HIDDEN}"
                        )
                    else:
                        original = _proof_state_model_prompt_text(
                            raw_target,
                            limit=220,
                            suppress_solution_placeholders=(
                                self.suppress_solution_placeholders
                            ),
                            statement=True,
                        )
                        if original:
                            original_root_note = (
                                f"; original_local_child_shell: `{original}`"
                                if local_child_scope
                                else f"; original_root_shell: `{original}`"
                            )
                reason = _proof_state_model_prompt_text(
                    localize_authority_language(
                        str(record.get("obligation_reason") or "")
                    ),
                    limit=220,
                    suppress_solution_placeholders=(
                        self.suppress_solution_placeholders
                    ),
                )
                action = _proof_state_model_prompt_text(
                    localize_authority_language(str(record.get("action") or "")),
                    limit=120,
                    suppress_solution_placeholders=(
                        self.suppress_solution_placeholders
                    ),
                )
                if record.get("formalization_required"):
                    if graph_statement_is_executable(target):
                        move = "prove this formalized manufactured obligation or split it into smaller checked bridges"
                    else:
                        move = (
                            "formalize the smallest executable Lean proposition "
                            "under the route hypotheses, then prove or schedule it"
                        )
                elif work_type == "mine_missing_obligation":
                    move = "prove this manufactured obligation or replace it with a smaller checked bridge"
                elif work_type == "materialize_replay_source":
                    move = (
                        "produce a replayable named Lean lemma for this "
                        "graph-certified fact so route assembly may cite it"
                    )
                elif work_type == "route_replan":
                    move = "repair this route by manufacturing the next local obligation"
                else:
                    move = (
                        "complete this selected graph work before local child target assembly"
                        if local_child_scope
                        else "complete this selected graph work before root assembly"
                    )
                lines.append(
                    f"  - `{work_type}` graph_node=`{node_id}`; action={action or work_type}; "
                    f"required move: {move}; target: `{target or '(formal target not yet available)'}`"
                    f"{original_root_note}"
                    + (f"; reason: {reason}" if reason else "")
                )
                parent_target = _proof_state_model_prompt_text(
                    str(
                        record.get("materialization_parent_statement")
                        or record.get("formalization_bridge_parent_statement")
                        or record.get("parent_repair_target_statement")
                        or ""
                    ),
                    limit=360,
                    suppress_solution_placeholders=(
                        self.suppress_solution_placeholders
                    ),
                    statement=True,
                )
                if parent_target and work_type == "formalize_missing_obligation":
                    lines.append(
                        f"    supporting target: `{parent_target}`"
                        if local_child_scope
                        else f"    parent target to support: `{parent_target}`"
                    )
                forbidden_fragments = [
                    _proof_state_model_prompt_text(
                        str(fragment or ""),
                        limit=120,
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                    )
                    for fragment in list(
                        record.get("forbidden_materialization_fragments") or ()
                    )
                    if str(fragment or "").strip()
                ]
                if forbidden_fragments and work_type == "formalize_missing_obligation":
                    lines.append(
                        "    stale rejected fragment(s), not standalone targets: "
                        + ", ".join(f"`{item}`" for item in forbidden_fragments[:4])
                    )
        proved = [
            node.proved_helper_name
            for node in self.nodes.values()
            if node.status == "proved" and node.proved_helper_name
        ]
        if proved:
            lines.append(
                "- proved scheduled helpers: "
                + ", ".join(
                    f"`{_proof_state_model_prompt_text(name, limit=120, suppress_solution_placeholders=self.suppress_solution_placeholders)}`"
                    for name in proved[-6:]
                )
            )
        return "\n".join(lines)

    def to_record(self) -> Dict[str, Any]:
        redact_solution_refs = bool(self.suppress_solution_placeholders)
        lemma_dag_child_statement_rejection_transitions = sum(
            1
            for node in self.nodes.values()
            for transition in node.typed_transitions
            if transition.error_type == "llm_lemma_dag_child_statement_rejected"
        )
        lemma_dag_child_source_rejection_transitions = sum(
            1
            for node in self.nodes.values()
            for transition in node.typed_transitions
            if transition.error_type == "llm_lemma_dag_child_source_rejected"
        )
        lemma_dag_parent_stub_spawn_transitions = sum(
            1
            for node in self.nodes.values()
            for transition in node.typed_transitions
            if transition.error_type == "llm_lemma_dag_parent_stub_spawned"
        )
        lemma_dag_parent_stub_rejection_transitions = sum(
            1
            for node in self.nodes.values()
            for transition in node.typed_transitions
            if transition.error_type == "llm_lemma_dag_parent_stub_rejected"
        )
        metrics = {
            "total_close_attempts": sum(node.close_attempts for node in self.nodes.values()),
            "total_tactic_attempts": sum(node.tactic_attempts for node in self.nodes.values()),
            "total_decl_application_attempts": sum(
                node.decl_application_attempts for node in self.nodes.values()
            ),
            "total_assembly_attempts": sum(node.assembly_attempts for node in self.nodes.values()),
            "cache_hits": sum(node.cache_hits for node in self.nodes.values()),
            "budget_skips": sum(node.budget_skips for node in self.nodes.values()),
            "retrieval_hit_count": sum(node.retrieval_hit_count for node in self.nodes.values()),
            "graph_frontier_errors_total": int(self.graph_frontier_errors_total),
            "graph_obligation_child_promotions": int(
                self.graph_obligation_child_promotions
            ),
            "graph_obligation_child_promotion_reuses": int(
                self.graph_obligation_child_promotion_reuses
            ),
            "graph_obligation_child_promotion_skipped_quarantined": int(
                self.graph_obligation_child_promotion_skipped_quarantined
            ),
            "graph_obligation_child_promotion_skipped_untrusted": int(
                self.graph_obligation_child_promotion_skipped_untrusted
            ),
            "graph_obligation_child_promotion_skipped_formalization_required": int(
                self.graph_obligation_child_promotion_skipped_formalization_required
            ),
            "graph_obligation_child_promotion_skipped_non_executable": int(
                self.graph_obligation_child_promotion_skipped_non_executable
            ),
            "graph_obligation_child_promotion_skipped_root_equivalent": int(
                self.graph_obligation_child_promotion_skipped_root_equivalent
            ),
            "graph_obligation_child_promotion_skipped_rejected": int(
                self.graph_obligation_child_promotion_skipped_rejected
            ),
            "graph_obligation_child_promotion_skipped_cycle": int(
                self.graph_obligation_child_promotion_skipped_cycle
            ),
            "graph_obligation_child_promotion_skipped_terminal_parent": int(
                self.graph_obligation_child_promotion_skipped_terminal_parent
            ),
            "open_child_nodes": sum(
                1
                for node in self.nodes.values()
                if node.kind != "root" and node.status == "open"
            ),
            "proved_child_nodes": sum(
                1
                for node in self.nodes.values()
                if node.kind != "root" and node.status == "proved"
            ),
            "failed_child_nodes": sum(
                1
                for node in self.nodes.values()
                if node.kind != "root" and node.status == "failed"
            ),
            "unverified_decomposition_tasks": sum(
                1
                for node in self.nodes.values()
                if node.kind == "decomposition_task"
                and node.status == "blocked"
                and node.action == "llm_lemma_dag_spawned_unverified"
            ),
            "partial_verified_decomposition_tasks": sum(
                1
                for node in self.nodes.values()
                if node.kind == "decomposition_task"
                and node.status == "blocked"
                and node.action == "llm_lemma_dag_spawned_partial_verified"
            ),
            "proved_decomposition_tasks_with_open_children": sum(
                1
                for node in self.nodes.values()
                if node.kind == "decomposition_task"
                and node.status == "proved"
                and node.action == "llm_lemma_dag_spawned"
                and any(
                    self.nodes.get(child_id) is not None
                    and self.nodes[child_id].kind == "child_goal"
                    and self.nodes[child_id].status not in {"proved", "obsolete"}
                    for child_id in node.child_node_ids
                )
            ),
            "lemma_dag_child_statement_rejections": max(
                int(self.lemma_dag_child_statement_rejections),
                lemma_dag_child_statement_rejection_transitions,
            ),
            "lemma_dag_child_source_rejections": max(
                int(self.lemma_dag_child_source_rejections),
                lemma_dag_child_source_rejection_transitions,
            ),
            "lemma_dag_decomposition_all_candidates_rejected": int(
                self.lemma_dag_decomposition_all_candidates_rejected
            ),
            "lemma_dag_parent_stub_spawns": max(
                int(self.lemma_dag_parent_stub_spawns),
                lemma_dag_parent_stub_spawn_transitions,
            ),
            "lemma_dag_parent_stub_rejections": max(
                int(self.lemma_dag_parent_stub_rejections),
                lemma_dag_parent_stub_rejection_transitions,
            ),
            "failed_proof_residual_batches_quarantined": int(
                self.failed_proof_residual_batches_quarantined
            ),
            "failed_proof_residual_goals_quarantined": int(
                self.failed_proof_residual_goals_quarantined
            ),
            "residual_goal_context_filtered": int(
                self.residual_goal_context_filtered
            ),
            "tactic_pattern_cache_lookups": int(
                self.tactic_pattern_cache_lookups
            ),
            "tactic_pattern_cache_exact_success_hits": int(
                self.tactic_pattern_cache_exact_success_hits
            ),
            "tactic_pattern_cache_shape_success_hits": int(
                self.tactic_pattern_cache_shape_success_hits
            ),
            "tactic_pattern_cache_failed_filtered": int(
                self.tactic_pattern_cache_failed_filtered
            ),
            "tactic_pattern_cache_all_candidates_pruned": int(
                self.tactic_pattern_cache_all_candidates_pruned
            ),
            "tactic_pattern_cache_cap_preserved_misses": int(
                self.tactic_pattern_cache_cap_preserved_misses
            ),
            "tactic_pattern_cache_failures_recorded": int(
                self.tactic_pattern_cache_failures_recorded
            ),
            "tactic_pattern_cache_failures_not_cached": int(
                self.tactic_pattern_cache_failures_not_cached
            ),
            "tactic_pattern_cache_successes_recorded": int(
                self.tactic_pattern_cache_successes_recorded
            ),
            "tactic_pattern_cache_shape_successes_recorded": int(
                self.tactic_pattern_cache_shape_successes_recorded
            ),
            "tactic_pattern_cache_successes_deferred": int(
                self.tactic_pattern_cache_successes_deferred
            ),
            "tactic_pattern_cache_acceptance_vetoes": int(
                self.tactic_pattern_cache_acceptance_vetoes
            ),
            "tactic_pattern_cache_suppressed_filtered": int(
                self.tactic_pattern_cache_suppressed_filtered
            ),
            "root_tactic_context_attempts": int(self.root_tactic_context_attempts),
            "root_tactic_context_skips": int(self.root_tactic_context_skips),
            "root_tactic_transient_deferrals": int(
                self.root_tactic_transient_deferrals
            ),
            "root_tactic_transient_retries": int(
                self.root_tactic_transient_retries
            ),
            "root_tactic_deferred_skips": int(self.root_tactic_deferred_skips),
            "root_tactic_reenabled_by_new_evidence": int(
                self.root_tactic_reenabled_by_new_evidence
            ),
            "root_tactic_terminal_after_continuation": int(
                self.root_tactic_terminal_after_continuation
            ),
            "assembly_selected_stale": int(self.assembly_selected_stale),
            "assembly_contracts_created": sum(
                len(getattr(node, "assembly_attempt_groups", []) or [])
                for node in self.nodes.values()
            ),
            "assembly_groups_ready": sum(
                1
                for node in self.nodes.values()
                for group in self.ready_assembly_groups(node)
            ),
        }
        return {
            "suppress_solution_placeholders": self.suppress_solution_placeholders,
            "statement_environment_hash": str(
                self.statement_environment_hash or ""
            ),
            "node_count": len(self.nodes),
            "open_nodes": sum(1 for node in self.nodes.values() if node.status == "open"),
            "proved_nodes": sum(1 for node in self.nodes.values() if node.status == "proved"),
            "plan_hints": list(self.plan_hints),
            "metrics": metrics,
            "graph_frontier_errors": _proof_state_prompt_safe_value(
                [dict(item) for item in self.graph_frontier_errors],
                redact_solution_refs=redact_solution_refs,
            ),
            "frontier": [node.node_id for node in self.frontier(max_nodes=8)],
            "work_frontier": [
                item.to_record(
                    suppress_solution_placeholders=self.suppress_solution_placeholders
                )
                for item in self.work_frontier(max_items=12)
            ],
            "nodes": [
                {
                    "node_id": node.node_id,
                    "kind": node.kind,
                    "target": _proof_state_durable_text(
                        node.target,
                        limit=2000,
                        suppress_solution_placeholders=(
                            self.suppress_solution_placeholders
                        ),
                    ),
                    "local_context": [
                        _proof_state_durable_text(
                            item,
                            limit=1000,
                            suppress_solution_placeholders=(
                                self.suppress_solution_placeholders
                            ),
                        )
                        for item in list(node.local_context)
                    ],
                    "local_argument_terms": {
                        str(key): _proof_state_durable_text(
                            value,
                            limit=1000,
                            suppress_solution_placeholders=(
                                self.suppress_solution_placeholders
                            ),
                        )
                        for key, value in dict(node.local_argument_terms).items()
                    },
                    "normalized_goal": (
                        node.goal.to_record(
                            suppress_solution_placeholders=(
                                self.suppress_solution_placeholders
                            )
                        )
                        if node.goal is not None
                        else None
                    ),
                    "status": node.status,
                    "action": _proof_state_prompt_safe_text(
                        node.action,
                        limit=240,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "blocker": _proof_state_prompt_safe_text(
                        node.blocker,
                        limit=1000,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "blocked_by_node_ids": list(node.blocked_by_node_ids),
                    "priority": node.priority,
                    "failed_attempts": node.failed_attempts,
                    "tactic_attempts": node.tactic_attempts,
                    "tactic_terminal_context_keys": list(
                        node.tactic_terminal_context_keys
                    ),
                    "tactic_timeout_retry_context_keys": list(
                        node.tactic_timeout_retry_context_keys
                    ),
                    "decl_application_attempts": node.decl_application_attempts,
                    "assembly_attempts": node.assembly_attempts,
                    "cache_hits": node.cache_hits,
                    "close_attempts": node.close_attempts,
                    "budget_skips": node.budget_skips,
                    "successful_family": node.successful_family,
                    "diagnostics": _proof_state_prompt_safe_value(
                        [dict(item) for item in node.diagnostics],
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "failure_transitions": _proof_state_prompt_safe_value(
                        list(node.failure_transitions),
                        limit=240,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "typed_transitions": [
                        transition.to_record(
                            suppress_solution_placeholders=(
                                self.suppress_solution_placeholders
                            )
                        )
                        for transition in node.typed_transitions
                    ],
                    "retrieval_attempted": node.retrieval_attempted,
                    "falsification_preflight_transient_context_keys": list(
                        node.falsification_preflight_transient_context_keys
                    ),
                    "child_executor_exception_retry_context_keys": list(
                        node.child_executor_exception_retry_context_keys
                    ),
                    "retrieval_signature": node.retrieval_signature,
                    "retrieval_hit_count": node.retrieval_hit_count,
                    "retrieval_error": _proof_state_prompt_safe_text(
                        node.retrieval_error,
                        limit=500,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "retrieval_error_signature": node.retrieval_error_signature,
                    "retrieval_error_transient": node.retrieval_error_transient,
                    "retrieval_error_attempt_count": node.retrieval_error_attempt_count,
                    "retrieval_retry_after_epoch_s": node.retrieval_retry_after_epoch_s,
                    "rejection_evidence_hash": node.rejection_evidence_hash,
                    "decl_application_signature": node.decl_application_signature,
                    "decl_application_tried_decl_names": _proof_state_prompt_safe_value(
                        list(node.decl_application_tried_decl_names or ()),
                        limit=240,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "decl_application_structural_miss_decl_names": (
                        _proof_state_prompt_safe_value(
                            list(
                                node.decl_application_structural_miss_decl_names or ()
                            ),
                            limit=240,
                            redact_solution_refs=redact_solution_refs,
                        )
                    ),
                    "decl_application_context_replay_decl_names": (
                        _proof_state_prompt_safe_value(
                            list(
                                node.decl_application_context_replay_decl_names or ()
                            ),
                            limit=240,
                            redact_solution_refs=redact_solution_refs,
                        )
                    ),
                    "decl_application_last_context_replay_turn": (
                        node.decl_application_last_context_replay_turn
                    ),
                    "decl_application_retry_keys": _proof_state_prompt_safe_value(
                        list(node.decl_application_retry_keys or ()),
                        limit=240,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "retrieved_fact_blocks": len(node.retrieved_facts),
                    "retrieved_facts": _proof_state_prompt_safe_value(
                        list(node.retrieved_facts),
                        limit=2000,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "retrieved_decl_names": _proof_state_prompt_safe_value(
                        list(node.retrieved_decl_names),
                        limit=240,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "retrieved_decl_provenance": {
                        str(key): str(value)
                        for key, value in node.retrieved_decl_provenance.items()
                    },
                    "retrieved_decl_signatures": {
                        str(key): str(value)
                        for key, value in node.retrieved_decl_signatures.items()
                    },
                    "graph_retrieved_decl_quarantine_names": (
                        _proof_state_prompt_safe_value(
                            list(node.graph_retrieved_decl_quarantine_names),
                            limit=240,
                            redact_solution_refs=redact_solution_refs,
                        )
                    ),
                    "retrieved_decl_execution_policy_version": str(
                        node.retrieved_decl_execution_policy_version or ""
                    ),
                    "dependencies": list(node.dependencies),
                    "parent_node_id": node.parent_node_id,
                    "child_node_ids": list(node.child_node_ids),
                    "parent_proof_stub": _proof_state_prompt_safe_code(
                        node.parent_proof_stub,
                        limit=4000,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "parent_proof_stub_preview": _proof_state_prompt_safe_code(
                        node.parent_proof_stub,
                        limit=400,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "assembly_attempt_groups": [
                        group.to_record(
                            suppress_solution_placeholders=(
                                self.suppress_solution_placeholders
                            )
                        )
                        for group in node.assembly_attempt_groups
                    ],
                    "residual_attestation_quarantine_snapshot": (
                        _proof_state_prompt_safe_attestation_quarantine_snapshot(
                            node.residual_attestation_quarantine_snapshot,
                            node_status=node.status,
                            node_action=node.action,
                            node_blocker=node.blocker,
                            redact_solution_refs=redact_solution_refs,
                        )
                    ),
                    "proved_helper_name": _proof_state_prompt_safe_text(
                        node.proved_helper_name,
                        limit=240,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    "falsified": bool(node.falsified),
                    "statement_environment_hash": str(
                        node.statement_environment_hash or ""
                    ),
                    "falsification_certificate_hash": str(
                        node.falsification_certificate_hash or ""
                    ),
                    "falsification_advisory_candidate_hash": str(
                        node.falsification_advisory_candidate_hash or ""
                    ),
                    "falsification_retired_assembly_routes": [
                        dict(item)
                        for item in node.falsification_retired_assembly_routes
                    ],
                    "falsification_reason": _proof_state_prompt_safe_text(
                        node.falsification_reason,
                        limit=240,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    # F1 fix (2026-05-11): round-trip Phase 2 recursive
                    # helper prover counters so the per-node attempt
                    # cap and per-cluster giveup cap survive the
                    # ``to_record`` → graph metadata → ``_node_from_record``
                    # rehydration that ``ProofSearchState.from_graph``
                    # performs when a parallel sample clones the parent
                    # proof_graph (B5). Without this, the sample sees
                    # the child as if no recursive attempts had ever
                    # happened, silently bypassing B8's cap.
                    "recursive_attempts": int(node.recursive_attempts or 0),
                    "last_recursive_attempt_iteration": int(
                        node.last_recursive_attempt_iteration
                        if node.last_recursive_attempt_iteration is not None
                        else -1
                    ),
                    "recursive_giveup_cluster": (
                        node.recursive_giveup_cluster
                        if node.recursive_giveup_cluster is not None
                        else None
                    ),
                    "recursive_giveup_counts": dict(
                        node.recursive_giveup_counts or {}
                    ),
                    "root_exact_rejected_helper_keys": list(
                        node.root_exact_rejected_helper_keys or ()
                    ),
                    "root_tactic_attempted_context_keys": list(
                        node.root_tactic_attempted_context_keys or ()
                    ),
                    "root_tactic_deferred_context_keys": list(
                        node.root_tactic_deferred_context_keys or ()
                    ),
                    "root_tactic_reenabled_context_keys": list(
                        node.root_tactic_reenabled_context_keys or ()
                    ),
                    "root_tactic_continued_context_keys": list(
                        node.root_tactic_continued_context_keys or ()
                    ),
                }
                for node in self.nodes.values()
            ],
        }

    def to_execution_record(self) -> Dict[str, Any]:
        """Return the exact executable state used by graph clones/checkpoints.

        This record contains unredacted Lean source and is therefore a private
        run artifact, never a prompt/reporting payload.  The versioned inverse
        is :meth:`from_execution_record`.
        """

        record = self.to_record()
        record["execution_schema_version"] = PROOF_STATE_EXECUTION_SCHEMA_VERSION
        by_id = {
            str(item.get("node_id") or ""): item
            for item in list(record.get("nodes") or [])
            if isinstance(item, dict)
        }
        for node in self.nodes.values():
            node_record = by_id.get(node.node_id)
            if node_record is None:
                continue
            node_record.update(
                {
                    "target": node.target,
                    "local_context": list(node.local_context),
                    "local_argument_terms": dict(node.local_argument_terms),
                    "normalized_goal": (
                        node.goal.to_execution_record()
                        if node.goal is not None
                        else None
                    ),
                    "status": node.status,
                    "action": node.action,
                    "blocker": node.blocker,
                    "blocked_by_node_ids": list(node.blocked_by_node_ids),
                    "diagnostics": clone_json_value(
                        node.diagnostics,
                        label=f"proof node {node.node_id} diagnostics",
                    ),
                    "failure_transitions": list(node.failure_transitions),
                    "typed_transitions": [
                        {
                            "transition_id": transition.transition_id,
                            "node_id": transition.node_id,
                            "source": transition.source,
                            "error_type": transition.error_type,
                            "action": transition.action,
                            "blocker": transition.blocker,
                            "phase": transition.phase,
                            "turn_index": transition.turn_index,
                            "payload": clone_json_value(
                                transition.payload,
                                label=(
                                    "proof-state transition "
                                    f"{transition.transition_id} payload"
                                ),
                            ),
                        }
                        for transition in node.typed_transitions
                    ],
                    "retrieved_facts": list(node.retrieved_facts),
                    "falsification_preflight_transient_context_keys": list(
                        node.falsification_preflight_transient_context_keys
                    ),
                    "retrieved_decl_names": list(node.retrieved_decl_names),
                    "retrieved_decl_execution_policy_version": str(
                        node.retrieved_decl_execution_policy_version or ""
                    ),
                    "retrieval_attempted": bool(node.retrieval_attempted),
                    "retrieval_signature": str(node.retrieval_signature or ""),
                    "retrieval_error": node.retrieval_error,
                    "decl_application_tried_context_hash": str(
                        node.decl_application_tried_context_hash or ""
                    ),
                    "decl_application_tried_decl_names": list(
                        node.decl_application_tried_decl_names
                    ),
                    "decl_application_structural_miss_decl_names": list(
                        node.decl_application_structural_miss_decl_names
                    ),
                    "decl_application_context_replay_decl_names": list(
                        node.decl_application_context_replay_decl_names
                    ),
                    "decl_application_last_context_replay_turn": int(
                        node.decl_application_last_context_replay_turn
                    ),
                    "decl_application_retry_keys": list(
                        node.decl_application_retry_keys
                    ),
                    "pending_helper_acceptance": dict(
                        node.pending_helper_acceptance or {}
                    ),
                    "root_tactic_portfolio_continuation": (
                        validated_root_tactic_portfolio_continuation(
                            node.root_tactic_portfolio_continuation
                        )
                    ),
                    "proved_helper_name": node.proved_helper_name,
                    "parent_proof_stub": node.parent_proof_stub,
                    "parent_proof_stub_preview": node.parent_proof_stub[:400],
                    "pending_residual_goal_extraction": clone_json_value(
                        node.pending_residual_goal_extraction,
                        label=(
                            f"proof node {node.node_id} pending residual "
                            "extraction"
                        ),
                    ),
                    "verifier_retry_states": clone_json_value(
                        node.verifier_retry_states,
                        label=(
                            f"proof node {node.node_id} verifier retry states"
                        ),
                    ),
                    "residual_attestation_rejected_request_hashes": list(
                        node.residual_attestation_rejected_request_hashes
                    ),
                    "residual_attestation_deferred_request_retries": dict(
                        node.residual_attestation_deferred_request_retries
                    ),
                    "residual_attestation_last_deferred_request_hash": str(
                        node.residual_attestation_last_deferred_request_hash
                    ),
                    "residual_goal_attestation": clone_json_value(
                        node.residual_goal_attestation,
                        label=(
                            f"proof node {node.node_id} residual goal "
                            "attestation"
                        ),
                    ),
                    "residual_attestation_quarantine_snapshot": (
                        clone_json_value(
                            _proof_state_residual_attestation_quarantine_snapshot(
                                node.residual_attestation_quarantine_snapshot,
                                node_status=node.status,
                                node_action=node.action,
                                node_blocker=node.blocker,
                            ),
                            label=(
                                f"proof node {node.node_id} residual "
                                "attestation quarantine snapshot"
                            ),
                        )
                    ),
                    "assembly_attempt_groups": [
                        group.to_execution_record()
                        for group in node.assembly_attempt_groups
                    ],
                }
            )
        return record

    @classmethod
    def from_execution_record(
        cls,
        record: Mapping[str, Any],
        *,
        theorem_name: str,
        root_statement: str,
        graph: Any,
    ) -> "ProofSearchState":
        """Rehydrate an exact executable checkpoint against its saved graph.

        ``from_graph`` already owns the invariants for rebuilding indices and
        reconciling graph topology.  Install the versioned private projection
        on the freshly rehydrated graph, bind it to that graph's fingerprint,
        then use the same invariant-preserving path as an in-process clone.
        """

        data = clone_json_value(
            record,
            label="proof-state execution restore record",
        )
        if int(data.get("execution_schema_version", 0) or 0) not in {1, 2}:
            raise ValueError("unsupported proof-state execution checkpoint schema")
        if graph is None:
            raise ValueError("proof-state execution checkpoint requires a proof graph")
        raw_suppress_solution_placeholders = data.get(
            "suppress_solution_placeholders",
            True,
        )
        if not isinstance(raw_suppress_solution_placeholders, bool):
            raise ValueError(
                "proof-state execution checkpoint has invalid solution policy"
            )
        setattr(graph, "_proof_state_execution_record", data)
        # Installing a serialized execution record is not a live Lean replay.
        # Clear any authority left by an older in-process snapshot on a reused
        # graph object before delegating to ``from_graph``.
        if hasattr(graph, "_proof_state_falsification_authorities"):
            delattr(graph, "_proof_state_falsification_authorities")
        setattr(
            graph,
            "_proof_state_execution_snapshot_fingerprint",
            cls._graph_execution_snapshot_fingerprint(graph),
        )
        return cls.from_graph(
            theorem_name=theorem_name,
            root_statement=root_statement,
            graph=graph,
            suppress_solution_placeholders=raw_suppress_solution_placeholders,
        )

    def _route_failure(self, analysis: Dict[str, Any]) -> Tuple[str, str]:
        family = str(analysis.get("error_type") or "lean_rejected")
        details = dict(analysis.get("details") or {})
        goals = list(analysis.get("remaining_goals") or [])
        if family == "unknown_identifier":
            return (
                "manufacture_or_retrieve_missing_identifier",
                str(details.get("unknown_identifier") or "unknown declaration"),
            )
        if family == "known_answer_no_construction_collapse":
            return ("force_graph_decomposition", "no durable construction emitted")
        if family == "sorry_used":
            return ("force_graph_decomposition", "proof used sorry/admit placeholder")
        if family == "parse_error":
            return ("repair_syntax_or_binders", family)
        if family in {"unknown_universe", "binder_arity_mismatch"}:
            return ("repair_syntax_or_binders", family)
        if family == "infra_failure":
            return ("retry_or_reduce_lean_batch", family)
        if family == "answer_safe_feedback_unavailable":
            return ("answer_safe_bridge_or_rederive", family)
        if family == "type_mismatch":
            return (
                "bridge_rewrite_or_coercion",
                str(details.get("expected_type") or "expected type mismatch"),
            )
        if family in {"unsolved_goals", "tactic_failed"} and goals:
            return ("spawn_child_goals", f"{len(goals)} remaining goal(s)")
        if family in {"timeout", "termination_failed"}:
            return ("split_or_normalize_target", family)
        if family == "missing_instance":
            return (
                "instance_or_domain_retrieval",
                str(details.get("missing_instance") or "missing instance"),
            )
        if family == "unification_failed":
            return (
                "explicit_instantiation_or_bridge",
                str(details.get("unification_failure") or "unification failed"),
            )
        if goals:
            return ("spawn_child_goals", f"{len(goals)} remaining goal(s)")
        return ("swap_tactic_family", family)

    def preview_remaining_goal_statement(self, goal: Any) -> str:
        """Reconstruct the standalone statement ``_spawn_remaining_goal`` would store.

        This runs the same target/context normalization + ``∀``-quantification as
        :meth:`_spawn_remaining_goal` but does **not** mutate the graph.  Callers
        (the executor's spawn-time elaboration gate) use it to type-check a
        reconstructed obligation before it becomes a durable search node —
        reconstructed goals come from Lean's pretty-printed goal text, which
        elides ``Finset.sum``/``∑`` binder domains and can leak ``sorry``, so the
        reconstructed statement may be ill-typed and unprovable.  Returns ``""``
        when the goal cannot be reconstructed.
        """
        if not isinstance(goal, dict):
            return ""
        raw_target_value = goal.get("target")
        raw_context = (
            goal.get("hypotheses")
            or goal.get("context")
            or goal.get("local_context")
            or []
        )
        if isinstance(raw_context, str):
            raw_context = [line for line in raw_context.splitlines() if line.strip()]
        context = [self._normalize_hypothesis(item) for item in list(raw_context or [])]
        context = [item for item in context if item]
        if goal.get("rendered_target"):
            target = _normalize_rendered_proof_state_target_text(raw_target_value)
        else:
            target = self._normalize_goal_text(raw_target_value)
        if not target or target == "(target unavailable)":
            return ""
        lean_target, lean_context, _local_argument_terms = (
            self._sanitize_context_for_statement_with_map(target, context)
        )
        return str(self._statement_from_context(lean_target, lean_context) or "")

    def _spawn_remaining_goal(
        self,
        goal: Any,
        *,
        source: str,
        parent_node_id: str = "",
        parent_proof_stub: str = "",
        assembly_id: str = "",
        statement_environment_hash: Optional[str] = None,
        standalone_statement: str = "",
        residual_goal_attestation: Optional[Mapping[str, Any]] = None,
    ) -> Optional[ProofStateNode]:
        if not isinstance(goal, dict):
            return None
        parent = str(parent_node_id or self.root_node_id)
        parent_node = self.nodes.get(parent)
        if parent_node is not None and parent_node.status in {
            "proved",
            "obsolete",
            "rejected",
            "failed",
        }:
            return None
        exact_standalone_statement = str(standalone_statement or "")
        if exact_standalone_statement:
            target = exact_standalone_statement
            statement = exact_standalone_statement
            lean_context: List[str] = []
            local_argument_terms: Dict[str, str] = {}
            signature = self._goal_signature(
                target,
                [],
                source_failure=source,
            )
        else:
            raw_target_value = goal.get("target")
            raw_context = (
                goal.get("hypotheses")
                or goal.get("context")
                or goal.get("local_context")
                or []
            )
            if isinstance(raw_context, str):
                raw_context = [
                    line for line in raw_context.splitlines() if line.strip()
                ]
            context = [
                self._normalize_hypothesis(item)
                for item in list(raw_context or [])
            ]
            context = [item for item in context if item]
            if goal.get("rendered_target"):
                target = _normalize_rendered_proof_state_target_text(
                    raw_target_value
                )
            else:
                target = self._normalize_goal_text(raw_target_value)
            if not target or target == "(target unavailable)":
                return None
            signature = self._goal_signature(
                target,
                context,
                source_failure=source,
            )
            lean_target, lean_context, local_argument_terms = (
                self._sanitize_context_for_statement_with_map(target, context)
            )
            statement = self._statement_from_context(lean_target, lean_context)
        target_environment_hash = str(
            self.statement_environment_hash
            if statement_environment_hash is None
            else statement_environment_hash
        ).strip()
        target_index_key = self._target_environment_index_key(
            signature.normalized_statement_hash,
            target_environment_hash,
        )
        existing = self._node_by_target.get(target_index_key)
        if existing:
            existing_node = self.nodes[existing]
            authority_key = ""
            if residual_goal_attestation:
                incoming_identity = str(
                    residual_goal_attestation.get("structural_identity") or ""
                )
                authority_key = _residual_goal_attestation_authority_key(
                    residual_goal_attestation
                )
                existing_authorities = _residual_goal_attestation_authorities(
                    existing_node.residual_goal_attestation
                )
                malformed_existing_ledger = bool(
                    existing_node.residual_goal_attestation
                    and not existing_authorities
                )
                if (
                    not authority_key
                    or (
                        existing_node.target != statement
                        and not self._residual_targets_are_equivalent(
                            existing_node.target,
                            statement,
                        )
                    )
                    or existing_node.statement_environment_hash
                    != target_environment_hash
                    or any(
                        str(authority.get("structural_identity") or "")
                        != incoming_identity
                        for authority in existing_authorities
                    )
                ):
                    return None
                if malformed_existing_ledger:
                    existing_node.residual_goal_attestation = {}
            if existing_node.status in {"obsolete", "failed", "rejected"}:
                parent_for_record = self.nodes.get(parent)
                if parent_for_record is not None:
                    self.record_transition(
                        node_id=parent_for_record.node_id,
                        source="remaining_goal_spawn",
                        error_type="terminal_existing_residual_goal_rejected",
                        action=parent_for_record.action,
                        blocker=(
                            "remaining goal matched a terminal unproved child "
                            f"({existing_node.status})"
                        ),
                        payload={
                            "existing_node_id": existing_node.node_id,
                            "existing_status": existing_node.status,
                            "source": str(source or ""),
                            "target": target,
                        },
                    )
                return None
            if self._would_create_cycle(parent_node_id or self.root_node_id, existing_node.node_id):
                parent_node = self.nodes.get(str(parent_node_id or self.root_node_id))
                if parent_node is not None:
                    self.record_transition(
                        node_id=parent_node.node_id,
                        source="remaining_goal_spawn",
                        error_type="cyclic_residual_goal_rejected",
                        action=parent_node.action,
                        blocker="remaining goal restated its parent/root",
                        payload={
                            "existing_node_id": existing_node.node_id,
                            "source": str(source or ""),
                            "target": target,
                        },
                    )
                return None
            if (
                residual_goal_attestation
                and authority_key
                and authority_key
                not in existing_node.residual_goal_attestation
            ):
                existing_node.residual_goal_attestation[authority_key] = (
                    clone_json_value(
                        dict(residual_goal_attestation),
                        label=(
                            f"proof node {existing_node.node_id} residual "
                            "goal attestation"
                        ),
                    )
                )
            if parent_node_id and parent_node_id not in existing_node.dependencies:
                existing_node.dependencies.append(parent_node_id)
            self._attach_child_to_parent(
                parent_node_id=parent_node_id,
                child_node_id=existing_node.node_id,
                assembly_id=assembly_id,
            )
            if existing_node.falsified and assembly_id:
                parent_for_route = self.nodes.get(str(parent_node_id or ""))
                if parent_for_route is not None:
                    for group in parent_for_route.assembly_attempt_groups:
                        if (
                            group.assembly_id != assembly_id
                            or group.status not in {"open", "failed"}
                        ):
                            continue
                        previous_status = group.status
                        group.status = "obsolete"
                        route = {
                            "parent_node_id": parent_for_route.node_id,
                            "assembly_id": assembly_id,
                            "previous_status": previous_status,
                            "certificate_hash": str(
                                existing_node.falsification_certificate_hash or ""
                            )[:128],
                        }
                        existing_node.falsification_retired_assembly_routes.append(
                            route
                        )
                        self.record_transition(
                            node_id=parent_for_route.node_id,
                            source="falsification",
                            error_type=(
                                "assembly_route_invalidated_by_falsified_child"
                            ),
                            action=parent_for_route.action,
                            blocker="assembly route reused a falsified child",
                            payload={
                                "child_node_id": existing_node.node_id,
                                **route,
                            },
                        )
                        break
            return existing_node

        self._next_index += 1
        node_id = f"goal_{self._next_index}"
        node = ProofStateNode(
            node_id=node_id,
            kind="child_goal",
            target=statement,
            statement_environment_hash=target_environment_hash,
            residual_goal_attestation=(
                {
                    _residual_goal_attestation_authority_key(
                        residual_goal_attestation
                    ): clone_json_value(
                        dict(residual_goal_attestation),
                        label=(
                            f"proof node {node_id} residual goal attestation"
                        ),
                    )
                }
                if residual_goal_attestation
                else {}
            ),
            suppress_solution_placeholders=self.suppress_solution_placeholders,
            goal=signature,
            local_context=lean_context,
            local_argument_terms=local_argument_terms,
            dependencies=[parent],
            parent_node_id=parent,
            parent_proof_stub=str(parent_proof_stub or ""),
            action="prove_child_helper",
            blocker=f"spawned from remaining Lean goal ({source})",
            priority=82.0,
        )
        node.priority = self._priority(node)
        self.nodes[node_id] = node
        self._node_by_target[target_index_key] = node_id
        self._attach_child_to_parent(
            parent_node_id=parent,
            child_node_id=node_id,
            assembly_id=assembly_id,
        )
        return node

    def _start_assembly_attempt(
        self,
        *,
        parent_node_id: str,
        source: str,
        proof_stub: str,
    ) -> str:
        parent = self.nodes.get(str(parent_node_id or ""))
        stub = str(proof_stub or "").strip()
        if parent is None or not stub:
            return ""
        # E6 fix (adversarial review 2026-05-09): refuse to add a fresh
        # assembly group to a parent that has already been closed
        # (proved) or cancelled (obsolete/rejected/failed). Otherwise
        # the orphan group would index ghost children that can never
        # contribute to closure.
        if parent.status in {"proved", "obsolete", "rejected", "failed"}:
            return ""
        assembly_id = f"{parent.node_id}:asm_{len(parent.assembly_attempt_groups) + 1}"
        parent.assembly_attempt_groups.append(
            ProofStateAssemblyAttempt(
                assembly_id=assembly_id,
                source=str(source or ""),
                proof_stub=stub,
            )
        )
        parent.action = "assemble_from_children"
        parent.priority = self._priority(parent)
        return assembly_id

    def _attach_child_to_parent(
        self,
        *,
        parent_node_id: str,
        child_node_id: str,
        assembly_id: str = "",
    ) -> bool:
        parent = self.nodes.get(str(parent_node_id or ""))
        if parent is None or child_node_id not in self.nodes:
            return False
        # E6 fix (adversarial review 2026-05-09): refuse to attach
        # children to a closed/cancelled parent. The new child would be
        # indexed forever as a ghost-work node — its parent's groups
        # are obsolete and will never be ready, but the inverse-index
        # entry would persist and the child would still appear in
        # frontier scans as open.
        if parent.status in {"proved", "obsolete", "rejected", "failed"}:
            return False
        if self._would_create_cycle(parent.node_id, child_node_id):
            self.record_transition(
                node_id=parent.node_id,
                source="proof_state_graph",
                error_type="cyclic_child_attachment_rejected",
                action=parent.action,
                blocker="residual goal matched its parent/root and would create a graph cycle",
                payload={"child_node_id": child_node_id, "assembly_id": assembly_id},
            )
            return False
        if child_node_id not in parent.child_node_ids:
            parent.child_node_ids.append(child_node_id)
        if assembly_id:
            for group in parent.assembly_attempt_groups:
                if group.assembly_id == assembly_id:
                    # Preserve legacy semantics: ``group.child_node_ids``
                    # may legitimately contain duplicates (one entry per
                    # residual slot when ``apply`` produced two copies of
                    # the same goal — see test_proof_state_rehydrates_*).
                    # The inverse index is set-based so duplicates collapse
                    # there without changing behavior.
                    group.child_node_ids.append(child_node_id)
                    self._register_assembly_child(
                        parent_node_id=parent.node_id,
                        child_node_id=child_node_id,
                        assembly_id=assembly_id,
                    )
                    break
        if not (
            parent.status == "blocked"
            and parent.action
            in {
                "llm_lemma_dag_spawned_unverified",
                "llm_lemma_dag_spawned_partial_verified",
            }
        ):
            parent.action = "assemble_from_children"
        parent.priority = self._priority(parent)
        return True

    def _move_primary_parent_if_rootish(
        self,
        *,
        child_node_id: str,
        parent_node_id: str,
    ) -> None:
        child = self.nodes.get(str(child_node_id or ""))
        parent = self.nodes.get(str(parent_node_id or ""))
        if child is None or parent is None:
            return
        prior_parent_id = str(child.parent_node_id or "")
        if prior_parent_id and prior_parent_id != self.root_node_id:
            return
        if prior_parent_id == parent.node_id:
            return
        if prior_parent_id == self.root_node_id:
            root = self.nodes.get(self.root_node_id)
            if root is not None:
                if any(
                    child.node_id in group.child_node_ids
                    for group in root.assembly_attempt_groups
                ):
                    return
                root.child_node_ids = [
                    cid for cid in root.child_node_ids if cid != child.node_id
                ]
        child.parent_node_id = parent.node_id

    # ------------------------------------------------------------------
    # E1 inverse index maintenance + lookup
    # ------------------------------------------------------------------

    def _register_assembly_child(
        self,
        *,
        parent_node_id: str,
        child_node_id: str,
        assembly_id: str,
    ) -> None:
        """Add a (parent, group) pair to the inverse index for one child."""

        if not parent_node_id or not child_node_id or not assembly_id:
            return
        self._assembly_parents_by_child.setdefault(child_node_id, set()).add(
            (parent_node_id, assembly_id)
        )

    def _rebuild_assembly_index(self) -> None:
        """Rebuild the inverse index from current ``self.nodes`` state.

        Call after any path that bulk-mutates ``self.nodes`` or replaces
        ``group.child_node_ids`` without going through
        ``_attach_child_to_parent`` (deserialization, graph rehydration,
        prune, rollback).
        """

        self._assembly_parents_by_child = {}
        for parent in self.nodes.values():
            for group in parent.assembly_attempt_groups:
                if not group.assembly_id:
                    continue
                for child_id in group.child_node_ids:
                    if not child_id:
                        continue
                    self._assembly_parents_by_child.setdefault(child_id, set()).add(
                        (parent.node_id, group.assembly_id)
                    )

    def parent_groups_for_child(
        self, child_node_id: str
    ) -> List[Tuple[str, str]]:
        """Return (parent_id, assembly_id) pairs whose group lists this child.

        Returns a list (not a set) so call sites can iterate deterministically.
        Parent existence is verified — stale entries (parent removed) are
        filtered out.
        """

        out: List[Tuple[str, str]] = []
        seen: Set[Tuple[str, str]] = set()
        for parent_id, assembly_id in self._assembly_parents_by_child.get(
            str(child_node_id or ""), ()
        ):
            if (parent_id, assembly_id) in seen:
                continue
            if parent_id not in self.nodes:
                continue
            seen.add((parent_id, assembly_id))
            out.append((parent_id, assembly_id))
        out.sort()
        return out

    def ready_parent_groups_after(
        self, child_node_id: str
    ) -> List[Tuple[str, str]]:
        """Return (parent_id, assembly_id) pairs whose group is now ready.

        "Ready" means the group is open, has not yet been attempted
        (``attempt_count == 0``), the parent itself is open, and every
        child in the group has status ``"proved"``. This mirrors the
        readiness predicate in ``_node_ready_for_assembly`` but answers
        the inverse question (given a just-proved child, which parents
        does it unblock?) without scanning every node.
        """

        out: List[Tuple[str, str]] = []
        for parent_id, assembly_id in self.parent_groups_for_child(child_node_id):
            parent = self.nodes.get(parent_id)
            if parent is None or parent.status != "open":
                continue
            for group in parent.assembly_attempt_groups:
                if group.assembly_id != assembly_id:
                    continue
                # E4: include groups that are tryable on the current
                # witness, including previously-failed groups whose
                # witness has changed since the last attempt.
                if not self._group_tryable_for_attempt(group):
                    break
                child_ids = [
                    cid
                    for cid in group.child_node_ids
                    if cid in self.nodes
                ]
                if not child_ids:
                    break
                if all(
                    self.nodes[cid].status == "proved"
                    for cid in child_ids
                ):
                    out.append((parent_id, assembly_id))
                break
        return out

    def _child_still_supports_open_work(
        self,
        child_id: str,
        *,
        exclude_parent: str = "",
    ) -> bool:
        """Return True if ``child_id`` is in any open assembly group of
        a parent OTHER than ``exclude_parent``. Used by E6 cancellation
        to decide whether a child made obsolete by one parent's close
        is still load-bearing for another open parent.

        Adversarial review fix 2026-05-09 (E6 F8) plus follow-up:
        terminal parent states are NOT a source of open work. Blocked
        and rejected parents are kept load-bearing because graph readiness
        can reopen them; failed/obsolete/proved parents cannot consume
        the child without an explicit replan. At the group level, E4
        means an already-failed group can still be live if its current
        witness differs from ``last_attempt_witness``.
        """

        if not child_id:
            return False
        for parent_id, assembly_id in self._assembly_parents_by_child.get(
            child_id, ()
        ):
            if parent_id == exclude_parent:
                continue
            parent = self.nodes.get(parent_id)
            if parent is None or parent.status in {
                "proved",
                "obsolete",
                "failed",
            }:
                continue
            for group in parent.assembly_attempt_groups:
                if group.assembly_id != assembly_id:
                    continue
                if self._group_tryable_for_attempt(group):
                    return True
                break
        return False

    def _cancel_obsolete_or_siblings(
        self,
        parent_id: str,
        *,
        winning_assembly_id: str = "",
        _seen_parents: Optional[Set[str]] = None,
        _depth: int = 0,
    ) -> List[str]:
        """E6: when ``parent_id`` closes, mark its non-winning open
        assembly groups ``"obsolete"`` and propagate to each child of
        those groups whose proof would no longer support any open
        parent work.

        ``winning_assembly_id`` distinguishes the assembly path that
        closed the parent (preserved as ``"proved"``) from sibling
        groups that are now superseded. When the parent closes via a
        non-assembly path (cache hit, direct tactic, helper match),
        ``winning_assembly_id`` is empty and ALL open or retryable/failed
        assembly groups are marked obsolete.

        Adversarial review fix 2026-05-09 (E6 F5): cascade transitively
        through cancelled subtrees. After flipping a child to
        ``"obsolete"``, recurse to cancel ITS sibling groups too, so
        granchildren that only supported the now-cancelled child are
        also retired. Bounded by ``max_cascade_depth`` (matching the
        ``_on_root_closure_path`` cap) and a ``_seen_parents`` set to
        prevent revisits / cycle expansion.

        Returns the list of child node ids actually flipped to
        obsolete — useful for caller telemetry and for chaining
        priority refresh.
        """

        max_cascade_depth = 32
        if _seen_parents is None:
            _seen_parents = set()
        if parent_id in _seen_parents or _depth > max_cascade_depth:
            return []
        _seen_parents.add(parent_id)

        parent = self.nodes.get(parent_id)
        if parent is None:
            return []
        obsolete_children: Set[str] = set()
        for group in parent.assembly_attempt_groups:
            if winning_assembly_id and group.assembly_id == winning_assembly_id:
                continue
            if group.status not in {"open", "failed"}:
                continue
            group.status = "obsolete"
            for child_id in group.child_node_ids:
                if child_id:
                    obsolete_children.add(child_id)

        flipped: List[str] = []
        for child_id in obsolete_children:
            child = self.nodes.get(child_id)
            if child is None:
                continue
            if child.status in {"proved", "obsolete"}:
                continue
            if self._child_still_supports_open_work(
                child_id, exclude_parent=parent_id
            ):
                continue
            child.status = "obsolete"
            child.priority = 0.0
            flipped.append(child_id)
            # E6 F5: transitively cancel the grandchild subtree. The
            # newly-obsolete child closes itself "via no path", so all
            # of its own assembly groups are obsolete (empty
            # ``winning_assembly_id``). Recurse with the seen-set so
            # diamonds don't double-cancel.
            grandchildren_flipped = self._cancel_obsolete_or_siblings(
                child_id,
                winning_assembly_id="",
                _seen_parents=_seen_parents,
                _depth=_depth + 1,
            )
            flipped.extend(grandchildren_flipped)
        return flipped

    def assembly_witness(
        self,
        group: ProofStateAssemblyAttempt,
    ) -> Tuple[str, ...]:
        """E4 (2026-05-09): compute the current witness tuple for a
        group — sorted ``"<child_id>:<proved_helper_name>"`` entries.

        Open children contribute an empty helper name. Children no
        longer in ``self.nodes`` are skipped. Duplicate child slots
        (legacy two-slot residual semantics) collapse to one witness
        entry — adversarial review fix 2026-05-09 (E4 F4): without
        this dedup, ``("X:hX", "X:hX")`` would change spuriously to
        ``("X:hX",)`` if the duplicate is later folded out, masking
        as a witness change. The result is stable for a given (group,
        child_proof_state) pair, so two calls return the same witness
        iff no child's status or helper has changed in between.
        """

        seen: Set[str] = set()
        entries: List[str] = []
        for cid in group.child_node_ids:
            if cid not in self.nodes:
                continue
            entry = f"{cid}:{self.nodes[cid].proved_helper_name or ''}"
            if entry in seen:
                continue
            seen.add(entry)
            entries.append(entry)
        entries.sort()
        return tuple(entries)

    def _group_tryable_for_attempt(
        self,
        group: ProofStateAssemblyAttempt,
    ) -> bool:
        """E4 readiness: a group is tryable when its terminal status
        permits it AND either no attempt has fired yet OR the children's
        witnesses have changed since the last attempt.

        Status semantics:
          - ``"open"`` with ``attempt_count == 0``: tryable (fresh).
          - ``"open"`` with ``attempt_count > 0``: tryable if witness
            changed since the last attempt.
          - ``"failed"``: tryable only if witness changed since last
            attempt — a fresh witness gives the assembler new
            candidates that may now succeed. A "failed" group with
            ``attempt_count == 0`` is malformed (state is never set
            without firing at least one candidate); refuse retry to
            avoid acting on inconsistent state. (Adversarial review
            fix 2026-05-09, E4 F2.)
          - ``"proved"`` / ``"obsolete"``: terminal; never retried.
        """

        if group.status not in {"open", "failed"}:
            return False
        if group.attempt_count <= 0:
            return group.status == "open"
        return self.assembly_witness(group) != tuple(
            group.last_attempt_witness or ()
        )

    def assembly_group_readiness(
        self,
        node: ProofStateNode,
        *,
        assembly_id: str = "",
    ) -> List[Dict[str, Any]]:
        """Return executable-readiness facts for one node's assembly groups."""

        wanted = str(assembly_id or "").strip()
        out: List[Dict[str, Any]] = []
        for group in list(getattr(node, "assembly_attempt_groups", ()) or ()):
            gid = str(group.assembly_id or "").strip()
            if wanted and gid != wanted:
                continue
            child_ids = [cid for cid in list(group.child_node_ids or ()) if cid in self.nodes]
            missing_child_ids = [
                cid for cid in list(group.child_node_ids or ()) if cid not in self.nodes
            ]
            unproved_child_ids = [
                cid for cid in child_ids if self.nodes[cid].status != "proved"
            ]
            tryable = self._group_tryable_for_attempt(group)
            ready = bool(child_ids and not missing_child_ids and not unproved_child_ids and tryable)
            if not child_ids:
                reason = "no_children"
            elif missing_child_ids:
                reason = "missing_children"
            elif unproved_child_ids:
                reason = "unproved_children"
            elif not tryable:
                reason = "not_tryable"
            else:
                reason = "ready"
            out.append(
                {
                    "assembly_id": gid,
                    "ready": ready,
                    "reason": reason,
                    "status": str(group.status or ""),
                    "attempt_count": _proof_state_durable_nonnegative_int(
                        group.attempt_count
                    ),
                    "child_node_ids": list(child_ids),
                    "missing_child_node_ids": list(missing_child_ids),
                    "unproved_child_node_ids": list(unproved_child_ids),
                    "witness": list(self.assembly_witness(group)),
                    "witness_hash": text_hash("|".join(self.assembly_witness(group))),
                }
            )
        return out

    def ready_assembly_groups(
        self,
        node: ProofStateNode,
        *,
        assembly_id: str = "",
    ) -> List[ProofStateAssemblyAttempt]:
        """Return exact assembly groups that are executable now."""

        readiness = {
            item["assembly_id"]: bool(item.get("ready"))
            for item in self.assembly_group_readiness(node, assembly_id=assembly_id)
        }
        return [
            group
            for group in list(getattr(node, "assembly_attempt_groups", ()) or ())
            if readiness.get(str(group.assembly_id or "").strip(), False)
        ]

    def assembly_work_version(
        self,
        node: ProofStateNode,
        *,
        assembly_id: str = "",
    ) -> Dict[str, Any]:
        """Stable version payload for assembly frontier keys."""

        records = self.assembly_group_readiness(node, assembly_id=assembly_id)
        ready_records = [record for record in records if bool(record.get("ready"))]
        selected = ready_records or records
        payload = [
            {
                "assembly_id": str(record.get("assembly_id") or ""),
                "status": str(record.get("status") or ""),
                "attempt_count": _proof_state_durable_nonnegative_int(
                    record.get("attempt_count")
                ),
                "witness_hash": str(record.get("witness_hash") or ""),
                "reason": str(record.get("reason") or ""),
            }
            for record in selected
        ]
        return {
            "assembly_group_status": ",".join(
                f"{item['assembly_id']}:{item['status']}:{item['attempt_count']}"
                for item in payload
            ),
            "assembly_witness_hash": text_hash(
                json.dumps(payload, sort_keys=True, default=str)
            )
            if payload
            else "",
        }

    def _is_structurally_dead(self, node_id: str) -> bool:
        """Return True if a node cannot contribute to its parent's closure.

        E5 dead-path bubble (2026-05-09; refined after adversarial
        review): a node is structurally dead in TWO cases.

        1. Its own status is ``rejected``/``failed``/``obsolete`` —
           Lean rejected it, the search exhausted its options, or E6
           cancelled it as part of an OR-sibling cleanup.

        2. Its status is ``"open"`` AND every assembly group is in the
           explicit dead set ``{"failed", "obsolete"}``, with E4
           retryable failed groups treated as live. The
           ``"open"`` precondition matters:
             - a ``"proved"`` node is terminal-alive (it CLOSED — its
               groups may include a successful one + sibling
               ``"failed"``s, but the node is not dead);
             - a ``"blocked"`` node is awaiting dependency resolution;
               its decomposition-exhaustion isn't structural deadness
               because unblocking can spawn fresh groups;
             - the explicit ``{"failed", "obsolete"}`` set
               (vs. ``not in {"open"}``) makes the assumption visible
               and fails-safe under future status-enum drift — an
               unfamiliar status is treated as alive, not dead.

        The predicate is non-recursive (it inspects only this node's
        own groups, never another node's deadness), so cycles cannot
        cause unbounded recursion.
        """

        node = self.nodes.get(node_id)
        if node is None:
            return False
        if node.status in {"rejected", "failed", "obsolete"}:
            return True
        if node.status != "open":
            return False
        if node.assembly_attempt_groups and all(
            group.status == "obsolete"
            or (
                group.status == "failed"
                and not self._group_tryable_for_attempt(group)
            )
            for group in node.assembly_attempt_groups
        ):
            return True
        return False

    def closure_unblocks_count(
        self, node: ProofStateNode
    ) -> Tuple[int, int]:
        """Return (last_child_count, second_to_last_count) for an open node.

        ``last_child_count``: number of parent assembly groups in which
        this node is the SOLE remaining unproved child (i.e., proving
        this node would immediately make the group ready).

        ``second_to_last_count``: number of parent assembly groups in
        which this node is the second-to-last unproved child (proving
        it leaves exactly one other open child).

        Returns (0, 0) for proved/failed/rejected/blocked nodes — they
        get no closure-value bonus. Runs in
        O(parent_groups_containing_this_child) using the inverse index;
        cheap relative to a full graph scan.

        Dead-group skip (adversarial review fix 2026-05-09): a group
        containing a ``rejected`` or ``failed`` sibling can never
        close, so this node's proof would not make it ready. Such
        groups are excluded entirely so the bonus reflects realistic
        unblock potential.

        Duplicate-slot dedup (adversarial review fix 2026-05-09):
        ``group.child_node_ids`` may legitimately contain duplicates
        from the legacy two-slot residual semantics. Counting each
        occurrence inflates ``unresolved``; dedup before counting so
        a 2-slot group with both slots being THIS node correctly
        registers as ``last_count`` (not ``near_count``).
        """

        if node.status != "open":
            return 0, 0
        last_count = 0
        near_count = 0
        for parent_id, assembly_id in self.parent_groups_for_child(node.node_id):
            parent = self.nodes.get(parent_id)
            if parent is None or parent.status != "open":
                continue
            for group in parent.assembly_attempt_groups:
                if group.assembly_id != assembly_id:
                    continue
                # E4: include groups that are tryable on the current
                # witness — covers both fresh open groups AND
                # previously-failed groups whose witness changed.
                if not self._group_tryable_for_attempt(group):
                    break
                child_ids = list(
                    dict.fromkeys(
                        cid
                        for cid in group.child_node_ids
                        if cid in self.nodes
                    )
                )
                if not child_ids or node.node_id not in child_ids:
                    break
                # E5 dead-path bubble: skip the group when ANY non-self
                # sibling is structurally dead (rejected/failed status
                # OR all of its own assembly groups exhausted). The
                # node we're scoring can still be in the candidate set;
                # we exclude only siblings that block closure.
                if any(
                    cid != node.node_id and self._is_structurally_dead(cid)
                    for cid in child_ids
                ):
                    break
                unresolved = sum(
                    1
                    for cid in child_ids
                    if self.nodes[cid].status != "proved"
                )
                if unresolved == 1:
                    last_count += 1
                elif unresolved == 2:
                    near_count += 1
                break
        return last_count, near_count

    def _refresh_priorities_for_neighbors(self, node_id: str) -> None:
        """Recompute priority for the closed node's neighborhood.

        E3 closure-value bonuses are computed at priority-refresh time
        from the inverse index. When a node flips to ``"proved"`` three
        sets of priorities go stale and need recomputation:

        1. The node's PARENTS (``assemble_from_children`` parents whose
           ``unresolved`` child count just dropped by one).
        2. The node's SIBLINGS in each parent group (their last/near-
           last position may have changed).
        3. The node's DIRECT CHILDREN whose closure bonus included the
           now-proved node as one of the parents they would close.
           Without this third set, a parent that closes via the cache /
           direct tactic path leaves its still-open children carrying
           stale closure-bonus credit for closing a parent that no
           longer needs them (caught by adversarial review,
           2026-05-09).

        Transitive refresh up/down beyond one hop is intentionally not
        performed — the bonus calculation only depends on direct
        relationships, and further hops fire naturally when those
        nodes themselves close.
        """

        if not node_id:
            return
        visited: Set[str] = {node_id}

        # (1) + (2) walk UP via inverse index.
        for parent_id, assembly_id in self._assembly_parents_by_child.get(
            node_id, ()
        ):
            parent = self.nodes.get(parent_id)
            if parent is None:
                continue
            # E6 (2026-05-09): "obsolete" is a sticky terminal status —
            # the scheduler ignores it; recomputing priority would
            # clobber the zero we set during cancellation. Only refresh
            # nodes whose status leaves them schedulable.
            if parent.status not in {"proved", "obsolete"}:
                parent.priority = self._priority(parent)
            for group in parent.assembly_attempt_groups:
                if group.assembly_id != assembly_id:
                    continue
                for sibling_id in group.child_node_ids:
                    if sibling_id in visited:
                        continue
                    visited.add(sibling_id)
                    sibling = self.nodes.get(sibling_id)
                    if sibling is None or sibling.status in {"proved", "obsolete"}:
                        continue
                    sibling.priority = self._priority(sibling)
                break

        # (3) walk DOWN: refresh open children whose closure bonus
        # depended on this just-proved node as a target parent.
        closed_node = self.nodes.get(node_id)
        if closed_node is not None:
            descendants: List[str] = []
            for child_id in closed_node.child_node_ids:
                if child_id and child_id not in visited:
                    descendants.append(child_id)
            for group in closed_node.assembly_attempt_groups:
                for child_id in group.child_node_ids:
                    if child_id and child_id not in visited:
                        descendants.append(child_id)
            for child_id in descendants:
                if child_id in visited:
                    continue
                visited.add(child_id)
                child = self.nodes.get(child_id)
                if child is None or child.status in {"proved", "obsolete"}:
                    continue
                child.priority = self._priority(child)

    def _on_root_closure_path(
        self,
        parent_id: str,
        *,
        max_depth: int = 32,
    ) -> bool:
        """True if ``parent_id`` reaches the root via assembly-group chains.

        Walks the inverse index upward up to ``max_depth`` ancestors.
        Cycle-safe via a ``seen`` set. Returns True when the root is
        encountered, False otherwise (including when the search depth
        is exhausted — closure value still applies, just at the lower
        weight).

        Depth cap raised from 8 to 32 (adversarial review 2026-05-09):
        Putnam decompositions can chain lemma-DAG → multi-step proof →
        structural decomposition + helper splits past 8 levels, and an
        8-cap silently zeros the +4 root-path bonus for legitimate
        deep paths. 32 matches the order of magnitude of the
        ``_run_proof_state_assembly_fixpoint`` safety cap.
        """

        if not parent_id:
            return False
        # E6 fix (adversarial review 2026-05-09): refuse to traverse
        # into obsolete or proved parents — neither can ever close
        # the root, so any path through them is a phantom that would
        # award a stale +4 root-path bonus.
        start_node = self.nodes.get(parent_id)
        if start_node is not None and start_node.status in {
            "obsolete",
            "proved",
        }:
            return False
        if parent_id == self.root_node_id:
            return True
        seen: Set[str] = set()
        frontier: List[Tuple[str, int]] = [(parent_id, 0)]
        while frontier:
            current_id, depth = frontier.pop()
            if current_id in seen:
                continue
            seen.add(current_id)
            if current_id == self.root_node_id:
                return True
            if depth >= max_depth:
                continue
            for grand_parent_id, _ in self._assembly_parents_by_child.get(
                current_id, ()
            ):
                if grand_parent_id in seen:
                    continue
                grand_parent = self.nodes.get(grand_parent_id)
                if grand_parent is not None and grand_parent.status in {
                    "obsolete",
                    "proved",
                }:
                    # ``proved`` ancestors are valid root-closure
                    # endpoints only if they ARE the root; otherwise
                    # treat them as terminated and don't traverse
                    # further. ``obsolete`` ancestors lead nowhere.
                    if grand_parent_id == self.root_node_id:
                        return True
                    continue
                frontier.append((grand_parent_id, depth + 1))
        return False

    def _would_create_cycle(self, parent_node_id: str, child_node_id: str) -> bool:
        parent_id = str(parent_node_id or "")
        child_id = str(child_node_id or "")
        if not parent_id or not child_id:
            return False
        if parent_id == child_id:
            return True
        if child_id == self.root_node_id:
            return True
        stack = [child_id]
        seen: Set[str] = set()
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            if current == parent_id:
                return True
            node = self.nodes.get(current)
            if node is None:
                continue
            stack.extend(node.child_node_ids)
        return False

    def _would_create_dependency_cycle(
        self,
        dependency_node_id: str,
        dependent_node_id: str,
    ) -> bool:
        dependency_id = str(dependency_node_id or "")
        dependent_id = str(dependent_node_id or "")
        if not dependency_id or not dependent_id:
            return False
        if dependency_id == dependent_id:
            return True
        if dependent_id == self.root_node_id:
            return True
        stack = [dependency_id]
        seen: Set[str] = set()
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            if current == dependent_id:
                return True
            node = self.nodes.get(current)
            if node is None:
                continue
            stack.extend(node.dependencies)
        return False

    def _remaining_goal_item_rejection(
        self,
        goal: Dict[str, Any],
        *,
        parent_proof_stub: str = "",
        source: str = "",
    ) -> str:
        if not isinstance(goal, dict):
            return ""
        target = self._normalize_goal_text(goal.get("target"))
        compact_target = " ".join(str(target or "").split()).strip()
        for _ in range(8):
            if (
                len(compact_target) >= 2
                and compact_target[0] == "("
                and compact_target[-1] == ")"
            ):
                compact_target = compact_target[1:-1].strip()
                continue
            break
        raw_context = (
            goal.get("hypotheses")
            or goal.get("context")
            or goal.get("local_context")
            or []
        )
        if isinstance(raw_context, str):
            raw_context = [line for line in raw_context.splitlines() if line.strip()]
        context = [
            self._normalize_hypothesis(item)
            for item in list(raw_context or [])
            if str(item or "").strip()
        ]
        if is_answer_unsafe_statement_text(
            compact_target,
            suppress_solution_placeholders=self.suppress_solution_placeholders,
        ) or any(
            is_answer_unsafe_statement_text(
                item,
                suppress_solution_placeholders=self.suppress_solution_placeholders,
            )
            for item in context
        ):
            return "answer_unsafe_remaining_goal"
        if _proof_state_text_has_prompt_control(compact_target) or any(
            _proof_state_text_has_prompt_control(item) for item in context
        ):
            return "prompt_unsafe_remaining_goal"
        # A reconstructed obligation must never carry a proof placeholder in its
        # own statement: `sorry`/`admit` leaking from a partial parent proof
        # yields an unsound, unprovable target.  (See the putnam_2004_a1
        # child-closure regression — pretty-printed goal text can embed both a
        # collapsed ∑ domain and a `sorry` hole.)
        if has_sorry_or_admit(compact_target) or any(
            has_sorry_or_admit(item) for item in context
        ):
            return "proof_placeholder_in_remaining_goal"
        false_elim_source = "False.elim" in str(parent_proof_stub or "") or (
            "False.elim" in str(source or "")
        )
        if compact_target in {"False", "false"} and not context and false_elim_source:
            return "closed_false_residual_goal"
        return ""

    def _residual_batch_admission(
        self,
        node_ids: Optional[Sequence[str]] = None,
        *,
        status: str,
        reason: str = "",
        goal_count: int = 0,
        parent_node: Optional[ProofStateNode] = None,
        source: str = "",
        error_payload: Optional[Mapping[str, Any]] = None,
        emit_transition: bool = False,
        blocker: str = "",
    ) -> ResidualBatchAdmission:
        """Settle one typed residual admission outcome.

        Terminal rejection and successful admission clear pending extraction.
        Deferrable failures leave pending for the executor to re-arm.
        """

        result = ResidualBatchAdmission(
            node_ids,
            status=status,
            reason=reason,
            goal_count=goal_count,
        )
        parent_id = str(getattr(parent_node, "node_id", "") or "")
        live_parent = self.nodes.get(parent_id) if parent_id else parent_node
        if live_parent is None:
            live_parent = parent_node
        if status in {"admitted", "terminal_rejected"}:
            if parent_id:
                self.clear_pending_residual_goal_extraction(parent_id)
            elif live_parent is not None:
                self.clear_pending_residual_goal_extraction(live_parent)
        if status == "terminal_rejected" and reason:
            payload = {
                "source": str(source or ""),
                "parent_node_id": parent_id or str(
                    getattr(live_parent, "node_id", "") or ""
                ),
                "error_type": reason,
            }
            payload.update(dict(error_payload or {}))
            self.record_graph_frontier_error(payload)
            if emit_transition and live_parent is not None:
                self.record_transition(
                    node_id=live_parent.node_id,
                    source=str(source or "spawn_typed_residual_batch"),
                    error_type=reason,
                    action=live_parent.action,
                    blocker=blocker or reason,
                    payload=dict(error_payload or {}),
                )
        return result

    def spawn_typed_residual_batch(
        self,
        batch_receipt: Any,
        *,
        source: str,
        parent_node_id: str,
        parent_proof_stub: str,
        max_goals: int = 4,
    ) -> ResidualBatchAdmission:
        """Bind one Lean runner receipt and atomically admit its child goals.

        This is the canonical production API. It derives the environment and
        parent statement from this state, so callers cannot mint or substitute
        either binding independently. Empty results still compare equal to
        ``[]``; ``status``/``reason`` say whether pending extraction is settled.
        """

        parent = str(parent_node_id or self.root_node_id)
        parent_node = self.nodes.get(parent)
        if parent_node is None:
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="parent_not_found",
                source=source,
            )
        attestations = bind_typed_residual_batch_attestations(
            batch_receipt,
            source=source,
            parent_node_id=parent,
            parent_statement=parent_node.target,
            parent_proof_stub=parent_proof_stub,
            statement_environment_hash=self.statement_environment_hash,
        )
        if not attestations:
            bind_status = str(getattr(attestations, "status", "") or "deferred")
            bind_reason = str(getattr(attestations, "reason", "") or "")
            if bind_status == "terminal_rejected":
                return self._residual_batch_admission(
                    status="terminal_rejected",
                    reason=bind_reason or "bind_contract_rejected",
                    parent_node=parent_node,
                    source=source,
                )
            return self._residual_batch_admission(
                status="deferred",
                reason=bind_reason or "bind_failed",
                parent_node=parent_node,
                source=source,
            )
        context_hash = str(
            attestations[0].get("elaboration_context_hash") or ""
        )
        return self.spawn_attested_remaining_goals(
            attestations,
            source=source,
            parent_node_id=parent,
            parent_proof_stub=parent_proof_stub,
            elaboration_context_hash=context_hash,
            max_goals=max_goals,
        )

    def spawn_attested_remaining_goals(
        self,
        attestations: Sequence[Mapping[str, Any]],
        *,
        source: str,
        parent_node_id: str,
        parent_proof_stub: str,
        elaboration_context_hash: str,
        max_goals: int = 4,
    ) -> ResidualBatchAdmission:
        """Atomically admit an already-bound ordered residual-goal batch.

        Attested batches are not truncated. An arity cap rejects the whole
        receipt; prefix admission would break ``batch_digest`` / ``slot_count``.
        Untyped ``spawn_remaining_goals`` remains the truncating diagnostic path.
        """

        records = list(attestations or ())
        parent = str(parent_node_id or self.root_node_id)
        parent_node = self.nodes.get(parent)
        limit = max(0, int(max_goals or 0))
        goal_count = len(records)
        if parent_node is None:
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="parent_not_found",
                goal_count=goal_count,
                source=source,
            )
        if parent_node.status in {"proved", "obsolete", "rejected", "failed"}:
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="terminal_parent_attested_goals_rejected",
                goal_count=goal_count,
                parent_node=parent_node,
                source=source,
                error_payload={
                    "parent_status": parent_node.status,
                    "blocked_goal_count": goal_count,
                },
                emit_transition=True,
                blocker="attested remaining goals were not spawned for a terminal parent",
            )
        if not records:
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="empty_attestation_batch",
                parent_node=parent_node,
                source=source,
            )
        if len(records) > limit:
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="attested_residual_goal_cap_exceeded",
                goal_count=goal_count,
                parent_node=parent_node,
                source=source,
                error_payload={
                    "residual_goal_count": goal_count,
                    "residual_goal_limit": limit,
                },
                emit_transition=True,
                blocker=(
                    f"typed residual batch left {goal_count} goal(s), "
                    f"exceeding configured limit {limit}"
                ),
            )
        if any(not isinstance(record, Mapping) for record in records):
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="attested_batch_record_invalid",
                goal_count=goal_count,
                parent_node=parent_node,
                source=source,
            )
        statements = [str(record.get("statement") or "") for record in records]
        recorded_parent_authorities = _residual_goal_attestation_authorities(
            parent_node.residual_goal_attestation
        )
        parent_requires_attestation = (
            self._parent_residual_attestation_ledger_is_authoritative(
                parent_node
            )
        )
        if (
            parent_requires_attestation
            and parent_node.residual_goal_attestation
            and not recorded_parent_authorities
        ):
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="malformed_parent_residual_ledger",
                goal_count=goal_count,
                parent_node=parent_node,
                source=source,
            )
        parent_authorities = (
            recorded_parent_authorities if parent_requires_attestation else []
        )
        parent_identities = {
            str(authority.get("structural_identity") or "")
            for authority in parent_authorities
        }
        parent_identities.update(
            self._residual_parent_bound_structural_identities(parent_node)
        )
        if len(parent_identities) > 1:
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="parent_structural_identity_conflict",
                goal_count=goal_count,
                parent_node=parent_node,
                source=source,
            )
        expected_parent_identity = next(iter(parent_identities), "")
        if not _validate_bound_residual_goal_attestation_batch(
            records,
            statements=statements,
            source=source,
            parent_node_id=parent,
            parent_statement=parent_node.target,
            parent_proof_stub=parent_proof_stub,
            statement_environment_hash=self.statement_environment_hash,
            elaboration_context_hash=elaboration_context_hash,
            expected_parent_structural_identity=expected_parent_identity,
        ):
            return self._residual_batch_admission(
                status="terminal_rejected",
                reason="attested_batch_validation_failed",
                goal_count=goal_count,
                parent_node=parent_node,
                source=source,
            )

        # Preflight every target and collision before opening the assembly
        # transaction. This makes any validation, order, environment, stub, or
        # reuse mismatch a strict zero-node/zero-group operation.
        prospective_by_index: Dict[Tuple[str, str], Tuple[str, str]] = {}
        for statement, record in zip(statements, records):
            rejection = self._remaining_goal_item_rejection(
                {"target": statement, "hypotheses": []},
                parent_proof_stub=parent_proof_stub,
                source=source,
            )
            if rejection:
                return self._residual_batch_admission(
                    status="terminal_rejected",
                    reason="attested_goal_policy_rejected",
                    goal_count=goal_count,
                    parent_node=parent_node,
                    source=source,
                    error_payload={"policy_rejection": rejection},
                )
            signature = self._goal_signature(
                statement,
                [],
                source_failure=source,
            )
            target_index_key = self._target_environment_index_key(
                signature.normalized_statement_hash,
                self.statement_environment_hash,
            )
            identity = str(record.get("structural_identity") or "")
            prospective = prospective_by_index.get(target_index_key)
            if prospective is not None:
                previous_statement, previous_identity = prospective
                if previous_identity != identity or (
                    previous_statement != statement
                    and not self._residual_targets_are_equivalent(
                        previous_statement,
                        statement,
                    )
                ):
                    return self._residual_batch_admission(
                        status="terminal_rejected",
                        reason="attested_batch_collision",
                        goal_count=goal_count,
                        parent_node=parent_node,
                        source=source,
                    )
            prospective_by_index[target_index_key] = (
                statement,
                identity,
            )
            existing_id = self._node_by_target.get(target_index_key)
            if not existing_id:
                continue
            existing = self.nodes.get(existing_id)
            existing_authorities = _residual_goal_attestation_authorities(
                existing.residual_goal_attestation if existing is not None else {}
            )
            if (
                existing is None
                or existing.status in {"obsolete", "failed", "rejected"}
                or (
                    existing.target != statement
                    and not self._residual_targets_are_equivalent(
                        existing.target,
                        statement,
                    )
                )
                or existing.statement_environment_hash
                != self.statement_environment_hash
                or self._would_create_cycle(parent, existing.node_id)
                or any(
                    str(authority.get("structural_identity") or "") != identity
                    for authority in existing_authorities
                )
            ):
                return self._residual_batch_admission(
                    status="terminal_rejected",
                    reason="attested_existing_goal_conflict",
                    goal_count=goal_count,
                    parent_node=parent_node,
                    source=source,
                )

        checkpoint_id = self.checkpoint(label="attested_remaining_goals")
        spawned: List[str] = []
        try:
            if (
                not parent_requires_attestation
                and parent_node.residual_goal_attestation
                and not recorded_parent_authorities
            ):
                # Root and other non-residual nodes do not derive execution
                # authority from a residual-goal ledger.  Once a fresh batch
                # has independently validated, heal an irrelevant malformed
                # durable value instead of allowing it to veto this route.
                parent_node.residual_goal_attestation = {}
            assembly_id = self._start_assembly_attempt(
                parent_node_id=parent,
                source=source,
                proof_stub=parent_proof_stub,
            )
            if not assembly_id:
                self.rollback(checkpoint_id)
                return self._residual_batch_admission(
                    status="terminal_rejected",
                    reason="attested_assembly_start_failed",
                    goal_count=goal_count,
                    parent_node=parent_node,
                    source=source,
                )
            for group in parent_node.assembly_attempt_groups:
                if group.assembly_id == assembly_id:
                    group.residual_goal_slot_count = len(records)
                    group.residual_goal_batch_digest = str(
                        records[0].get("batch_digest") or ""
                    )
                    group.residual_goal_elaboration_context_hash = str(
                        records[0].get("elaboration_context_hash") or ""
                    )
                    break
            for statement, record in zip(statements, records):
                node = self._spawn_remaining_goal(
                    {"target": statement, "hypotheses": []},
                    source=source,
                    parent_node_id=parent,
                    parent_proof_stub=parent_proof_stub,
                    assembly_id=assembly_id,
                    statement_environment_hash=self.statement_environment_hash,
                    standalone_statement=statement,
                    residual_goal_attestation=record,
                )
                if node is None:
                    self.rollback(checkpoint_id)
                    return self._residual_batch_admission(
                        status="terminal_rejected",
                        reason="attested_spawn_partial_failed",
                        goal_count=goal_count,
                        parent_node=parent_node,
                        source=source,
                    )
                if node.node_id not in spawned:
                    spawned.append(node.node_id)
            # The inverse transition needs a complete attached route.  Reuse
            # the centralized validator so restored nodes recover their exact
            # saved lifecycle only after every batch authority is present.
            self._quarantine_residual_goal_attestation_failures()
            self.commit(checkpoint_id)
            current_parent = self.nodes.get(parent)
            return self._residual_batch_admission(
                spawned,
                status="admitted",
                reason="admitted",
                goal_count=goal_count,
                parent_node=current_parent,
                source=source,
            )
        except Exception:
            self.rollback(checkpoint_id)
            return self._residual_batch_admission(
                status="deferred",
                reason="admission_exception",
                goal_count=goal_count,
                parent_node=parent_node,
                source=source,
            )

    def spawn_remaining_goals(
        self,
        goals: Sequence[Any],
        *,
        source: str,
        parent_node_id: str,
        parent_proof_stub: str = "",
        max_goals: int = 4,
        allow_unvalidated_spawn: bool = False,
    ) -> List[str]:
        """Admit diagnostic remaining goals, truncating to ``max_goals``.

        Typed residual receipts must use ``spawn_typed_residual_batch``. That
        path rejects an over-cap attested batch instead of admitting a prefix,
        because ``batch_digest`` and ``slot_count`` describe the full Lean
        remainder.
        """
        spawned: List[str] = []
        parent = str(parent_node_id or self.root_node_id)
        parent_node = self.nodes.get(parent)
        if parent_node is not None and parent_node.status in {
            "proved",
            "obsolete",
            "rejected",
            "failed",
        }:
            self.record_graph_frontier_error(
                {
                    "source": str(source or ""),
                    "parent_node_id": parent,
                    "error_type": "terminal_parent_remaining_goals_rejected",
                    "parent_status": parent_node.status,
                    "blocked_goal_count": len(list(goals or [])),
                }
            )
            self.record_transition(
                node_id=parent_node.node_id,
                source=str(source or "spawn_remaining_goals"),
                error_type="terminal_parent_remaining_goals_rejected",
                action=parent_node.action,
                blocker="remaining goals were not spawned for a terminal parent",
                payload={
                    "blocked_goal_count": len(list(goals or [])),
                    "parent_status": parent_node.status,
                },
            )
            return []
        if not str(parent_proof_stub or "").strip() and not bool(
            allow_unvalidated_spawn
        ):
            blocker = (
                "remaining goals were not spawned because no validated parent "
                "proof stub was supplied"
            )
            self.record_graph_frontier_error(
                {
                    "source": str(source or ""),
                    "parent_node_id": parent,
                    "error_type": "unvalidated_remaining_goals_rejected",
                    "blocked_goal_count": len(list(goals or [])),
                }
            )
            if parent_node is not None:
                self.record_transition(
                    node_id=parent_node.node_id,
                    source=str(source or "spawn_remaining_goals"),
                    error_type="unvalidated_remaining_goals_rejected",
                    action=parent_node.action,
                    blocker=blocker,
                    payload={"blocked_goal_count": len(list(goals or []))},
                )
            return []
        previous_action = parent_node.action if parent_node is not None else ""
        previous_priority = parent_node.priority if parent_node is not None else 0.0
        goal_items: List[Dict[str, Any]] = []
        for item in list(goals or []):
            if isinstance(item, dict):
                goal_items.append(item)
            elif isinstance(item, str):
                parsed_goals = self._goals_from_rendered_text(
                    item,
                    max_goals=max_goals,
                )
                if parsed_goals:
                    goal_items.extend(parsed_goals)
                else:
                    plain_target = self._plain_remaining_goal_target(item)
                    if plain_target:
                        goal_items.append({"target": plain_target, "hypotheses": []})
            if len(goal_items) >= max(0, int(max_goals or 0)):
                break
        goal_items = goal_items[: max(0, int(max_goals or 0))]
        for goal in goal_items:
            rejection = self._remaining_goal_item_rejection(
                goal,
                parent_proof_stub=parent_proof_stub,
                source=source,
            )
            if not rejection:
                continue
            blocker = f"remaining goal rejected before spawn: {rejection}"
            self.record_graph_frontier_error(
                {
                    "source": str(source or ""),
                    "parent_node_id": parent,
                    "error_type": "remaining_goal_rejected",
                    "reason": rejection,
                    "target": str(goal.get("target") or ""),
                }
            )
            if parent_node is not None:
                self.record_transition(
                    node_id=parent_node.node_id,
                    source=str(source or "spawn_remaining_goals"),
                    error_type="remaining_goal_rejected",
                    action=parent_node.action,
                    blocker=blocker,
                    payload={
                        "reason": rejection,
                        "target": str(goal.get("target") or ""),
                    },
                )
                parent_node.blocker = blocker
                parent_node.priority = self._priority(parent_node)
            return []
        if proof_state_source_requires_residual_goal_attestation(source):
            # Production residual goals must enter through the typed atomic
            # API. ``allow_unvalidated_spawn`` is deliberately unable to
            # bypass this boundary, but content-policy diagnostics above keep
            # their established precedence and audit trail.
            return []
        assembly_id = self._start_assembly_attempt(
            parent_node_id=parent,
            source=source,
            proof_stub=parent_proof_stub,
        )
        for goal in goal_items:
            node = self._spawn_remaining_goal(
                goal,
                source=source,
                parent_node_id=parent,
                parent_proof_stub=parent_proof_stub,
                assembly_id=assembly_id,
            )
            if node is not None and node.node_id not in spawned:
                spawned.append(node.node_id)
        if assembly_id and not spawned:
            parent_node = self.nodes.get(parent)
            if parent_node is not None:
                parent_node.assembly_attempt_groups = [
                    group
                    for group in parent_node.assembly_attempt_groups
                    if group.assembly_id != assembly_id
                ]
                if not parent_node.child_node_ids and not parent_node.assembly_attempt_groups:
                    parent_node.action = previous_action
                    parent_node.priority = previous_priority
        return spawned

    def spawn_remaining_goals_from_text(
        self,
        rendered: str,
        *,
        source: str,
        parent_node_id: str,
        parent_proof_stub: str = "",
        max_goals: int = 3,
        allow_unvalidated_spawn: bool = False,
    ) -> List[str]:
        goals = self._goals_from_rendered_text(rendered, max_goals=max_goals)
        return self.spawn_remaining_goals(
            goals,
            source=source,
            parent_node_id=parent_node_id,
            parent_proof_stub=parent_proof_stub,
            max_goals=max_goals,
            allow_unvalidated_spawn=allow_unvalidated_spawn,
        )

    def _goals_from_rendered_text(
        self,
        rendered: str,
        *,
        max_goals: int,
    ) -> List[Dict[str, Any]]:
        text = str(rendered or "")
        if "⊢" not in text:
            return []
        blocks = self._split_rendered_goal_blocks(text)
        if not blocks:
            blocks = [text]
        goals: List[Dict[str, Any]] = []
        for block in blocks:
            raw_lines = block.splitlines()
            target_lines: List[str] = []
            hypotheses: List[str] = []
            for raw_line in raw_lines:
                line = raw_line.strip()
                if not line:
                    if target_lines:
                        target_lines.append("")
                    continue
                if "⊢" in line:
                    target_lines = [line.split("⊢", 1)[1].strip()]
                    continue
                if target_lines:
                    prev = (target_lines[-1] or "").rstrip()
                    is_indented = raw_line[:1].isspace()
                    target_prefix = "\n".join(target_lines).rstrip()
                    target_prefix_last = next(
                        (
                            item.strip()
                            for item in reversed(target_prefix.splitlines())
                            if item.strip()
                        ),
                        "",
                    )
                    blank_layout_body = bool(
                        not prev
                        and (
                            _has_layout_sensitive_local_let(target_prefix)
                            or _line_has_layout_local_let_without_body(
                                target_prefix_last
                            )
                        )
                    )
                    if (
                        _residual_target_needs_continuation(prev)
                        or is_indented
                        or blank_layout_body
                    ):
                        target_lines.append(
                            raw_line.rstrip()
                            if is_indented or not blank_layout_body
                            else "  " + line
                        )
                        continue
                    continue
                hypothesis = sanitize_goal_hypothesis(line)
                if hypothesis:
                    hypotheses.append(hypothesis)
                elif ":" in line:
                    self.residual_goal_context_filtered += 1
            target_multiline = "\n".join(
                item.rstrip() for item in target_lines
            ).strip()
            if (
                "\n" in target_multiline
                and _has_layout_sensitive_local_let(target_multiline)
            ):
                target = target_multiline
            else:
                target = " ".join(item.strip() for item in target_lines if item).strip()
            if target:
                goals.append(
                    {
                        "target": target,
                        "hypotheses": hypotheses,
                        "rendered_target": True,
                    }
                )
            if len(goals) >= max(0, int(max_goals or 0)):
                break
        return goals

    @staticmethod
    def _split_rendered_goal_blocks(text: str) -> List[str]:
        blocks: List[str] = []
        current: List[str] = []
        lines = str(text or "").splitlines()

        def flush() -> None:
            nonlocal current
            block = "\n".join(current).strip()
            if block and "⊢" in block:
                blocks.append(block)
            current = []

        def context_block_before_next_turnstile(start_idx: int) -> bool:
            for rest in lines[start_idx:]:
                if not rest.strip():
                    return False
                if "⊢" in rest:
                    return True
                if not sanitize_goal_hypothesis(rest.strip()):
                    return False
            return False

        for idx, line in enumerate(lines):
            if re.match(r"^\s*case\s+", line) and current:
                flush()
                current.append(line)
                continue
            if (
                current
                and "⊢" not in line
                and any("⊢" in part for part in current)
                and context_block_before_next_turnstile(idx)
            ):
                flush()
                current.append(line)
                continue
            if "⊢" in line and any("⊢" in part for part in current):
                flush()
                current.append(line)
                continue
            if not line.strip():
                next_nonempty = next(
                    (rest for rest in lines[idx + 1 :] if rest.strip()),
                    "",
                )
                if "⊢" in next_nonempty:
                    flush()
                    continue
                if any("⊢" in part for part in current) and next_nonempty[:1].isspace():
                    current.append(line)
                    continue
                if any("⊢" in part for part in current):
                    rendered_so_far = "\n".join(current)
                    target_so_far = rendered_so_far.split("⊢", 1)[1]
                    target_last = next(
                        (
                            item.strip()
                            for item in reversed(target_so_far.splitlines())
                            if item.strip()
                        ),
                        "",
                    )
                    if (
                        _has_layout_sensitive_local_let(target_so_far)
                        or _line_has_layout_local_let_without_body(target_last)
                    ):
                        current.append(line)
                        continue
                flush()
                continue
            current.append(line)
        flush()
        return blocks

    def _priority(self, node: ProofStateNode) -> float:
        if node.status == "proved":
            return 0.0
        base = 100.0 if node.kind == "root" else 72.0
        fanout = sum(
            1
            for other in self.nodes.values()
            if node.node_id in getattr(other, "dependencies", [])
        )
        base += min(12.0, 3.0 * fanout)
        if node.action in {"spawn_child_goals", "prove_child_helper"}:
            base += 12.0
        if node.action in {
            "manufacture_or_retrieve_missing_identifier",
            "namespace_type_retrieval",
            "bridge_rewrite_or_coercion",
        }:
            base += 8.0
        if node.action == "assemble_from_children":
            unresolved = sum(
                1
                for child_id in node.child_node_ids
                if self.nodes.get(child_id) is not None
                and self.nodes[child_id].status != "proved"
            )
            base += max(0.0, 10.0 - 3.0 * unresolved)
        # E3: closure-value bonus. An open child whose proof would close
        # one or more parent assembly groups gets a bonus. Scaled by
        # whether any unblocked parent is on the root-closure path
        # (those moves are strictly more valuable than closing a side
        # branch). Computed via the inverse index in O(parents-of-this-
        # child) — cheap relative to a graph scan.
        if node.status == "open" and self._assembly_parents_by_child.get(node.node_id):
            last_count, near_count = self.closure_unblocks_count(node)
            if last_count or near_count:
                root_path_bonus = 0.0
                if last_count:
                    on_root = any(
                        self._on_root_closure_path(parent_id)
                        for parent_id, _assembly_id in self.parent_groups_for_child(
                            node.node_id
                        )
                    )
                    root_path_bonus = 4.0 if on_root else 0.0
                # +6 per parent we'd immediately close (capped),
                # +1.5 per parent we'd bring to second-to-last (capped),
                # +4 if any unblocked parent reaches the root.
                base += min(18.0, 6.0 * last_count)
                base += min(6.0, 1.5 * near_count)
                base += root_path_bonus
        if node.goal is not None and node.goal.shape_tags:
            base += min(8.0, 1.5 * len(node.goal.shape_tags))
        if node.retrieval_hit_count:
            base += min(10.0, 1.2 * node.retrieval_hit_count)
        if node.cache_hits:
            base += min(8.0, 2.0 * node.cache_hits)
        if node.close_attempts:
            base -= min(24.0, 2.0 * float(node.close_attempts))
        if node.budget_skips:
            base -= min(30.0, 7.5 * float(node.budget_skips))
        base -= min(40.0, 6.0 * float(node.failed_attempts))
        return max(1.0, base)

    def _statement_from_context(self, target: str, context: Sequence[str]) -> str:
        target, context = self._sanitize_context_for_statement(target, context)
        body = target
        pending_binders: List[str] = []

        def flush_binders() -> None:
            nonlocal body, pending_binders
            if not pending_binders:
                return
            body = "∀ " + " ".join(reversed(pending_binders)) + ", " + body
            pending_binders = []

        for hyp in reversed(context):
            if self._is_local_definition_context(hyp):
                flush_binders()
                let_text = str(hyp or "").strip().rstrip(";")
                if not let_text:
                    continue
                prefix = let_text if let_text.startswith("let ") else f"let {let_text}"
                body = f"{prefix}; {body}"
                continue
            if ":" not in hyp or "\n" in hyp or "⊢" in hyp:
                continue
            pending_binders.append(f"({hyp})")
        flush_binders()
        return body

    def _sanitize_context_for_statement(
        self,
        target: str,
        context: Sequence[str],
    ) -> Tuple[str, List[str]]:
        sanitized_target, sanitized_context, _argument_terms = (
            self._sanitize_context_for_statement_with_map(target, context)
        )
        return sanitized_target, sanitized_context

    def _sanitize_context_for_statement_with_map(
        self,
        target: str,
        context: Sequence[str],
    ) -> Tuple[str, List[str], Dict[str, str]]:
        parsed_entries_raw: List[Tuple[str, List[str], str]] = []
        reserved_clean_names: Set[str] = set()
        for hyp in context:
            safe_hyp = sanitize_goal_hypothesis(str(hyp or ""))
            if not safe_hyp:
                continue
            if self._is_local_definition_context(safe_hyp):
                names = self._split_local_definition_names(safe_hyp)
                parsed_entries_raw.append(("let", names, safe_hyp))
                for name in names:
                    if self._is_clean_local_name(name):
                        reserved_clean_names.add(str(name).strip())
                continue
            names, typ = self._split_hypothesis_binder(safe_hyp)
            if not names or not typ:
                continue
            parsed_entries_raw.append(("binder", names, typ))
            for name in names:
                if self._is_clean_local_name(name):
                    reserved_clean_names.add(str(name).strip())

        replacements: Dict[str, str] = {}
        used: Set[str] = set()
        argument_terms: Dict[str, str] = {}

        def apply_replacements(text: str) -> str:
            return self._replace_local_names_tokenwise(text, replacements)

        sanitized_context: List[str] = []
        for kind, names, value in parsed_entries_raw:
            if kind == "let":
                sanitized_context.append(
                    self._sanitize_local_definition_line(
                        value,
                        names,
                        replacements,
                        used,
                        reserved_clean_names=reserved_clean_names,
                    )
                )
                continue
            sanitized_names: List[str] = []
            for name in names:
                sanitized = self._sanitize_local_name(
                    name,
                    used,
                    reserved_clean_names=reserved_clean_names,
                )
                sanitized_names.append(sanitized)
            sanitized_context.append(f"{' '.join(sanitized_names)} : {apply_replacements(value)}")
            for original, sanitized in zip(names, sanitized_names):
                replacements[original] = sanitized
                argument_terms[sanitized] = self._parent_argument_term_for_local(
                    original,
                    sanitized,
                )
        return apply_replacements(target), sanitized_context, argument_terms

    def _parent_argument_term_for_local(self, original: str, sanitized: str) -> str:
        raw = str(original or "").strip()
        clean = str(sanitized or "").strip()
        if raw and raw == clean and self._is_clean_local_name(raw):
            return raw
        if raw and self._is_clean_local_name(raw):
            return raw
        return "_"

    def _sanitize_local_definition_line(
        self,
        value: str,
        names: Sequence[str],
        replacements: Dict[str, str],
        used: Set[str],
        *,
        reserved_clean_names: Set[str],
    ) -> str:
        head, body = split_goal_definition_binding(str(value or "").strip())
        if not head or not body or not names:
            return self._replace_local_names_tokenwise(value, replacements)
        raw_head = head.strip()
        has_let = raw_head.startswith("let ")
        inner = raw_head[4:].strip() if has_let else raw_head
        original = str(names[0] or "").strip()
        sanitized = self._sanitize_local_name(
            original,
            used,
            reserved_clean_names=reserved_clean_names,
        )
        colon = _find_top_level_colon(inner)
        if colon >= 0:
            typ = inner[colon + 1 :].strip()
            typ = self._replace_local_names_tokenwise(typ, replacements)
            sanitized_inner = f"{sanitized} : {typ}" if typ else sanitized
        else:
            sanitized_inner = sanitized
        body = self._replace_local_names_tokenwise(body.strip(), replacements)
        replacements[original] = sanitized
        prefix = "let " if has_let else ""
        return f"{prefix}{sanitized_inner} := {body}"

    @staticmethod
    def _is_local_name_char(ch: str) -> bool:
        return _is_local_name_char(ch)

    @classmethod
    def _has_local_name_boundary(cls, text: str, start: int, end: int) -> bool:
        return _has_local_name_boundary(text, start, end)

    @classmethod
    def _replace_local_names_tokenwise(
        cls,
        text: str,
        replacements: Dict[str, str],
    ) -> str:
        return _replace_local_names_tokenwise_text(text, replacements)

    def _split_hypothesis_binder(self, hyp: str) -> Tuple[List[str], str]:
        text = str(hyp or "").strip()
        if (
            self._is_local_definition_context(text)
            or "\n" in text
            or "⊢" in text
        ):
            return [], ""
        colon = _find_top_level_colon(text)
        if colon < 0:
            return [], ""
        lhs, rhs = text[:colon].strip(), text[colon + 1 :].strip()
        names: List[str] = []
        index = 0
        while index < len(lhs):
            if lhs[index].isspace():
                index += 1
                continue
            quote_end = _lean_quote_end(lhs, index)
            if quote_end > index:
                names.append(lhs[index:quote_end].strip())
                index = quote_end
                continue
            start = index
            while index < len(lhs) and not lhs[index].isspace():
                index += 1
            names.append(lhs[start:index].strip())
        return [item for item in names if item], rhs.strip()

    def _is_local_definition_context(self, hyp: str) -> bool:
        head, body = split_goal_definition_binding(str(hyp or "").strip())
        if not head or not body:
            return False
        raw = head.strip()
        if raw.startswith("let "):
            raw = raw[4:].strip()
        colon = _find_top_level_colon(raw)
        if colon >= 0:
            _names, typ = raw[:colon], raw[colon + 1 :]
            typ_text = typ.strip()
            if typ_text.startswith("let ") or " let " in typ_text:
                return False
        return bool(self._split_local_definition_names(hyp))

    def _split_local_definition_names(self, hyp: str) -> List[str]:
        head, body = split_goal_definition_binding(str(hyp or "").strip())
        if not head or not body:
            return []
        raw = head.strip()
        if raw.startswith("let "):
            raw = raw[4:].strip()
        colon = _find_top_level_colon(raw)
        if colon >= 0:
            raw = raw[:colon].strip()
        if not raw:
            return []
        if (
            re.fullmatch(r"«[^»]+»", raw)
            or self._is_clean_local_name(raw)
            or re.fullmatch(r"(?:[^\W\d]|_)[\w'✝]*", raw, flags=re.UNICODE)
        ):
            return [raw]
        return []

    @staticmethod
    def _is_clean_local_name(name: str) -> bool:
        raw = str(name or "").strip()
        if (
            raw
            and _LEAN_LOCAL_IDENT_RE.fullmatch(raw)
            and raw not in _LEAN_RESERVED_LOCAL_NAMES
            and "✝" not in raw
        ):
            return True
        return False

    def _sanitize_local_name(
        self,
        name: str,
        used: Set[str],
        *,
        reserved_clean_names: Set[str],
    ) -> str:
        raw = str(name or "").strip()
        if self._is_clean_local_name(raw) and raw not in used:
            used.add(raw)
            return raw
        base = re.sub(r"\W+", "_", raw, flags=re.UNICODE).strip("_")
        if (
            not base
            or not _LEAN_LOCAL_IDENT_RE.fullmatch(base)
            or base in _LEAN_RESERVED_LOCAL_NAMES
        ):
            base = "h_inacc"
        candidate = base
        i = 1
        while (
            candidate in used
            or candidate in reserved_clean_names
            or not _LEAN_LOCAL_IDENT_RE.fullmatch(candidate)
        ):
            candidate = f"{base}_{i}"
            i += 1
        used.add(candidate)
        return candidate

    def _normalize_hypothesis(self, value: Any) -> str:
        return _normalize_proof_state_context_item(value)

    def _normalize_goal_text(self, value: Any) -> str:
        return _normalize_proof_state_goal_text(value)

    def _plain_remaining_goal_target(self, value: Any) -> str:
        text = self._normalize_goal_text(value)
        if not text:
            return ""
        lower = text.lower()
        if re.match(r"^[^:\s]+\.lean:\d+:\d+:\s*(error|warning|info)\b", text):
            return ""
        if lower.startswith(("error:", "warning:", "info:", "note:", "unsolved goals")):
            return ""
        diagnostic_needles = (
            "no goals to be solved",
            "tactic failed",
            "type mismatch",
            "failed to synthesize",
            "unknown identifier",
            "invalid field",
            "invalid projection",
            "parse error",
            "unexpected token",
        )
        if any(needle in lower for needle in diagnostic_needles):
            return ""
        return text

    def _context_defined_names(self, hyp: str) -> List[str]:
        if self._is_local_definition_context(hyp):
            return self._split_local_definition_names(hyp)
        names, _typ = self._split_hypothesis_binder(hyp)
        return names

    def _free_local_names(self, text: str) -> List[str]:
        names: List[str] = []
        seen: Set[str] = set()
        source = str(text or "")
        for match in _LEAN_LOCAL_TOKEN_RE.finditer(source):
            token = match.group(0)
            if (
                not self._has_local_name_boundary(source, match.start(), match.end())
                or "." in token
                or token in _LEAN_BUILTIN_WORDS
            ):
                continue
            if token and token not in seen:
                seen.add(token)
                names.append(token)
        return names

    def _normalize_statement_for_hash(
        self,
        statement: str,
        *,
        bound_names: Sequence[str],
    ) -> str:
        return canonicalize_lean_statement_for_identity(
            statement,
            extra_bound_names=bound_names,
        )

    def _extract_goal_constants(
        self,
        text: str,
        *,
        bound_names: Set[str],
    ) -> List[str]:
        constants: List[str] = []
        seen: Set[str] = set()
        source = _blank_lean_quoted_identifier_contents(str(text or ""))
        for symbol, replacement in _LEAN_TYPE_SYMBOLS.items():
            if symbol in source and replacement not in seen:
                constants.append(replacement)
                seen.add(replacement)
        method_aliases = {
            ".choose": "Nat.choose",
            ".factorial": "Nat.factorial",
            ".succ": "Nat.succ",
            "LocallyFiniteOrder.finsetIcc": "Finset.Icc",
        }
        for needle, replacement in method_aliases.items():
            if needle in source and replacement not in seen:
                seen.add(replacement)
                constants.append(replacement)
        for match in _LEAN_IDENTIFIER_RE.finditer(source):
            if not self._has_local_name_boundary(source, match.start(), match.end()):
                continue
            token = match.group(0)
            if not token or token in seen:
                continue
            short = token.rsplit(".", 1)[-1]
            if token in bound_names:
                continue
            if "." in token and token.split(".", 1)[0] in bound_names:
                continue
            if short in _LEAN_BUILTIN_WORDS or token in _LEAN_BUILTIN_WORDS:
                continue
            if short.startswith("_b") or short.startswith("?m"):
                continue
            seen.add(token)
            constants.append(token)
            if "." in token:
                namespace = token.split(".", 1)[0]
                if namespace and namespace not in seen and namespace not in bound_names:
                    seen.add(namespace)
                    constants.append(namespace)
        return constants[:32]

    def _first_constant(self, text: str) -> str:
        constants = self._extract_goal_constants(text, bound_names=set())
        return constants[0] if constants else ""

    def _goal_result_head(self, target: str, *, bound_names: Optional[Set[str]] = None) -> str:
        text = lean_statement_conclusion(self._normalize_goal_text(target))
        bound = set(bound_names or set()).union(lean_statement_bound_names(target))
        for symbol, tag in _GOAL_OPERATOR_TAGS:
            if _has_goal_operator(text, symbol):
                return tag
        for keyword in ("Prop", "Type", "Nat", "Int", "Rat", "Real", "Complex", "Finset", "Set"):
            if re.search(rf"(?<![A-Za-z0-9_']){re.escape(keyword)}(?![A-Za-z0-9_'])", text):
                return keyword
        constants = self._extract_goal_constants(text, bound_names=bound)
        return constants[0] if constants else ""

    def _typeclass_needs(self, text: str) -> List[str]:
        out: List[str] = []
        seen: Set[str] = set()
        for bracketed in re.findall(r"\[([^\[\]]{1,160})\]", str(text or "")):
            compact = _compact_search_text(bracketed, limit=120)
            if compact and compact not in seen:
                seen.add(compact)
                out.append(compact)
        return out[:12]

    def _namespace_list(self, constants: Sequence[str]) -> List[str]:
        seen: Set[str] = set()
        out: List[str] = []
        for constant in constants:
            text = str(constant or "").strip()
            if "." in text:
                ns = text.split(".", 1)[0]
            else:
                ns = text if text in {"Nat", "Int", "Rat", "Real", "Complex", "Finset", "Set", "List", "Polynomial"} else ""
            if ns and ns not in seen:
                seen.add(ns)
                out.append(ns)
        return out[:12]

    def _goal_shape_tags(
        self,
        *,
        constants: Sequence[str],
        target: str,
        typeclass_needs: Sequence[str],
        binder_structure: Sequence[str],
    ) -> List[str]:
        tags: List[str] = []
        seen: Set[str] = set()

        def add(value: str) -> None:
            item = str(value or "").strip()
            if item and item not in seen:
                seen.add(item)
                tags.append(item)

        constant_tokens = {
            token
            for constant in constants
            for token in (
                str(constant or "").strip(),
                str(constant or "").split(".", 1)[0],
                str(constant or "").rsplit(".", 1)[-1],
            )
            if token
        }
        for keyword in sorted(_MATHLIB_SHAPE_KEYWORDS, key=len, reverse=True):
            if keyword in constant_tokens:
                add(keyword)
        for symbol, tag in _GOAL_OPERATOR_TAGS:
            if _has_goal_operator(target, symbol):
                add(tag)
        if ".choose" in target:
            add("Nat.choose")
        if "↑" in target:
            add("cast")
        for need in typeclass_needs:
            head = self._first_constant(need)
            if head:
                add(f"typeclass:{head}")
        for binder in binder_structure[:6]:
            add(f"binder:{binder}")
        return tags[:24]

    def _plan_hints(self, goal: NormalizedProofGoal) -> List[str]:
        tags = set(goal.shape_tags)
        constants = set(goal.constants_used)
        hints: List[str] = []
        if {"Nat.choose", "Finset"} & constants or {"Nat.choose", "Finset"} & tags:
            hints.append("binomial/finite-sum route: retrieve choose identities, normalize ranges, then prove residual sums")
        if any("inequality" in tag for tag in tags):
            hints.append("inequality route: split hypotheses, normalize casts, try nlinarith/omega after bridge lemmas")
        if {"dvd", "divisibility dvd"} & tags or "Nat.Prime" in constants:
            hints.append("number-theory route: retrieve divisibility/prime facts, expose gcd/parity sublemmas")
        if "equality rewrite" in tags:
            hints.append("rewrite route: prove local normalization lemmas, then assemble by simpa/ring_nf")
        if "membership set" in tags or "Set" in constants:
            hints.append("set route: extensionality/membership child goals before root assembly")
        if not hints:
            hints.append("direct route: search exact/apply facts, then split remaining goals into helper nodes")
        return hints[:6]
