"""Run-local proof graph for mini-prover search state.

The graph is intentionally small and serializable.  It records root/helper/
scratch nodes, dependency edges, and proof attempts so the controller can make
future scheduling decisions from structured state instead of reconstructing
everything from a chat transcript and flat helper list.
"""

from __future__ import annotations

import copy
import hashlib
import hmac
import json
import re
import unicodedata
from dataclasses import asdict, dataclass, field
from functools import lru_cache
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from .lean_syntax import (
    lean_relation_binder_bound_names,
    lean_relation_binder_equivalent,
    lean_relation_binder_premise,
    split_lean_top_level_implications,
)
from .contract_identity import (
    has_lean_contract_identity,
    lean_contract_evidence_receipt_matches,
    make_lean_contract_evidence_receipt,
    parse_lean_contract_identity,
)
from .proof_lineage import ProofLineageEnvelope
from .utils import (
    contains_metavariable_placeholder,
    has_sorry_or_admit,
    is_non_theorem_standalone_lean_expr,
    is_standalone_sort_like_lean_expr,
    normalize_statement,
    normalize_subgoal_statement,
    _lean_lexical_skip_end,
)


def graph_text_hash(text: str) -> str:
    return hashlib.sha256(str(text or "").encode("utf-8")).hexdigest()[:16]


def graph_helper_answer_safety_receipt(
    *,
    source_hash: str,
    source_digest: str,
    statement_key: str,
    environment_hash: str,
    render_policy: str,
    visibility_policy: str,
    admission_policy: str,
) -> str:
    """Bind dossier answer-safety admission to the exact helper context."""

    source = str(source_hash or "").strip()
    digest = str(source_digest or "").strip().lower()
    statement = str(statement_key or "").strip()
    policy = str(admission_policy or "").strip()
    if (
        not source
        or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        or not statement
        or policy not in {
            "official_answer_visible",
            "solution_suppressed",
        }
    ):
        return ""
    payload = json.dumps(
        {
            "admission_policy": policy,
            "environment_hash": str(environment_hash or "").strip(),
            "render_policy": str(render_policy or "").strip(),
            "source_hash": source,
            "source_digest": digest,
            "statement_key": statement,
            "visibility_policy": str(visibility_policy or "").strip(),
            "version": 1,
        },
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    return "graph-answer-safety-v1:" + hashlib.sha256(
        payload.encode("utf-8", errors="replace")
    ).hexdigest()


def graph_helper_answer_safety_receipt_matches(
    receipt: str,
    **metadata: str,
) -> bool:
    expected = graph_helper_answer_safety_receipt(**metadata)
    return bool(
        expected
        and hmac.compare_digest(str(receipt or "").strip(), expected)
    )


_GRAPH_CONTRACT_IDENTITY_KEYS = (
    "contract_identity",
    "statement_contract_identity",
    "structural_statement_identity",
)


FORMALIZATION_BRIDGE_OPEN_PREMISE_TRUST = "verified_bridge_open_premise"


def _graph_metadata_raw_lean_identities(
    metadata: Mapping[str, Any],
) -> tuple[str, ...]:
    """Collect format-valid raw Lean identity tokens from graph metadata aliases."""

    identities: list[str] = []
    seen: set[str] = set()
    for key in _GRAPH_CONTRACT_IDENTITY_KEYS:
        raw = str(metadata.get(key) or "").strip()
        if not has_lean_contract_identity(raw) or raw in seen:
            continue
        seen.add(raw)
        identities.append(raw)
    return tuple(identities)


def _graph_metadata_contract_identity(metadata: Mapping[str, Any]) -> str:
    """Return one unambiguous structural identity from graph metadata."""

    identities = set(_graph_metadata_raw_lean_identities(metadata))
    return next(iter(identities)) if len(identities) == 1 else ""

def bind_graph_contract_identity_metadata(
    statement: str,
    metadata: Dict[str, Any],
) -> None:
    """Retain only structural evidence already bound by Lean analysis.

    Graph construction is not an elaboration boundary and must never mint
    authority from a format-valid token supplied in arbitrary metadata.
    """

    identity = _graph_metadata_contract_identity(metadata)
    statement_key = graph_statement_key(statement)
    environment_hash = str(
        metadata.get("statement_environment_hash") or ""
    ).strip()
    receipt = str(metadata.get("contract_identity_evidence_receipt") or "").strip()
    if (
        not identity
        or not statement_key
        or str(metadata.get("contract_identity_statement_key") or "").strip()
        != statement_key
        or str(
            metadata.get("contract_identity_environment_hash") or ""
        ).strip()
        != environment_hash
        or not lean_contract_evidence_receipt_matches(
            receipt,
            identity=identity,
            statement_key=statement_key,
            environment_hash=environment_hash,
        )
    ):
        metadata.pop("contract_identity_statement_key", None)
        metadata.pop("contract_identity_environment_hash", None)
        metadata.pop("contract_identity_evidence_receipt", None)
        # An unbound format-valid token is not Lean evidence. Leaving it in
        # place lets surface equality ignore a conflicting structural identity
        # because bound-identity lookups treat it as absent. Strip the litter.
        for key in _GRAPH_CONTRACT_IDENTITY_KEYS:
            metadata.pop(key, None)
        return


def graph_node_bound_contract_identity(node: Any) -> str:
    """Return a graph target identity only when its durable receipt matches."""

    metadata = dict(getattr(node, "metadata", {}) or {})
    identity = _graph_metadata_contract_identity(metadata)
    statement_key = str(
        metadata.get("contract_identity_statement_key") or ""
    ).strip()
    environment_hash = str(
        metadata.get("contract_identity_environment_hash") or ""
    ).strip()
    if (
        not identity
        or statement_key != graph_statement_key(getattr(node, "statement", "") or "")
        or environment_hash
        != str(metadata.get("statement_environment_hash") or "").strip()
        or not lean_contract_evidence_receipt_matches(
            str(metadata.get("contract_identity_evidence_receipt") or ""),
            identity=identity,
            statement_key=statement_key,
            environment_hash=environment_hash,
        )
    ):
        return ""
    return identity


_SEMANTIC_WORK_AUTHORITY_BOOL_FIELDS: Tuple[str, ...] = (
    "certified_fact",
    "pending_adjudication",
    "target_integrity_adjudication",
    "allow_root_equivalent_target_integrity_adjudication",
    "formalization_required",
    "materialization_required",
    "advisory_only",
)
_SEMANTIC_WORK_AUTHORITY_TEXT_FIELDS: Tuple[str, ...] = (
    "obligation_trust",
    "proof_authority",
)


def graph_node_semantic_work_key(
    graph: Any,
    node: Any,
    *,
    exact_environment_hash: str = "",
    allow_exact_surface_identity: bool = False,
    normalize_schedulable_status: bool = False,
) -> Optional[Tuple[Any, ...]]:
    """Return a safe owner key for one open formal-work obligation.

    A key assigns scheduler ownership; it does not merge lifecycle nodes or
    confer proof status. Structural identity requires a valid Lean-bound
    receipt. Exact source text may be used only for duplicate elaboration work
    in the same non-empty stamped environment.
    """

    if node is None or str(getattr(node, "status", "") or "") not in {
        "open",
        "blocked",
    }:
        return None
    is_tombstone = getattr(graph, "is_superseded_tombstone", None)
    if callable(is_tombstone) and bool(is_tombstone(node)):
        return None
    metadata = dict(getattr(node, "metadata", {}) or {})
    if any(
        bool(metadata.get(flag))
        for flag in (
            "proposal_superseded",
            "proposal_invalidated",
            "route_retired",
            "route_dependency_contradicted",
            "retired_by_repeated_repair_failure",
        )
    ):
        return None
    environment_hash = str(metadata.get("statement_environment_hash") or "").strip()
    helper_context_hash = str(metadata.get("helper_context_hash") or "").strip()
    if not environment_hash or (
        exact_environment_hash and environment_hash != exact_environment_hash
    ):
        return None

    bound_identity = graph_node_bound_contract_identity(node)
    parsed_identity = parse_lean_contract_identity(bound_identity)
    if parsed_identity is not None:
        # v2/v3 changed telescope-profile semantics; Lean's full expression
        # hash remains the exact proposition identity across those formats.
        proposition_identity = ("lean_full_expr", parsed_identity[0])
    elif allow_exact_surface_identity:
        statement_key = graph_statement_key(getattr(node, "statement", "") or "")
        if not statement_key:
            return None
        proposition_identity = ("exact_surface", statement_key)
    else:
        return None

    authority_profile = (
        tuple(
            bool(metadata.get(field))
            for field in _SEMANTIC_WORK_AUTHORITY_BOOL_FIELDS
        ),
        tuple(
            str(metadata.get(field) or "").strip()
            for field in _SEMANTIC_WORK_AUTHORITY_TEXT_FIELDS
        ),
    )
    return (
        str(getattr(node, "kind", "") or ""),
        (
            "schedulable"
            if normalize_schedulable_status
            else str(getattr(node, "status", "") or "")
        ),
        proposition_identity,
        environment_hash,
        helper_context_hash,
        authority_profile,
    )


def graph_helper_bound_contract_identity(node: Any) -> str:
    """Return helper structural evidence only when its graph receipt matches."""

    metadata = dict(getattr(node, "metadata", {}) or {})
    identity = str(
        metadata.get("verified_helper_contract_identity") or ""
    ).strip()
    statement_key = str(
        metadata.get("verified_helper_contract_identity_statement_key") or ""
    ).strip()
    environment_hash = str(
        metadata.get("verified_helper_contract_identity_environment_hash") or ""
    ).strip()
    if (
        not has_lean_contract_identity(identity)
        or statement_key
        != graph_statement_key(getattr(node, "statement", "") or "")
        or environment_hash
        != str(metadata.get("verified_helper_environment_hash") or "").strip()
        or not lean_contract_evidence_receipt_matches(
            str(
                metadata.get(
                    "verified_helper_contract_identity_evidence_receipt"
                )
                or ""
            ),
            identity=identity,
            statement_key=statement_key,
            environment_hash=environment_hash,
        )
    ):
        return ""
    return identity


def stamp_graph_node_environment(
    node: Any,
    *,
    environment_hash: str,
    ancestor_hashes: Sequence[str] = (),
    stamp_source: str = "",
) -> None:
    """Stamp a target environment without invalidating prior Lean evidence."""

    metadata = getattr(node, "metadata", None)
    if not isinstance(metadata, dict):
        return
    # Validate authority before changing the environment field that is part
    # of its receipt. Invalid/unbound raw tokens remain non-authoritative.
    identity = graph_node_bound_contract_identity(node)
    environment = str(environment_hash or "").strip()
    metadata["statement_environment_hash"] = environment
    metadata["statement_environment_ancestor_hashes"] = [
        str(item or "").strip()
        for item in ancestor_hashes
        if str(item or "").strip()
    ]
    if stamp_source:
        metadata["statement_environment_stamp_source"] = str(stamp_source)
    if not identity:
        metadata.pop("contract_identity_statement_key", None)
        metadata.pop("contract_identity_environment_hash", None)
        metadata.pop("contract_identity_evidence_receipt", None)
        return
    statement_key = graph_statement_key(getattr(node, "statement", "") or "")
    metadata["contract_identity_statement_key"] = statement_key
    metadata["contract_identity_environment_hash"] = environment
    metadata["contract_identity_evidence_receipt"] = (
        make_lean_contract_evidence_receipt(
            identity,
            statement_key,
            environment,
        )
    )


_GRAPH_NON_THEOREM_STANDALONE_TYPES = {
    "ℕ",
    "Nat",
    "ℤ",
    "Int",
    "ℚ",
    "Rat",
    "ℝ",
    "Real",
    "Prop",
}
_GRAPH_NON_THEOREM_DATA_HEADS = {
    "Set",
    "Finset",
    "List",
    "Multiset",
    "Option",
    "Array",
    "Fin",
    "ZMod",
    "Polynomial",
    "Matrix",
    "Vector",
    "Subtype",
    "ULift",
    "PLift",
    "WithTop",
    "WithBot",
    "OrderDual",
    "Additive",
    "Multiplicative",
}
_GRAPH_NON_THEOREM_DATA_TERM_HEADS = {
    "Nat.add",
    "Nat.mul",
    "Nat.sub",
    "Nat.succ",
    "Nat.pred",
    "Int.natAbs",
    "Real.sqrt",
    "String.length",
    "List.map",
    "List.length",
    "List.filter",
    "List.range",
    "Finset.range",
    "Finset.image",
    "Finset.filter",
    "Finset.card",
    "Set.Icc",
    "Set.Ico",
    "Set.Ioc",
    "Set.Ioo",
    "Set.image",
    "Set.preimage",
}
_GRAPH_PROPOSITION_MARKERS = (
    "→",
    "↔",
    "∧",
    "∨",
    "∈",
    "∉",
    "⊆",
    "⊂",
    "≤",
    "≥",
    "≠",
    "∣",
    "∤",
    "=",
    "<",
    ">",
    "->",
    "<->",
    "/\\",
    "\\/",
    "<=",
    ">=",
    "!=",
)


def _graph_contains_proposition_marker(text: str) -> bool:
    raw = str(text or "")
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        if any(raw.startswith(marker, index) for marker in _GRAPH_PROPOSITION_MARKERS):
            return True
        index += 1
    return False


def _graph_contains_top_level_proposition_marker(text: str) -> bool:
    raw = str(text or "")
    depth = 0
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0 and any(
            raw.startswith(marker, index) for marker in _GRAPH_PROPOSITION_MARKERS
        ):
            return True
        index += 1
    return False


def _graph_normalize_ascii_quantifier_tokens(text: str) -> str:
    raw = str(text or "")
    if not raw:
        return ""
    out: List[str] = []
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            out.append(raw[index:skip_to])
            index = skip_to
            continue
        if _graph_keyword_at(raw, index, "forall"):
            out.append("∀")
            index += len("forall")
            continue
        if _graph_keyword_at(raw, index, "exists"):
            out.append("∃")
            index += len("exists")
            continue
        out.append(raw[index])
        index += 1
    return "".join(out)


def graph_statement_non_theorem_reason(text: str) -> str:
    """Return why a Lean-like graph statement cannot be a theorem target.

    Natural-language graph labels and residual descriptions are handled by
    ``graph_statement_is_executable``.  This helper is intentionally narrower:
    it catches statements that look like standalone Lean expressions, but whose
    type is itself data/sort-valued rather than ``Prop``.  Those must never be
    materialized as ``theorem name : <statement> := ...`` declarations.
    """

    compact = graph_identity_text(text)
    if not compact:
        return ""

    def direct_non_theorem_reason(candidate: str) -> str:
        candidate = _graph_strip_balanced_outer_parens(graph_identity_text(candidate))
        if not candidate:
            return ""
        candidate_shape = _graph_normalize_ascii_quantifier_tokens(candidate)
        if is_standalone_sort_like_lean_expr(candidate):
            return "standalone_sort"
        if candidate in _GRAPH_NON_THEOREM_STANDALONE_TYPES:
            return "standalone_type"
        candidate_head = candidate.split(None, 1)[0]
        if candidate_head in _GRAPH_NON_THEOREM_DATA_HEADS:
            return "standalone_data_type"
        if candidate_head in _GRAPH_NON_THEOREM_DATA_TERM_HEADS and not (
            _graph_contains_top_level_proposition_marker(candidate)
        ):
            return "data_term"
        if _graph_direct_application_has_non_prop_class_head(candidate):
            return "non_prop_codomain"
        if (
            _graph_top_level_quantifier_token_len(candidate_shape, 0) > 0
            and _graph_quantified_statement_has_non_prop_codomain(candidate)
        ):
            return "non_prop_codomain"
        if (
            _graph_top_level_quantifier_token_len(candidate_shape, 0) > 0
            and _graph_quantified_statement_has_prose_or_proof_tail(candidate)
        ):
            return ""
        if (
            _graph_top_level_quantifier_token_len(candidate_shape, 0) > 0
            and _graph_quantified_statement_is_executable(candidate)
        ):
            return ""
        if _graph_top_level_quantifier_token_len(
            candidate_shape,
            0,
        ) > 0 and is_non_theorem_standalone_lean_expr(candidate_shape):
            return "non_prop_codomain"
        return ""

    compact_unwrapped = _graph_strip_balanced_outer_parens(compact)
    compact_shape = _graph_normalize_ascii_quantifier_tokens(compact_unwrapped)

    if compact_unwrapped.startswith("¬"):
        return direct_non_theorem_reason(compact_unwrapped[1:].strip())
    if compact_unwrapped.startswith("not "):
        return direct_non_theorem_reason(compact_unwrapped[4:].strip())

    if is_standalone_sort_like_lean_expr(compact_unwrapped):
        return "standalone_sort"
    if compact_unwrapped in _GRAPH_NON_THEOREM_STANDALONE_TYPES:
        return "standalone_type"
    head = compact_unwrapped.split(None, 1)[0]
    if head in _GRAPH_NON_THEOREM_DATA_HEADS:
        return "standalone_data_type"
    if head in _GRAPH_NON_THEOREM_DATA_TERM_HEADS and not (
        _graph_contains_top_level_proposition_marker(compact_unwrapped)
    ):
        return "data_term"
    if _graph_direct_application_has_non_prop_class_head(compact_unwrapped):
        return "non_prop_codomain"
    if (
        "∀" in compact_shape
        or "∃" in compact_shape
        or "→" in compact_shape
        or "->" in compact_shape
    ):
        if (
            _graph_top_level_quantifier_token_len(compact_shape, 0) > 0
            and _graph_quantified_statement_has_non_prop_codomain(
                compact_unwrapped
            )
        ):
            return "non_prop_codomain"
        if (
            _graph_top_level_quantifier_token_len(compact_shape, 0) > 0
            and _graph_quantified_statement_has_prose_or_proof_tail(
                compact_unwrapped
            )
        ):
            return ""
        if (
            _graph_top_level_quantifier_token_len(compact_shape, 0) > 0
            and _graph_quantified_statement_is_executable(compact_unwrapped)
        ):
            return ""
        if is_non_theorem_standalone_lean_expr(compact_shape):
            return "non_prop_codomain"
    return ""


def _graph_statement_is_obvious_non_proposition(text: str) -> bool:
    """Reject graph targets that cannot be stored as theorem/lemma helpers."""

    return bool(graph_statement_non_theorem_reason(text))


def _graph_bare_prop_atom_name(text: str) -> str:
    compact = graph_identity_text(graph_formal_statement_text(text))
    return _graph_unicode_identifier_name(compact)


def _graph_context_prop_atom_tail_is_formal(
    atom: str,
    binder_text: str,
    tail_text: str,
) -> bool:
    tail = graph_identity_text(tail_text)
    if not tail:
        return True
    for separator in ("->", "=>", "→", ","):
        if tail.startswith(separator):
            tail = tail[len(separator) :].strip()
            break
    tail = graph_identity_text(tail)
    if not tail or _graph_statement_looks_like_prose_instruction(tail):
        return False
    bare_tail_atom = _graph_bare_prop_atom_name(tail)
    if bare_tail_atom:
        return bool(
            bare_tail_atom == str(atom or "").strip()
            or _graph_context_declares_prop_atom_in_binder(
                bare_tail_atom,
                binder_text,
            )
        )
    return bool(
        graph_statement_is_executable(tail)
        or _graph_context_prop_atom_tail_uses_declared_atoms(binder_text, tail)
    )


def _graph_context_declares_prop_atom_in_binder(atom: str, binder_text: str) -> bool:
    clean_atom = str(atom or "").strip()
    if not clean_atom:
        return False
    escaped_atom = re.escape(clean_atom)
    compact = graph_identity_text(binder_text)
    return bool(
        re.search(
            rf"(?:^|[\s\(\{{\[⦃])[^,)]*\b{escaped_atom}\b[^,)]*:\s*Prop\b",
            compact,
        )
    )


def _graph_context_prop_atom_tail_uses_declared_atoms(
    binder_text: str,
    tail_text: str,
) -> bool:
    tail = graph_identity_text(tail_text)
    if not tail or not _graph_contains_top_level_proposition_marker(tail):
        return False
    for token in _graph_lean_identifier_tokens(tail):
        if token in {"True", "False"} or token.lower() in {"not"}:
            continue
        if not _graph_context_declares_prop_atom_in_binder(token, binder_text):
            return False
    return True


def _graph_context_can_declare_prop_atom(atom: str, context_text: str) -> bool:
    compact = graph_identity_text(context_text)
    if not compact or _graph_statement_looks_like_prose_instruction(compact):
        return False
    lowered = compact.lower()
    if compact.startswith(("∀", "∃")) or lowered.startswith(
        ("forall ", "exists ")
    ):
        quantifier_len = _graph_top_level_quantifier_token_len(compact, 0)
        if quantifier_len <= 0:
            return False
        comma = _graph_find_top_level_comma(compact[quantifier_len:])
        if comma < 0:
            return False
        binder = compact[quantifier_len : quantifier_len + comma]
        tail = compact[quantifier_len + comma + 1 :]
        return bool(
            _graph_context_declares_prop_atom_in_binder(atom, binder)
            and _graph_context_prop_atom_tail_is_formal(atom, binder, tail)
        )
    if compact[0] not in "({[⦃":
        return False
    end = _graph_matching_group_index(compact, 0)
    if end < 0:
        return False
    binder = compact[: end + 1]
    tail = compact[end + 1 :].lstrip()
    return bool(
        _graph_context_declares_prop_atom_in_binder(atom, binder)
        and (not tail or tail.startswith((",", "→", "->", "=>")))
        and _graph_context_prop_atom_tail_is_formal(atom, binder, tail)
    )


def _graph_context_declares_prop_atom(atom: str, context_text: str) -> bool:
    clean_atom = str(atom or "").strip()
    if not clean_atom:
        return False
    compact = graph_identity_text(context_text)
    if not compact or not _graph_context_can_declare_prop_atom(clean_atom, compact):
        return False
    return True


def _graph_context_binder_text(context_text: str) -> str:
    compact = graph_identity_text(context_text)
    if not compact or _graph_statement_looks_like_prose_instruction(compact):
        return ""
    lowered = compact.lower()
    if compact.startswith(("∀", "∃")) or lowered.startswith(
        ("forall ", "exists ")
    ):
        binders: List[str] = []
        body = compact
        while body:
            quantifier_len = _graph_top_level_quantifier_token_len(body, 0)
            if quantifier_len <= 0:
                break
            remainder = body[quantifier_len:].lstrip()
            comma = _graph_find_top_level_comma(remainder)
            if comma < 0:
                break
            binder = remainder[:comma].strip()
            next_body = remainder[comma + 1 :].strip()
            if not binder or not next_body:
                break
            binders.append(binder)
            body = _graph_strip_balanced_outer_parens(next_body)
        return ", ".join(binders)
    if compact[0] not in "({[⦃":
        return ""
    end = _graph_matching_group_index(compact, 0)
    if end < 0:
        return ""
    return compact[: end + 1]


def _graph_statement_is_context_prop_predicate_application(
    text: str,
    *,
    parent_statement: str = "",
    root_statement: str = "",
) -> bool:
    compact = graph_identity_text(text)
    head = _graph_leading_identifier(compact)
    if not head:
        return False
    arg_count = _graph_application_arg_count(compact, head)
    if arg_count is None or arg_count <= 0:
        return False
    for context in (parent_statement, root_statement):
        binder = _graph_context_binder_text(context)
        if not binder:
            continue
        prop_arity = _graph_binder_prop_signatures(binder).get(head)
        if prop_arity is None:
            continue
        if arg_count == prop_arity and _graph_application_args_are_formal(
            compact,
            head,
        ):
            return True
    return False


def _graph_statement_is_context_bare_prop_atom(
    text: str,
    *,
    parent_statement: str = "",
    root_statement: str = "",
    metadata: Optional[Mapping[str, Any]] = None,
) -> bool:
    """Return whether ``text`` is admissible as a context-bound Prop atom."""

    del metadata
    atom = _graph_bare_prop_atom_name(text)
    if not atom:
        return False
    return any(
        _graph_context_declares_prop_atom(atom, context)
        for context in (parent_statement, root_statement)
        if str(context or "").strip()
    )


_ROUTE_DEPENDENCY_EDGE_KINDS = {"route_requires", "route_blocked_by", "route_replan"}
_ROUTE_SCOPE_PARTIAL = "partial_route"
_ROUTE_SCOPE_ROOT_ASSEMBLY = "root_assembly"
_ROUTE_ASSEMBLY_CONTRACT_KEY = "route_assembly_contract"
_ROUTE_RETIRED_STATUSES = {"rejected", "failed", "superseded", "blocked"}
_REPLAY_MATERIALIZATION_METADATA_KEYS = {
    "needs_replay_materialization",
    "replay_materialization_reason",
    "replay_materialization_helper_name",
    "replay_materialization_helper_node_id",
    "replay_materialization_statement_key",
    "replay_materialization_helper_proof_hash",
    "replay_materialization_helper_source_hash",
}


_GRAPH_SOLUTION_REFERENCE_RE = re.compile(
    r"(?:«[^»]*_solution[^»]*»|"
    r"[A-Za-z_][A-Za-z0-9_'.]*_solution[A-Za-z0-9_'.]*)"
)


def _helper_source_solution_references(src: str) -> Set[str]:
    text = _graph_answer_safety_skeleton(str(src or ""))
    return {
        str(match.group(0) or "").strip().removeprefix("«").removesuffix("»")
        for match in _GRAPH_SOLUTION_REFERENCE_RE.finditer(text)
        if str(match.group(0) or "").strip()
    }


def _helper_source_mentions_solution(src: str) -> bool:
    return bool(_helper_source_solution_references(src))


_GRAPH_CONFUSABLE_ASCII_MAP = str.maketrans({
    "Α": "A",
    "А": "A",
    "ɑ": "a",
    "α": "a",
    "а": "a",
    "С": "C",
    "Ϲ": "C",
    "с": "c",
    "ϲ": "c",
    "Ε": "E",
    "Е": "E",
    "е": "e",
    "Ι": "I",
    "І": "I",
    "і": "i",
    "Μ": "M",
    "М": "M",
    "м": "m",
    "Ν": "N",
    "О": "O",
    "Ο": "O",
    "ο": "o",
    "о": "o",
    "Ѕ": "S",
    "ѕ": "s",
    "Τ": "T",
    "Т": "T",
    "τ": "t",
    "т": "t",
    "Υ": "Y",
    "У": "Y",
    "υ": "y",
    "у": "y",
})


def _graph_answer_safety_skeleton(text: str) -> str:
    out: List[str] = []
    for ch in str(text or ""):
        normalized = unicodedata.normalize("NFKC", ch)
        if not normalized:
            continue
        for item in normalized:
            if unicodedata.category(item) == "Cf":
                continue
            out.append(item.translate(_GRAPH_CONFUSABLE_ASCII_MAP))
    return "".join(out)


_GRAPH_SOLUTION_REF_RE = re.compile(
    r"(?:«[^»]*_solution[^»]*»|[A-Za-z_][A-Za-z0-9_'.]*_solution[A-Za-z0-9_'.]*)"
)
_GRAPH_PROMPT_ROLE_RE = re.compile(
    r"\b(?:SYSTEM|DEVELOPER|USER|ASSISTANT)\b(?:"
    r"\s*[:：﹕꞉]\s*[^\n;]*"
    r"|\s+\S+(?:\s+\S+){0,12}"
    r"|\s*[.!?-]\s+\S+(?:\s+\S+){0,12}"
    r")",
    flags=re.IGNORECASE,
)
_GRAPH_PROMPT_IGNORE_RE = re.compile(
    r"\bignore\s+(?:this|previous|all|above|instructions?)(?:\s+\S+){0,8}",
    flags=re.IGNORECASE,
)
_GRAPH_PROMPT_DISREGARD_RE = re.compile(
    r"\bdisregard\s+(?:all\s+)?(?:prior|previous|above)?\s*"
    r"instructions?(?:\s+\S+){0,8}",
    flags=re.IGNORECASE,
)


def _graph_redact_skeleton_matches(
    raw: str,
    skeleton: str,
    index_map: Sequence[int],
    patterns: Sequence[Tuple[re.Pattern[str], str]],
) -> str:
    spans: List[Tuple[int, int, str]] = []
    for pattern, label in patterns:
        for match in pattern.finditer(skeleton):
            if match.start() >= len(index_map) or match.end() <= 0:
                continue
            start = index_map[match.start()]
            end = index_map[min(match.end() - 1, len(index_map) - 1)] + 1
            if start < end:
                spans.append((start, end, label))
    if not spans:
        return raw
    spans.sort(key=lambda item: (item[0], -item[1]))
    merged: List[Tuple[int, int, str]] = []
    for start, end, label in spans:
        if not merged or start > merged[-1][1]:
            merged.append((start, end, label))
        else:
            prev_start, prev_end, prev_label = merged[-1]
            merged[-1] = (prev_start, max(prev_end, end), prev_label)
    out: List[str] = []
    last = 0
    for start, end, label in merged:
        out.append(raw[last:start])
        out.append(f"{label}_{graph_text_hash(raw[start:end])}")
        last = end
    out.append(raw[last:])
    return "".join(out)


def _graph_prompt_safe_decl_application_preview(
    text: str,
    *,
    limit: int = 500,
) -> str:
    raw = str(text or "").strip()
    if not raw:
        return ""
    skeleton = _graph_answer_safety_skeleton(raw)
    index_map: List[int] = []
    for index, ch in enumerate(raw):
        normalized = unicodedata.normalize("NFKC", ch)
        for item in normalized:
            if unicodedata.category(item) == "Cf":
                continue
            index_map.append(index)
    raw = _graph_redact_skeleton_matches(
        raw,
        skeleton,
        index_map,
        (
            (_GRAPH_SOLUTION_REF_RE, "solution_ref_hidden"),
            (_GRAPH_PROMPT_ROLE_RE, "prompt_control_hidden"),
            (_GRAPH_PROMPT_IGNORE_RE, "prompt_control_hidden"),
            (_GRAPH_PROMPT_DISREGARD_RE, "prompt_control_hidden"),
        ),
    )
    return raw[:limit]


def _sanitize_decl_application_metadata(metadata: Mapping[str, Any]) -> Dict[str, Any]:
    out = copy.deepcopy(dict(metadata or {}))
    for key in ("decl_name", "proof_stub", "error_preview", "decl_type"):
        if key in out:
            out[key] = _graph_prompt_safe_decl_application_preview(
                out.get(key),
                limit=500,
            )
    if "remaining_goals" in out:
        out["remaining_goals"] = [
            _graph_prompt_safe_decl_application_preview(goal, limit=500)
            for goal in list(out.get("remaining_goals") or [])[:5]
        ]
    return out


def graph_identity_text(text: str) -> str:
    """Compact text used for graph-native mathematical search identities."""

    return " ".join(str(text or "").split()).strip()


def graph_formal_statement_text(
    text: str,
    *,
    canonicalize_guarded_iff: bool = True,
) -> str:
    """Compact, Lean-parseable formal statement text for graph-native nodes."""

    normalized = normalize_subgoal_statement(
        str(text or "").strip(),
        canonicalize_guarded_iff=canonicalize_guarded_iff,
    )
    if "\n" not in normalized:
        return graph_identity_text(normalized)
    lines: List[str] = []
    for line_index, line in enumerate(normalized.splitlines()):
        if not line.strip():
            lines.append("")
            continue
        body = " ".join(line.strip().split())
        if line_index == 0:
            lines.append(body)
            continue
        leading = re.match(r"\s*", line).group(0)
        lines.append(f"{leading or '  '}{body}")
    return "\n".join(lines).strip()


def _graph_statement_looks_like_prose_instruction(text: str) -> bool:
    compact = graph_identity_text(text)
    if not compact:
        return False
    lowered = compact.lower()
    if compact.startswith(("∀", "∃", "¬")) or lowered.startswith(
        ("forall ", "exists ")
    ):
        return False
    relation_shaped_identifier_statement = bool(
        re.match(
            r"^[A-Za-z_][A-Za-z0-9_'.]*\s*(?:=|≠|∈|∉|≤|≥|<|>|⊆|⊂|∣|∤|->|→|↔)",
            compact,
        )
    )
    relation_prose_markers = (
        " follows from ",
        " to show ",
        " to prove ",
        " prove ",
        " show ",
        " should ",
        " need ",
        " missing ",
        " selected ",
    )
    if relation_shaped_identifier_statement and not any(
        marker in f" {lowered} " for marker in relation_prose_markers
    ):
        return False
    prose_prefixes = (
        "need ",
        "needs ",
        "we need ",
        "we need to ",
        "we can ",
        "we have ",
        "we must ",
        "please ",
        "please prove ",
        "please show ",
        "please formalize ",
        "it follows that ",
        "it suffices ",
        "it remains ",
        "there remains ",
        "there exists a proof ",
        "there is a proof ",
        "missing ",
        "the missing ",
        "this missing ",
        "the selected ",
        "selected ",
        "the bridge ",
        "prove ",
        "show ",
        "use ",
        "using ",
        "find ",
        "to finish ",
        "to finish, ",
        "write ",
        "add ",
        "replace ",
        "repair ",
        "residual ",
    )
    if lowered.startswith(prose_prefixes):
        leading = _graph_leading_identifier(compact)
        if (
            leading
            and _graph_head_looks_like_non_prop_class(leading)
            and _graph_contains_top_level_proposition_marker(compact)
        ):
            return False
        return True
    prose_fragments = (
        " we need ",
        " please show ",
        " please prove ",
        " please formalize ",
        " selected target ",
        " target is ",
        " prove it",
        ", prove ",
        " to prove ",
        " to show ",
        " should prove ",
        " should show ",
        " should establish ",
        " follows from ",
        " proof of ",
        " proving ",
        " as a helper",
        " missing step ",
        " missing bridge ",
        " formalize ",
    )
    if any(fragment in f" {lowered} " for fragment in prose_fragments):
        return True
    if lowered.endswith((".", "?", "!")) and re.search(
        r"\b(?:target|selected|missing|bridge|helper|prove|show|need|needs|route|residual)\b",
        lowered,
    ):
        return True
    return False


_GRAPH_LEAN_GROUP_OPEN_TO_CLOSE = {
    "(": ")",
    "[": "]",
    "{": "}",
    "⦃": "⦄",
    "⟨": "⟩",
}
_GRAPH_LEAN_IDENTIFIER_PATTERN = r"(?:[A-Za-z_][A-Za-z0-9_'.]*|«[^»]+»)"
_GRAPH_RELATION_BINDER_TOKENS = (
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
_GRAPH_NON_PROP_CLASS_HEADS = {
    "AddCommMonoidWithOne",
    "AddCommGroup",
    "AddCommMonoid",
    "AddCommSemigroup",
    "AddGroup",
    "Add",
    "AddMonoid",
    "AddSemigroup",
    "Algebra",
    "Append",
    "BEq",
    "Bornology",
    "Category",
    "Coe",
    "CoeDep",
    "CoeFun",
    "CoeSort",
    "CoeTail",
    "CommGroup",
    "CommMonoid",
    "CommRing",
    "CommSemigroup",
    "CommSemiring",
    "DecidableEq",
    "Decidable",
    "DistribLattice",
    "Div",
    "Dvd",
    "EmptyCollection",
    "Encodable",
    "DivisionRing",
    "Field",
    "Fintype",
    "Functor",
    "GetElem",
    "Group",
    "HAdd",
    "HAppend",
    "HDiv",
    "HMod",
    "HMul",
    "HPow",
    "HShiftLeft",
    "HShiftRight",
    "HSub",
    "Hashable",
    "Inhabited",
    "Insert",
    "Inv",
    "IntCast",
    "Lattice",
    "LinearOrder",
    "LinearOrderedField",
    "LinearOrderedRing",
    "LE",
    "LT",
    "Max",
    "Membership",
    "MeasurableSpace",
    "MetricSpace",
    "Min",
    "Module",
    "Mod",
    "Mul",
    "Monad",
    "Monoid",
    "NatCast",
    "Neg",
    "NormedField",
    "NormedAddCommGroup",
    "NormedRing",
    "NormedSpace",
    "OfNat",
    "One",
    "OrderedRing",
    "OrderedSemiring",
    "PartialOrder",
    "Pow",
    "Preadditive",
    "Preorder",
    "Quiver",
    "RatCast",
    "Repr",
    "Ring",
    "SMul",
    "Semigroup",
    "SemilatticeInf",
    "SemilatticeSup",
    "Semiring",
    "Singleton",
    "Sub",
    "TopologicalSpace",
    "ToString",
    "Unique",
    "Zero",
}
_GRAPH_KNOWN_DATA_ATOM_TYPES = {
    "Bool",
    "Char",
    "Complex",
    "Empty",
    "Float",
    "Int",
    "Nat",
    "PUnit",
    "Rat",
    "Real",
    "String",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "USize",
    "Unit",
    "ℂ",
    "ℕ",
    "ℤ",
    "ℚ",
    "ℝ",
}
_GRAPH_LET_IN_BINDER_OPERATORS = (
    "∀ᶠ",
    "∃ᶠ",
    "∑",
    "∏",
    "∫",
    "⨍",
    "⋃",
    "⋂",
    "⨆",
    "⨅",
    "∐",
)


def _graph_lean_keyword_char(ch: str) -> bool:
    return bool(ch) and (ch.isalnum() or ch in "_'.")


def _graph_keyword_at(text: str, index: int, keyword: str) -> bool:
    token = str(keyword or "")
    if not token or not text.startswith(token, index):
        return False
    before_ok = index == 0 or not _graph_lean_keyword_char(text[index - 1])
    after_index = index + len(token)
    after_ok = after_index >= len(text) or not _graph_lean_keyword_char(
        text[after_index]
    )
    return before_ok and after_ok


def _graph_lean_identifier_tokens(text: str) -> Tuple[str, ...]:
    raw = str(text or "")
    tokens: List[str] = []
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            if raw.startswith("«", index):
                tokens.append(raw[index:skip_to])
            index = skip_to
            continue
        match = re.match(r"[^\W\d][\w']*", raw[index:], flags=re.UNICODE)
        if match is not None:
            tokens.append(match.group(0))
            index += len(match.group(0))
            continue
        index += 1
    return tuple(tokens)


def _graph_contract_key_discriminator_tokens(key: str) -> frozenset[str]:
    """Canonical unordered ingredients for the narrow bridge variant guard."""

    normalized_key = str(key or "").strip()
    if not normalized_key:
        return frozenset()
    tokens: Set[str] = set()
    index = 0
    while index < len(normalized_key):
        skip_to = _lean_lexical_skip_end(normalized_key, index)
        if skip_to is not None:
            if normalized_key.startswith("«", index):
                tokens.add(f"identifier:{normalized_key[index:skip_to]}")
            index = skip_to
            continue
        identifier_match = re.match(
            r"[^\W\d][\w']*",
            normalized_key[index:],
            flags=re.UNICODE,
        )
        if identifier_match is not None:
            token = identifier_match.group(0)
            tokens.add(f"identifier:{token}")
            index += len(token)
            continue
        literal_match = re.match(r"\d+(?:\.\d+)?", normalized_key[index:])
        if literal_match is not None:
            token = literal_match.group(0)
            tokens.add(f"literal:{token}")
            index += len(token)
            continue
        if normalized_key[index].isspace():
            index += 1
            continue
        delimiter_match = re.match(r"[()\[\]{},;]", normalized_key[index:])
        if delimiter_match is not None:
            token = delimiter_match.group(0)
            tokens.add(f"symbol:{token}")
            index += len(token)
            continue
        symbol_match = re.match(
            r"[^\w\s()\[\]{},;]+",
            normalized_key[index:],
            flags=re.UNICODE,
        )
        token = symbol_match.group(0) if symbol_match is not None else normalized_key[index]
        tokens.add(f"symbol:{token}")
        index += len(token)
    return frozenset(tokens)


_GRAPH_BRIDGE_EXPLICIT_OPERATOR_MARKERS: Tuple[Tuple[str, str], ...] = (
    ("@Membership.mem", "operator:∈"),
    ("@LE.le", "operator:≤"),
    ("@LT.lt", "operator:<"),
    ("@Ne ", "operator:≠"),
    ("@Ne.", "operator:≠"),
    ("@Eq ", "operator:="),
    ("@Not ", "operator:¬"),
    ("@And ", "operator:∧"),
    ("@Or ", "operator:∨"),
    ("@Iff ", "operator:↔"),
    ("Not ", "operator:¬"),
    ("And ", "operator:∧"),
    ("Or ", "operator:∨"),
    ("Iff ", "operator:↔"),
    ("@Exists ", "operator:∃"),
    ("@Exists.", "operator:∃"),
    ("Exists ", "operator:∃"),
    ("@Dvd.dvd", "operator:∣"),
    ("@Set.Subset", "operator:⊆"),
    ("@HasSubset.Subset", "operator:⊆"),
    ("@Inv.inv", "operator:⁻¹"),
    ("@HSub.hSub", "operator:-"),
    ("@Sub.sub", "operator:-"),
    ("@HAdd.hAdd", "operator:+"),
    ("@Add.add", "operator:+"),
    ("@HMul.hMul", "operator:*"),
    ("@Mul.mul", "operator:*"),
    ("@HDiv.hDiv", "operator:/"),
    ("@Div.div", "operator:/"),
    ("@HPow.hPow", "operator:^"),
    ("@Pow.pow", "operator:^"),
)


def _graph_bridge_key_uses_explicit_operator_scaffolding(key: str) -> bool:
    raw = str(key or "")
    return bool(
        re.search(r"@[A-Za-z_]", raw)
        or any(
            marker in raw
            for marker, _operator in _GRAPH_BRIDGE_EXPLICIT_OPERATOR_MARKERS
        )
    )


def _graph_bridge_variant_rejection_tokens(key: str) -> frozenset[str]:
    """Return notation-insensitive ingredients for a fail-closed bridge guard.

    Lean's explicit pretty-printer renders a parent hypothesis with applications
    such as ``@Membership.mem`` and ``@LE.le`` while a checked helper normally
    retains ``∈`` and ``≤`` surface notation.  Those are the same elaborated
    operators, but the ordinary graph key deliberately keeps the distinction:
    globally erasing instances and type ascriptions would be unsound for proof
    identity.

    This coarser token set is therefore used only to *reject* projection of a
    possible parent hypothesis as a standalone theorem.  It is never evidence
    that two propositions are equal, proved, or interchangeable.  A false
    positive can decline one bridge route; a false negative can manufacture a
    globally quantified proposition that the parent only assumed.
    """

    raw = str(key or "").strip()
    if not raw:
        return frozenset()
    normalized: Set[str] = {
        operator
        for marker, operator in _GRAPH_BRIDGE_EXPLICIT_OPERATOR_MARKERS
        if marker in raw
    }
    elaboration_identifiers = {
        "Membership",
        "mem",
        "LE",
        "le",
        "LT",
        "lt",
        "Eq",
        "Not",
        "And",
        "Or",
        "Iff",
        "Exists",
        "Dvd",
        "dvd",
        "OfNat",
        "ofNat",
        "nat_lit",
        "Inv",
        "inv",
        "HSub",
        "hSub",
        "Sub",
        "sub",
        "HAdd",
        "hAdd",
        "Add",
        "add",
        "HMul",
        "hMul",
        "Mul",
        "mul",
        "HDiv",
        "hDiv",
        "Div",
        "div",
        "HPow",
        "hPow",
        "Pow",
        "pow",
        "NatCast",
        "natCast",
        "cast",
        # The discriminator sees the superscript one in ``⁻¹`` as an
        # identifier.  The inverse operator token below carries its meaning.
        "¹",
    }
    surface_operators: Tuple[Tuple[str, str], ...] = (
        ("↔", "operator:↔"),
        ("→", "operator:→"),
        ("¬", "operator:¬"),
        ("∧", "operator:∧"),
        ("∨", "operator:∨"),
        ("∀", "operator:∀"),
        ("∃", "operator:∃"),
        ("∉", "operator:∉"),
        ("∈", "operator:∈"),
        ("≤", "operator:≤"),
        ("≥", "operator:≥"),
        ("≠", "operator:≠"),
        ("∣", "operator:∣"),
        ("⊆", "operator:⊆"),
        ("⁻", "operator:⁻¹"),
        ("∑", "operator:∑"),
        ("=", "operator:="),
        ("<", "operator:<"),
        (">", "operator:>"),
        ("-", "operator:-"),
        ("+", "operator:+"),
        ("*", "operator:*"),
        ("/", "operator:/"),
        ("^", "operator:^"),
    )
    for token in _graph_contract_key_discriminator_tokens(raw):
        kind, _separator, value = token.partition(":")
        if kind == "literal":
            normalized.add(token)
            continue
        if kind == "identifier":
            if value in elaboration_identifiers or value.startswith("inst"):
                continue
            normalized.add(token)
            continue
        if kind != "symbol":
            continue
        for glyph, operator in surface_operators:
            if glyph in value:
                normalized.add(operator)
    return frozenset(normalized)


def _graph_let_in_candidate_is_body_separator(
    raw: str,
    assign_index: int,
    in_index: int,
) -> bool:
    last_binder_operator = -1
    last_comma = -1
    depth = 0
    index = assign_index + 2
    while index < in_index:
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = min(skip_to, in_index)
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0:
            if ch == ",":
                last_comma = index
            else:
                for operator in _GRAPH_LET_IN_BINDER_OPERATORS:
                    if raw.startswith(operator, index):
                        last_binder_operator = index
                        index += len(operator) - 1
                        break
        index += 1
    return not (last_binder_operator != -1 and last_comma < last_binder_operator)


def _graph_let_binding_name_from_prefix(binding: str) -> str:
    match = re.match(
        rf"\s*let\s+(?:rec\s+)?({_GRAPH_LEAN_IDENTIFIER_PATTERN})(?:\s|$)",
        str(binding or "").strip(),
    )
    return str(match.group(1) or "").strip() if match else ""


def _graph_let_layout_suffix_starts_body(
    raw: str,
    *,
    assign_index: int,
    newline_index: int,
    line_end: int,
) -> bool:
    assigned_prefix = raw[assign_index + 2 : newline_index].strip()
    if not assigned_prefix:
        return False
    suffix = raw[line_end:]
    if not suffix.strip():
        return False
    indent_len = len(suffix) - len(suffix.lstrip(" \t"))
    visible_suffix = suffix[indent_len:].lstrip()
    if not visible_suffix:
        return False
    if indent_len == 0:
        return True
    name = _graph_let_binding_name_from_prefix(raw[:assign_index])
    return bool(
        name
        and (
            visible_suffix == name
            or visible_suffix.startswith(f"{name} ")
            or visible_suffix.startswith(f"{name}(")
        )
    )


def _graph_text_has_balanced_groups(text: str) -> bool:
    """Return whether Lean grouping delimiters are balanced outside literals."""

    raw = str(text or "")
    stack: List[str] = []
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            stack.append(_GRAPH_LEAN_GROUP_OPEN_TO_CLOSE[ch])
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            if not stack or ch != stack[-1]:
                return False
            stack.pop()
        index += 1
    return not stack


def _graph_let_binding_is_syntactically_complete(binding: str) -> bool:
    """Recognize a complete leading Lean ``let`` binding conservatively."""

    raw = str(binding or "").strip()
    if not raw or not _graph_text_has_balanced_groups(raw):
        return False
    equation_style_let_rec = bool(re.match(r"^let\s+rec\b", raw))
    assign_index = _graph_top_level_token_index(raw, ":=")
    if assign_index < 0:
        # Equation-style recursive lets have no ``:=``, but must still name a
        # declaration and contain at least one complete equation branch.
        return bool(
            equation_style_let_rec
            and _graph_let_binding_name_from_prefix(raw)
            and _graph_top_level_token_index(raw, "|") >= 0
            and _graph_top_level_token_index(raw, "=>") >= 0
        )

    prefix = raw[:assign_index].strip()
    rhs = raw[assign_index + 2 :].strip()
    if not rhs or not _graph_text_has_balanced_groups(rhs):
        return False
    match = re.match(
        rf"^let\s+(?:rec\s+)?({_GRAPH_LEAN_IDENTIFIER_PATTERN})(?P<tail>.*)$",
        prefix,
    )
    if match is None:
        # Lean also permits destructuring patterns as the binder head.  Keep
        # those only when the entire pattern is one balanced group.
        pattern = re.match(r"^let\s+(?P<pattern>[\(⟨].*)$", prefix)
        if pattern is None:
            return False
        pattern_text = str(pattern.group("pattern") or "").strip()
        return bool(
            pattern_text
            and _graph_matching_group_index(pattern_text, 0)
            == len(pattern_text) - 1
        )

    tail = str(match.group("tail") or "").strip()
    if not tail:
        return True
    # A type annotation must contain a type.  Function parameters may precede
    # it, but every unparenthesized parameter must itself be an identifier;
    # this rejects malformed surfaces such as ``let a ℕ := ...`` without
    # excluding valid ``let f x : Nat := ...`` declarations.
    colon_index = _graph_top_level_token_index(tail, ":")
    parameter_surface = tail[:colon_index].strip() if colon_index >= 0 else tail
    annotation = tail[colon_index + 1 :].strip() if colon_index >= 0 else ""
    if colon_index >= 0 and not annotation:
        return False
    index = 0
    while index < len(parameter_surface):
        while index < len(parameter_surface) and parameter_surface[index].isspace():
            index += 1
        if index >= len(parameter_surface):
            break
        if parameter_surface[index] in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            end = _graph_matching_group_index(parameter_surface, index)
            if end < 0:
                return False
            index = end + 1
            continue
        identifier = re.match(_GRAPH_LEAN_IDENTIFIER_PATTERN, parameter_surface[index:])
        if identifier is None:
            return False
        index += len(identifier.group(0))
    return bool(
        _graph_text_has_balanced_groups(parameter_surface)
        and (not annotation or _graph_text_has_balanced_groups(annotation))
    )


def _graph_top_level_let_parts(text: str) -> Tuple[str, str]:
    raw = str(text or "").strip()
    if not re.match(r"^let(?:\s|\(|⟨)", raw):
        return "", ""
    equation_style_let_rec = bool(re.match(r"^let\s+rec\b", raw))
    assign_index = -1
    depth = 0
    index = 0
    while index < len(raw) - 1:
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ":" and raw[index + 1] == "=" and depth == 0:
            assign_index = index
            break
        elif equation_style_let_rec and depth == 0 and ch == ";":
            binding = raw[:index].strip()
            remainder = raw[index + 1 :].strip()
            return (
                (binding, remainder)
                if remainder and _graph_let_binding_is_syntactically_complete(binding)
                else ("", "")
            )
        elif equation_style_let_rec and depth == 0 and ch in "\r\n":
            line_end = (
                index + 2
                if ch == "\r" and index + 1 < len(raw) and raw[index + 1] == "\n"
                else index + 1
            )
            suffix = raw[line_end:]
            indent_len = len(suffix) - len(suffix.lstrip(" \t"))
            visible_suffix = suffix[indent_len:].lstrip()
            if indent_len == 0 and visible_suffix and not visible_suffix.startswith("|"):
                binding = raw[:index].strip()
                remainder = raw[line_end:].strip()
                return (
                    (binding, remainder)
                    if remainder
                    and _graph_let_binding_is_syntactically_complete(binding)
                    else ("", "")
                )
        index += 1
    if assign_index == -1:
        return "", ""

    depth = 0
    index = assign_index + 2
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0 and ch == ";":
            binding = raw[:index].strip()
            remainder = raw[index + 1 :].strip()
            return (
                (binding, remainder)
                if remainder and _graph_let_binding_is_syntactically_complete(binding)
                else ("", "")
            )
        elif depth == 0 and ch in "\r\n":
            line_end = (
                index + 2
                if ch == "\r" and index + 1 < len(raw) and raw[index + 1] == "\n"
                else index + 1
            )
            if _graph_let_layout_suffix_starts_body(
                raw,
                assign_index=assign_index,
                newline_index=index,
                line_end=line_end,
            ):
                binding = raw[:index].strip()
                remainder = raw[line_end:].strip()
                return (
                    (binding, remainder)
                    if remainder
                    and _graph_let_binding_is_syntactically_complete(binding)
                    else ("", "")
                )
        elif depth == 0 and _graph_keyword_at(raw, index, "in"):
            if _graph_let_in_candidate_is_body_separator(raw, assign_index, index):
                binding = raw[:index].strip()
                remainder = raw[index + len("in") :].strip()
                return (
                    (binding, remainder)
                    if remainder
                    and _graph_let_binding_is_syntactically_complete(binding)
                    else ("", "")
                )
        index += 1
    return "", ""


def _graph_top_level_let_body(text: str) -> str:
    _binding, body = _graph_top_level_let_parts(text)
    return body


def _graph_top_level_token_index(text: str, token: str, *, start: int = 0) -> int:
    raw = str(text or "")
    depth = 0
    index = max(0, int(start or 0))
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0 and raw.startswith(token, index):
            return index
        index += 1
    return -1


def _graph_prop_annotation_arity(type_text: str) -> int | None:
    clean = graph_identity_text(type_text).strip()
    if clean.startswith(":"):
        clean = clean[1:].strip()
    if not clean:
        return None
    parts = split_lean_top_level_implications(clean)
    if len(parts) == 1 and graph_identity_text(parts[0]) == "Prop":
        return 0
    if len(parts) >= 2 and graph_identity_text(parts[-1]) == "Prop":
        return len(parts) - 1
    return None


def _graph_binder_name_count(surface: str) -> int:
    pattern = rf"(?:_|{_GRAPH_LEAN_IDENTIFIER_PATTERN})"
    return len(re.findall(pattern, str(surface or "")))


def _graph_fun_arg_arity(args_text: str) -> int | None:
    raw = str(args_text or "").strip()
    if not raw:
        return 0
    count = 0
    index = 0
    while index < len(raw):
        while index < len(raw) and raw[index].isspace():
            index += 1
        if index >= len(raw):
            break
        if raw[index] in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            end = _graph_matching_group_index(raw, index)
            if end < 0:
                return None
            group_body = raw[index + 1 : end].strip()
            colon = _graph_top_level_token_index(group_body, ":")
            names_surface = group_body[:colon] if colon >= 0 else group_body
            count += _graph_binder_name_count(names_surface)
            index = end + 1
            continue
        segment = raw[index:]
        colon = _graph_top_level_token_index(segment, ":")
        names_surface = segment[:colon] if colon >= 0 else segment
        count += _graph_binder_name_count(names_surface)
        break
    return count


def _graph_fun_rhs_prop_arity(rhs: str) -> int | None:
    clean = graph_identity_text(rhs)
    parts = split_lean_top_level_implications(clean)
    if len(parts) >= 2 and graph_identity_text(parts[-1]) == "Prop":
        return None
    match = re.match(r"^fun\s+(.+?)\s*=>\s*(.+)$", clean)
    if match is None:
        if clean in {"True", "False"} or _graph_contains_top_level_proposition_marker(
            clean
        ):
            return 0
        return None
    args_text = str(match.group(1) or "").strip()
    body = str(match.group(2) or "").strip()
    if not body or not (
        body in {"True", "False"} or _graph_contains_top_level_proposition_marker(body)
    ):
        return None
    return _graph_fun_arg_arity(args_text)


def _graph_let_binding_prop_signature(binding: str) -> Tuple[str, int] | Tuple[str, None]:
    binding_text = graph_identity_text(binding)
    bind_match = re.match(
        rf"let\s+(?:rec\s+)?({_GRAPH_LEAN_IDENTIFIER_PATTERN})(?P<tail>.*)$",
        binding_text,
    )
    if bind_match is None:
        return "", None
    name = str(bind_match.group(1) or "").strip()
    if not name:
        return "", None
    assign_index = _graph_top_level_token_index(binding_text, ":=")
    annotation_end = assign_index if assign_index >= 0 else len(binding_text)
    branch_index = _graph_top_level_token_index(binding_text, "|")
    if assign_index < 0 and branch_index >= 0:
        annotation_end = branch_index
    colon_index = _graph_top_level_token_index(binding_text, ":")
    arity: int | None = None
    if colon_index >= 0 and colon_index < annotation_end:
        arity = _graph_prop_annotation_arity(binding_text[colon_index:annotation_end])
    if arity is None and assign_index >= 0:
        arity = _graph_fun_rhs_prop_arity(binding_text[assign_index + 2 :])
    return name, arity


def _graph_application_arg_count(body: str, head: str) -> int | None:
    text = graph_identity_text(body)
    if not text.startswith(head):
        return None
    tail = text[len(head) :]
    if tail and not tail[0].isspace() and tail[0] != "(":
        return None
    count = 0
    index = 0
    while index < len(tail):
        while index < len(tail) and tail[index].isspace():
            index += 1
        if index >= len(tail):
            break
        if tail[index] in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            end = _graph_matching_group_index(tail, index)
            if end < 0:
                return None
            count += 1
            index = end + 1
            continue
        start = index
        while index < len(tail) and not tail[index].isspace():
            skip_to = _lean_lexical_skip_end(tail, index)
            if skip_to is not None:
                index = skip_to
                continue
            index += 1
        if index > start:
            count += 1
    return count


def _graph_matching_group_index(text: str, start: int) -> int:
    raw = str(text or "")
    opener = raw[start] if 0 <= start < len(raw) else ""
    expected = _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.get(opener)
    if expected is None:
        return -1
    stack = [expected]
    index = start + 1
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            stack.append(_GRAPH_LEAN_GROUP_OPEN_TO_CLOSE[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
            if not stack:
                return index
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            return -1
        index += 1
    return -1


def _graph_let_body_is_plausibly_local_prop(
    text: str,
    *,
    binding: str = "",
) -> bool:
    compact = graph_identity_text(text)
    if not compact:
        return False
    lowered = compact.lower()
    if (
        has_sorry_or_admit(compact)
        or contains_metavariable_placeholder(compact)
        or graph_statement_non_theorem_reason(compact)
        or _graph_statement_looks_like_prose_instruction(compact)
    ):
        return False
    if lowered.startswith(
        (
            "by ",
            "case ",
            "fun ",
            "let ",
            "error ",
            "unknown identifier",
            "type mismatch",
            "parse error",
            "tactic failed",
        )
    ):
        return False
    prop_head, prop_arity = _graph_let_binding_prop_signature(binding)
    if not prop_head or prop_arity is None:
        return False
    arg_count = _graph_application_arg_count(compact, prop_head)
    return arg_count == prop_arity


def _graph_quantified_body_looks_like_prose(text: str) -> bool:
    compact = graph_identity_text(text)
    if not compact:
        return True
    lowered = compact.lower()
    if _graph_statement_looks_like_prose_instruction(compact):
        return True
    prose_tail_patterns = (
        r"\b(?:using|via|because|with)\b",
        r"\b(?:assuming|under|when|if)\s+\S+",
        r"\band\s+then\b",
        r"\b(?:in|inside|from|for|of|as)\s+"
        r"(?:the|a|this|that|supposed)\s+"
        r"(?:parent\s+)?(?:goal|claim|target|statement|context|proof|helper)\b",
        r"\b(?:in|inside|from|for|of|as)\s+"
        r"(?:parent\s+)?(?:goal|claim|target|statement|context|proof|helper)\b",
        r"\bby\s+(?:assumption|context|helper|proof|target|claim|goal)\b",
        r"\b(?:parent\s+goal|selected\s+target|missing\s+step|proof\s+obligation)\b",
    )
    return any(
        re.search(pattern, lowered, flags=re.IGNORECASE)
        for pattern in prose_tail_patterns
    )


def _graph_quantified_final_body(text: str) -> str:
    body = graph_identity_text(text)
    while body:
        quantifier_len = _graph_top_level_quantifier_token_len(body, 0)
        if quantifier_len <= 0:
            break
        remainder = body[quantifier_len:].lstrip()
        comma = _graph_find_top_level_comma(remainder)
        if comma < 0:
            return ""
        next_body = remainder[comma + 1 :].strip()
        if not next_body:
            return ""
        body = _graph_strip_balanced_outer_parens(next_body)
    return body


def _graph_quantified_statement_has_prose_or_proof_tail(text: str) -> bool:
    body = _graph_quantified_final_body(text)
    return bool(
        body
        and (
            _graph_quantified_body_looks_like_prose(body)
            or _graph_has_top_level_proof_tail(body)
        )
    )


def _graph_has_top_level_proof_tail(text: str) -> bool:
    raw = graph_identity_text(text)
    if not raw:
        return False
    stripped = _graph_strip_balanced_outer_parens(raw)
    if stripped != raw and stripped:
        return _graph_has_top_level_proof_tail(stripped)
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            end = _graph_matching_group_index(raw, index)
            if end >= 0:
                index = end + 1
                continue
        if ch == ";":
            return True
        for keyword in ("by", "from", "where", "using", "via", "because", "with"):
            if _graph_keyword_at(raw, index, keyword):
                return True
        index += 1
    return False


def _graph_quantified_body_has_proof_tail(text: str) -> bool:
    """Inspect a quantified body without treating ``let`` delimiters as tactics.

    A semicolon at the top level normally separates a proposition from proof
    syntax and must therefore fail closed.  In a body such as
    ``let x := value; let y := other; proposition``, however, those same
    semicolons are part of the Lean term that *forms* the proposition.  Peel
    only syntactically complete leading ``let`` bindings, check each binding
    itself for proof syntax, and leave the final body to the ordinary strict
    proof-tail detector.
    """

    def fragment_has_proof_tail(fragment: str) -> bool:
        body = _graph_strip_balanced_outer_parens(graph_identity_text(fragment))
        if not body or not _graph_text_has_balanced_groups(body):
            return True
        while _graph_top_level_quantifier_token_len(body, 0) > 0:
            quantifier_len = _graph_top_level_quantifier_token_len(body, 0)
            remainder = body[quantifier_len:].lstrip()
            comma = _graph_find_top_level_comma(remainder)
            if comma < 0:
                return True
            body = _graph_strip_balanced_outer_parens(
                remainder[comma + 1 :].strip()
            )
            if not body:
                return True
        implication_parts = split_lean_top_level_implications(body)
        if len(implication_parts) > 1:
            return any(fragment_has_proof_tail(part) for part in implication_parts)
        while body.startswith(("let ", "let\n")):
            binding, remainder = _graph_top_level_let_parts(body)
            if (
                not binding
                or not remainder
                or not _graph_let_binding_is_syntactically_complete(binding)
            ):
                return True
            if _graph_has_top_level_proof_tail(binding):
                return True
            body = _graph_strip_balanced_outer_parens(remainder)
        return _graph_has_top_level_proof_tail(body) if body else False

    return fragment_has_proof_tail(text)


def _graph_binder_context_parts(binder_text: str) -> Tuple[str, ...]:
    raw = str(binder_text or "").strip()
    if not raw:
        return ()
    parts: List[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            part = raw[start:index].strip()
            if part:
                parts.append(part)
            start = index + 1
        index += 1
    tail = raw[start:].strip()
    if tail:
        parts.append(tail)
    return tuple(parts or (raw,))


def _graph_binder_context_names(binder_text: str) -> Tuple[str, ...]:
    names: List[str] = []
    for part in _graph_binder_context_parts(binder_text):
        for name in _graph_binder_names_from_chunk(part):
            if name not in names:
                names.append(name)
    return tuple(names)


def _graph_binder_prop_signatures(binder_text: str) -> Dict[str, int | None]:
    raw = graph_identity_text(binder_text)
    signatures: Dict[str, int | None] = {}
    if not raw:
        return signatures
    chunks: List[str] = []
    for part in _graph_binder_context_parts(raw):
        chunks.extend(_graph_binder_group_chunks(part))
    for chunk in chunks:
        body = _graph_unwrap_binder_group(str(chunk or "").strip())
        colon = _graph_top_level_token_index(body, ":")
        if colon < 0:
            continue
        names = _graph_binder_names_from_chunk(body[:colon])
        if not names:
            continue
        arity = _graph_prop_annotation_arity(body[colon:])
        if arity is None:
            continue
        for name in names:
            signatures[name] = arity
    return signatures


def _graph_binder_type_signatures(binder_text: str) -> Dict[str, str]:
    raw = graph_identity_text(binder_text)
    signatures: Dict[str, str] = {}
    if not raw:
        return signatures
    chunks: List[str] = []
    for part in _graph_binder_context_parts(raw):
        chunks.extend(_graph_binder_group_chunks(part))
    for chunk in chunks:
        body = _graph_unwrap_binder_group(str(chunk or "").strip())
        colon = _graph_top_level_token_index(body, ":")
        if colon < 0:
            continue
        names = _graph_binder_names_from_chunk(body[:colon])
        if not names:
            continue
        type_text = graph_identity_text(body[colon + 1 :])
        if not type_text:
            continue
        for name in names:
            signatures[name] = type_text
    return signatures


def _graph_binder_type_is_prop(type_text: str) -> bool:
    return graph_identity_text(type_text) == "Prop"


def _graph_unicode_identifier_name(text: str) -> str:
    compact = graph_identity_text(text)
    if re.fullmatch(r"(?:[^\W\d_]|_)[\w'.]*", compact, flags=re.UNICODE):
        return compact
    if re.fullmatch(r"«[^»]+»", compact):
        return compact
    return ""


def _graph_leading_identifier(text: str) -> str:
    raw = graph_identity_text(text)
    if not raw:
        return ""
    if raw.startswith("«"):
        end = _lean_lexical_skip_end(raw, 0)
        return raw[:end] if end is not None else ""
    match = re.match(r"(?:[^\W\d_]|_)[\w'.]*", raw, flags=re.UNICODE)
    return str(match.group(0) or "") if match else ""


def _graph_head_base_name(head: str) -> str:
    text = str(head or "").strip()
    if not text:
        return ""
    if text.startswith("«") and text.endswith("»"):
        return text.strip("«»")
    return text.rsplit(".", 1)[-1]


def _graph_identifier_starts_upper(text: str) -> bool:
    head = _graph_head_base_name(text)
    if not head:
        return False
    return bool(head[0].isupper())


def _graph_head_looks_like_non_prop_class(head: str) -> bool:
    base = _graph_head_base_name(head)
    if not base:
        return False
    if base in _GRAPH_NON_PROP_CLASS_HEADS:
        return True
    return bool(
        re.search(
            r"(?:Group|Monoid|Semigroup|Ring|Semiring|Field|Lattice|Order|"
            r"Space|Category|Module|Algebra|Functor|Monad|Quiver|Preadditive|"
            r"Hashable|Ord)$",
            base,
        )
        or re.search(
            r"(?:WithOne|WithZero|Action|SMul|VAdd|CommGroup|SemilatticeSup|"
            r"SemilatticeInf)$",
            base,
        )
    )


def _graph_application_first_argument(text: str, head: str) -> str:
    raw = graph_identity_text(text)
    if not raw.startswith(head):
        return ""
    tail = raw[len(head) :].lstrip()
    if not tail:
        return ""
    if tail[0] in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
        end = _graph_matching_group_index(tail, 0)
        return tail[: end + 1].strip() if end >= 0 else ""
    index = 0
    while index < len(tail) and not tail[index].isspace():
        skip_to = _lean_lexical_skip_end(tail, index)
        if skip_to is not None:
            index = skip_to
            continue
        index += 1
    return tail[:index].strip()


def _graph_quantified_application_has_non_prop_head(
    body: str,
    binder_context: str,
) -> bool:
    head = _graph_leading_identifier(body)
    if head and head in _graph_binder_prop_signatures(binder_context):
        return False
    return bool(head and _graph_head_looks_like_non_prop_class(head))


def _graph_direct_application_has_non_prop_class_head(text: str) -> bool:
    compact = graph_identity_text(text)
    if _graph_contains_top_level_proposition_marker(compact):
        return False
    head = _graph_leading_identifier(compact)
    if not head or not _graph_head_looks_like_non_prop_class(head):
        return False
    tail = compact[len(head) :].strip()
    return bool(tail)


def _graph_quantified_non_prop_codomain(body: str, binder_context: str) -> bool:
    type_signatures = _graph_binder_type_signatures(binder_context)
    if not type_signatures:
        return False
    parts = split_lean_top_level_implications(graph_identity_text(body))
    conclusion = _graph_strip_balanced_outer_parens(parts[-1] if parts else body)
    conclusion_name = _graph_unicode_identifier_name(conclusion)
    if (
        conclusion_name
        and conclusion_name in type_signatures
        and not _graph_binder_type_is_prop(type_signatures[conclusion_name])
    ):
        return True
    return _graph_quantified_application_has_non_prop_head(conclusion, binder_context)


def _graph_quantified_statement_has_non_prop_codomain(text: str) -> bool:
    body = graph_identity_text(text)
    if not body:
        return False
    binder_contexts: List[str] = []
    while body:
        quantifier_len = _graph_top_level_quantifier_token_len(body, 0)
        if quantifier_len <= 0:
            break
        remainder = body[quantifier_len:].lstrip()
        comma = _graph_find_top_level_comma(remainder)
        if comma < 0:
            return False
        binder = remainder[:comma].strip()
        next_body = remainder[comma + 1 :].strip()
        if not binder or not next_body:
            return False
        binder_contexts.append(binder)
        body = _graph_strip_balanced_outer_parens(next_body)
    return bool(
        binder_contexts
        and _graph_quantified_non_prop_codomain(body, ", ".join(binder_contexts))
    )


def _graph_application_args_are_bound(body: str, head: str, bound_names: Set[str]) -> bool:
    text = graph_identity_text(body)
    if not text.startswith(head):
        return False
    tail = text[len(head) :]
    if tail and not tail[0].isspace() and tail[0] != "(":
        return False
    if re.search(
        r"\b(?:from|by|as|in|inside|context|assumption|helper|goal|claim|"
        r"target|statement|proof|parent|selected|missing)\b",
        tail,
        flags=re.IGNORECASE,
    ):
        return False
    tokens = tuple(
        token
        for token in _graph_lean_identifier_tokens(tail)
        if token.lower()
        not in {"fun", "let", "in", "by", "from", "where", "match", "with"}
    )
    return bool(tail.strip()) and (
        all(token in bound_names for token in tokens)
        or _graph_application_args_are_formal(body, head)
    )


def _graph_application_args_are_formal(body: str, head: str) -> bool:
    text = graph_identity_text(body)
    if not text.startswith(head):
        return False
    tail = text[len(head) :]
    if tail and not tail[0].isspace() and tail[0] != "(":
        return False
    if re.search(
        r"\b(?:from|by|as|in|inside|context|assumption|helper|goal|claim|"
        r"target|statement|proof|parent|selected|missing|using|via|because|with)\b",
        tail,
        flags=re.IGNORECASE,
    ):
        return False
    return bool(tail.strip())


def _graph_quantified_predicate_body_is_formal(
    body: str,
    binder_context: str,
) -> bool:
    compact = graph_identity_text(body)
    if not compact:
        return False
    prop_signatures = _graph_binder_prop_signatures(binder_context)
    bound_names = set(_graph_binder_context_names(binder_context))
    app_match = re.match(
        rf"^((?:{_GRAPH_LEAN_IDENTIFIER_PATTERN}|[^\W\d_][\w'.]*))(?:\s+|\().+",
        compact,
        flags=re.UNICODE,
    )
    if app_match is None:
        return False
    head = str(app_match.group(1) or "").strip()
    if not head:
        return False
    arg_count = _graph_application_arg_count(compact, head)
    if arg_count is None or arg_count <= 0:
        return False
    prop_arity = prop_signatures.get(head)
    if prop_arity is not None:
        return arg_count == prop_arity and _graph_application_args_are_formal(
            compact,
            head,
        )
    if "." not in head and not _graph_identifier_starts_upper(head):
        return False
    return _graph_application_args_are_bound(compact, head, bound_names)


def _graph_quantified_statement_is_executable(text: str) -> bool:
    body = graph_identity_text(text)
    if not body:
        return False
    saw_quantifier = False
    binder_contexts: List[str] = []
    while body:
        quantifier_len = _graph_top_level_quantifier_token_len(body, 0)
        if quantifier_len <= 0:
            break
        saw_quantifier = True
        remainder = body[quantifier_len:].lstrip()
        comma = _graph_find_top_level_comma(remainder)
        if comma < 0:
            return False
        binder = remainder[:comma].strip()
        next_body = remainder[comma + 1 :].strip()
        if not binder or not next_body:
            return False
        binder_contexts.append(binder)
        body = _graph_strip_balanced_outer_parens(next_body)
    if not saw_quantifier or not body:
        return False
    if _graph_quantified_body_looks_like_prose(
        body
    ) or _graph_quantified_body_has_proof_tail(body):
        return False
    binder_context = ", ".join(binder_contexts)
    bare_tail_atom = _graph_bare_prop_atom_name(body)
    if bare_tail_atom and _graph_context_declares_prop_atom_in_binder(
        bare_tail_atom,
        binder_context,
    ):
        return True
    if _graph_context_prop_atom_tail_uses_declared_atoms(binder_context, body):
        return True
    if body.startswith(("let ", "let\n")):
        # A quantified proposition may introduce local data before its final
        # proposition. Delegate the complete let-chain to the same guarded
        # parser used for a top-level let instead of treating its local value
        # head as the quantified codomain.
        return graph_statement_is_executable(body)
    if _graph_quantified_non_prop_codomain(body, binder_context):
        return False
    if graph_statement_non_theorem_reason(body):
        return False
    implication_parts = split_lean_top_level_implications(body)
    if len(implication_parts) > 1:
        # Lean arrows accept premises in any Sort (for example
        # ``Decidable P -> P ∨ ¬ P``), so requiring each premise to look
        # independently like a proposition rejects valid theorem statements.
        # The whole-statement codomain guard above establishes that the arrow
        # ends in Prop; the proof-tail and balance guards establish that its
        # premises are complete terms.
        return graph_statement_is_executable(implication_parts[-1])
    return bool(
        graph_statement_is_executable(body)
        or _graph_quantified_predicate_body_is_formal(body, binder_context)
    )


def graph_statement_is_executable(text: str) -> bool:
    """Return whether text is plausibly an executable Lean proposition.

    Graph labels such as ``pf_decomposition`` or natural-language failure
    reasons are useful metadata, but they are not proof targets.  This guard is
    intentionally syntactic and conservative: it admits normal theorem
    statements and rejects bare identifiers/reasons before they can be used as
    ``goal_statement_override`` or recursive sub-goals.
    """

    raw_compact = graph_identity_text(text)
    if not raw_compact:
        return False
    raw_lowered = raw_compact.lower()
    if (
        "⊢" in raw_compact
        or raw_lowered.startswith(("case ", "tactic "))
        or has_sorry_or_admit(raw_compact)
        or contains_metavariable_placeholder(raw_compact)
    ):
        return False

    stmt = graph_formal_statement_text(text)
    compact = graph_identity_text(stmt)
    if not compact:
        return False
    if not _graph_text_has_balanced_groups(compact):
        return False
    if _graph_statement_is_obvious_non_proposition(compact):
        return False
    if compact in {"True", "False"}:
        return True
    if has_sorry_or_admit(compact) or contains_metavariable_placeholder(compact):
        return False
    bare_ident = re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", compact)
    if bare_ident:
        return False
    lowered = compact.lower()
    diagnostic_fragments = (
        "⊢",
        "diagnostics:",
        "missing instance",
        "unknown identifier",
        "unknown constant",
        "type mismatch",
        "parse error",
        "parser error",
        "unexpected token",
        "unknown namespace",
        "failed to synthesize",
        "failed to prove",
        "failed to elaborate",
        "invalid field notation",
        "application type mismatch",
        "invalid projection",
        "invalid constructor",
        "invalid argument:",
        "not a proposition",
        "not a term",
        "not a type",
        "not a function",
        "no applicable",
        "remaining goals",
        "unsolved goals",
        "tactic failed",
    )
    diagnostic_text = f"{raw_lowered}\n{lowered}"
    if any(fragment in diagnostic_text for fragment in diagnostic_fragments):
        return False
    diagnostic_prefixes = (
        "error ",
        "error:",
        "error :",
        "unknown identifier",
        "unknown constant",
        "unknown namespace",
        "type mismatch",
        "parse error",
        "parser error",
        "unexpected token",
        "failed to synthesize",
        "failed to prove",
        "failed to elaborate",
        "invalid field notation",
        "application type mismatch",
        "invalid projection",
        "invalid constructor",
        "not enough arguments",
        "not a theorem",
        "no goals to be solved",
        "no goals",
        "no goal",
        "no applicable",
        "no such field",
        "unsolved goals",
        "expected ",
        "function expected",
        "missing cases",
        "missing field",
        "invalid declaration",
        "tactic failed",
        "cannot ",
        "could not ",
    )
    if lowered.startswith(diagnostic_prefixes) or raw_lowered.startswith(
        diagnostic_prefixes
    ):
        return False
    if lowered.startswith(
        (
            "by ",
            "by\n",
            "case ",
            "fail_if_success",
            "exact ",
            "refine ",
            "apply ",
            "first ",
            "tactic ",
            "| ",
        )
    ):
        return False
    if compact.startswith(("fun ", "fun\n")):
        return False
    if compact.startswith(("let ", "let\n")):
        let_binding, let_body = _graph_top_level_let_parts(text)
        if not let_body:
            let_binding, let_body = _graph_top_level_let_parts(stmt)
        local_head, _local_arity = _graph_let_binding_prop_signature(let_binding)
        if (
            local_head
            and _graph_application_arg_count(let_body, local_head) is not None
            and not _graph_contains_top_level_proposition_marker(let_body)
        ):
            return _graph_let_body_is_plausibly_local_prop(
                let_body,
                binding=let_binding,
            )
        return bool(
            let_body
            and (
                graph_statement_is_executable(let_body)
                or _graph_let_body_is_plausibly_local_prop(
                    let_body,
                    binding=let_binding,
                )
            )
        )
    if lowered.startswith(
        (
            "claim has ",
            "claim was ",
            "convert ",
            "formalize ",
            "state ",
            "show that ",
            "prove that ",
            "derive ",
            "explain ",
            "construct ",
            "prove missing dependency ",
            "missing dependency ",
            "sample check ",
            "formal variant ",
            "variant ",
            "tactic rejected",
            "claim exhausted",
        )
    ):
        return False
    if _graph_statement_looks_like_prose_instruction(compact):
        return False
    if _graph_top_level_quantifier_token_len(compact, 0) > 0:
        # Quantified bodies need the let-aware proof-tail parser. The generic
        # detector treats every top-level semicolon as tactic syntax, including
        # the delimiters in a valid quantified let-chain.
        return _graph_quantified_statement_is_executable(compact)
    if _graph_has_top_level_proof_tail(compact):
        return False
    if compact.startswith("¬"):
        return True
    if compact.startswith("not "):
        return graph_statement_is_executable(compact[4:].strip())
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*\s*:\s*[^,()]+", compact):
        return False
    if _graph_contains_proposition_marker(compact):
        return True
    structural_markers = (
        " ∑",
        "∑'",
        "Summable",
        "Set.",
    )
    if any(marker in compact for marker in structural_markers):
        return True
    if _graph_direct_application_has_non_prop_class_head(compact):
        return False
    predicate_match = re.fullmatch(
        r"(?P<pred>(?:[^\W\d_]|_)[\w'.]*)"
        r"(?P<args>\s+.+|\s*\(.+\))",
        compact,
        flags=re.UNICODE,
    )
    if predicate_match:
        pred = str(predicate_match.group("pred") or "").strip()
        args = str(predicate_match.group("args") or "").strip()
        if "." not in pred and not _graph_identifier_starts_upper(pred):
            return False
        if args.startswith("(") and args.endswith(")"):
            return True
        if "." in pred:
            return True
        leanish_tokens = (
            "ℕ",
            "ℤ",
            "ℚ",
            "ℝ",
            "ℂ",
            "^",
            "↑",
            "⟨",
            "⟩",
            "Set.",
        )
        if any(token in args for token in leanish_tokens):
            return True
        if re.search(r"\b\d+\b", args):
            return True
    return False


def _mark_non_theorem_graph_target(
    node: "ProofGraphNode",
    *,
    reason: str,
    raw_statement: str = "",
) -> None:
    """Quarantine a graph-native theorem target whose statement is not a Prop."""

    reason_text = str(reason or "non_theorem_statement").strip()
    node.status = "rejected"
    node.proof_hash = ""
    node.metadata["schedulable"] = False
    node.metadata["graph_statement_non_theorem"] = True
    node.metadata["graph_statement_non_theorem_reason"] = reason_text
    node.metadata["rejection_reason"] = "graph_statement_non_theorem"
    node.metadata["last_rejection_evidence_hash"] = graph_text_hash(
        "\n".join(
            item
            for item in (
                "graph_statement_non_theorem",
                reason_text,
                raw_statement or node.statement,
            )
            if str(item or "").strip()
        )
    )


_GRAPH_FORMAL_STATEMENT_KINDS = frozenset(
    {
        "proposed_claim",
        "formal_variant",
        "missing_obligation",
    }
)


def _rehydrate_graph_node_statement(kind: str, statement: str) -> str:
    kind_text = str(kind or "")
    if (
        kind_text in _GRAPH_FORMAL_STATEMENT_KINDS
        or kind_text.startswith("proof_state_")
    ):
        return graph_formal_statement_text(statement)
    return graph_identity_text(statement)


def _replace_outside_lean_quotes(text: str, replacer: Any) -> str:
    out: List[str] = []
    raw = str(text or "")
    index = 0
    while index < len(raw):
        start = raw.find("«", index)
        if start < 0:
            out.append(str(replacer(raw[index:])))
            break
        out.append(str(replacer(raw[index:start])))
        end = raw.find("»", start + 1)
        if end < 0:
            out.append(raw[start:])
            break
        out.append(raw[start : end + 1])
        index = end + 1
    return "".join(out)


def graph_node_frontier_quarantined(node: Any) -> bool:
    """Return whether an open graph node is intentionally unschedulable."""

    metadata = dict(getattr(node, "metadata", {}) or {})
    target_integrity_root_equiv_bypass = bool(
        metadata.get("target_integrity_adjudication")
        and metadata.get("allow_root_equivalent_target_integrity_adjudication")
    )
    return bool(
        metadata.get("schedulable") is False
        or metadata.get("residual_goal_quarantined") is True
        or metadata.get("failed_proof_residual_quarantined") is True
        or metadata.get("route_retired") is True
        or metadata.get("route_dependency_contradicted") is True
        or (
            metadata.get("root_equivalent_work_suppressed") is True
            and not target_integrity_root_equiv_bypass
        )
        or str(metadata.get("obligation_trust") or "")
        == "untrusted_failed_proof_residual"
    )


def graph_node_frontier_promoted_to_proof_state(node: Any) -> bool:
    """Return whether graph-native work is delegated to proof-state child work."""

    metadata = dict(getattr(node, "metadata", {}) or {})
    return bool(
        metadata.get("promoted_to_proof_state") is True
        or str(metadata.get("proof_state_child_node_id") or "").strip()
        or str(metadata.get("proof_state_child_graph_node_id") or "").strip()
    )


def _shield_lean_quotes_for_identity(text: str) -> str:
    """Replace Lean lexical literals with stable identifier-shaped tokens.

    NUL-delimited internal tokens cannot occur in valid Lean source, while the
    graph parser still recognizes them as atomic binder identities.  Strings,
    raw strings, character literals, and quoted identifiers must remain opaque
    to every later algebraic and surface-syntax rewrite.  Hashing the exact
    lexical spelling keeps every byte identity-bearing without an in-band
    placeholder that user notation could reproduce.
    """

    raw = str(text or "")
    if (
        '"' not in raw
        and "«" not in raw
        and ("'" not in raw or re.search(r"(?<![\w'»])'", raw) is None)
    ):
        return raw
    out: List[str] = []
    index = 0
    while index < len(raw):
        lexical_end = _lean_lexical_skip_end(raw, index)
        if lexical_end is None:
            out.append(raw[index])
            index += 1
            continue
        lexical = raw[index:lexical_end]
        digest = hashlib.sha256(lexical.encode("utf-8")).hexdigest()[:20]
        token_kind = "Q" if raw.startswith("«", index) else "L"
        out.append(f"\x00{token_kind}{digest}\x00")
        index = lexical_end
    return "".join(out)


def _scoped_statement_identity_text(text: str) -> str:
    try:
        from .proof_state import canonicalize_lean_statement_for_identity
    except Exception:
        return str(text or "")
    try:
        return canonicalize_lean_statement_for_identity(str(text or ""))
    except Exception:
        return str(text or "")


def _helper_render_policy_context_visible(render_policy: str) -> bool:
    return str(render_policy or "").strip() in {"", "root_authoritative"}


def _consume_explicit_set_univ_type_arg(text: str, start: int) -> Tuple[str, int]:
    source = str(text or "")
    idx = int(start or 0)
    while idx < len(source) and source[idx].isspace():
        idx += 1
    if idx >= len(source):
        return "", idx
    opener_to_closer = {"(": ")", "{": "}", "[": "]", "⟨": "⟩"}
    opener = source[idx]
    closer = opener_to_closer.get(opener)
    if closer is not None:
        depth = 0
        cursor = idx
        while cursor < len(source):
            skip_to = _lean_lexical_skip_end(source, cursor)
            if skip_to is not None:
                cursor = skip_to
                continue
            char = source[cursor]
            if char == opener:
                depth += 1
            elif char == closer:
                depth -= 1
                if depth == 0:
                    cursor += 1
                    return source[idx:cursor].strip(), cursor
            cursor += 1
        return source[idx:].strip(), len(source)

    cursor = idx
    while cursor < len(source):
        char = source[cursor]
        if char.isspace() or char in ",)=↔→<>&|+-*/;⊆⊂≤≥∈∉≠":
            break
        cursor += 1
    return source[idx:cursor].strip(), cursor


def _preserve_explicit_set_univ_type_args(text: str) -> str:
    source = str(text or "")
    marker = "@Set.univ"
    pieces: List[str] = []
    cursor = 0
    while cursor < len(source):
        skip_to = _lean_lexical_skip_end(source, cursor)
        if skip_to is not None:
            pieces.append(source[cursor:skip_to])
            cursor = skip_to
            continue
        if not source.startswith(marker, cursor):
            pieces.append(source[cursor])
            cursor += 1
            continue
        after_marker = cursor + len(marker)
        if (
            after_marker < len(source)
            and re.match(r"[A-Za-z0-9_']", source[after_marker])
        ):
            pieces.append(source[cursor:after_marker])
            cursor = after_marker
            continue
        if source.startswith(".{", after_marker):
            depth = 1
            after_marker += 2
            while after_marker < len(source) and depth > 0:
                if source[after_marker] == "{":
                    depth += 1
                elif source[after_marker] == "}":
                    depth -= 1
                after_marker += 1
        elif after_marker < len(source) and source[after_marker] == ".":
            after_marker += 1
            while (
                after_marker < len(source)
                and re.match(r"[A-Za-z0-9_']", source[after_marker])
            ):
                after_marker += 1
        type_arg, end = _consume_explicit_set_univ_type_arg(source, after_marker)
        if type_arg:
            pieces.append(
                f"Set.univ[{_graph_strip_balanced_outer_parens(type_arg)}]"
            )
            cursor = end
        else:
            pieces.append("Set.univ")
            cursor = after_marker
    return "".join(pieces)


def _binder_type_map_for_statement_key(text: str) -> Dict[str, str]:
    mapping: Dict[str, str] = {}
    ambiguous: Set[str] = set()
    ident_re = re.compile(r"(?:⟪Q[0-9a-f]{20}⟫|(?:[^\W\d]|_)[\w'✝]*)")
    opener_to_closer = {"(": ")", "{": "}", "[": "]"}
    closer_to_opener = {closer: opener for opener, closer in opener_to_closer.items()}
    source = str(text or "")

    def normalize_type(type_text: str) -> str:
        return _graph_strip_balanced_outer_parens(
            " ".join(str(type_text or "").split()).strip()
        )

    def split_top_level_colon(value: str) -> Tuple[str, str]:
        depth = 0
        cursor = 0
        while cursor < len(value):
            skip_to = _lean_lexical_skip_end(value, cursor)
            if skip_to is not None:
                cursor = skip_to
                continue
            char = value[cursor]
            if char in opener_to_closer:
                depth += 1
            elif char in closer_to_opener:
                depth = max(0, depth - 1)
            elif char == ":" and depth == 0:
                return value[:cursor], value[cursor + 1 :]
            cursor += 1
        return "", ""

    def consume_group(value: str, start: int) -> Tuple[str, int]:
        opener = value[start]
        closer = opener_to_closer.get(opener)
        if closer is None:
            return "", start
        stack = [opener]
        cursor = start + 1
        while cursor < len(value) and stack:
            skip_to = _lean_lexical_skip_end(value, cursor)
            if skip_to is not None:
                cursor = skip_to
                continue
            char = value[cursor]
            if char in opener_to_closer:
                stack.append(char)
            elif char in closer_to_opener and stack[-1] == closer_to_opener[char]:
                stack.pop()
            cursor += 1
        if stack:
            return "", start + 1
        return value[start + 1 : cursor - 1], cursor

    def remember(names_text: str, type_text: str) -> None:
        type_clean = normalize_type(type_text)
        if not type_clean:
            return
        for name in ident_re.findall(str(names_text or "")):
            if not name or name in ambiguous:
                continue
            previous = mapping.get(name)
            if previous is not None and previous != type_clean:
                mapping.pop(name, None)
                ambiguous.add(name)
                continue
            mapping[name] = type_clean

    def quantifier_at(index: int) -> int:
        char = source[index]
        if char in {"∀", "∃"}:
            end = index + 1
            if end < len(source) and source[end].isspace():
                return end
            return 0
        for word in ("forall", "exists"):
            end = index + len(word)
            if (
                source.startswith(word, index)
                and (index == 0 or not re.match(r"[\w'✝]", source[index - 1]))
                and end < len(source)
                and source[end].isspace()
            ):
                return end
        return 0

    index = 0
    while index < len(source):
        skip_to = _lean_lexical_skip_end(source, index)
        if skip_to is not None:
            index = skip_to
            continue
        quantifier_end = quantifier_at(index)
        if not quantifier_end:
            index += 1
            continue
        cursor = quantifier_end
        while cursor < len(source) and source[cursor].isspace():
            cursor += 1
        binder_start = cursor
        depth = 0
        while cursor < len(source):
            skip_to = _lean_lexical_skip_end(source, cursor)
            if skip_to is not None:
                cursor = skip_to
                continue
            char = source[cursor]
            if char in opener_to_closer:
                depth += 1
            elif char in closer_to_opener:
                depth = max(0, depth - 1)
            elif char == "," and depth == 0:
                break
            cursor += 1
        binder_part = source[binder_start:cursor]
        bare_chars = list(binder_part)
        group_index = 0
        while group_index < len(binder_part):
            skip_to = _lean_lexical_skip_end(binder_part, group_index)
            if skip_to is not None:
                group_index = skip_to
                continue
            if binder_part[group_index] not in opener_to_closer:
                group_index += 1
                continue
            body, group_end = consume_group(binder_part, group_index)
            names_text, type_text = split_top_level_colon(body)
            if names_text and type_text:
                remember(names_text, type_text)
            for blank_index in range(group_index, min(group_end, len(bare_chars))):
                bare_chars[blank_index] = " "
            group_index = max(group_end, group_index + 1)
        names_text, type_text = split_top_level_colon("".join(bare_chars))
        if names_text and type_text:
            remember(names_text, type_text)
        index = cursor + 1 if cursor < len(source) else cursor
    return mapping


def _set_element_type_from_binder_type(type_text: str) -> str:
    clean = _graph_strip_balanced_outer_parens(
        " ".join(str(type_text or "").split()).strip()
    )
    if clean.startswith("Set "):
        return _graph_strip_balanced_outer_parens(clean[len("Set ") :].strip())
    return ""


def _sub_outside_lean_literals(
    text: str,
    pattern: str,
    repl: Any,
) -> str:
    source = str(text or "")
    compiled = re.compile(pattern)
    pieces: List[str] = []
    segment_start = 0
    index = 0
    while index < len(source):
        skip_to = _lean_lexical_skip_end(source, index)
        if skip_to is not None:
            if segment_start < index:
                pieces.append(compiled.sub(repl, source[segment_start:index]))
            pieces.append(source[index:skip_to])
            index = skip_to
            segment_start = index
            continue
        index += 1
    if segment_start < len(source):
        pieces.append(compiled.sub(repl, source[segment_start:]))
    return "".join(pieces)


def _normalize_subset_spacing_outside_lean_literals(text: str) -> str:
    source = str(text or "")
    pieces: List[str] = []
    index = 0
    while index < len(source):
        skip_to = _lean_lexical_skip_end(source, index)
        if skip_to is not None:
            pieces.append(source[index:skip_to])
            index = skip_to
            continue
        if source.startswith("⊆", index):
            while pieces and pieces[-1].isspace():
                pieces.pop()
            pieces.append("⊆")
            index += 1
            while index < len(source) and source[index].isspace():
                index += 1
            continue
        pieces.append(source[index])
        index += 1
    return "".join(pieces)


def _annotate_inferred_set_univ_type_args(text: str) -> str:
    source = str(text or "")
    binder_types = _binder_type_map_for_statement_key(source)
    if not binder_types or "Set.univ" not in source:
        return source

    def membership_replacement(match: re.Match[str]) -> str:
        name = str(match.group("name") or "")
        type_arg = binder_types.get(name, "")
        if not type_arg:
            return match.group(0)
        return f"{name}∈Set.univ[{type_arg}]"

    def right_equality_replacement(match: re.Match[str]) -> str:
        name = str(match.group("name") or "")
        type_arg = _set_element_type_from_binder_type(binder_types.get(name, ""))
        if not type_arg:
            return match.group(0)
        return f"{name}=Set.univ[{type_arg}]"

    def left_equality_replacement(match: re.Match[str]) -> str:
        name = str(match.group("name") or "")
        type_arg = _set_element_type_from_binder_type(binder_types.get(name, ""))
        if not type_arg:
            return match.group(0)
        return f"Set.univ[{type_arg}]={name}"

    def right_subset_replacement(match: re.Match[str]) -> str:
        name = str(match.group("name") or "")
        type_arg = _set_element_type_from_binder_type(binder_types.get(name, ""))
        if not type_arg:
            return match.group(0)
        return f"{name}⊆Set.univ[{type_arg}]"

    def left_subset_replacement(match: re.Match[str]) -> str:
        name = str(match.group("name") or "")
        type_arg = _set_element_type_from_binder_type(binder_types.get(name, ""))
        if not type_arg:
            return match.group(0)
        return f"Set.univ[{type_arg}]⊆{name}"

    source = _sub_outside_lean_literals(
        source,
        r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*∈\s*Set\.univ(?!\[)",
        membership_replacement,
    )
    source = _sub_outside_lean_literals(
        source,
        r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*=\s*Set\.univ(?!\[)",
        right_equality_replacement,
    )
    source = _sub_outside_lean_literals(
        source,
        r"Set\.univ(?!\[)\s*=\s*(?P<name>[A-Za-z_][A-Za-z0-9_']*)",
        left_equality_replacement,
    )
    source = _sub_outside_lean_literals(
        source,
        r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*⊆\s*Set\.univ(?!\[)",
        right_subset_replacement,
    )
    source = _sub_outside_lean_literals(
        source,
        r"Set\.univ(?!\[)\s*⊆\s*(?P<name>[A-Za-z_][A-Za-z0-9_']*)",
        left_subset_replacement,
    )
    return source


@lru_cache(maxsize=32768)
def graph_statement_key(text: str) -> str:
    """Small graph-local equivalence key for matching proved helper statements."""

    normalized = normalize_statement(
        _shield_lean_quotes_for_identity(_scoped_statement_identity_text(text))
    )
    # Capture guard (external review): rewriting Nat→ℕ in a statement that
    # ALSO contains ℕ merges a binder named Nat with the real ℕ — skip the
    # unification when both spellings coexist (false-mismatch only).
    if not re.search(r"(?<![\w'✝.])ℕ(?![\w'✝])", normalized):
        normalized = re.sub(r"(?<![\w'✝.])Nat(?![\w'✝])", "ℕ", normalized)
    normalized = re.sub(r"(?<![\w'✝])forall(?=\s+)", "∀", normalized)
    normalized = re.sub(r"(?<![\w'✝])exists(?=\s+)", "∃", normalized)
    normalized = _preserve_explicit_set_univ_type_args(normalized)
    normalized = _annotate_inferred_set_univ_type_args(normalized)
    normalized = _normalize_subset_spacing_outside_lean_literals(normalized)

    def is_nat_binder_type(type_text: str) -> bool:
        clean = " ".join(str(type_text or "").split()).strip()
        while clean.startswith("(") and clean.endswith(")"):
            clean = clean[1:-1].strip()
        clean = clean.strip("{}[]")
        return clean == "ℕ"

    def strip_balanced_outer_parens(value: str) -> str:
        clean = str(value or "").strip()
        while clean.startswith("(") and clean.endswith(")"):
            depth = 0
            wraps = True
            for idx, char in enumerate(clean):
                if char == "(":
                    depth += 1
                elif char == ")":
                    depth -= 1
                    if depth == 0 and idx != len(clean) - 1:
                        wraps = False
                        break
                if depth < 0:
                    wraps = False
                    break
            if not wraps or depth != 0:
                break
            clean = clean[1:-1].strip()
        return clean

    def split_typed_binder_groups(
        binder_part: str,
    ) -> Tuple[List[Tuple[str, str]], List[str], str]:
        groups: List[Tuple[str, str]] = []
        untyped_groups: List[str] = []
        chars = list(str(binder_part or ""))
        open_to_close = {"(": ")", "{": "}", "[": "]"}
        close_to_open = {close: open_ for open_, close in open_to_close.items()}
        index = 0
        while index < len(chars):
            opener = chars[index]
            if opener not in open_to_close:
                index += 1
                continue
            stack = [opener]
            end = index + 1
            while end < len(chars) and stack:
                char = chars[end]
                if char in open_to_close:
                    stack.append(char)
                elif char in close_to_open and stack[-1] == close_to_open[char]:
                    stack.pop()
                end += 1
            if stack:
                index += 1
                continue
            prefix = "".join(chars[:index]).rstrip()
            if _graph_relation_binder_prefix_expects_group_rhs(prefix):
                index = end
                continue
            body = "".join(chars[index + 1 : end - 1])
            if ":" in body:
                names_text, type_text = body.split(":", 1)
                groups.append((names_text, type_text))
            elif opener in {"(", "{"}:
                untyped_groups.append(body)
            for blank_index in range(index, end):
                chars[blank_index] = " "
            index = end
        return groups, untyped_groups, "".join(chars)

    quoted_identity_token = "\x00[LQ][0-9a-f]{20}\x00"
    identifier_body = rf"(?:{quoted_identity_token}|(?:[^\W\d]|_)\w*(?:['✝]\w*)*)"
    identifier_pattern = rf"(?<![\w'✝]){identifier_body}(?![\w'✝])"
    while True:
        unwrapped = re.sub(
            rf"\(\s*({identifier_body})\s*\)",
            r"\1",
            normalized,
        )
        if unwrapped == normalized:
            break
        normalized = unwrapped
    nat_bound_names: Set[str] = set()
    quantifier_binder_pattern = r"(?:∀|∃|forall|exists)\s+([^,]+),"
    for match in re.finditer(quantifier_binder_pattern, normalized):
        binder_part = match.group(1)
        typed_groups, _untyped_groups, bare_part = split_typed_binder_groups(binder_part)
        for names_text, type_text in typed_groups:
            if not is_nat_binder_type(type_text):
                continue
            for name in re.findall(identifier_pattern, names_text):
                nat_bound_names.add(name)
        if ":" in bare_part:
            bare_names, bare_type = bare_part.split(":", 1)
            if is_nat_binder_type(bare_type):
                for name in re.findall(identifier_pattern, bare_names):
                    nat_bound_names.add(name)
    if nat_bound_names:
        nat_name_alt = "|".join(re.escape(name) for name in sorted(nat_bound_names))

        def rewrite_nat_succ_chain(match: re.Match[str]) -> str:
            expr = str(match.group("name") or "")
            chain = str(match.group("chain") or "")
            for _ in range(chain.count(".succ")):
                expr = (
                    f"ℕ.succ ({expr})"
                    if expr.startswith("ℕ.succ ")
                    else f"ℕ.succ {expr}"
                )
            return expr

        def rewrite_parenthesized_nat_succ_receiver(value: str) -> str:
            text_value = str(value or "")
            scan = 0
            while True:
                marker = text_value.find(").succ", scan)
                if marker < 0:
                    return text_value
                depth = 0
                start = -1
                for pos in range(marker, -1, -1):
                    char = text_value[pos]
                    if char == ")":
                        depth += 1
                    elif char == "(":
                        depth -= 1
                        if depth == 0:
                            start = pos
                            break
                if start < 0:
                    scan = marker + len(").succ")
                    continue
                inner = strip_balanced_outer_parens(text_value[start + 1 : marker])
                if not inner.startswith("ℕ.succ "):
                    scan = marker + len(").succ")
                    continue
                replacement = f"ℕ.succ ({inner})"
                text_value = (
                    text_value[:start]
                    + replacement
                    + text_value[marker + len(").succ") :]
                )
                scan = max(0, start - 1)

        def balanced_group_end(value: str, start: int) -> int:
            if start < 0 or start >= len(value) or value[start] != "(":
                return -1
            depth = 0
            for pos in range(start, len(value)):
                char = value[pos]
                if char == "(":
                    depth += 1
                elif char == ")":
                    depth -= 1
                    if depth == 0:
                        return pos
                if depth < 0:
                    return -1
            return -1

        def normalize_nat_succ_argument_parens(value: str) -> str:
            text_value = str(value or "")
            scan = 0
            while True:
                start = text_value.find("ℕ.succ", scan)
                if start < 0:
                    return text_value
                arg_start = start + len("ℕ.succ")
                while arg_start < len(text_value) and text_value[arg_start].isspace():
                    arg_start += 1
                if arg_start >= len(text_value) or text_value[arg_start] != "(":
                    scan = arg_start
                    continue
                arg_end = balanced_group_end(text_value, arg_start)
                if arg_end < 0:
                    scan = arg_start + 1
                    continue
                arg_text = text_value[arg_start : arg_end + 1]
                stripped = strip_balanced_outer_parens(arg_text)
                replacement = f"({stripped})"
                if replacement == arg_text:
                    scan = arg_start + 1
                    continue
                text_value = text_value[:arg_start] + replacement + text_value[arg_end + 1 :]
                scan = start

        while True:
            prior = normalized
            normalized = re.sub(
                rf"(?<![\w'✝])(?P<name>{nat_name_alt})(?P<chain>(?:\.succ)+)\b",
                rewrite_nat_succ_chain,
                normalized,
            )
            normalized = rewrite_parenthesized_nat_succ_receiver(normalized)
            normalized = normalize_nat_succ_argument_parens(normalized)
            if normalized == prior:
                break
    normalized = re.sub(r":\s*\(+\s*ℕ\s*\)+([\)\}\]])", r": ℕ\1", normalized)
    normalized = re.sub(r":\s*\(+\s*ℕ\s*\)+(,)", r": ℕ\1", normalized)
    normalized = re.sub(r"\(\s*0\s*:\s*\(\s*ℕ\s*\)\s*\)", "0", normalized)
    normalized = re.sub(r"\(\s*0\s*:\s*ℕ\s*\)", "0", normalized)
    while True:
        unwrapped_zero = re.sub(r"\(\s*0\s*\)", "0", normalized)
        if unwrapped_zero == normalized:
            break
        normalized = unwrapped_zero
    normalized = re.sub(
        rf"\(\s*({identifier_body})\s*\)",
        r"\1",
        normalized,
    )

    def rewrite_zero_bound_inequality(match: re.Match[str]) -> str:
        tail = normalized[match.end() :].lstrip()
        allowed_tail_prefixes = (
            ")",
            "]",
            "}",
            ",",
            ";",
            "→",
            "->",
            "=>",
            "∧",
            "∨",
            "↔",
        )
        if tail and not tail.startswith(allowed_tail_prefixes):
            return match.group(0)
        operator = ">" if match.group("op") == "<" else "≥"
        return f"{match.group('name')} {operator} 0"

    normalized = re.sub(
        rf"(?<![\w'✝])0\s*(?P<op><|≤)\s*(?P<name>{identifier_body})(?![\w'✝])",
        rewrite_zero_bound_inequality,
        normalized,
    )
    binder_names: List[str] = []
    for match in re.finditer(quantifier_binder_pattern, normalized):
        binder_part = match.group(1)
        typed_groups, untyped_groups, bare_part = split_typed_binder_groups(binder_part)
        name_groups = [names_text for names_text, _type_text in typed_groups]
        for group in untyped_groups:
            if lean_relation_binder_premise(group):
                name_groups.extend(_graph_binder_names_from_chunk(group))
            else:
                name_groups.append(group)
        bare_clean = str(bare_part or "").strip()
        if ":" in bare_clean:
            name_groups.append(bare_clean.split(":", 1)[0])
        elif lean_relation_binder_premise(bare_clean):
            name_groups.extend(_graph_binder_names_from_chunk(bare_clean))
        elif bare_clean:
            name_groups.append(bare_clean)
        if not name_groups and bare_part:
            name_groups = [bare_part]
        for group in name_groups:
            for name in re.findall(identifier_pattern, group):
                if name not in binder_names:
                    binder_names.append(name)
    for index, name in enumerate(binder_names):
        normalized = re.sub(
            rf"(?<![\w'✝]){re.escape(name)}(?![\w'✝])",
            f"__b{index}",
            normalized,
        )
    normalized = re.sub(
        r"((?:∀|∃|forall|exists)\s+__b\d+\s*:\s*ℕ)\)+\s*,",
        r"\1,",
        normalized,
    )
    while True:
        compact_parens = re.sub(r"\(\s+", "(", normalized)
        compact_parens = re.sub(r"\s+\)", ")", compact_parens)
        if compact_parens == normalized:
            break
        normalized = compact_parens

    def safe_strip_side_parens(side: str) -> str:
        value = str(side or "").strip()
        while True:
            stripped = strip_balanced_outer_parens(value)
            if stripped == value:
                return value
            # Parentheses around propositions/arrows are not presentation-only
            # in Lean surface syntax.  Keep those intact; this identity pass is
            # only erasing redundant grouping around expression sides such as
            # ``(a / b) = c``.
            if any(token in stripped for token in ("∀", "∃", "→", "↔", "->", "<->")):
                return value
            value = stripped

    def split_top_level_identity_operator(
        value: str,
    ) -> Optional[Tuple[str, str, str]]:
        text = str(value or "")
        open_to_close = {"(": ")", "{": "}", "[": "]"}
        close_to_open = {close: open_ for open_, close in open_to_close.items()}
        stack: List[str] = []
        operators = ("≤", "≥", "≠", "=", "<", ">", "∈", "∉", "∣")
        index = 0
        while index < len(text):
            char = text[index]
            if char in open_to_close:
                stack.append(char)
                index += 1
                continue
            if char in close_to_open:
                if stack and stack[-1] == close_to_open[char]:
                    stack.pop()
                index += 1
                continue
            if not stack:
                for operator in operators:
                    if text.startswith(operator, index):
                        left = text[:index].strip()
                        right = text[index + len(operator) :].strip()
                        if left and right:
                            return left, operator, right
            index += 1
        return None

    def split_leading_quantifier_body(value: str) -> Optional[Tuple[str, str]]:
        text = str(value or "").strip()
        if not text.startswith(("∀", "∃")):
            return None
        open_to_close = {"(": ")", "{": "}", "[": "]"}
        close_to_open = {close: open_ for open_, close in open_to_close.items()}
        stack: List[str] = []
        for index, char in enumerate(text):
            if char in open_to_close:
                stack.append(char)
                continue
            if char in close_to_open:
                if stack and stack[-1] == close_to_open[char]:
                    stack.pop()
                continue
            if char == "," and not stack:
                prefix = text[: index + 1].strip()
                body = text[index + 1 :].strip()
                if prefix and body:
                    return prefix, body
        return None

    def normalize_redundant_identity_side_parens(value: str) -> str:
        text = str(value or "").strip()
        quantifier_split = split_leading_quantifier_body(text)
        if quantifier_split is not None:
            prefix, body = quantifier_split
            return f"{prefix} {normalize_redundant_identity_side_parens(body)}"
        identity_split = split_top_level_identity_operator(text)
        if identity_split is None:
            return text
        left, operator, right = identity_split
        return (
            f"{safe_strip_side_parens(left)} {operator} "
            f"{safe_strip_side_parens(right)}"
        )

    normalized = normalize_redundant_identity_side_parens(normalized)
    normalized = re.sub(r"\s*([<>=≤≥∣:∈∉])\s*", r"\1", normalized)
    return " ".join(normalized.split()).strip()


def _graph_strip_balanced_outer_parens(text: str) -> str:
    value = str(text or "").strip()
    while value.startswith("(") and value.endswith(")"):
        depth = 0
        balanced = True
        for index, ch in enumerate(value):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and index != len(value) - 1:
                    balanced = False
                    break
                if depth < 0:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        value = value[1:-1].strip()
    return value


def graph_negated_statement_key(text: str) -> str:
    """Return the graph statement key for ``P`` when ``text`` refutes ``P``."""

    def negative_conclusion(value: str) -> bool:
        compact_value = " ".join(str(value or "").split()).strip()
        return bool(
            compact_value == "False"
            or compact_value.startswith("False ")
            or compact_value.startswith("¬")
            or compact_value.startswith("Not ")
        )

    body = _graph_strip_balanced_outer_parens(str(text or "").strip())
    if not body:
        return ""
    try:
        premises, conclusion, _bound_names = _graph_statement_premises_and_conclusion(
            body
        )
        if len(premises) == 1 and negative_conclusion(conclusion):
            return graph_statement_key(premises[0])
        if conclusion:
            body = conclusion
    except Exception:
        pass
    compact = " ".join(body.split()).strip()
    inner = ""
    if compact.startswith("¬"):
        inner = compact[1:].strip()
    elif compact.startswith("Not "):
        inner = compact[4:].strip()
    if not inner:
        return ""
    inner = _graph_strip_balanced_outer_parens(inner)
    return graph_statement_key(inner)


def _graph_find_top_level_comma(text: str) -> int:
    raw = str(text or "")
    depth = 0
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            return index
        index += 1
    return -1


def _graph_split_top_level_implications(text: str) -> List[str]:
    return [
        _graph_strip_balanced_outer_parens(part)
        for part in split_lean_top_level_implications(text)
    ]


def _graph_split_top_level_iffs(text: str) -> List[str]:
    value = str(text or "")
    parts: List[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(value):
        skip_to = _lean_lexical_skip_end(value, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = value[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "↔" and depth == 0:
            parts.append(value[start:index].strip())
            start = index + 1
        elif depth == 0 and value.startswith("<->", index):
            parts.append(value[start:index].strip())
            start = index + 3
            index += 2
        index += 1
    parts.append(value[start:].strip())
    return [_graph_strip_balanced_outer_parens(part) for part in parts if part.strip()]


def _graph_split_top_level_conjunctions(text: str) -> List[str]:
    value = str(text or "")
    parts: List[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(value):
        skip_to = _lean_lexical_skip_end(value, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = value[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "∧" and depth == 0:
            parts.append(value[start:index].strip())
            start = index + 1
        index += 1
    parts.append(value[start:].strip())
    return [_graph_strip_balanced_outer_parens(part) for part in parts if part.strip()]


def _graph_split_top_level_disjunctions(text: str) -> List[str]:
    value = str(text or "")
    parts: List[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(value):
        skip_to = _lean_lexical_skip_end(value, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = value[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "∨" and depth == 0:
            parts.append(value[start:index].strip())
            start = index + 1
        index += 1
    parts.append(value[start:].strip())
    return [_graph_strip_balanced_outer_parens(part) for part in parts if part.strip()]


def _graph_flatten_top_level_disjunctions(text: str) -> List[str]:
    """Return branch leaves for a Lean disjunction proposition.

    Lean's ``∨`` notation is right-associative in normal planner output, but
    graph contracts should not depend on a single flat textual spelling.
    This flattens any parenthesized/top-level disjunction tree while keeping
    branch positions intact for proof synthesis.
    """

    parts = _graph_split_top_level_disjunctions(text)
    if len(parts) < 2:
        return [_graph_strip_balanced_outer_parens(text)] if str(text or "").strip() else []
    out: List[str] = []
    for part in parts:
        nested = _graph_flatten_top_level_disjunctions(part)
        out.extend(nested or [part])
    return [_graph_strip_balanced_outer_parens(part) for part in out if part.strip()]


def _graph_disjunction_tree(text: str) -> Dict[str, Any]:
    """Return a lightweight syntax tree for a top-level Lean ``Or`` expression."""

    body = _graph_strip_balanced_outer_parens(text)
    parts = _graph_split_top_level_disjunctions(body)
    if len(parts) < 2:
        return {"leaf": body}
    if len(parts) == 2:
        return {
            "or": [
                _graph_disjunction_tree(parts[0]),
                _graph_disjunction_tree(parts[1]),
            ]
        }
    # Lean parses unparenthesized chained ``∨`` notation right-associatively.
    tail = _graph_disjunction_tree(parts[-1])
    for part in reversed(parts[1:-1]):
        tail = {"or": [_graph_disjunction_tree(part), tail]}
    return {"or": [_graph_disjunction_tree(parts[0]), tail]}


def _graph_disjunction_tree_leaves(
    tree: Dict[str, Any],
    *,
    path: Tuple[int, ...] = (),
) -> List[Dict[str, Any]]:
    if not isinstance(tree, dict):
        return []
    if "leaf" in tree:
        leaf = _graph_strip_balanced_outer_parens(str(tree.get("leaf") or ""))
        return [{"statement": leaf, "path": list(path)}] if leaf else []
    children = list(tree.get("or") or [])
    if len(children) != 2:
        return []
    leaves: List[Dict[str, Any]] = []
    leaves.extend(
        _graph_disjunction_tree_leaves(
            dict(children[0] or {}),
            path=(*path, 0),
        )
    )
    leaves.extend(
        _graph_disjunction_tree_leaves(
            dict(children[1] or {}),
            path=(*path, 1),
        )
    )
    return leaves


def _graph_case_disjunction_support(statement: str) -> Dict[str, Any]:
    """Return top-level disjunction evidence for branch-frame synthesis.

    Branch frames model Lean ``cases`` over an actual ``Or`` value.  A theorem
    whose body is an implication mentioning ``∨`` is a reducer, not case
    evidence, and must not create branch scopes.
    """

    body, bound_names = _graph_strip_leading_forall_binders_with_names(statement)
    if len(_graph_split_top_level_implications(body)) != 1:
        return {}
    tree = _graph_disjunction_tree(body)
    leaves = _graph_disjunction_tree_leaves(tree)
    if len(leaves) < 2:
        return {}
    return {
        "full_statement": str(statement or "").strip(),
        "statement": _graph_strip_balanced_outer_parens(body),
        "bound_names": tuple(bound_names),
        "tree": tree,
        "leaves": leaves,
    }


def _graph_top_level_binder_separator_index(text: str, tokens: Sequence[str]) -> int:
    raw = str(text or "")
    depth = 0
    index = 0
    matches: List[int] = []
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0:
            for token in tokens:
                if raw.startswith(token, index):
                    matches.append(index)
                    break
        index += 1
    return min(matches) if matches else -1


def _graph_top_level_colon_index(text: str) -> int:
    return _graph_top_level_binder_separator_index(text, (":",))


def _graph_typed_binder_annotation_index(text: str) -> int:
    """Return a genuine top-level binder annotation colon, if present.

    The general colon splitter intentionally also sees ``:=`` and ``::``.
    Those tokens are meaningful inside ordinary parenthesized expressions but
    cannot introduce a typed binder annotation.  This narrower recognizer is
    used when deciding whether a leading group is Pi-telescope syntax.
    """

    raw = str(text or "")
    depth = 0
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif (
            depth == 0
            and ch == ":"
            and not raw.startswith(":=", index)
            and not raw.startswith("::", index)
            and (index == 0 or raw[index - 1] != ":")
        ):
            return index
        index += 1
    return -1


def _graph_is_binder_name_surface(text: str) -> bool:
    """Whether text is one or more Lean identifier binder names."""

    raw = str(text or "").strip()
    if not raw:
        return False
    index = 0
    found = False
    reserved = {
        "by",
        "do",
        "else",
        "forall",
        "from",
        "fun",
        "have",
        "if",
        "in",
        "let",
        "match",
        "show",
        "then",
        "with",
    }
    while index < len(raw):
        while index < len(raw) and raw[index].isspace():
            index += 1
        if index >= len(raw):
            break
        if raw.startswith("«", index):
            end = raw.find("»", index + 1)
            if end < 0 or end == index + 1:
                return False
            index = end + 1
            found = True
            continue
        match = re.match(r"[^\W\d][\w']*", raw[index:], flags=re.UNICODE)
        if match is None:
            return False
        if match.group(0).lower() in reserved:
            return False
        index += len(match.group(0))
        found = True
    return found


def _graph_binder_names_from_chunk(chunk: str) -> Tuple[str, ...]:
    raw = str(chunk or "").strip()
    chunks = _graph_binder_group_chunks(raw)
    groups = chunks if chunks != (raw,) else (raw,)
    names: List[str] = []
    for group in groups:
        group_text = str(group or "").strip()
        body = _graph_unwrap_binder_group(group_text)
        separator = _graph_top_level_binder_separator_index(
            body,
            (":", *_GRAPH_RELATION_BINDER_TOKENS),
        )
        if separator >= 0:
            body = body[:separator]
        body = body.translate(str.maketrans({ch: " " for ch in "(){}[]⦃⦄⟨⟩"}))
        for name in _graph_lean_identifier_tokens(body):
            if name.lower() in {"forall", "exists", "fun", "by", "let", "in"}:
                continue
            if name not in names:
                names.append(name)
    return tuple(names)


def _graph_unwrap_binder_group(text: str) -> str:
    raw = str(text or "").strip()
    if len(raw) >= 2:
        closer = _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.get(raw[0])
        if closer and raw.endswith(closer):
            return raw[1:-1].strip()
    return raw


def _graph_relation_binder_prefix_expects_group_rhs(text: str) -> bool:
    raw = str(text or "").strip()
    if not raw:
        return False
    # Ask the shared Lean-surface parser with a synthetic RHS. This supports
    # user-defined and Unicode infix relations instead of duplicating a closed
    # operator list merely to decide whether a following group belongs here.
    return bool(lean_relation_binder_premise(f"{raw} __mini_rhs"))


def _graph_typed_binder_prefix_expects_group_rhs(text: str) -> bool:
    """Whether an opener belongs to an ungrouped binder's type expression."""

    return _graph_top_level_colon_index(str(text or "")) >= 0


def _graph_binder_type_without_default(type_text: str) -> str:
    """Strip a top-level binder default without truncating ``let ... :=``."""

    clean = str(type_text or "").strip()
    assignment = _graph_top_level_binder_separator_index(clean, (":=",))
    if assignment < 0:
        return clean
    prefix = clean[:assignment].strip()
    if re.search(r"(?:^|[^A-Za-z0-9_'])let(?:$|[^A-Za-z0-9_'])", prefix):
        return clean
    return prefix


def _graph_binder_group_chunks(chunk: str) -> Tuple[str, ...]:
    raw = str(chunk or "").strip()
    chunks: List[str] = []
    open_to_close = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    closers = set(open_to_close.values())
    index = 0
    while index < len(raw):
        while index < len(raw) and raw[index].isspace():
            index += 1
        if index >= len(raw):
            break
        if raw[index] in open_to_close:
            start = index
            stack = [open_to_close[raw[index]]]
            index += 1
            while index < len(raw) and stack:
                skip_to = _lean_lexical_skip_end(raw, index)
                if skip_to is not None:
                    index = skip_to
                    continue
                ch = raw[index]
                if ch in open_to_close:
                    stack.append(open_to_close[ch])
                elif ch in closers and ch == stack[-1]:
                    stack.pop()
                index += 1
            group = raw[start:index].strip()
            if group:
                chunks.append(group)
            continue
        start = index
        while index < len(raw):
            skip_to = _lean_lexical_skip_end(raw, index)
            if skip_to is not None:
                index = skip_to
                continue
            if raw[index] in open_to_close:
                prefix = raw[start:index]
                if (
                    _graph_relation_binder_prefix_expects_group_rhs(prefix)
                    or _graph_typed_binder_prefix_expects_group_rhs(prefix)
                ):
                    end = _graph_matching_group_index(raw, index)
                    if end >= 0:
                        index = end + 1
                        continue
                break
            index += 1
        group = raw[start:index].strip()
        if group:
            chunks.append(group)
    return tuple(chunks) if chunks else ((raw,) if raw else ())


def _graph_leading_telescope_step(
    statement_body: str,
) -> Tuple[Tuple[str, ...], str] | None:
    """Return one leading Lean telescope step and its remaining body.

    Lean's dependent function (Pi) surface has two equivalent leading forms:
    ``forall/∀ ... , body`` and ``(x : α) → body``.  The latter must contain a
    typed binder group; an ordinary parenthesized implication premise such as
    ``(P) → Q`` is deliberately not reclassified as a declaration.  Keeping
    both forms in this shared parser prevents downstream contract consumers
    from maintaining incomplete, policy-specific binder recognizers.
    """

    body = str(statement_body or "").strip()
    quantifier_match = re.match(r"^(?:∀|forall\b)\s*", body)
    if quantifier_match is not None:
        comma = _graph_find_top_level_comma(body)
        if comma < 0:
            return None
        binder_chunk = body[quantifier_match.end() : comma]
        groups = _graph_binder_group_chunks(binder_chunk)
        if not groups:
            return None
        return groups, body[comma + 1 :]

    # These are Lean's binder delimiters.  Do not accept every balanced term
    # delimiter here (notably ``⟨...⟩``), because that would turn malformed or
    # ordinary expression syntax into a local declaration.
    if not body or body[0] not in "({[⦃":
        return None
    group_end = _graph_matching_group_index(body, 0)
    if group_end < 0:
        return None
    raw_group = body[: group_end + 1]
    unwrapped = _graph_unwrap_binder_group(raw_group)
    annotation = _graph_typed_binder_annotation_index(unwrapped)
    anonymous_instance = body[0] == "[" and bool(unwrapped)
    if annotation < 0 and not anonymous_instance:
        return None
    if annotation >= 0 and not _graph_is_binder_name_surface(
        unwrapped[:annotation]
    ):
        return None
    suffix = body[group_end + 1 :].lstrip()
    arrow_match = re.match(r"^(?:→|->)\s*", suffix)
    if arrow_match is None:
        return None
    return (raw_group,), suffix[arrow_match.end() :]


def _graph_explicit_binder_group_arity(chunk: str) -> int:
    raw = str(chunk or "").strip()
    if not raw or raw[0] in "{[⦃":
        return 0
    body = _graph_unwrap_binder_group(raw)
    colon = _graph_top_level_colon_index(body)
    relation = _graph_top_level_binder_separator_index(
        body,
        _GRAPH_RELATION_BINDER_TOKENS,
    )
    split_points = [idx for idx in (colon, relation) if idx >= 0]
    names_part = body[: min(split_points)] if split_points else body
    names = [
        name
        for name in _graph_lean_identifier_tokens(names_part)
        if name.lower() not in {"forall", "exists", "fun", "by", "let", "in"}
    ]
    return max(1, len(names))


def _graph_type_returns_prop(type_text: str) -> bool:
    """Whether a local declaration structurally returns a proposition."""

    clean = _graph_strip_balanced_outer_parens(str(type_text or "").strip())
    if not clean:
        return False

    def is_prop_sort(text: str) -> bool:
        compact = " ".join(_graph_strip_balanced_outer_parens(text).split())
        return compact == "Prop" or bool(
            re.fullmatch(r"Sort\s+(?:0|\(0\))", compact)
        )

    parts = _graph_split_top_level_implications(clean)
    if len(parts) >= 2:
        return is_prop_sort(parts[-1])
    body = clean
    while True:
        match = re.match(r"^(?:∀|forall\b)\s*", body)
        if match is None:
            break
        comma = _graph_find_top_level_comma(body)
        if comma < 0:
            break
        body = _graph_strip_balanced_outer_parens(body[comma + 1 :])
    return is_prop_sort(body)


def _graph_type_returns_type(type_text: str) -> bool:
    """Whether a local declaration structurally returns a data sort."""

    clean = _graph_strip_balanced_outer_parens(str(type_text or "").strip())
    if not clean:
        return False
    parts = _graph_split_top_level_implications(clean)
    body = parts[-1] if len(parts) >= 2 else clean
    while True:
        match = re.match(r"^(?:∀|forall\b)\s*", body)
        if match is None:
            break
        comma = _graph_find_top_level_comma(body)
        if comma < 0:
            break
        body = _graph_strip_balanced_outer_parens(body[comma + 1 :])
    compact = " ".join(_graph_strip_balanced_outer_parens(body).split())
    return bool(
        re.fullmatch(
            r"Type(?:\s*(?:\*|[^\s()]+|\([^)]*\)))?",
            compact,
        )
        or (
            re.fullmatch(r"Sort\s+(?:[1-9]\d*|\([^)]*[1-9][^)]*\))", compact)
            and not re.fullmatch(r"Sort\s+(?:0|\(0\))", compact)
        )
    )


def _graph_type_leading_identifier(type_text: str) -> Tuple[str, bool]:
    """Return a Lean identifier head and whether it is being applied."""

    clean = _graph_strip_balanced_outer_parens(str(type_text or "").strip())
    while clean.startswith("@"):
        clean = clean[1:].lstrip()
    if clean.startswith("("):
        end = _graph_matching_group_index(clean, 0)
        if end >= 0:
            inner = _graph_strip_balanced_outer_parens(clean[: end + 1])
            while inner.startswith("@"):
                inner = inner[1:].lstrip()
            head = _graph_leading_identifier(inner)
            if head and not inner[len(head) :].strip():
                return head, bool(clean[end + 1 :].strip())
    head = _graph_leading_identifier(clean)
    if not head:
        return "", False
    return head, bool(clean[len(head) :].strip())


def _graph_type_uses_local_constructor(
    type_text: str,
    constructors: Iterable[str],
) -> bool:
    """Whether a binder type uses a locally declared sort-valued symbol."""

    head, _applied = _graph_type_leading_identifier(type_text)
    return bool(head and head in {str(name or "").strip() for name in constructors})


def _graph_applied_leading_identifier(type_text: str) -> str:
    """Return the qualified/escaped head when ``type_text`` is an application."""

    head, applied = _graph_type_leading_identifier(type_text)
    return head if applied else ""


def _graph_binder_type_sort_hint(
    type_text: str,
    *,
    binder_names: Sequence[str] = (),
    local_prop_constructors: Iterable[str] = (),
    local_type_constructors: Iterable[str] = (),
) -> str:
    """Classify the sort inhabited by a binder type.

    Returns ``prop``, ``type``, or ``ambiguous``.  Arrow/Pi types are
    classified from their codomain, which prevents function-valued data from
    being mistaken for implication merely because the binder name starts with
    ``h``.
    """

    clean = _graph_strip_balanced_outer_parens(str(type_text or "").strip())
    if not clean:
        return "ambiguous"
    parts = _graph_split_top_level_implications(clean)
    if len(parts) >= 2:
        return _graph_binder_type_sort_hint(
            parts[-1],
            binder_names=binder_names,
            local_prop_constructors=local_prop_constructors,
            local_type_constructors=local_type_constructors,
        )
    body = clean
    while True:
        match = re.match(r"^(?:∀|forall\b)\s*", body)
        if match is None:
            break
        comma = _graph_find_top_level_comma(body)
        if comma < 0:
            return "ambiguous"
        body = _graph_strip_balanced_outer_parens(body[comma + 1 :])
    if body != clean:
        return _graph_binder_type_sort_hint(
            body,
            binder_names=binder_names,
            local_prop_constructors=local_prop_constructors,
            local_type_constructors=local_type_constructors,
        )
    if graph_identity_text(body) in {"True", "False"}:
        return "prop"
    if _graph_type_uses_local_constructor(body, local_prop_constructors):
        return "prop"
    if _graph_type_uses_local_constructor(body, local_type_constructors):
        return "type"
    if _graph_type_returns_prop(body) or _graph_type_returns_type(body):
        # ``p : Prop`` and ``α : Type`` declare objects in a sort; they are
        # not proofs of the sort expression itself.
        return "type"
    head, applied = _graph_type_leading_identifier(body)
    if head and _graph_head_looks_like_non_prop_class(head):
        return "type"
    if _graph_looks_like_parameter_type_part(body):
        return "type"
    if _graph_looks_like_proof_premise_type(body, ()):
        return "prop"
    if applied:
        return "ambiguous"
    if _graph_looks_like_proof_premise_type(body, binder_names):
        return "prop"
    return "ambiguous"


def _graph_binder_type_needs_ambiguity_signal(type_text: str) -> bool:
    """Whether an unresolved binder type must fail closed.

    Sort classification runs before this predicate and already accepts local
    Type constructors, known concrete data atoms, classes, and structural data
    constructors.  Anything still unresolved could be a bare global Prop just
    as easily as an unknown data type, so bridge/planner admission must not
    silently choose the data interpretation.
    """

    clean = _graph_strip_balanced_outer_parens(str(type_text or "").strip())
    if len(_graph_split_top_level_implications(clean)) >= 2:
        return True
    body = clean
    while True:
        match = re.match(r"^(?:∀|forall\b)\s*", body)
        if match is None:
            break
        comma = _graph_find_top_level_comma(body)
        if comma < 0:
            return bool(clean)
        body = _graph_strip_balanced_outer_parens(body[comma + 1 :])
    return bool(body)


def _graph_binder_group_is_proof_premise(
    chunk: str,
    *,
    local_prop_constructors: Iterable[str] = (),
    local_type_constructors: Iterable[str] = (),
) -> bool:
    raw = str(chunk or "").strip()
    if not raw:
        return False
    body = _graph_unwrap_binder_group(raw)
    colon = _graph_top_level_colon_index(body)
    if colon < 0:
        return bool(lean_relation_binder_premise(body))
    names = _graph_binder_names_from_chunk(body[:colon])
    type_text = _graph_binder_type_without_default(body[colon + 1 :])
    if _graph_type_returns_prop(type_text) or _graph_type_returns_type(type_text):
        # ``p : Prop`` and ``good : α → Prop`` declare proposition objects or
        # sort-valued constructors; they are not proofs.  Later applications
        # are classified from the registered result sort.
        return False
    return (
        _graph_binder_type_sort_hint(
            type_text,
            binder_names=names,
            local_prop_constructors=local_prop_constructors,
            local_type_constructors=local_type_constructors,
        )
        == "prop"
    )


def _graph_leading_binder_analysis(
    statement: str,
) -> Tuple[str, Tuple[Tuple[str, Tuple[str, ...], str, bool, bool], ...]]:
    """Parse leading binders with local dependent-Prop propagation.

    Each record is ``(source_group, names, type_text, is_proof, ambiguous)``.  A local
    declaration such as ``good : Nat → Prop`` registers ``good`` as a
    proposition constructor, so a later ``w : good n`` is recognized without
    relying on the spelling of ``w``.  A final conclusion comparison catches
    own-conclusion premises even when their type comes from an external symbol.
    """

    body = _graph_strip_balanced_outer_parens(graph_formal_statement_text(statement))
    records: List[Tuple[str, Tuple[str, ...], str, bool, bool]] = []
    local_prop_constructors: Set[str] = set()
    local_type_constructors: Set[str] = set()
    bound_names: List[str] = []
    while True:
        telescope_step = _graph_leading_telescope_step(body)
        if telescope_step is None:
            break
        binder_groups, remaining_body = telescope_step
        for group in binder_groups:
            raw = str(group or "").strip()
            unwrapped = _graph_unwrap_binder_group(raw)
            colon = _graph_top_level_colon_index(unwrapped)
            names: Tuple[str, ...] = ()
            type_text = ""
            is_proof = False
            ambiguous = False
            if colon < 0:
                relation_premise = str(
                    lean_relation_binder_premise(unwrapped) or ""
                ).strip()
                anonymous_instance = bool(
                    raw.startswith("[") and raw.endswith("]")
                )
                if anonymous_instance:
                    names = ()
                    type_text = unwrapped
                    sort_hint = _graph_binder_type_sort_hint(
                        type_text,
                        local_prop_constructors=local_prop_constructors,
                        local_type_constructors=local_type_constructors,
                    )
                    is_proof = sort_hint == "prop"
                    ambiguous = bool(
                        sort_hint == "ambiguous"
                        and _graph_binder_type_needs_ambiguity_signal(type_text)
                    )
                elif relation_premise:
                    names = (
                        lean_relation_binder_bound_names(unwrapped)
                        or _graph_binder_names_from_chunk(unwrapped)
                    )
                    type_text = relation_premise
                    is_proof = True
                else:
                    parsed_names = _graph_binder_names_from_chunk(unwrapped)
                    tokens = unwrapped.split()
                    ordinary_untyped_names = bool(
                        tokens
                        and len(parsed_names) == len(tokens)
                        and all(token not in {"True", "False"} for token in tokens)
                    )
                    names = parsed_names if ordinary_untyped_names else parsed_names[:1]
                    # Lean's binderPred syntax is extensible. Unknown
                    # multi-token binder chunks cannot be assumed to be data:
                    # they may elaborate to a hidden proposition premise.
                    if len(tokens) > 1 and not ordinary_untyped_names:
                        type_text = unwrapped
                        ambiguous = True
            else:
                names = _graph_binder_names_from_chunk(unwrapped[:colon])
                type_text = _graph_binder_type_without_default(
                    unwrapped[colon + 1 :]
                )
                is_proof = _graph_binder_group_is_proof_premise(
                    raw,
                    local_prop_constructors=local_prop_constructors,
                    local_type_constructors=local_type_constructors,
                )
                sort_hint = _graph_binder_type_sort_hint(
                        type_text,
                        binder_names=names,
                        local_prop_constructors=local_prop_constructors,
                        local_type_constructors=local_type_constructors,
                    )
                ambiguous = bool(
                    sort_hint == "ambiguous"
                    and _graph_binder_type_needs_ambiguity_signal(type_text)
                )
            records.append((raw, names, type_text, is_proof, ambiguous))
            if not is_proof and _graph_type_returns_prop(type_text):
                local_prop_constructors.update(names)
                ambiguous = False
                records[-1] = (raw, names, type_text, is_proof, ambiguous)
            elif not is_proof and _graph_type_returns_type(type_text):
                local_type_constructors.update(names)
                ambiguous = False
                records[-1] = (raw, names, type_text, is_proof, ambiguous)
            bound_names.extend(names)
        body = _graph_strip_balanced_outer_parens(remaining_body)

    implication_parts = _graph_split_top_level_implications(body)
    conclusion = implication_parts[-1] if implication_parts else body
    conclusion_key = _graph_contract_alpha_norm(
        conclusion,
        context_bound_names=tuple(dict.fromkeys(bound_names)),
    )
    if conclusion_key:
        records = [
            (
                raw,
                names,
                type_text,
                bool(
                    is_proof
                    or (
                        type_text
                        and _graph_contract_alpha_norm(
                            type_text,
                            context_bound_names=tuple(dict.fromkeys(bound_names)),
                        )
                        == conclusion_key
                    )
                ),
                ambiguous,
            )
            for raw, names, type_text, is_proof, ambiguous in records
        ]
    return body, tuple(records)


def _graph_forall_explicit_arity(
    statement: str,
    *,
    exclude_proof_binders: bool = False,
) -> int:
    _body, binder_records = _graph_leading_binder_analysis(statement)
    count = 0
    for raw, _names, type_text, is_proof, _ambiguous in binder_records:
        data_arity = _graph_explicit_binder_group_arity(raw)
        relation_binder = bool(
            is_proof
            and type_text
            and _graph_top_level_colon_index(_graph_unwrap_binder_group(raw)) < 0
        )
        if relation_binder:
            count += data_arity
            if not exclude_proof_binders:
                count += 1
        elif not (exclude_proof_binders and is_proof):
            count += data_arity
    return count


def _graph_root_forall_support_arguments(
    statement: str,
) -> List[Tuple[str, Tuple[str, ...], int]]:
    _body, binder_records = _graph_leading_binder_analysis(statement)
    supports: List[Tuple[str, Tuple[str, ...], int]] = []
    bound_names: List[str] = []
    explicit_index = 0
    for raw, names, type_text, is_proof, _ambiguous in binder_records:
        data_arity = _graph_explicit_binder_group_arity(raw)
        relation_binder = bool(
            is_proof
            and type_text
            and _graph_top_level_colon_index(_graph_unwrap_binder_group(raw)) < 0
        )
        context_names = tuple(dict.fromkeys([*bound_names, *names]))
        if relation_binder:
            supports.append(
                (type_text, context_names, explicit_index + data_arity + 1)
            )
        elif is_proof and type_text and data_arity > 0:
            for offset in range(data_arity):
                supports.append(
                    (type_text, context_names, explicit_index + offset + 1)
                )
        bound_names.extend(names)
        explicit_index += data_arity + int(relation_binder)
    return supports


def _graph_looks_like_proof_premise_type(
    type_text: str,
    binder_names: Sequence[str],
) -> bool:
    clean = _graph_strip_balanced_outer_parens(str(type_text or "").strip())
    if not clean:
        return False
    # A subtype/set-builder is a data type. Proposition syntax inside its
    # predicate (including nested quantifiers) must not turn the enclosing
    # value binder into a proof-valued binder.
    if clean.startswith("{") and clean.endswith("}"):
        subtype_body = clean[1:-1].strip()
        if _graph_top_level_binder_separator_index(
            subtype_body,
            ("//", "|"),
        ) >= 0:
            return False
    compact = " ".join(clean.split()).strip("{}[]")
    lowered = compact.lower()
    def proof_like_binder_name(name: str) -> bool:
        clean_name = str(name or "").strip().lower()
        if clean_name == "_":
            return True
        name_key = clean_name.lstrip("_")
        return bool(name_key) and name_key.startswith(
            (
                "h",
                "hyp",
                "this",
                "proof",
                "assump",
                "premise",
                "cond",
                "given",
            )
        )

    hyp_like_name = any(
        proof_like_binder_name(name) for name in binder_names
    )
    if lowered in {
        "nat",
        "ℕ",
        "int",
        "ℤ",
        "rat",
        "ℚ",
        "real",
        "ℝ",
        "bool",
        "prop",
        "type",
    }:
        return False
    if re.fullmatch(r"(?:Type|Sort|Prop)(?:\s+\d+|\s+u)?", compact):
        return False
    if re.match(
        r"^(?:Set|Finset|List|Multiset|Option|Array|Seq|Fin|ZMod|Polynomial|"
        r"Matrix|Vector|Subtype|ULift|PLift|WithTop|WithBot|OrderDual|"
        r"Additive|Multiplicative|Ideal|Submodule|Subgroup|Subsemiring|"
        r"Subring|Subfield|Equiv|LinearEquiv|RingEquiv|OrderIso|Type|Sort)\b",
        compact,
    ):
        return False
    if re.match(
        r"^(?:Fintype|Finite|DecidableEq|Inhabited|Subsingleton|Unique|"
        r"Group|CommGroup|AddGroup|AddCommGroup|Monoid|CommMonoid|"
        r"AddMonoid|AddCommMonoid|Semigroup|CommSemigroup|Ring|CommRing|"
        r"Semiring|CommSemiring|Field|DivisionRing|LinearOrder|PartialOrder|"
        r"Preorder|Lattice|DistribLattice|LinearOrderedRing|"
        r"LinearOrderedField|OrderedRing|OrderedSemiring|TopologicalSpace|"
        r"MetricSpace|NormedRing|NormedField|NormedSpace|Module|Algebra)\b",
        compact,
    ):
        return False
    if "→" in compact or "->" in compact:
        arrow_parts = _graph_split_top_level_implications(compact)
        codomain = arrow_parts[-1] if arrow_parts else compact
        codomain = _graph_strip_balanced_outer_parens(codomain).strip()
        codomain_lower = codomain.lower()
        type_like_arrow = len(arrow_parts) >= 2 and all(
            _graph_looks_like_parameter_type_part(part) for part in arrow_parts
        )
        if (
            type_like_arrow
            or codomain_lower in {"prop", "type", "sort"}
            or codomain_lower in {"nat", "int", "rat", "real", "bool"}
            or codomain in {"ℕ", "ℤ", "ℚ", "ℝ", "Nat", "Int", "Rat", "Real", "Bool"}
            or re.match(
                r"^(?:Set|Finset|List|Multiset|Option|Array|Seq|Fin|ZMod|"
                r"Polynomial|MvPolynomial|Matrix|Vector|Subtype|ULift|PLift|WithTop|WithBot|"
                r"OrderDual|Additive|Multiplicative|Ideal|Submodule|Subgroup|"
                r"Subsemiring|Subring|Subfield|Equiv|LinearEquiv|RingEquiv|"
                r"OrderIso)\b",
                codomain,
            )
            or re.fullmatch(r"(?:Type|Sort|Prop)(?:\s+\d+|\s+u)?", codomain)
            or (
                not hyp_like_name
                and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", codomain)
            )
        ):
            return False
    if any(symbol in compact for symbol in ("=", "<", ">", "≤", "≥", "≠", "∈", "∉", "∣")):
        return True
    if any(symbol in compact for symbol in ("→", "->", "↔", "¬", "∧", "∨", "∀", "∃")):
        return True
    if re.search(
        r"\b(?:Odd|Even|Prime|Nat\.Prime|Irreducible|Nonempty|Pairwise|"
        r"Monotone|StrictMono|Injective|Surjective|Bijective|Continuous)\b",
        compact,
    ):
        return True
    if re.fullmatch(r"[A-Z](?:\s+.+)?", compact):
        return True
    if hyp_like_name and re.fullmatch(
        r"[A-Za-z_][A-Za-z0-9_'.]*(?:\s+.+)+",
        compact,
    ):
        return True
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", compact):
        return hyp_like_name
    return False


def _graph_looks_like_parameter_type_part(text: str) -> bool:
    compact = _graph_strip_balanced_outer_parens(
        " ".join(str(text or "").split()).strip("{}[]")
    )
    lowered = compact.lower()
    if lowered in {"nat", "int", "rat", "real", "bool", "prop", "type", "sort"}:
        return True
    if compact in _GRAPH_KNOWN_DATA_ATOM_TYPES:
        return True
    if re.fullmatch(r"(?:Type|Sort|Prop)(?:\s+\d+|\s+u)?", compact):
        return True
    return bool(
        re.match(
            r"^(?:Set|Finset|List|Multiset|Option|Array|Seq|Fin|ZMod|"
            r"Polynomial|MvPolynomial|Matrix|Vector|Subtype|ULift|PLift|WithTop|WithBot|"
            r"OrderDual|Additive|Multiplicative|Ideal|Submodule|Subgroup|"
            r"Subsemiring|Subring|Subfield|Equiv|LinearEquiv|RingEquiv|"
            r"OrderIso)\b",
            compact,
        )
    )


def _graph_statement_premises_and_conclusion(
    statement: str,
) -> Tuple[Tuple[str, ...], str, Tuple[str, ...]]:
    body, binder_records = _graph_leading_binder_analysis(statement)
    binder_premises = [
        type_text
        for _raw, _names, type_text, is_proof, _ambiguous in binder_records
        if is_proof and type_text
    ]
    bound_names = [
        name
        for _raw, names, _type_text, _is_proof, _ambiguous in binder_records
        for name in names
    ]
    parts = _graph_split_top_level_implications(body)
    if len(parts) < 2:
        return tuple(binder_premises), body, tuple(dict.fromkeys(bound_names))
    return (
        tuple([*binder_premises, *parts[:-1]]),
        parts[-1],
        tuple(dict.fromkeys(bound_names)),
    )


def _graph_statement_root_adjacent(
    conclusion: str,
    root_statement: str,
    *,
    conclusion_bound_names: Sequence[str] = (),
) -> bool:
    conclusion_norm = _graph_contract_alpha_norm(
        conclusion,
        context_bound_names=conclusion_bound_names,
    )
    if not conclusion_norm:
        return False
    for candidate, root_bound_names in _graph_root_conclusion_candidates(root_statement):
        root_norm = _graph_contract_alpha_norm(
            candidate,
            context_bound_names=root_bound_names,
        )
        if root_norm and conclusion_norm == root_norm:
            return True
    return False


def _graph_contract_profile(statement: str) -> Tuple[Tuple[str, ...], str]:
    premises, conclusion, bound_names = _graph_statement_premises_and_conclusion(
        graph_formal_statement_text(statement)
    )
    premise_keys: List[str] = []
    for premise in premises:
        premise_text, premise_names = _graph_strip_leading_forall_binders_with_names(
            premise
        )
        key = _graph_contract_alpha_norm(
            premise_text,
            context_bound_names=tuple(dict.fromkeys(bound_names + premise_names)),
        )
        if key:
            premise_keys.append(key)
    conclusion_key = _graph_contract_alpha_norm(
        conclusion,
        context_bound_names=bound_names,
    )
    return tuple(sorted(dict.fromkeys(premise_keys))), conclusion_key


def graph_statement_contract_profile(statement: str) -> Tuple[Tuple[str, ...], str]:
    """Return alpha-normalized proof-premise and conclusion identities.

    Unlike text splitting, this recognizes proof-valued ``forall`` binders and
    respects nesting inside quantified propositions.  The public wrapper keeps
    bridge admission, graph scheduling, and theory auditing on one contract
    identity instead of maintaining subtly different parsers.
    """

    return _graph_contract_profile(statement)


def graph_statement_premises_and_conclusion(
    statement: str,
) -> Tuple[Tuple[str, ...], str, Tuple[str, ...]]:
    """Return the shared proof-premise, conclusion, and binder-name contract."""

    return _graph_statement_premises_and_conclusion(statement)


def graph_statement_leading_contract(
    statement: str,
) -> Tuple[str, Tuple[str, ...], Tuple[str, ...]]:
    """Strip the leading Pi telescope using the shared proof classifier.

    The result is ``(body, bound_names, binder_premises)``.  Relation
    shorthand contributes both its bound data name and its proof premise.
    Both ``forall/∀`` binders and grouped dependent-arrow binders are handled.
    """

    body, binder_records = _graph_leading_binder_analysis(statement)
    bound_names = tuple(
        dict.fromkeys(
            name
            for _raw, names, _type_text, _is_proof, _ambiguous in binder_records
            for name in names
        )
    )
    binder_premises = tuple(
        dict.fromkeys(
            type_text
            for _raw, _names, type_text, is_proof, _ambiguous in binder_records
            if is_proof and type_text
        )
    )
    return body, bound_names, binder_premises


def graph_statement_forall_application_entries(
    statement: str,
) -> Tuple[Tuple[int, bool], ...]:
    """Return explicit forall-group arities and shared proof classifications."""

    _body, binder_records = _graph_leading_binder_analysis(statement)
    entries: List[Tuple[int, bool]] = []
    for raw, _names, type_text, is_proof, _ambiguous in binder_records:
        data_arity = _graph_explicit_binder_group_arity(raw)
        relation_binder = bool(
            is_proof
            and type_text
            and _graph_top_level_colon_index(_graph_unwrap_binder_group(raw)) < 0
        )
        if data_arity > 0:
            entries.append((data_arity, False if relation_binder else is_proof))
        if relation_binder:
            entries.append((1, True))
    return tuple(entries)


def graph_statement_explicit_arity(
    statement: str,
    *,
    exclude_proof_binders: bool = False,
) -> int:
    """Return explicit forall arity under the shared binder classifier."""

    return _graph_forall_explicit_arity(
        statement,
        exclude_proof_binders=exclude_proof_binders,
    )


def graph_statement_contract_ambiguities(statement: str) -> Tuple[str, ...]:
    """Return unresolved application-shaped leading binder types.

    A statement-only parser cannot decide whether an external lowercase head
    such as ``foo`` in ``w : foo n`` is a Prop-valued predicate or a Type-valued
    family.  Bridge admission must therefore fail closed instead of either
    manufacturing a proof obligation from possible data or overlooking a
    possible proof premise.  Lean may still verify and bank the helper itself.
    """

    _body, binder_records = _graph_leading_binder_analysis(statement)
    ambiguities: List[str] = []
    for _raw, _names, type_text, _is_proof, ambiguous in binder_records:
        normalized = _graph_strip_balanced_outer_parens(type_text)
        if ambiguous and normalized and normalized not in ambiguities:
            ambiguities.append(normalized)
    return tuple(ambiguities)


def graph_statement_has_circular_premise(statement: str) -> bool:
    """Return whether a theorem assumes its own conclusion.

    Lean-valid ``(h : P) : P`` wrappers are certificates of an implication,
    not progress toward proving ``P``.  Detect them modulo binder placement and
    alpha-renaming so nested quantified targets cannot evade the guard.
    """

    formal_statement = graph_formal_statement_text(statement)
    def closed_telescope_key(closed_statement: str) -> str:
        body, records = _graph_leading_binder_analysis(closed_statement)
        if not records:
            return graph_statement_key(closed_statement)
        rendered_groups: List[str] = []
        for raw, names, type_text, _is_proof, _ambiguous in records:
            if not names or _graph_binder_record_is_relation(
                (raw, names, type_text, _is_proof, _ambiguous)
            ):
                return graph_statement_key(closed_statement)
            compact_raw = str(raw or "").strip()
            opener = compact_raw[:1] if compact_raw[:1] in "({[" else "("
            closer = {"(": ")", "{": "}", "[": "]"}[opener]
            for name in names:
                inner = (
                    f"{name} : {type_text}"
                    if str(type_text or "").strip()
                    else name
                )
                rendered_groups.append(f"{opener}{inner}{closer}")
        rendered = (
            f"∀ {' '.join(rendered_groups)}, {body}"
            if rendered_groups
            else body
        )
        return graph_statement_key(rendered)

    # Close each side over its own data telescope, then split grouped binders
    # into ordered single-binder records.  This equates ``∀ a b : Nat`` with
    # ``∀ a : Nat, ∀ b : Nat`` while preserving binder domains, visibility,
    # arity, and shadowing.
    closed_conclusion = graph_statement_closed_conclusion(formal_statement)
    closed_conclusion_key = closed_telescope_key(closed_conclusion)
    if closed_conclusion_key and any(
        closed_telescope_key(premise) == closed_conclusion_key
        for premise in graph_statement_closed_premises(formal_statement)
    ):
        return True

    def pattern_lambda_rejection_key(closed_statement: str) -> str:
        key = closed_telescope_key(closed_statement)
        branch_pattern = re.compile(
            r"(?P<prefix>(?:fun\s*)?\|\s*)"
            r"(?P<pattern>[^|=]*?)"
            r"(?P<arrow>\s*=>\s*)"
            r"(?P<body>.*?)"
            r"(?=(?:\s*\|\s*[^|=]*=>)|$)"
        )
        branch_index = 0
        nullary_constructors = {
            "none", "nil", "true", "false", "unit", "zero",
        }

        def normalize_branch(match: re.Match[str]) -> str:
            nonlocal branch_index
            pattern = match.group("pattern")
            body = match.group("body")
            identifiers = re.findall(r"[A-Za-z_][A-Za-z0-9_']*", pattern)
            bound_names: List[str] = []
            if len(identifiers) == 1:
                candidate = identifiers[0]
                if candidate.lower() not in nullary_constructors:
                    bound_names.append(candidate)
            elif identifiers:
                # In a constructor application the head is the constructor;
                # tuple/record patterns have punctuation before the first
                # identifier, so every identifier binds.
                stripped = pattern.lstrip()
                constructor_head = re.match(
                    r"(?:_root_\.)?[A-Za-z_][A-Za-z0-9_']*"
                    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*\s+",
                    stripped,
                )
                if constructor_head:
                    head_identifier_count = len(
                        re.findall(
                            r"[A-Za-z_][A-Za-z0-9_']*",
                            constructor_head.group(0),
                        )
                    )
                    bound_names.extend(identifiers[head_identifier_count:])
                else:
                    bound_names.extend(identifiers)
            normalized_pattern = pattern
            normalized_body = body
            for name in bound_names:
                normalized_name = f"__pattern_b{branch_index}"
                branch_index += 1
                token = rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])"
                normalized_pattern = re.sub(token, normalized_name, normalized_pattern)
                normalized_body = re.sub(token, normalized_name, normalized_body)
            return (
                match.group("prefix")
                + normalized_pattern
                + match.group("arrow")
                + normalized_body
            )

        return branch_pattern.sub(normalize_branch, key)

    if closed_conclusion_key and any(
        pattern_lambda_rejection_key(premise)
        == pattern_lambda_rejection_key(closed_conclusion)
        for premise in graph_statement_closed_premises(formal_statement)
    ):
        return True

    def inferred_telescope_rejection_key(
        closed_statement: str,
    ) -> Tuple[str, bool]:
        body, records = _graph_leading_binder_analysis(closed_statement)
        if not records:
            return graph_statement_key(closed_statement), False
        rendered: List[str] = []
        missing_type = False
        for raw, names, type_text, is_proof, ambiguous in records:
            if not names or _graph_binder_record_is_relation(
                (raw, names, type_text, is_proof, ambiguous)
            ):
                return graph_statement_key(closed_statement), False
            missing_type = missing_type or not bool(str(type_text or "").strip())
            compact_raw = str(raw or "").strip()
            opener = compact_raw[:1] if compact_raw[:1] in "({[" else "("
            closer = {"(": ")", "{": "}", "[": "]"}[opener]
            rendered.extend(f"{opener}{name}{closer}" for name in names)
        statement_without_domains = f"∀ {' '.join(rendered)}, {body}"
        return graph_statement_key(statement_without_domains), missing_type

    conclusion_inferred_key, conclusion_has_missing_type = (
        inferred_telescope_rejection_key(closed_conclusion)
    )
    for premise in graph_statement_closed_premises(formal_statement):
        premise_inferred_key, premise_has_missing_type = (
            inferred_telescope_rejection_key(premise)
        )
        if (
            (conclusion_has_missing_type or premise_has_missing_type)
            and conclusion_inferred_key
            and premise_inferred_key == conclusion_inferred_key
        ):
            return True

    premises, conclusion, _bound_names = _graph_statement_premises_and_conclusion(
        formal_statement
    )
    return any(
        lean_relation_binder_equivalent(premise, conclusion)
        for premise in premises
    )


def _graph_binder_record_is_relation(
    record: Tuple[str, Tuple[str, ...], str, bool, bool],
) -> bool:
    raw, _names, type_text, is_proof, _ambiguous = record
    return bool(
        is_proof
        and type_text
        and _graph_top_level_colon_index(_graph_unwrap_binder_group(raw)) < 0
    )


def _graph_projection_render_binder_group(raw_group: str) -> str:
    """Render one projected binder group as composable Lean syntax.

    Lean accepts ``∀ i j : α, P`` when that is the quantifier's complete
    binder telescope.  It does not accept the same ungrouped typed fragment
    after another binder, as in ``∀ (A : T) i j : α, P``.  Projection
    combines groups originating in separate quantifiers, so typed groups must
    retain an explicit delimiter at that boundary.
    """

    raw = str(raw_group or "").strip()
    if not raw:
        return ""
    closer = _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.get(raw[0])
    if closer and _graph_matching_group_index(raw, 0) == len(raw) - 1:
        return raw
    if _graph_top_level_colon_index(raw) >= 0:
        return f"({raw})"
    return raw


def _graph_projection_binder_groups(
    binder_records: Sequence[Tuple[str, Tuple[str, ...], str, bool, bool]],
    *,
    cutoff: int,
    target_text: str,
    current_relation_names: Sequence[str] = (),
) -> Tuple[str, ...]:
    """Close a projection while retaining proof terms needed by dependencies."""

    limit = max(0, min(int(cutoff), len(binder_records)))
    selected_proof_indexes: Set[int] = set()
    required_names = set(_graph_lean_identifier_tokens(target_text))
    for index, record in enumerate(binder_records[:limit]):
        raw, _names, type_text, is_proof, _ambiguous = record
        if not is_proof:
            required_names.update(_graph_lean_identifier_tokens(type_text or raw))
        elif _graph_binder_record_is_relation(record):
            # Relation shorthand binds data names plus an anonymous proof.  Its
            # data names remain in scope, but no later type can name the proof.
            continue
    changed = True
    while changed:
        changed = False
        for index, record in enumerate(binder_records[:limit]):
            raw, names, type_text, is_proof, _ambiguous = record
            if (
                index in selected_proof_indexes
                or not is_proof
                or _graph_binder_record_is_relation(record)
                or not set(names).intersection(required_names)
            ):
                continue
            selected_proof_indexes.add(index)
            required_names.update(_graph_lean_identifier_tokens(type_text or raw))
            changed = True
    groups: List[str] = []
    for index, record in enumerate(binder_records[:limit]):
        raw, names, _type_text, is_proof, _ambiguous = record
        if _graph_binder_record_is_relation(record):
            if names:
                groups.append(" ".join(names))
        elif not is_proof or index in selected_proof_indexes:
            if raw:
                groups.append(_graph_projection_render_binder_group(raw))
    if current_relation_names:
        groups.append(" ".join(current_relation_names))
    return tuple(group for group in groups if str(group or "").strip())


def graph_statement_parent_existential_payload_premise(
    statement: str,
    parent_statement: str,
) -> str:
    """Return a helper premise that assumes an existential parent's payload.

    For a parent ``∃ x : T, P x``, a helper of shape
    ``∀ (x : T) (h : P x), Q x`` is Lean-valid but makes no progress toward
    constructing the existential: its closed premise is ``∀ x : T, P x``.
    Compare that payload structurally, including alpha-renaming and complete
    leading existential telescopes, rather than relying on binder names.
    """

    parent_surface = _graph_strip_balanced_outer_parens(
        graph_formal_statement_text(parent_statement)
    )
    _parent_body, parent_binder_records = _graph_leading_binder_analysis(
        parent_surface
    )
    _parent_premises, parent_conclusion, _parent_bound_names = (
        _graph_statement_premises_and_conclusion(parent_surface)
    )
    parent_body = _graph_strip_balanced_outer_parens(parent_conclusion)
    existential_groups: List[str] = list(
        _graph_projection_binder_groups(
            parent_binder_records,
            cutoff=len(parent_binder_records),
            target_text=parent_body,
        )
    )
    existential_witness_count = 0
    while True:
        quantifier_match = re.match(r"^(?:∃|exists\b)\s*", parent_body)
        if quantifier_match is None:
            break
        comma = _graph_find_top_level_comma(parent_body)
        if comma < 0:
            return ""
        binder_chunk = parent_body[quantifier_match.end() : comma]
        groups = _graph_binder_group_chunks(binder_chunk)
        if not groups:
            return ""
        rendered_groups = tuple(
            _graph_projection_render_binder_group(group) for group in groups
        )
        if any(not group for group in rendered_groups):
            return ""
        existential_groups.extend(rendered_groups)
        existential_witness_count += len(rendered_groups)
        parent_body = _graph_strip_balanced_outer_parens(
            parent_body[comma + 1 :]
        )
    if existential_witness_count <= 0 or not parent_body:
        return ""
    payload_statement = f"∀ {' '.join(existential_groups)}, {parent_body}"
    payload_key = graph_statement_key(payload_statement)
    if not payload_key:
        return ""
    for premise_statement in graph_statement_closed_premises(statement):
        if graph_statement_key(premise_statement) == payload_key or (
            graph_statement_root_equivalent(
                premise_statement,
                payload_statement,
                active_target_statements=(payload_statement,),
            )
        ):
            return premise_statement
    return ""


def graph_statement_leading_telescope_is_universal(statement: str) -> bool:
    """Whether a statement's outer binder telescope is not existential.

    ``graph_statement_closed_premises`` projects a helper premise into a
    standalone ``∀ <data binders>, <premise>`` obligation.  That projection is
    only valid against a parent whose own telescope universally quantifies the
    same binders: under an existential the premise is conditional on the
    witness, so promoting it standalone asserts something strictly stronger
    than the parent ever claimed.

    The leading-binder walker only recognises an outer ``∀``/``forall``
    telescope, so an existential-headed parent silently yields an EMPTY
    certifying premise set rather than an error.  Callers that treat "no
    certifying premises" as "nothing to certify" must consult this predicate
    first and fail closed.

    Only the outer quantifier kind belongs to this surface guard.  After a
    universal binder comma, ``∃`` begins the proposition body (for example
    ``∀ n, ∃ m, n ≤ m``); descending into that body incorrectly treats an
    existential conclusion as another outer telescope binder and rejects
    legitimate universally-scoped bridge work.
    """

    body = _graph_strip_balanced_outer_parens(
        graph_formal_statement_text(statement)
    )
    return re.match(r"^(?:∃|exists\b)\s*", body) is None


def graph_statement_closed_premises(statement: str) -> Tuple[str, ...]:
    """Return proof premises closed over the theorem's data binders.

    Helper-quality diagnostics historically stored premise bodies such as
    ``Target D`` after stripping ``D``'s binder.  Such text is useful for
    comparison but is not an executable standalone graph obligation.  This
    projection preserves every non-proof leading binder and removes only the
    proof binders, yielding obligations such as ``∀ D, Target D``.
    """

    body, binder_records = _graph_leading_binder_analysis(statement)
    binder_premises: List[Tuple[Tuple[str, ...], str]] = []
    for index, record in enumerate(binder_records):
        _raw, names, type_text, is_proof, _ambiguous = record
        if is_proof and type_text:
            binder_premises.append(
                (
                    _graph_projection_binder_groups(
                        binder_records,
                        cutoff=index,
                        target_text=type_text,
                        current_relation_names=(
                            names if _graph_binder_record_is_relation(record) else ()
                        ),
                    ),
                    type_text,
                )
            )
    implication_parts = _graph_split_top_level_implications(body)
    premises: List[Tuple[Tuple[str, ...], str]] = [
        *binder_premises,
        *(
            (
                _graph_projection_binder_groups(
                    binder_records,
                    cutoff=len(binder_records),
                    target_text=premise,
                ),
                premise,
            )
            for premise in (
                implication_parts[:-1] if len(implication_parts) >= 2 else ()
            )
        ),
    ]
    closed: List[str] = []
    for premise_binders, premise in premises:
        premise_text = _graph_strip_balanced_outer_parens(str(premise or "").strip())
        if not premise_text:
            continue
        binder_prefix = " ".join(premise_binders).strip()
        framed = f"∀ {binder_prefix}, {premise_text}" if binder_prefix else premise_text
        if framed not in closed:
            closed.append(framed)
    return tuple(closed)


def _graph_type_is_syntactically_inhabited(type_text: str) -> bool:
    """Recognize only data types with a uniform constructor/default witness."""

    compact = _graph_strip_balanced_outer_parens(
        " ".join(str(type_text or "").split()).strip("{}[]")
    )
    if not compact:
        return False
    if compact in (_GRAPH_KNOWN_DATA_ATOM_TYPES - {"Empty"}):
        return True
    if re.fullmatch(r"(?:Type|Sort|Prop)(?:\s+.+)?", compact):
        return True
    # These constructors have a witness independently of their parameters.
    # Deliberately exclude Fin, Subtype, PLift, ULift, products, and function
    # spaces: their inhabitance depends on data that the helper may not have.
    return bool(
        re.match(
            r"^(?:List|Multiset|Option|Array|Set|Finset|PUnit|Unit|Bool|"
            r"Nat|Int|Rat|Real|Complex|String|WithTop|WithBot)\b",
            compact,
        )
    )


def graph_statement_closed_data_requirements(
    statement: str,
    *,
    reference_statement: str = "",
) -> Tuple[str, ...]:
    """Return witness contracts needed to instantiate extra data binders.

    A theorem ``∀ x : T, P`` does not establish ``P`` until a value of ``T``
    is available. Proof-premise projection alone misses hollow reducers such
    as ``Empty → False`` because ``Empty`` is data, not ``Prop``. Requirements
    are expressed as closed ``Nonempty T`` propositions so the dossier can
    discharge them from verified support without pretending arbitrary data is
    synthesizable.
    """

    _body, binder_records = _graph_leading_binder_analysis(statement)
    reference_counts: Dict[str, int] = {}
    for marker in _graph_nonproof_parameter_profile(reference_statement):
        reference_counts[marker] = reference_counts.get(marker, 0) + 1
    context_names: List[str] = []
    freely_chosen_sort_names: Set[str] = set()
    required: List[str] = []
    for index, record in enumerate(binder_records):
        raw, names, type_text, is_proof, _ambiguous = record
        if is_proof:
            context_names.extend(names)
            continue
        marker = (
            _graph_contract_alpha_norm(
                type_text,
                context_bound_names=tuple(context_names),
            )
            if type_text
            else "__untyped_binder__"
        )
        anonymous_instance = bool(
            not names and raw.startswith("[") and raw.endswith("]") and type_text
        )
        binder_slots = names or (
            ("__anonymous_instance__",) if anonymous_instance else ()
        )
        # Application witnesses are reusable: one root value of type α can
        # instantiate any number of extra helper binders of the same type.
        # Counts are therefore availability markers, not linear resources.
        unmatched = (
            0
            if marker and reference_counts.get(marker, 0) > 0
            else len(binder_slots)
        )
        type_tokens = _graph_lean_identifier_tokens(type_text)
        typeclass_head = (
            str(type_tokens[0]).split(".")[-1] if type_tokens else ""
        )
        uniformly_synthesizable_instance = bool(
            unmatched
            and typeclass_head in _GRAPH_NON_PROP_CLASS_HEADS
            and all(
                token in freely_chosen_sort_names
                or token in (_GRAPH_KNOWN_DATA_ATOM_TYPES - {"Empty"})
                or token in {"Type", "Sort", "Prop"}
                for token in type_tokens[1:]
            )
        )
        if (
            unmatched
            and type_text
            and not _graph_type_is_syntactically_inhabited(type_text)
            and not uniformly_synthesizable_instance
        ):
            groups = _graph_projection_binder_groups(
                binder_records,
                cutoff=index,
                target_text=type_text,
            )
            binder_prefix = " ".join(groups).strip()
            witness = f"Nonempty ({type_text})"
            framed = f"∀ {binder_prefix}, {witness}" if binder_prefix else witness
            if framed not in required:
                required.append(framed)
        if unmatched and re.fullmatch(
            r"(?:Type|Sort|Prop)(?:\s+.+)?",
            _graph_strip_balanced_outer_parens(type_text),
        ):
            freely_chosen_sort_names.update(names)
        context_names.extend(names)
    return tuple(required)


def graph_statement_closed_conclusion(statement: str) -> str:
    """Return the conclusion closed over all leading non-proof binders."""

    body, binder_records = _graph_leading_binder_analysis(statement)
    implication_parts = _graph_split_top_level_implications(body)
    conclusion = _graph_strip_balanced_outer_parens(
        implication_parts[-1] if implication_parts else body
    )
    nonproof_groups = _graph_projection_binder_groups(
        binder_records,
        cutoff=len(binder_records),
        target_text=conclusion,
    )
    binder_prefix = " ".join(nonproof_groups).strip()
    return f"∀ {binder_prefix}, {conclusion}" if binder_prefix else conclusion


def _graph_nonproof_parameter_profile(statement: str) -> Tuple[str, ...]:
    """Return normalized non-proof binder types in the leading theorem frame."""

    _body, binder_records = _graph_leading_binder_analysis(statement)
    context_names: List[str] = []
    profile: List[str] = []
    for raw, names, type_text, is_proof, _ambiguous in binder_records:
        anonymous_instance = bool(
            not names and raw.startswith("[") and raw.endswith("]") and type_text
        )
        if not names and not anonymous_instance:
            continue
        if is_proof:
            context_names.extend(names)
            continue
        if not type_text:
            marker = "__untyped_binder__"
        else:
            marker = _graph_contract_alpha_norm(
                type_text,
                context_bound_names=tuple(context_names),
            )
        slots = names or (("__anonymous_instance__",) if anonymous_instance else ())
        profile.extend(marker for _name in slots)
        context_names.extend(names)
    return tuple(profile)


def graph_statement_nonproof_parameter_profile(statement: str) -> Tuple[str, ...]:
    """Return the shared normalized non-proof leading-binder profile."""

    return _graph_nonproof_parameter_profile(statement)


def graph_statements_contract_equivalent(left: str, right: str) -> bool:
    """Return whether two theorem-shaped statements have the same contract.

    ``graph_statement_key`` is intentionally strict and misses common theorem
    reshapes such as moving a proof-valued forall binder into an implication.
    Graph scheduling needs a looser root-equivalence check so root-shaped work
    cannot masquerade as a smaller subgoal.
    """

    left_key = graph_statement_key(left)
    right_key = graph_statement_key(right)
    if left_key and right_key and left_key == right_key:
        return True
    left_premises, left_conclusion = _graph_contract_profile(left)
    right_premises, right_conclusion = _graph_contract_profile(right)
    left_nonproof_params = _graph_nonproof_parameter_profile(left)
    right_nonproof_params = _graph_nonproof_parameter_profile(right)
    return bool(
        left_conclusion
        and right_conclusion
        and left_conclusion == right_conclusion
        and left_premises == right_premises
        and left_nonproof_params == right_nonproof_params
    )


def graph_statement_root_equivalent(
    statement: str,
    root_statement: str,
    *,
    active_target_statements: Sequence[str] = (),
) -> bool:
    """Return whether ``statement`` is the root theorem in another frame."""

    stmt = str(statement or "").strip()
    root = str(root_statement or "").strip()
    if not stmt or not root:
        return False
    if graph_statements_contract_equivalent(stmt, root):
        return True
    for active in active_target_statements:
        if graph_statements_contract_equivalent(stmt, str(active or "")):
            return True
    return False


@dataclass(frozen=True)
class GraphRootEquivalentSuppressionDecision:
    root_equivalent: bool
    exact_root_statement: bool
    active_root_statement: bool
    suppress: bool


def graph_root_equivalent_suppression_decision(
    statement: str,
    root_statement: str,
    *,
    active_target_statements: Sequence[str] = (),
    route_backed_work: bool = False,
    allow_route_backed_work: bool = False,
    reopened_after_superseded_spawn: bool = False,
    keep_non_solution_counterexample_obligation: bool = False,
) -> GraphRootEquivalentSuppressionDecision:
    """Central policy for suppressing duplicate root-shaped graph work.

    Exact root statements are first-class graph evidence.  Contract-equivalent
    rewrites and active-root restatements are duplicate scheduler work unless
    durable repair provenance says the work was explicitly reopened, or a
    route-backed missing obligation/replan needs to mine the residual root.
    """

    statement_key = graph_statement_key(statement)
    root_statement_key = graph_statement_key(root_statement)
    active_target_keys = {
        graph_statement_key(active) for active in active_target_statements
    }
    active_target_keys.discard("")
    exact_root_statement = bool(
        statement_key and root_statement_key and statement_key == root_statement_key
    )
    active_root_statement = bool(statement_key and statement_key in active_target_keys)
    root_equivalent = bool(
        str(statement or "").strip()
        and graph_statement_root_equivalent(
            statement,
            root_statement,
            active_target_statements=active_target_statements,
        )
        and not keep_non_solution_counterexample_obligation
    )
    suppress = bool(
        root_equivalent
        and (active_root_statement or not exact_root_statement)
        and not reopened_after_superseded_spawn
    )
    if (
        suppress
        and allow_route_backed_work
        and route_backed_work
        and not active_root_statement
    ):
        suppress = False
    return GraphRootEquivalentSuppressionDecision(
        root_equivalent=root_equivalent,
        exact_root_statement=exact_root_statement,
        active_root_statement=active_root_statement,
        suppress=suppress,
    )


def graph_statement_is_root_bridge(statement: str, root_statement: str) -> bool:
    """Return whether a dependency can act as an assembly bridge to root."""

    stmt = str(statement or "").strip()
    root = str(root_statement or "").strip()
    if not stmt or not root:
        return False
    if graph_statement_root_equivalent(stmt, root):
        return True
    premises, conclusion, bound_names = _graph_statement_premises_and_conclusion(stmt)
    if not premises:
        return False
    return _graph_statement_root_adjacent(
        conclusion,
        root,
        conclusion_bound_names=bound_names,
    )


def _graph_support_candidates(
    statement: str,
    *,
    include_implication_premises: bool = False,
    premises_are_assumptions: bool = False,
) -> List[Tuple[str, Tuple[str, ...]]]:
    body, base_names, binder_premises = graph_statement_leading_contract(statement)
    candidates: List[Tuple[str, Tuple[str, ...]]] = []
    seen: Set[Tuple[str, Tuple[str, ...]]] = set()

    def add_candidate(statement_text: str, names: Sequence[str]) -> None:
        candidate = (str(statement_text or "").strip(), tuple(names or ()))
        if candidate[0] and candidate not in seen:
            seen.add(candidate)
            candidates.append(candidate)

    def add_assumption_candidate(
        statement_text: str,
        names: Sequence[str],
    ) -> None:
        item_body, item_names = _graph_strip_leading_forall_binders_with_names(
            statement_text
        )
        item_bound_names = tuple(dict.fromkeys(tuple(names or ()) + item_names))
        add_candidate(item_body, item_bound_names)
        if (
            "→" in item_body
            or "->" in item_body
            or "∀" in item_body
            or "∃" in item_body
        ):
            items = [item_body]
        else:
            items = _graph_split_top_level_conjunctions(item_body)
        for item in items:
            conjunct_body, conjunct_names = (
                _graph_strip_leading_forall_binders_with_names(item)
            )
            add_candidate(
                conjunct_body,
                tuple(dict.fromkeys(item_bound_names + conjunct_names)),
            )

    if premises_are_assumptions:
        for premise in binder_premises:
            add_assumption_candidate(premise, base_names)
    parts = _graph_split_top_level_implications(body)
    conclusion = parts[-1] if parts else body
    if (
        premises_are_assumptions
        and include_implication_premises
        and len(parts) >= 2
    ):
        selected = parts[:-1]
    elif include_implication_premises:
        selected = []
    elif binder_premises:
        selected = []
    else:
        selected = [body]
    if premises_are_assumptions and include_implication_premises:
        iff_parts = _graph_split_top_level_iffs(conclusion)
        if len(iff_parts) >= 2:
            selected.extend(iff_parts)
            for iff_part in iff_parts:
                iff_body, iff_names, iff_binder_premises = (
                    graph_statement_leading_contract(iff_part)
                )
                iff_bound_names = tuple(dict.fromkeys(base_names + tuple(iff_names)))
                for premise in iff_binder_premises:
                    add_assumption_candidate(premise, iff_bound_names)
                iff_implication_parts = _graph_split_top_level_implications(iff_body)
                if len(iff_implication_parts) >= 2:
                    for premise in iff_implication_parts[:-1]:
                        premise_body, premise_names = (
                            _graph_strip_leading_forall_binders_with_names(premise)
                        )
                        add_candidate(
                            premise_body,
                            tuple(dict.fromkeys(iff_bound_names + premise_names)),
                        )
    for item in selected:
        add_assumption_candidate(item, base_names)
    return candidates


def _graph_strip_leading_forall_binders(text: str) -> str:
    body = _graph_strip_balanced_outer_parens(text)
    while True:
        quantifier_match = re.match(r"^(?:∀|forall\b)\s*", body)
        if quantifier_match is None:
            break
        comma = _graph_find_top_level_comma(body)
        if comma < 0:
            break
        body = _graph_strip_balanced_outer_parens(body[comma + 1 :])
    return body


def _graph_strip_leading_forall_binders_with_names(
    text: str,
) -> Tuple[str, Tuple[str, ...]]:
    body = _graph_strip_balanced_outer_parens(text)
    names: List[str] = []
    while True:
        quantifier_match = re.match(r"^(?:∀|forall\b)\s*", body)
        if quantifier_match is None:
            break
        comma = _graph_find_top_level_comma(body)
        if comma < 0:
            break
        binder_chunk = body[quantifier_match.end() : comma]
        names.extend(_graph_binder_names_from_chunk(binder_chunk))
        body = _graph_strip_balanced_outer_parens(body[comma + 1 :])
    return body, tuple(dict.fromkeys(names))


def _graph_contract_norm(text: str) -> str:
    stripped = _graph_strip_leading_forall_binders(text)
    stripped = _graph_normalize_numeric_casts_for_contract(stripped)
    stripped = re.sub(r"\((\d+)\s*:\s*[^()]+\)", r"\1", stripped)
    return re.sub(r"\s+", "", stripped)


def _graph_quantifier_bound_names(text: str) -> Tuple[str, ...]:
    names: List[str] = []
    for match in re.finditer(r"(?:[∀∃]|forall|exists)\s*([^,]+),", str(text or "")):
        names.extend(_graph_binder_names_from_chunk(match.group(1)))
    return tuple(dict.fromkeys(names))


def _graph_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'"


def _graph_top_level_quantifier_token_len(text: str, index: int) -> int:
    raw = str(text or "")
    ch = raw[index] if 0 <= index < len(raw) else ""
    if ch in {"∀", "∃"}:
        return 1
    for token in ("forall", "exists"):
        end = index + len(token)
        if not raw.startswith(token, index):
            continue
        before_ok = index == 0 or not _graph_ident_char(raw[index - 1])
        after_ok = end >= len(raw) or not _graph_ident_char(raw[end])
        if before_ok and after_ok:
            return len(token)
    return 0


_GRAPH_ALPHA_BOUND_PLACEHOLDER_RE = re.compile(r"^__bound\d+__$")
_GRAPH_ALPHA_FREE_IDENTIFIER_ESCAPE_PREFIX = "\0mini-alpha-free-identifier:"


def _graph_contract_alpha_identifier_token(
    token: str,
    mapping: Mapping[str, str],
) -> str:
    if token in mapping:
        return mapping[token]
    if _GRAPH_ALPHA_BOUND_PLACEHOLDER_RE.fullmatch(token):
        return f"{_GRAPH_ALPHA_FREE_IDENTIFIER_ESCAPE_PREFIX}{token}\0"
    return token


def _graph_contract_alpha_norm(
    text: str,
    *,
    context_bound_names: Sequence[str] = (),
    preserve_type_ascriptions: bool = False,
) -> str:
    stripped, leading_names = _graph_strip_leading_forall_binders_with_names(text)
    bound_names = tuple(
        dict.fromkeys(
            tuple(
                str(name or "").strip()
                for name in context_bound_names
                if str(name or "").strip()
            )
            + leading_names
        )
    )
    mapping = {name: f"__bound{idx}__" for idx, name in enumerate(bound_names)}

    if not preserve_type_ascriptions:
        stripped = _graph_normalize_numeric_casts_for_contract(stripped)
        stripped = re.sub(r"\((\d+)\s*:\s*[^()]+\)", r"\1", stripped)
    normalized = _graph_contract_alpha_replace_scoped(stripped, mapping)
    return re.sub(r"\s+", "", normalized)


def _graph_contract_alpha_replace_scoped(
    text: str,
    mapping: Mapping[str, str],
) -> str:
    raw = str(text or "")
    out: List[str] = []
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            token = raw[index:skip_to]
            out.append(mapping.get(token, token) if raw.startswith("«", index) else token)
            index = skip_to
            continue
        ch = raw[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            end = _graph_matching_group_index(raw, index)
            if end >= 0:
                out.append(ch)
                out.append(
                    _graph_contract_alpha_replace_scoped(
                        raw[index + 1 : end],
                        mapping,
                    )
                )
                out.append(raw[end])
                index = end + 1
                continue
        quantifier_len = _graph_top_level_quantifier_token_len(raw, index)
        if quantifier_len:
            tail_start = index + quantifier_len
            comma = _graph_find_top_level_comma(raw[tail_start:])
            if comma >= 0:
                binder = raw[tail_start : tail_start + comma]
                body = raw[tail_start + comma + 1 :]
                local_mapping = dict(mapping)
                next_index = len(local_mapping)
                for name in _graph_binder_names_from_chunk(binder):
                    local_mapping[name] = f"__bound{next_index}__"
                    next_index += 1
                out.append(raw[index : index + quantifier_len])
                out.append(_graph_contract_alpha_replace_scoped(binder, local_mapping))
                out.append(",")
                out.append(_graph_contract_alpha_replace_scoped(body, local_mapping))
                return "".join(out)
        match = re.match(r"[^\W\d][\w']*", raw[index:], flags=re.UNICODE)
        if match is not None:
            token = match.group(0)
            out.append(_graph_contract_alpha_identifier_token(token, mapping))
            index += len(token)
            continue
        out.append(raw[index])
        index += 1
    return "".join(out)


def _graph_matching_paren_index(text: str, start: int) -> int:
    depth = 0
    for index in range(start, len(text)):
        ch = text[index]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return index
        if depth < 0:
            return -1
    return -1


def _graph_normalize_numeric_casts_for_contract(text: str) -> str:
    numeric_type_re = re.compile(r"(?:ℚ|Rat|ℝ|Real|ℤ|Int|ℕ|Nat)")

    def normalize(value: str) -> str:
        out: List[str] = []
        index = 0
        while index < len(value):
            if value[index] != "(":
                out.append(value[index])
                index += 1
                continue
            end = _graph_matching_paren_index(value, index)
            if end < 0:
                out.append(value[index])
                index += 1
                continue
            body = normalize(value[index + 1 : end])
            colon = _graph_top_level_colon_index(body)
            if colon >= 0:
                expr = body[:colon].strip()
                type_text = _graph_strip_balanced_outer_parens(
                    body[colon + 1 :].strip()
                )
                if expr and re.search(r"\d", expr) and numeric_type_re.fullmatch(type_text):
                    out.append(_graph_strip_balanced_outer_parens(expr))
                    index = end + 1
                    continue
            out.append("(")
            out.append(body)
            out.append(")")
            index = end + 1
        return "".join(out)

    return normalize(str(text or ""))


def _graph_root_conclusion_candidates(
    root_statement: str,
) -> Tuple[Tuple[str, Tuple[str, ...]], ...]:
    candidates: List[Tuple[str, Tuple[str, ...]]] = []
    seen: Set[str] = set()

    def add_candidate(candidate_text: str, candidate_bound_names: Tuple[str, ...]) -> None:
        key = _graph_contract_alpha_norm(
            candidate_text,
            context_bound_names=candidate_bound_names,
        )
        if key and key not in seen:
            seen.add(key)
            candidates.append((candidate_text, candidate_bound_names))

    body, bound_names = _graph_strip_leading_forall_binders_with_names(
        str(root_statement or "")
    )
    parts = _graph_split_top_level_implications(body)
    conclusion = parts[-1] if parts else body
    conclusion_parts = _graph_split_top_level_iffs(conclusion)
    for candidate in conclusion_parts or [conclusion]:
        candidate, candidate_names = _graph_strip_leading_forall_binders_with_names(
            candidate
        )
        all_names = tuple(dict.fromkeys(bound_names + candidate_names))
        add_candidate(candidate, all_names)
        candidate_implications = _graph_split_top_level_implications(candidate)
        if len(candidate_implications) >= 2:
            add_candidate(candidate_implications[-1], all_names)
    return tuple(candidates)


_SCOPED_OPEN_NAME_COMPONENT_RE = r"(?:«[^»\r\n]+»|[^\W\d][\w']*)"
_SCOPED_OPEN_NAME_RE = (
    _SCOPED_OPEN_NAME_COMPONENT_RE
    + r"(?:\."
    + _SCOPED_OPEN_NAME_COMPONENT_RE
    + r")*"
)
_SCOPED_OPEN_DECL_PREFIX_RE = re.compile(
    r"^\s*open(?:\s+scoped)?\s+"
    + _SCOPED_OPEN_NAME_RE
    + r"(?:\s+"
    + _SCOPED_OPEN_NAME_RE
    + r")*\s+in\s+"
)


def _helper_decl_header(src: str) -> Optional[Tuple[str, str, str]]:
    text = str(src or "").strip()
    if not text:
        return None
    # Extracted fenced blocks retain leading ``open`` semantics by wrapping
    # each helper in Lean's command-local ``open ... in`` syntax.  Peel only
    # that conservative generated prefix for declaration metadata parsing;
    # the stored helper source itself remains scoped and is what Lean checks.
    while True:
        scoped_open = _SCOPED_OPEN_DECL_PREFIX_RE.match(text)
        if scoped_open is None:
            break
        text = text[scoped_open.end() :].lstrip()
    decl = re.match(
        r"^\s*"
        r"(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
        r"(?P<kind>theorem|lemma|def|abbrev|instance)\b"
        r"(?P<after>[\s\S]*)$",
        text,
    )
    if decl is None:
        return None
    kind = str(decl.group("kind") or "").strip()
    after = str(decl.group("after") or "")
    named = re.match(
        r"^\s+"
        r"(?P<name>"
        + _SCOPED_OPEN_NAME_RE
        + r")"
        r"(?=\s|[:({\[]|$)"
        r"(?P<tail>[\s\S]*)$",
        after,
    )
    if named is not None:
        return kind, str(named.group("name") or "").strip(), str(
            named.group("tail") or ""
        )
    if kind == "instance":
        stripped = after.lstrip()
        if stripped and stripped[0] in ":({[":
            return kind, "", after
    return None


def helper_decl_statement(src: str) -> str:
    """Best-effort statement extraction from a Lean helper declaration."""

    header = _helper_decl_header(src)
    if header is None:
        return ""
    kind, _name, tail = header
    colon = _declaration_type_colon(tail)
    if colon is None:
        return ""
    marker = _declaration_body_marker(tail, start=colon + 1)
    if marker is None:
        return ""
    marker_index, _marker_len = marker
    statement = graph_formal_statement_text(
        _strip_lean_decl_comments_preserving_strings(tail[colon + 1 : marker_index]),
        canonicalize_guarded_iff=False,
    )
    binders = _strip_declaration_binder_defaults(" ".join(tail[:colon].split()))
    if kind in {"theorem", "lemma"} and binders:
        return f"∀ {binders}, {statement}"
    return statement


def helper_decl_kind(src: str) -> str:
    """Best-effort declaration kind extraction from a Lean helper declaration."""

    header = _helper_decl_header(src)
    return header[0] if header is not None else ""


def helper_decl_name(src: str) -> str:
    """Best-effort declared name extraction from a Lean helper declaration."""

    header = _helper_decl_header(src)
    return header[1] if header is not None else ""


def helper_decl_body(src: str) -> str:
    """Best-effort body extraction from a Lean helper declaration."""

    header = _helper_decl_header(src)
    if header is None:
        return ""
    _kind, _name, tail = header
    colon = _declaration_type_colon(tail)
    if colon is None:
        return ""
    marker = _declaration_body_marker(tail, start=colon + 1)
    if marker is None:
        return ""
    marker_index, marker_len = marker
    return tail[marker_index + marker_len :].strip()


def _declaration_body_marker(tail: str, *, start: int) -> Optional[Tuple[int, int]]:
    """Return the top-level declaration body marker, skipping comments/strings."""

    depth = 0
    in_top_level_let = False
    s = str(tail or "")
    index = max(0, int(start or 0))
    while index < len(s):
        if s.startswith("--", index):
            newline = s.find("\n", index)
            if newline < 0:
                return None
            index = newline + 1
            continue
        if s.startswith("/-", index):
            index = _skip_lean_block_comment(s, index)
            continue
        ch = s[index]
        if ch == '"':
            index = _skip_lean_string(s, index)
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and _starts_token(s, index, "let"):
            in_top_level_let = True
            index += len("let")
            continue
        elif depth == 0 and in_top_level_let and ch == ";":
            in_top_level_let = False
        elif depth == 0 and in_top_level_let and ch in "\n\r":
            in_top_level_let = False
        elif depth == 0 and s.startswith(":=", index):
            if in_top_level_let:
                index += 2
                continue
            return index, 2
        elif (
            depth == 0
            and not in_top_level_let
            and _starts_token(s, index, "where")
        ):
            return index, len("where")
        index += 1
    return None


def _skip_lean_string(text: str, index: int) -> int:
    s = str(text or "")
    index += 1
    while index < len(s):
        if s[index] == "\\":
            index += 2
            continue
        if s[index] == '"':
            return index + 1
        index += 1
    return len(s)


def _skip_lean_block_comment(text: str, index: int) -> int:
    s = str(text or "")
    depth = 1
    index += 2
    while index < len(s):
        if s.startswith("/-", index):
            depth += 1
            index += 2
            continue
        if s.startswith("-/", index):
            depth -= 1
            index += 2
            if depth <= 0:
                return index
            continue
        index += 1
    return len(s)


def _strip_lean_decl_comments_preserving_strings(text: str) -> str:
    s = str(text or "")
    out: List[str] = []
    index = 0
    while index < len(s):
        if s.startswith("--", index):
            newline = s.find("\n", index)
            if newline < 0:
                break
            out.append("\n")
            index = newline + 1
            continue
        if s.startswith("/-", index):
            index = _skip_lean_block_comment(s, index)
            continue
        if s[index] == '"':
            end = _skip_lean_string(s, index)
            out.append(s[index:end])
            index = end
            continue
        out.append(s[index])
        index += 1
    return "".join(out)


def _declaration_body_assign(tail: str, *, start: int) -> Optional[int]:
    """Return the top-level ``:=`` that starts the declaration body."""

    depth = 0
    in_top_level_let = False
    s = str(tail or "")
    index = max(0, int(start or 0))
    while index < len(s) - 1:
        ch = s[index]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and _starts_token(s, index, "let"):
            in_top_level_let = True
            index += len("let")
            continue
        elif depth == 0 and in_top_level_let and ch == ";":
            in_top_level_let = False
        elif depth == 0 and in_top_level_let and ch in "\n\r":
            in_top_level_let = False
        elif ch == ":" and s[index + 1] == "=" and depth == 0:
            if in_top_level_let:
                index += 2
                continue
            return index
        index += 1
    return None


def _declaration_body_where(tail: str, *, start: int) -> Optional[int]:
    """Return the top-level ``where`` that starts a declaration body."""

    depth = 0
    s = str(tail or "")
    index = max(0, int(start or 0))
    while index < len(s):
        ch = s[index]
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0 and _starts_token(s, index, "where"):
            return index
        index += 1
    return None


def _strip_declaration_binder_defaults(text: str) -> str:
    """Remove Lean declaration default values from binder groups for identity."""

    source = str(text or "")
    out: List[str] = []
    index = 0
    while index < len(source):
        ch = source[index]
        close = _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.get(ch)
        if close is None or ch == "⟨":
            out.append(ch)
            index += 1
            continue
        depth = 0
        end = index
        while end < len(source):
            if source[end] == ch:
                depth += 1
            elif source[end] == close:
                depth -= 1
                if depth == 0:
                    break
            end += 1
        if end >= len(source):
            out.append(source[index:])
            break
        inner = source[index + 1 : end]
        out.append(ch + _strip_default_assignments_in_binder(inner) + close)
        index = end + 1
    return " ".join("".join(out).split())


def _strip_default_assignments_in_binder(inner: str) -> str:
    text = str(inner or "")
    assign = text.find(":=")
    if assign < 0:
        return text
    return text[:assign].rstrip()


def _starts_token(text: str, index: int, token: str) -> bool:
    s = str(text or "")
    if not s.startswith(token, index):
        return False
    before = s[index - 1] if index > 0 else " "
    after_index = index + len(token)
    after = s[after_index] if after_index < len(s) else " "
    return not (before.isalnum() or before == "_") and not (
        after.isalnum() or after == "_"
    )


def _declaration_type_colon(tail: str) -> Optional[int]:
    """Return the top-level theorem-type colon after optional binders."""

    depth = 0
    for index, ch in enumerate(str(tail or "")):
        if ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GRAPH_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            return index
    return None


@dataclass
class ProofGraphEdge:
    source: str
    target: str
    kind: str


@dataclass
class ProofGraphAttempt:
    attempt_id: str
    node_id: str
    phase: str
    turn_index: int
    verdict: str
    proof_hash: str = ""
    error_type: str = ""
    helper_names: List[str] = field(default_factory=list)
    source: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ProofGraphNode:
    node_id: str
    kind: str
    name: str
    statement: str
    status: str = "open"
    phase: str = ""
    turn_index: int = 0
    source_hash: str = ""
    proof_hash: str = ""
    support_names: List[str] = field(default_factory=list)
    attempt_ids: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ProofGraphBranchFrame:
    """Route-local branch context supplied by a proved case split.

    A frame names one branch assumption from a route-local case split and,
    when available, the verified reducer that consumes that assumption to
    reach the route target.  Frames are first-class graph records rather than
    prose annotations so route assembly can distinguish branch-local premises
    from missing global dependencies.
    """

    frame_id: str
    route_id: str
    case_node_id: str
    case_helper_name: str
    case_statement: str
    branch_name: str
    branch_index: int
    assumption_statement: str
    assumption_key: str
    case_full_statement: str = ""
    reducer_node_id: str = ""
    reducer_helper_name: str = ""
    reducer_statement: str = ""
    status: str = "open"
    metadata: Dict[str, Any] = field(default_factory=dict)


_MAX_PROOF_GRAPH_SCRATCH_NODES = 128
_MAX_PROOF_GRAPH_ATTEMPTS = 256
_PROOF_GRAPH_REHYDRATION_VERDICTS = frozenset(
    {"solved", "proved", "helper_accepted", "scratch_ok"}
)


@dataclass
class ProofGraph:
    theorem_name: str
    root_statement: str
    root_node_id: str = "root"
    nodes: Dict[str, ProofGraphNode] = field(default_factory=dict)
    edges: List[ProofGraphEdge] = field(default_factory=list)
    helper_name_to_node_id: Dict[str, str] = field(default_factory=dict)
    attempts: List[ProofGraphAttempt] = field(default_factory=list)
    attempt_history_pruned: int = 0
    branch_frames: Dict[str, ProofGraphBranchFrame] = field(default_factory=dict)
    active_root_target_statements: List[str] = field(default_factory=list)
    active_root_target_contract_identities: List[str] = field(default_factory=list)
    active_root_target_universe_observed: bool = False
    _edge_keys: Set[Tuple[str, str, str]] = field(
        default_factory=set,
        init=False,
        repr=False,
    )
    _next_attempt_index: int = field(default=1, init=False, repr=False)
    _attempt_ids: Set[str] = field(default_factory=set, init=False, repr=False)
    _value_propagation_cache_signature: Tuple[Any, ...] = field(
        default_factory=tuple,
        init=False,
        repr=False,
    )
    _value_propagation_cache_values: Dict[str, float] = field(
        default_factory=dict,
        init=False,
        repr=False,
    )

    def __post_init__(self) -> None:
        observed_active_universe = bool(
            self.active_root_target_universe_observed
            or self.active_root_target_statements
            or self.active_root_target_contract_identities
        )
        self.active_root_target_statements = [
            " ".join(str(item or "").split()).strip()
            for item in list(self.active_root_target_statements or [])
            if str(item or "").strip()
        ]
        self.set_active_root_target_contract_identities(
            self.active_root_target_contract_identities
        )
        self.active_root_target_universe_observed = observed_active_universe
        self._rebuild_edge_index()
        self.ensure_root(self.root_statement)
        self._sync_next_attempt_index()

    def set_active_root_target_statements(self, targets: Iterable[str]) -> None:
        seen: Set[str] = set()
        cleaned: List[str] = []
        for item in list(targets or ()):
            text = " ".join(str(item or "").split()).strip()
            if not text or text in seen:
                continue
            seen.add(text)
            cleaned.append(text)
        self.active_root_target_statements = cleaned
        self.active_root_target_universe_observed = True

    def set_active_root_target_contract_identities(
        self,
        identities: Iterable[str],
    ) -> None:
        seen: Set[str] = set()
        cleaned: List[str] = []
        for item in list(identities or ()):
            identity = str(item or "").strip()
            if (
                not has_lean_contract_identity(identity)
                or identity in seen
            ):
                continue
            seen.add(identity)
            cleaned.append(identity)
        self.active_root_target_contract_identities = cleaned
        self.active_root_target_universe_observed = True

    def clone(self) -> "ProofGraph":
        graph = ProofGraph(
            theorem_name=self.theorem_name,
            root_statement=self.root_statement,
            root_node_id=self.root_node_id,
            nodes={
                node_id: ProofGraphNode(
                    node_id=node.node_id,
                    kind=node.kind,
                    name=node.name,
                    statement=node.statement,
                    status=node.status,
                    phase=node.phase,
                    turn_index=node.turn_index,
                    source_hash=node.source_hash,
                    proof_hash=node.proof_hash,
                    support_names=list(node.support_names),
                    attempt_ids=list(node.attempt_ids),
                    metadata=copy.deepcopy(node.metadata),
                )
                for node_id, node in self.nodes.items()
            },
            edges=[
                ProofGraphEdge(
                    source=edge.source,
                    target=edge.target,
                    kind=edge.kind,
                )
                for edge in self.edges
            ],
            helper_name_to_node_id=dict(self.helper_name_to_node_id),
            attempts=[
                ProofGraphAttempt(
                    attempt_id=attempt.attempt_id,
                    node_id=attempt.node_id,
                    phase=attempt.phase,
                    turn_index=attempt.turn_index,
                    verdict=attempt.verdict,
                    proof_hash=attempt.proof_hash,
                    error_type=attempt.error_type,
                    helper_names=list(attempt.helper_names),
                    source=attempt.source,
                    metadata=copy.deepcopy(attempt.metadata),
                )
                for attempt in self.attempts
            ],
            attempt_history_pruned=self.attempt_history_pruned,
            branch_frames={
                frame_id: ProofGraphBranchFrame(
                    frame_id=frame.frame_id,
                    route_id=frame.route_id,
                    case_node_id=frame.case_node_id,
                    case_helper_name=frame.case_helper_name,
                    case_statement=frame.case_statement,
                    case_full_statement=frame.case_full_statement,
                    branch_name=frame.branch_name,
                    branch_index=frame.branch_index,
                    assumption_statement=frame.assumption_statement,
                    assumption_key=frame.assumption_key,
                    reducer_node_id=frame.reducer_node_id,
                    reducer_helper_name=frame.reducer_helper_name,
                    reducer_statement=frame.reducer_statement,
                    status=frame.status,
                    metadata=copy.deepcopy(frame.metadata),
                )
                for frame_id, frame in self.branch_frames.items()
            },
            active_root_target_statements=list(self.active_root_target_statements),
            active_root_target_contract_identities=list(
                self.active_root_target_contract_identities
            ),
            active_root_target_universe_observed=(
                self.active_root_target_universe_observed
            ),
        )
        graph._rebuild_edge_index()
        graph._next_attempt_index = self._next_attempt_index
        execution_snapshot = getattr(self, "_proof_state_execution_record", None)
        if isinstance(execution_snapshot, dict):
            # Deliberately private: a clone shares the live scheduler state,
            # whereas ``to_record`` remains prompt-safe and serializable.
            graph._proof_state_execution_record = copy.deepcopy(execution_snapshot)
            graph._proof_state_execution_snapshot_fingerprint = str(
                getattr(
                    self,
                    "_proof_state_execution_snapshot_fingerprint",
                    "",
                )
                or ""
            )
        falsification_authorities = getattr(
            self,
            "_proof_state_falsification_authorities",
            None,
        )
        if isinstance(falsification_authorities, dict):
            graph._proof_state_falsification_authorities = copy.deepcopy(
                falsification_authorities
            )
        return graph

    def _sync_next_attempt_index(self) -> None:
        self._rebuild_attempt_index()
        self._compact_attempt_history()
        max_index = 0
        for attempt in self.attempts:
            raw_id = str(getattr(attempt, "attempt_id", "") or "")
            if not raw_id.startswith("attempt:"):
                continue
            try:
                max_index = max(max_index, int(raw_id.split(":", 1)[1]))
            except ValueError:
                continue
        self._next_attempt_index = max(self._next_attempt_index, max_index + 1)

    def _rebuild_attempt_index(self) -> None:
        self._attempt_ids = {
            str(attempt.attempt_id or "")
            for attempt in self.attempts
            if str(attempt.attempt_id or "")
        }

    def _compact_attempt_history(
        self,
        *,
        max_attempts: int = _MAX_PROOF_GRAPH_ATTEMPTS,
    ) -> int:
        """Retain bounded recent diagnostics without retaining stale node IDs."""

        limit = max(0, int(max_attempts or 0))
        if len(self.attempts) <= limit:
            return 0
        repair_needed_node_ids = {
            node.node_id
            for node in self.nodes.values()
            if node.status == "proved" and not node.proof_hash
        }
        protected_attempt_ids: Set[str] = set()
        for attempt in reversed(self.attempts):
            if attempt.node_id not in repair_needed_node_ids:
                continue
            if (
                str(attempt.verdict or "").strip().lower()
                not in _PROOF_GRAPH_REHYDRATION_VERDICTS
                or not attempt.proof_hash
            ):
                continue
            protected_attempt_ids.add(attempt.attempt_id)
            repair_needed_node_ids.discard(attempt.node_id)
            if not repair_needed_node_ids:
                break
        recent_budget = max(0, limit - len(protected_attempt_ids))
        recent_candidates = [
            item
            for item in self.attempts
            if item.attempt_id not in protected_attempt_ids
        ]
        recent_attempt_ids = (
            {
                attempt.attempt_id
                for attempt in recent_candidates[-recent_budget:]
            }
            if recent_budget
            else set()
        )
        retained_attempt_ids = protected_attempt_ids | recent_attempt_ids
        evicted = [
            attempt
            for attempt in self.attempts
            if attempt.attempt_id not in retained_attempt_ids
        ]
        self.attempts = [
            attempt
            for attempt in self.attempts
            if attempt.attempt_id in retained_attempt_ids
        ]
        overflow = len(evicted)
        evicted_by_node: Dict[str, Set[str]] = {}
        for attempt in evicted:
            evicted_by_node.setdefault(attempt.node_id, set()).add(attempt.attempt_id)
            self._attempt_ids.discard(attempt.attempt_id)
        for node_id, attempt_ids in evicted_by_node.items():
            node = self.nodes.get(node_id)
            if node is not None:
                node.attempt_ids = [
                    attempt_id
                    for attempt_id in node.attempt_ids
                    if attempt_id not in attempt_ids
                ]
        self.attempt_history_pruned += overflow
        return overflow

    def _allocate_attempt_id(self) -> str:
        while True:
            attempt_id = f"attempt:{self._next_attempt_index}"
            self._next_attempt_index += 1
            if attempt_id not in self._attempt_ids:
                return attempt_id

    def ensure_root(self, statement: str) -> ProofGraphNode:
        statement_text = str(statement or "").strip()
        node = self.nodes.get(self.root_node_id)
        if node is None:
            node = ProofGraphNode(
                node_id=self.root_node_id,
                kind="root",
                name=str(self.theorem_name or "root"),
                statement=statement_text,
            )
            self.nodes[self.root_node_id] = node
        else:
            node.name = str(self.theorem_name or "root")
            if statement_text:
                node.statement = statement_text
        self.root_statement = statement_text or self.root_statement
        return node

    def helper_node_id(self, name: str) -> str:
        return f"helper:{str(name or '').strip()}"

    def claim_node_id(self, key: str) -> str:
        return f"claim:{graph_text_hash(graph_identity_text(key))}"

    def formal_variant_node_id(self, claim_node_id: str, key: str) -> str:
        payload = f"{str(claim_node_id or '').strip()}\n{graph_identity_text(key)}"
        return f"variant:{graph_text_hash(payload)}"

    def strategy_route_node_id(self, key: str) -> str:
        return f"route:{graph_text_hash(graph_identity_text(key))}"

    def missing_obligation_node_id(self, key: str) -> str:
        return f"obligation:{graph_text_hash(graph_identity_text(key))}"

    def replan_node_id(self, key: str) -> str:
        return f"replan:{graph_text_hash(graph_identity_text(key))}"

    @staticmethod
    def _coerce_float(value: Any, default: float = 0.0) -> float:
        try:
            return float(value)
        except Exception:
            return float(default)

    @staticmethod
    def _bounded_search_value(value: float) -> float:
        return max(-1.0, min(2.0, float(value)))

    def _active_proposal_identity(
        self,
        identity: str,
        *,
        node_id_for_identity: Any,
        metadata: Dict[str, Any],
        tombstone_metadata_prefix: str,
    ) -> Tuple[str, str]:
        """Return an identity/node id pair that does not target a tombstone."""

        base_identity = graph_identity_text(identity)
        node_id = str(node_id_for_identity(base_identity) or "")
        if not self.is_superseded_tombstone(self.nodes.get(node_id)):
            return base_identity, node_id
        revival_index = 2
        while True:
            revived_identity = (
                f"{base_identity}\nproposal_revival:{revival_index}"
            )
            revived_node_id = str(node_id_for_identity(revived_identity) or "")
            revived_node = self.nodes.get(revived_node_id)
            if not self.is_superseded_tombstone(revived_node):
                metadata[f"{tombstone_metadata_prefix}_base_identity_hash"] = (
                    graph_text_hash(base_identity)
                )
                metadata[f"{tombstone_metadata_prefix}_base_node_id"] = node_id
                metadata["proposal_revival_index"] = revival_index
                return revived_identity, revived_node_id
            revival_index += 1

    @staticmethod
    def _proposal_generation_name(
        *,
        node_name: str = "",
        metadata: Optional[Dict[str, Any]] = None,
        prefer_variant_name: bool = False,
    ) -> str:
        """Return the stable proposal-generation name used for live dedup."""

        data = dict(metadata or {})
        if prefer_variant_name:
            node_label = str(node_name or "").strip()
            variant_name = str(data.get("variant_name") or "").strip()
            if (
                not variant_name
                and node_label
                and not re.fullmatch(r"variant_[0-9a-f]{16}", node_label)
            ):
                variant_name = node_label
            helper_context_name = str(
                data.get("proposed_helper_name")
                or data.get("helper_name")
                or ""
            ).strip()
            parent_claim_id = str(data.get("claim_node_id") or "").strip()
            context_name = helper_context_name
            if not context_name and parent_claim_id:
                context_name = f"claim:{parent_claim_id}"
            if not context_name:
                context_name = str(data.get("claim_name") or "").strip()
            if variant_name and context_name and variant_name != context_name:
                return f"{context_name}\nvariant:{variant_name}"
            if variant_name:
                return variant_name
            if context_name:
                return context_name
            return str(node_name or "").strip()
        name_keys = (
            "proposal_generation_key",
            "proposed_helper_name",
            "helper_name",
            "claim_name",
            "variant_name",
        )
        for key in name_keys:
            value = str(data.get(key) or "").strip()
            if value:
                return value
        return str(node_name or "").strip()

    def _repair_revived_claim_child_variants(
        self,
        claim: ProofGraphNode,
        *,
        live_source: bool = True,
    ) -> None:
        if claim.kind != "proposed_claim" or self.is_superseded_tombstone(claim):
            return
        metadata = dict(claim.metadata or {})
        base_claim_id = str(metadata.get("claim_base_node_id") or "").strip()
        base_claim = self.nodes.get(base_claim_id)
        if (
            not base_claim_id
            or base_claim is None
            or base_claim.kind != "proposed_claim"
            or not self.is_superseded_tombstone(base_claim)
        ):
            return
        claim_key = graph_statement_key(claim.statement)
        base_key = graph_statement_key(base_claim.statement)
        if not claim_key or claim_key != base_key:
            return
        if not str(
            (base_claim.metadata or {}).get("superseded_source_node_id") or ""
        ).strip():
            if live_source:
                self._set_live_superseded_source(base_claim, claim.node_id)
            else:
                base_claim.metadata["superseded_source_node_id"] = claim.node_id
        variant_ids = {
            edge.target
            for edge in self.outgoing(base_claim_id, kind="claim_formalized_as")
        }
        for variant in self.nodes_by_kind("formal_variant"):
            parent_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
            if parent_id == base_claim_id:
                variant_ids.add(variant.node_id)
        for variant_id in variant_ids:
            variant = self.nodes.get(variant_id)
            if (
                variant is None
                or variant.kind != "formal_variant"
                or self.is_superseded_tombstone(variant)
                or graph_statement_key(variant.statement) != claim_key
            ):
                continue
            self._reparent_equivalent_child_variant_from_superseded_claim(
                variant,
                parent_id=base_claim_id,
            )

    def _repair_revived_claim_child_variants_for_all(self) -> None:
        """Replay repair for revived claims serialized before source links existed."""

        for claim in self.nodes_by_kind("proposed_claim"):
            self._repair_revived_claim_child_variants(claim, live_source=False)

    def _repair_revived_claim_route_dependencies_for_all(self) -> None:
        """Replay repair for revived claims serialized before source links existed."""

        for claim in self.nodes_by_kind("proposed_claim"):
            if self.is_superseded_tombstone(claim):
                continue
            metadata = dict(claim.metadata or {})
            base_claim_id = str(metadata.get("claim_base_node_id") or "").strip()
            base_claim = self.nodes.get(base_claim_id)
            if (
                not base_claim_id
                or base_claim is None
                or base_claim.kind != "proposed_claim"
                or not self.is_superseded_tombstone(base_claim)
            ):
                continue
            claim_key = graph_statement_key(claim.statement)
            base_key = graph_statement_key(base_claim.statement)
            if not claim_key or claim_key != base_key:
                continue
            if not str(
                (base_claim.metadata or {}).get("superseded_source_node_id") or ""
            ).strip():
                base_claim.metadata["superseded_source_node_id"] = claim.node_id
            self._retarget_equivalent_route_dependencies(
                base_claim,
                source_node_id=claim.node_id,
                allow_newer_revision=not bool(
                    (base_claim.metadata or {}).get("route_retarget_revision_guarded")
                ),
            )

    def _repair_revived_variant_route_dependencies_for_all(self) -> None:
        """Replay repair for revived variants serialized before source links existed."""

        for variant in self.nodes_by_kind("formal_variant"):
            if self.is_superseded_tombstone(variant):
                continue
            metadata = dict(variant.metadata or {})
            base_variant_id = str(metadata.get("variant_base_node_id") or "").strip()
            base_variant = self.nodes.get(base_variant_id)
            if (
                not base_variant_id
                or base_variant is None
                or base_variant.kind != "formal_variant"
                or not self.is_superseded_tombstone(base_variant)
            ):
                continue
            variant_key = graph_statement_key(variant.statement)
            base_key = graph_statement_key(base_variant.statement)
            if not variant_key or variant_key != base_key:
                continue
            if not str(
                (base_variant.metadata or {}).get("superseded_source_node_id") or ""
            ).strip():
                base_variant.metadata["superseded_source_node_id"] = variant.node_id
            self._retarget_equivalent_route_dependencies(
                base_variant,
                source_node_id=variant.node_id,
                allow_newer_revision=not bool(
                    (base_variant.metadata or {}).get("route_retarget_revision_guarded")
                ),
            )

    def _set_live_superseded_source(
        self,
        node: ProofGraphNode,
        source_node_id: str,
    ) -> None:
        source = str(source_node_id or "").strip()
        if not source:
            return
        node.metadata["superseded_source_node_id"] = source
        node.metadata["route_retarget_revision_guarded"] = True

    def ensure_helper(
        self,
        name: str,
        *,
        statement: str = "",
        phase: str = "",
        turn_index: int = 0,
        support_names: Optional[Iterable[str]] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphNode:
        helper_name = str(name or "").strip()
        if not helper_name:
            raise ValueError("helper node requires a non-empty name")
        node_id = self.helper_node_id(helper_name)
        node = self.nodes.get(node_id)
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="helper",
                name=helper_name,
                statement=str(statement or "").strip(),
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                metadata=dict(metadata or {}),
            )
            self.nodes[node_id] = node
        else:
            if statement:
                node.statement = str(statement or "").strip()
            if phase:
                node.phase = str(phase or "")
            if turn_index and not node.turn_index:
                node.turn_index = int(turn_index or 0)
            if metadata:
                node.metadata.update(dict(metadata))
        self.helper_name_to_node_id[helper_name] = node_id
        self._add_edge(self.root_node_id, node_id, "decomposes_to")
        if support_names is not None:
            self._set_supports(node, support_names, replace=True)
        self._backfill_support_edges(helper_name, node_id)
        return node

    def record_proposed_claim(
        self,
        *,
        name: str = "",
        statement: str = "",
        informal_statement: str = "",
        source: str = "",
        phase: str = "",
        turn_index: int = 0,
        claim_key: str = "",
        route_id: str = "",
        score: Optional[float] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphNode:
        """Create or refresh a first-class unverified mathematical claim."""

        claim_name = str(name or "").strip()
        incoming_metadata = dict(metadata or {})
        claim_generation_name = self._proposal_generation_name(
            node_name=claim_name,
            metadata=incoming_metadata,
            prefer_variant_name=False,
        )
        formal_statement = graph_formal_statement_text(statement)
        bind_graph_contract_identity_metadata(
            formal_statement,
            incoming_metadata,
        )
        non_theorem_reason = graph_statement_non_theorem_reason(formal_statement)
        informal = graph_identity_text(informal_statement)
        identity = (
            graph_identity_text(claim_key)
            or formal_statement
            or informal
            or claim_name
        )
        if not identity:
            raise ValueError("proposed claim requires a name or statement")
        base_node_id = self.claim_node_id(identity)
        new_statement_key = graph_statement_key(formal_statement or informal)
        superseded_prior_statement_ids: List[str] = []
        for prior in self.nodes_by_kind("proposed_claim"):
            prior_name = self._proposal_generation_name(
                node_name=prior.name,
                metadata=prior.metadata,
                prefer_variant_name=False,
            )
            if (
                claim_generation_name
                and prior_name == claim_generation_name
                and prior.node_id != base_node_id
                and not self.is_superseded_tombstone(prior)
                and (
                    prior.status != "proved"
                    or not graph_statement_key(prior.statement)
                )
                and new_statement_key
                and (
                    not graph_statement_key(prior.statement)
                    or graph_statement_key(prior.statement) == new_statement_key
                )
            ):
                self._mark_node_superseded_by_source(prior)
                superseded_prior_statement_ids.append(prior.node_id)
        existing = self.nodes.get(base_node_id)
        if (
            existing is not None
            and existing.kind == "proposed_claim"
            and not self.is_superseded_tombstone(existing)
            and existing.status != "proved"
            and graph_statement_key(existing.statement)
            and graph_statement_key(formal_statement or informal)
            and graph_statement_key(existing.statement)
            != graph_statement_key(formal_statement or informal)
        ):
            self._mark_node_superseded_by_source(existing)
            identity = "\n".join(
                [
                    graph_identity_text(identity),
                    "statement_revision",
                    graph_statement_key(formal_statement or informal)
                    or graph_text_hash(formal_statement or informal),
                ]
            )
            self.enforce_superseded_tombstones()
        allocation_identity = identity
        revival_metadata: Dict[str, Any] = {}
        identity, node_id = self._active_proposal_identity(
            allocation_identity,
            node_id_for_identity=self.claim_node_id,
            metadata=revival_metadata,
            tombstone_metadata_prefix="claim",
        )
        active_node = self.nodes.get(node_id)
        if (
            active_node is not None
            and active_node.kind == "proposed_claim"
            and active_node.status == "proved"
            and not self.is_superseded_tombstone(active_node)
            and graph_statement_key(active_node.statement)
            and new_statement_key
            and graph_statement_key(active_node.statement) != new_statement_key
        ):
            identity = "\n".join(
                [
                    graph_identity_text(allocation_identity),
                    "rejected_after_proved_claim",
                    new_statement_key,
                ]
            )
            revival_metadata = {}
            identity, node_id = self._active_proposal_identity(
                identity,
                node_id_for_identity=self.claim_node_id,
                metadata=revival_metadata,
                tombstone_metadata_prefix="claim",
            )
        while True:
            active_node = self.nodes.get(node_id)
            if not (
                active_node is not None
                and active_node.kind == "proposed_claim"
                and not self.is_superseded_tombstone(active_node)
                and active_node.status != "proved"
                and graph_statement_key(active_node.statement)
                and graph_statement_key(formal_statement or informal)
                and graph_statement_key(active_node.statement)
                != graph_statement_key(formal_statement or informal)
            ):
                break
            self._mark_node_superseded_by_source(active_node)
            self.enforce_superseded_tombstones()
            revival_metadata = {}
            identity, node_id = self._active_proposal_identity(
                allocation_identity,
                node_id_for_identity=self.claim_node_id,
                metadata=revival_metadata,
                tombstone_metadata_prefix="claim",
            )
        node_metadata: Dict[str, Any] = {
            "claim_key": graph_text_hash(identity),
            "claim_name": claim_name,
            "informal_statement": informal,
            "source_hash": graph_text_hash(source) if source else "",
            "unverified": True,
            **revival_metadata,
        }
        if non_theorem_reason:
            node_metadata.update(
                {
                    "schedulable": False,
                    "graph_statement_non_theorem": True,
                    "graph_statement_non_theorem_reason": non_theorem_reason,
                    "rejection_reason": "graph_statement_non_theorem",
                }
            )
        if score is not None:
            node_metadata["score"] = self._coerce_float(score)
        node_metadata.update(incoming_metadata)
        node = self.nodes.get(node_id)
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="proposed_claim",
                name=claim_name or f"claim_{graph_text_hash(identity)}",
                statement=formal_statement or informal,
                status="open",
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                source_hash=graph_text_hash(source) if source else "",
                metadata=node_metadata,
            )
            self.nodes[node_id] = node
        else:
            node.kind = "proposed_claim"
            if claim_name:
                node.name = claim_name
            if formal_statement or informal:
                node.statement = formal_statement or informal
            if phase:
                node.phase = str(phase or "")
            if turn_index:
                node.turn_index = int(turn_index or 0)
            if source:
                node.source_hash = graph_text_hash(source)
            node.metadata.update(node_metadata)
        if non_theorem_reason:
            _mark_non_theorem_graph_target(
                node,
                reason=non_theorem_reason,
                raw_statement=formal_statement,
            )
        base_claim_id = str(revival_metadata.get("claim_base_node_id") or "").strip()
        base_claim = self.nodes.get(base_claim_id)
        if (
            base_claim is not None
            and base_claim.node_id != node.node_id
            and self.is_superseded_tombstone(base_claim)
        ):
            self._set_live_superseded_source(base_claim, node.node_id)
            self._retarget_equivalent_route_dependencies(
                base_claim,
                source_node_id=node.node_id,
            )
        if superseded_prior_statement_ids:
            for prior_id in superseded_prior_statement_ids:
                prior = self.nodes.get(prior_id)
                if prior is not None:
                    self._set_live_superseded_source(prior, node.node_id)
                    self._retarget_equivalent_route_dependencies(
                        prior,
                        source_node_id=node.node_id,
                    )
            self.enforce_superseded_tombstones()
        self._add_edge(self.root_node_id, node.node_id, "proposes_claim")
        if route_id:
            self.attach_claim_to_route(route_id, node.node_id)
        self._repair_revived_claim_child_variants(node)
        helper = (
            None
            if non_theorem_reason
            else self._proved_helper_for_statement(
                node.statement,
                require_replayable_source=False,
                consumer_node=node,
            )
        )
        if helper is not None:
            self.mark_claim_proved_by_helper(
                node.node_id,
                helper.node_id,
                source_hash=helper.source_hash,
                proof_hash=helper.proof_hash or helper.source_hash,
            )
        if claim_generation_name and not graph_statement_key(node.statement):
            for prior in self.nodes_by_kind("proposed_claim"):
                if prior.node_id == node.node_id:
                    continue
                if self.is_superseded_tombstone(prior):
                    continue
                prior_name = self._proposal_generation_name(
                    node_name=prior.name,
                    metadata=prior.metadata,
                    prefer_variant_name=False,
                )
                if (
                    prior_name == claim_generation_name
                    and graph_statement_key(prior.statement)
                ):
                    self._mark_node_superseded_by_source(
                        node,
                        source_node_id=prior.node_id,
                    )
                    self.enforce_superseded_tombstones()
                    break
        if (
            claim_generation_name
            and new_statement_key
            and not self.is_superseded_tombstone(node)
        ):
            for prior in self.nodes_by_kind("proposed_claim"):
                if prior.node_id == node.node_id:
                    continue
                if self.is_superseded_tombstone(prior) or prior.status != "proved":
                    continue
                prior_name = self._proposal_generation_name(
                    node_name=prior.name,
                    metadata=prior.metadata,
                    prefer_variant_name=False,
                )
                if (
                    prior_name == claim_generation_name
                    and graph_statement_key(prior.statement)
                ):
                    self._mark_node_superseded_by_source(
                        node,
                        source_node_id=prior.node_id,
                    )
                    self.enforce_superseded_tombstones()
                    break
        return node

    def record_formal_variant(
        self,
        *,
        claim_node_id: str = "",
        claim_name: str = "",
        statement: str,
        variant_name: str = "",
        source: str = "",
        phase: str = "",
        turn_index: int = 0,
        variant_key: str = "",
        variant_index: Optional[int] = None,
        variant_mode: str = "",
        relation_to: str = "",
        relation_kind: str = "mutates_to",
        score: Optional[float] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphNode:
        """Record one formalization candidate for an informal/proposed claim."""

        formal_statement = graph_formal_statement_text(statement)
        if not formal_statement:
            raise ValueError("formal variant requires a statement")
        non_theorem_reason = graph_statement_non_theorem_reason(formal_statement)
        incoming_metadata = dict(metadata or {})
        bind_graph_contract_identity_metadata(
            formal_statement,
            incoming_metadata,
        )
        if variant_name and not str(incoming_metadata.get("variant_name") or "").strip():
            incoming_metadata["variant_name"] = str(variant_name or "").strip()
        if claim_name and not str(incoming_metadata.get("claim_name") or "").strip():
            incoming_metadata["claim_name"] = str(claim_name or "").strip()
        claim_id = str(claim_node_id or "").strip()
        if not claim_id:
            claim = self.record_proposed_claim(
                name=claim_name or variant_name,
                statement=formal_statement,
                source=source,
                phase=phase,
                turn_index=turn_index,
            )
            claim_id = claim.node_id
        incoming_metadata["claim_node_id"] = claim_id
        parent_claim = self.nodes.get(claim_id)
        parent_superseded = self.is_superseded_tombstone(parent_claim)
        parent_statement_key = (
            graph_statement_key(parent_claim.statement)
            if parent_claim is not None
            else ""
        )
        parent_context_statement = str(
            incoming_metadata.get("materialization_parent_statement")
            or incoming_metadata.get("formalization_bridge_parent_statement")
            or incoming_metadata.get("parent_repair_target_statement")
            or incoming_metadata.get("parent_statement")
            or incoming_metadata.get("parent_goal_statement")
            or (parent_claim.statement if parent_claim is not None else "")
            or ""
        ).strip()
        context_bare_prop_atom = _graph_statement_is_context_bare_prop_atom(
            formal_statement,
            parent_statement=parent_context_statement,
            root_statement=self.root_statement,
            metadata=incoming_metadata,
        )
        context_prop_application = _graph_statement_is_context_prop_predicate_application(
            formal_statement,
            parent_statement=parent_context_statement,
            root_statement=self.root_statement,
        )
        if context_bare_prop_atom:
            incoming_metadata.setdefault("context_bound_prop_atom", True)
            if parent_context_statement:
                incoming_metadata.setdefault(
                    "formalization_bridge_parent_statement",
                    parent_context_statement,
                )
        if context_prop_application:
            incoming_metadata.setdefault("context_bound_prop_application", True)
            if parent_context_statement:
                incoming_metadata.setdefault(
                    "formalization_bridge_parent_statement",
                    parent_context_statement,
                )
        if context_bare_prop_atom or context_prop_application:
            non_theorem_reason = ""
        if (
            not non_theorem_reason
            and not graph_statement_is_executable(formal_statement)
            and not context_bare_prop_atom
            and not context_prop_application
        ):
            non_theorem_reason = "non_executable_statement"
        parent_proved_mismatch = (
            parent_claim is not None
            and parent_claim.kind == "proposed_claim"
            and parent_claim.status == "proved"
            and bool(parent_statement_key)
            and parent_statement_key != graph_statement_key(formal_statement)
        )
        variant_identity = graph_identity_text(variant_key) or formal_statement
        base_variant_id = self.formal_variant_node_id(claim_id, variant_identity)
        new_variant_statement_key = graph_statement_key(formal_statement)
        variant_label = self._proposal_generation_name(
            node_name=str(variant_name or claim_name or "").strip(),
            metadata=incoming_metadata,
            prefer_variant_name=True,
        )
        superseded_prior_variant_statement_ids: List[str] = []
        for prior in self.nodes_by_kind("formal_variant"):
            prior_name = self._proposal_generation_name(
                node_name=prior.name,
                metadata=prior.metadata,
                prefer_variant_name=True,
            )
            if (
                variant_label
                and prior_name == variant_label
                and prior.node_id != base_variant_id
                and not parent_superseded
                and not parent_proved_mismatch
                and not self.is_superseded_tombstone(prior)
                and (
                    prior.status != "proved"
                    or not graph_statement_key(prior.statement)
                )
                and graph_statement_key(prior.statement)
                and new_variant_statement_key
                and graph_statement_key(prior.statement)
                == new_variant_statement_key
            ):
                self._mark_node_superseded_by_source(prior, source_node_id=claim_id)
                superseded_prior_variant_statement_ids.append(prior.node_id)
        revival_metadata: Dict[str, Any] = {}
        variant_identity, node_id = self._active_proposal_identity(
            variant_identity,
            node_id_for_identity=lambda key: self.formal_variant_node_id(
                claim_id, key
            ),
            metadata=revival_metadata,
            tombstone_metadata_prefix="variant",
        )
        node_metadata: Dict[str, Any] = {
            "claim_node_id": claim_id,
            "claim_name": str(claim_name or "").strip(),
            "variant_name": str(variant_name or "").strip(),
            "variant_key": graph_text_hash(variant_identity),
            "variant_mode": str(variant_mode or "").strip(),
            "source_hash": graph_text_hash(source) if source else "",
            "unverified": True,
            **revival_metadata,
        }
        if non_theorem_reason:
            node_metadata.update(
                {
                    "schedulable": False,
                    "graph_statement_non_theorem": True,
                    "graph_statement_non_theorem_reason": non_theorem_reason,
                    "rejection_reason": "graph_statement_non_theorem",
                }
            )
        if parent_superseded:
            node_metadata["proposal_superseded"] = True
            node_metadata["superseded_source_node_id"] = claim_id
        if parent_proved_mismatch:
            node_metadata["proposal_superseded"] = True
            node_metadata["superseded_source_node_id"] = claim_id
            node_metadata["superseded_active_statement_key"] = parent_statement_key
        incoming_invalid = parent_superseded or parent_proved_mismatch
        if (
            incoming_invalid
            and self.nodes.get(node_id) is not None
            and not self.is_superseded_tombstone(self.nodes.get(node_id))
        ):
            variant_identity = "\n".join(
                [
                    graph_identity_text(variant_identity),
                    "rejected_child_revision",
                    graph_statement_key(formal_statement)
                    or graph_text_hash(formal_statement),
                ]
            )
            revival_metadata = {}
            variant_identity, node_id = self._active_proposal_identity(
                variant_identity,
                node_id_for_identity=lambda key: self.formal_variant_node_id(
                    claim_id, key
                ),
                metadata=revival_metadata,
                tombstone_metadata_prefix="variant",
            )
            node_metadata.update(
                {
                    "variant_key": graph_text_hash(variant_identity),
                    **revival_metadata,
                }
            )
        active_existing = self.nodes.get(node_id)
        if (
            active_existing is not None
            and active_existing.kind == "formal_variant"
            and active_existing.status == "proved"
            and not self.is_superseded_tombstone(active_existing)
            and graph_statement_key(active_existing.statement)
            and new_variant_statement_key
            and graph_statement_key(active_existing.statement)
            != new_variant_statement_key
        ):
            variant_identity = "\n".join(
                [
                    graph_identity_text(variant_identity),
                    "rejected_after_proved_variant",
                    new_variant_statement_key,
                ]
            )
            revival_metadata = {}
            variant_identity, node_id = self._active_proposal_identity(
                variant_identity,
                node_id_for_identity=lambda key: self.formal_variant_node_id(
                    claim_id, key
                ),
                metadata=revival_metadata,
                tombstone_metadata_prefix="variant",
            )
            node_metadata.update(
                {
                    "variant_key": graph_text_hash(variant_identity),
                    **revival_metadata,
                }
            )
        allocation_variant_identity = variant_identity
        existing_variant = self.nodes.get(base_variant_id)
        if (
            existing_variant is not None
            and existing_variant.kind == "formal_variant"
            and not incoming_invalid
            and not self.is_superseded_tombstone(existing_variant)
            and existing_variant.status != "proved"
            and graph_statement_key(existing_variant.statement)
            and graph_statement_key(formal_statement)
            and graph_statement_key(existing_variant.statement)
            != graph_statement_key(formal_statement)
        ):
            self._mark_node_superseded_by_source(
                existing_variant,
                source_node_id=claim_id,
            )
            variant_identity = "\n".join(
                [
                    graph_identity_text(variant_identity),
                    "statement_revision",
                    graph_statement_key(formal_statement)
                    or graph_text_hash(formal_statement),
                ]
            )
            revival_metadata = {}
            variant_identity, node_id = self._active_proposal_identity(
                allocation_variant_identity,
                node_id_for_identity=lambda key: self.formal_variant_node_id(
                    claim_id, key
                ),
                metadata=revival_metadata,
                tombstone_metadata_prefix="variant",
            )
            node_metadata.update(
                {
                    "variant_key": graph_text_hash(variant_identity),
                    **revival_metadata,
                }
            )
            self.enforce_superseded_tombstones()
        while True:
            active_variant = self.nodes.get(node_id)
            if not (
                active_variant is not None
                and active_variant.kind == "formal_variant"
                and not incoming_invalid
                and not self.is_superseded_tombstone(active_variant)
                and active_variant.status != "proved"
                and graph_statement_key(active_variant.statement)
                and graph_statement_key(formal_statement)
                and graph_statement_key(active_variant.statement)
                != graph_statement_key(formal_statement)
            ):
                break
            self._mark_node_superseded_by_source(
                active_variant,
                source_node_id=claim_id,
            )
            self.enforce_superseded_tombstones()
            revival_metadata = {}
            variant_identity, node_id = self._active_proposal_identity(
                allocation_variant_identity,
                node_id_for_identity=lambda key: self.formal_variant_node_id(
                    claim_id, key
                ),
                metadata=revival_metadata,
                tombstone_metadata_prefix="variant",
            )
            node_metadata.update(
                {
                    "variant_key": graph_text_hash(variant_identity),
                    **revival_metadata,
                }
            )
        if variant_index is not None:
            node_metadata["variant_index"] = int(variant_index or 0)
        if score is not None:
            node_metadata["score"] = self._coerce_float(score)
        node_metadata.update(incoming_metadata)
        node = self.nodes.get(node_id)
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="formal_variant",
                name=str(variant_name or "").strip()
                or f"variant_{graph_text_hash(variant_identity)}",
                statement=formal_statement,
                status="open",
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                source_hash=graph_text_hash(source) if source else "",
                metadata=node_metadata,
            )
            self.nodes[node_id] = node
        else:
            node.kind = "formal_variant"
            if variant_name:
                node.name = str(variant_name or "").strip()
            node.statement = formal_statement
            if phase:
                node.phase = str(phase or "")
            if turn_index:
                node.turn_index = int(turn_index or 0)
            if source:
                node.source_hash = graph_text_hash(source)
            node.metadata.update(node_metadata)
        if non_theorem_reason:
            _mark_non_theorem_graph_target(
                node,
                reason=non_theorem_reason,
                raw_statement=formal_statement,
            )
        base_variant_id = str(revival_metadata.get("variant_base_node_id") or "").strip()
        base_variant = self.nodes.get(base_variant_id)
        if (
            base_variant is not None
            and base_variant.node_id != node.node_id
            and self.is_superseded_tombstone(base_variant)
        ):
            self._set_live_superseded_source(base_variant, node.node_id)
            self._retarget_equivalent_route_dependencies(
                base_variant,
                source_node_id=node.node_id,
            )
        if superseded_prior_variant_statement_ids:
            for prior_id in superseded_prior_variant_statement_ids:
                prior = self.nodes.get(prior_id)
                if prior is not None:
                    self._retarget_equivalent_route_dependencies(
                        prior,
                        source_node_id=node.node_id,
                    )
                    self._set_live_superseded_source(prior, node.node_id)
            self.enforce_superseded_tombstones()
        self._add_edge(claim_id, node.node_id, "claim_formalized_as")
        if relation_to:
            self.add_variant_relation(relation_to, node.node_id, relation_kind)
        if parent_superseded or parent_proved_mismatch:
            self._mark_node_superseded_by_source(node, source_node_id=claim_id)
        self._repair_revision_crossing_tombstones(cascade_all=True)
        if (
            variant_label
            and new_variant_statement_key
            and not self.is_superseded_tombstone(node)
        ):
            for prior in self.nodes_by_kind("formal_variant"):
                if prior.node_id == node.node_id:
                    continue
                if self.is_superseded_tombstone(prior) or prior.status != "proved":
                    continue
                prior_name = self._proposal_generation_name(
                    node_name=prior.name,
                    metadata=prior.metadata,
                    prefer_variant_name=True,
                )
                if (
                    prior_name == variant_label
                    and graph_statement_key(prior.statement)
                    and graph_statement_key(prior.statement)
                    == new_variant_statement_key
                ):
                    self._mark_node_superseded_by_source(
                        node,
                        source_node_id=prior.node_id,
                    )
                    self.enforce_superseded_tombstones()
                    break
        self._repair_revision_crossing_tombstones()
        helper = (
            None
            if non_theorem_reason
            else self._proved_helper_for_statement(
                node.statement,
                require_replayable_source=False,
                consumer_node=node,
            )
        )
        if helper is not None:
            self.mark_variant_proved_by_helper(
                node.node_id,
                helper.node_id,
                source_hash=helper.source_hash,
                proof_hash=helper.proof_hash or helper.source_hash,
            )
        return node

    def record_strategy_route(
        self,
        *,
        name: str = "",
        description: str = "",
        route_key: str = "",
        score: float = 0.0,
        phase: str = "",
        turn_index: int = 0,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphNode:
        """Record a scored proof-strategy alternative in the graph."""

        route_name = str(name or "").strip()
        route_text = graph_identity_text(description)
        identity = graph_identity_text(route_key) or route_text or route_name
        if not identity:
            raise ValueError("strategy route requires a name or description")
        node_id = self.strategy_route_node_id(identity)
        incoming_metadata = dict(metadata or {})
        node = self.nodes.get(node_id)
        # New live routes are explicit. Legacy serialized routes lack this
        # marker, allowing projection to distinguish history from current work.
        if node is not None and bool(
            (node.metadata or {}).get("route_retired")
            or (node.metadata or {}).get("route_dependency_contradicted")
            or (node.metadata or {}).get("activation_status") == "archived"
        ):
            incoming_metadata["activation_status"] = "archived"
        else:
            incoming_metadata.setdefault("activation_status", "active")
        route_scope = str(incoming_metadata.get("route_scope") or "").strip()
        incoming_contract = incoming_metadata.get(_ROUTE_ASSEMBLY_CONTRACT_KEY)
        if not route_scope and isinstance(incoming_contract, dict):
            route_scope = str(incoming_contract.get("scope") or "").strip()
        if not route_scope:
            route_scope = _ROUTE_SCOPE_PARTIAL
        node_metadata: Dict[str, Any] = {
            "route_key": graph_text_hash(identity),
            "route_scope": route_scope,
            "score": self._coerce_float(score),
            "base_score": self._coerce_float(score),
        }
        node_metadata.update(incoming_metadata)
        node_metadata["route_scope"] = route_scope
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="strategy_route",
                name=route_name or f"route_{graph_text_hash(identity)}",
                statement=route_text,
                status="open",
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                metadata=node_metadata,
            )
            self.nodes[node_id] = node
        else:
            node.kind = "strategy_route"
            if route_name:
                node.name = route_name
            if route_text:
                node.statement = route_text
            if phase:
                node.phase = str(phase or "")
            if turn_index:
                node.turn_index = int(turn_index or 0)
            node.metadata.update(node_metadata)
        self._add_edge(self.root_node_id, node.node_id, "has_route")
        return node

    def attach_claim_to_route(
        self,
        route_id: str,
        claim_node_id: str,
        *,
        edge_kind: str = "route_requires",
    ) -> None:
        route = str(route_id or "").strip()
        claim = str(claim_node_id or "").strip()
        if route and claim:
            self._add_edge(route, claim, str(edge_kind or "route_requires"))

    @staticmethod
    def branch_frame_id(
        route_id: str,
        case_node_id: str,
        branch_index: int,
        assumption_key: str,
    ) -> str:
        identity = "\n".join(
            [
                str(route_id or "").strip(),
                str(case_node_id or "").strip(),
                str(max(0, int(branch_index or 0))),
                str(assumption_key or "").strip(),
            ]
        )
        return f"branch_frame:{graph_text_hash(identity)}"

    def route_branch_frames(self, route_id: str) -> List[ProofGraphBranchFrame]:
        clean_route_id = str(route_id or "").strip()
        frames = [
            frame
            for frame in self.branch_frames.values()
            if frame.route_id == clean_route_id
        ]
        return sorted(frames, key=lambda frame: (frame.case_node_id, frame.branch_index))

    def _replace_route_branch_frames(
        self,
        route_id: str,
        frames: Iterable[ProofGraphBranchFrame],
    ) -> List[ProofGraphBranchFrame]:
        """Replace persisted branch scopes for ``route_id`` idempotently."""

        clean_route_id = str(route_id or "").strip()
        if not clean_route_id:
            return []
        cleaned: Dict[str, ProofGraphBranchFrame] = {}
        for frame in list(frames or []):
            if not isinstance(frame, ProofGraphBranchFrame):
                continue
            if frame.route_id != clean_route_id or not frame.frame_id:
                continue
            cleaned[frame.frame_id] = frame
        for frame_id, frame in list(self.branch_frames.items()):
            if frame.route_id == clean_route_id and frame_id not in cleaned:
                self.branch_frames.pop(frame_id, None)
        self.branch_frames.update(cleaned)
        return self.route_branch_frames(clean_route_id)

    def refresh_route_branch_frames(self) -> None:
        """Synchronize branch-frame records with current route contracts."""

        live_route_ids = {
            route.node_id
            for route in self.nodes_by_kind("strategy_route")
            if str(route.node_id or "").strip()
        }
        for frame_id, frame in list(self.branch_frames.items()):
            if frame.route_id not in live_route_ids:
                self.branch_frames.pop(frame_id, None)
        for route_id in sorted(live_route_ids):
            try:
                self.route_assembly_contract_status(route_id)
            except Exception:
                self._replace_route_branch_frames(route_id, [])

    @staticmethod
    def _node_helper_name(node: Optional[ProofGraphNode]) -> str:
        if node is None:
            return ""
        if node.kind == "helper":
            return str(node.name or "").strip()
        metadata = dict(node.metadata or {})
        for key in (
            "verified_by_helper_name",
            "resolved_by_helper_name",
            "helper_name",
        ):
            value = str(metadata.get(key) or "").strip()
            if value:
                return value
        return ""

    def _remove_route_dependency_edges(
        self,
        route_id: str,
        target_node_id: str,
    ) -> bool:
        route = str(route_id or "").strip()
        target = str(target_node_id or "").strip()
        if not route or not target:
            return False
        before = len(self.edges)
        self.edges = [
            edge
            for edge in self.edges
            if not (
                edge.source == route
                and edge.target == target
                and edge.kind in _ROUTE_DEPENDENCY_EDGE_KINDS
            )
        ]
        if len(self.edges) == before:
            return False
        self._rebuild_edge_index()
        return True

    @staticmethod
    def _route_target_statement_key(statement: str) -> str:
        target = graph_formal_statement_text(str(statement or ""))
        key = graph_statement_key(target)
        if key:
            return key
        return graph_text_hash(graph_identity_text(target)) if target else ""

    def set_route_assembly_contract(
        self,
        route_id: str,
        *,
        required_node_ids: Iterable[str],
        required_helper_names: Iterable[str] = (),
        required_helper_source_hashes: Optional[Mapping[str, str]] = None,
        target_statement: str = "",
        scope: str = _ROUTE_SCOPE_ROOT_ASSEMBLY,
        phase: str = "",
        turn_index: int = 0,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """Declare the complete obligations needed before a route may close root."""

        clean_route_id = str(route_id or "").strip()
        route = self.nodes.get(clean_route_id)
        if route is None or route.kind != "strategy_route":
            raise ValueError("route assembly contract requires a strategy_route")
        stale_replan_ids = {
            str((route.metadata or {}).get("route_assembly_contract_replan_id") or "").strip(),
            str(
                (route.metadata or {}).get(
                    "route_assembly_contract_replan_obligation_id"
                )
                or ""
            ).strip(),
        }
        stale_replan_ids.discard("")
        if stale_replan_ids:
            self.edges = [
                edge
                for edge in self.edges
                if not (
                    (edge.source == clean_route_id and edge.target in stale_replan_ids)
                    or (edge.source in stale_replan_ids and edge.target in stale_replan_ids)
                    or (edge.source in stale_replan_ids and edge.target == clean_route_id)
                )
            ]
            self._rebuild_edge_index()
            for stale_id in stale_replan_ids:
                stale_node = self.nodes.get(stale_id)
                if stale_node is not None:
                    stale_node.status = "rejected"
                    stale_node.metadata["route_assembly_contract_replan_obsolete"] = True
            route.metadata.pop("route_assembly_contract_replan_id", None)
            route.metadata.pop("route_assembly_contract_replan_obligation_id", None)
        required_ids: List[str] = []
        for raw_id in list(required_node_ids or ()):
            node_id = str(raw_id or "").strip()
            if node_id and node_id not in required_ids:
                required_ids.append(node_id)
        required_names: List[str] = []
        unresolved_required_names: List[str] = []
        for raw_name in list(required_helper_names or ()):
            helper_name = str(raw_name or "").strip()
            if not helper_name or helper_name in required_names:
                continue
            required_names.append(helper_name)
            helper_id = self.helper_name_to_node_id.get(helper_name)
            if helper_id:
                if helper_id not in required_ids:
                    required_ids.append(helper_id)
            else:
                unresolved_required_names.append(helper_name)
        scope_text = str(scope or _ROUTE_SCOPE_ROOT_ASSEMBLY).strip()
        if not scope_text:
            scope_text = _ROUTE_SCOPE_ROOT_ASSEMBLY
        target = str(target_statement or self.root_statement or "").strip()
        contract: Dict[str, Any] = {
            "scope": scope_text,
            "target_node_id": self.root_node_id
            if scope_text == _ROUTE_SCOPE_ROOT_ASSEMBLY
            else "",
            "target_statement": target,
            "target_statement_key": self._route_target_statement_key(target),
            "required_node_ids": list(required_ids),
            "required_helper_names": list(required_names),
            "required_helper_source_hashes": {
                str(name or "").strip(): str(source_hash or "").strip()
                for name, source_hash in dict(
                    required_helper_source_hashes or {}
                ).items()
                if str(name or "").strip() in required_names
                and str(source_hash or "").strip()
            },
            "required_obligation_count": (
                len(required_ids) + len(unresolved_required_names)
            ),
            "phase": str(phase or route.phase or ""),
            "turn_index": int(turn_index or route.turn_index or 0),
        }
        extra = dict(metadata or {})
        if extra:
            contract["metadata"] = extra
        route.metadata["route_scope"] = scope_text
        route.metadata[_ROUTE_ASSEMBLY_CONTRACT_KEY] = contract
        route.metadata.pop("route_assembly_contract_last_verdict", None)
        route.metadata.pop("route_assembly_contract_missing_node_ids", None)
        route.metadata.pop("route_assembly_contract_unproved_node_ids", None)
        # Drop dependency edges to targets that are no longer required.  The
        # setter previously only ADDED edges, so shrinking or replacing a
        # contract on the same route left stale route_requires/route_blocked_by
        # edges — which the status check then flags as
        # route_dependency_not_in_contract.  (retarget_route_assembly_contract_
        # requirement already unwinds edges via _remove_route_dependency_edges.)
        required_id_set = set(required_ids)
        stale_dependency_targets = {
            str(edge.target or "").strip()
            for edge in self._route_dependency_edges(clean_route_id)
            if str(edge.target or "").strip()
            and str(edge.target or "").strip() not in required_id_set
        }
        for stale_target in stale_dependency_targets:
            self._remove_route_dependency_edges(clean_route_id, stale_target)
        for node_id in required_ids:
            self.attach_claim_to_route(clean_route_id, node_id)
        return dict(contract)

    def route_assembly_contract_status(
        self,
        route_id: str,
        *,
        target_statement: str = "",
        mutate: bool = True,
    ) -> Dict[str, Any]:
        """Return whether a strategy route has a complete root assembly contract."""

        clean_route_id = str(route_id or "").strip()
        route = self.nodes.get(clean_route_id)
        route_metadata = dict(getattr(route, "metadata", {}) or {}) if route else {}
        internal_contract_replan_ids = {
            str(route_metadata.get("route_assembly_contract_replan_id") or "").strip(),
            str(
                route_metadata.get("route_assembly_contract_replan_obligation_id")
                or ""
            ).strip(),
        }
        internal_contract_replan_ids.discard("")
        dependency_node_ids = [
            edge.target
            for edge in self._route_dependency_edges(clean_route_id)
            if edge.target not in internal_contract_replan_ids
        ]
        dependency_node_ids = list(dict.fromkeys(dependency_node_ids))
        def invalid_status(payload: Dict[str, Any]) -> Dict[str, Any]:
            if mutate:
                self._replace_route_branch_frames(clean_route_id, [])
            return payload

        if route is None or route.kind != "strategy_route":
            return invalid_status({
                "ready": False,
                "verdict": "missing_strategy_route",
                "route_id": clean_route_id,
                "dependency_node_ids": dependency_node_ids,
            })
        metadata = dict(route.metadata or {})
        route_status = str(getattr(route, "status", "") or "").strip()
        route_status_is_retryable = (
            route_status == "rejected"
            and not bool(
                metadata.get("route_retired")
                or metadata.get("route_dependency_contradicted")
            )
            and self.node_has_new_rejection_evidence(route)
        )
        if (route_status in _ROUTE_RETIRED_STATUSES and not route_status_is_retryable) or bool(
            metadata.get("route_retired")
            or metadata.get("route_dependency_contradicted")
            or metadata.get("proposal_invalidated")
        ):
            return invalid_status({
                "ready": False,
                "verdict": str(
                    metadata.get("route_retirement_verdict")
                    or metadata.get("route_retired_verdict")
                    or "route_retired"
                ),
                "route_id": clean_route_id,
                "route_status": route_status,
                "route_scope": str(metadata.get("route_scope") or "").strip(),
                "retirement_reason": str(
                    metadata.get("route_retired_reason")
                    or metadata.get("invalid_reason")
                    or ""
                ),
                "retired_dependency_node_id": str(
                    metadata.get("route_retired_dependency_node_id") or ""
                ),
                "dependency_node_ids": dependency_node_ids,
            })
        route_scope = str(metadata.get("route_scope") or "").strip()
        contract = metadata.get(_ROUTE_ASSEMBLY_CONTRACT_KEY)
        if not isinstance(contract, dict):
            return invalid_status({
                "ready": False,
                "verdict": "missing_route_assembly_contract",
                "route_id": clean_route_id,
                "route_scope": route_scope or "unscoped",
                "dependency_node_ids": dependency_node_ids,
            })
        contract_scope = str(contract.get("scope") or "").strip()
        effective_scope = contract_scope or route_scope
        if not route_scope:
            return invalid_status({
                "ready": False,
                "verdict": "route_scope_missing",
                "route_id": clean_route_id,
                "contract_scope": contract_scope,
                "dependency_node_ids": dependency_node_ids,
            })
        if not contract_scope:
            return invalid_status({
                "ready": False,
                "verdict": "route_contract_scope_missing",
                "route_id": clean_route_id,
                "route_scope": route_scope,
                "dependency_node_ids": dependency_node_ids,
            })
        if route_scope != contract_scope:
            return invalid_status({
                "ready": False,
                "verdict": "route_scope_contract_mismatch",
                "route_id": clean_route_id,
                "route_scope": route_scope,
                "contract_scope": contract_scope,
                "dependency_node_ids": dependency_node_ids,
            })
        if effective_scope != _ROUTE_SCOPE_ROOT_ASSEMBLY:
            return invalid_status({
                "ready": False,
                "verdict": "route_scope_not_root_assembly",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "dependency_node_ids": dependency_node_ids,
            })
        expected_target = str(target_statement or self.root_statement or "").strip()
        target_forall_arity = _graph_forall_explicit_arity(expected_target)
        expected_target_key = self._route_target_statement_key(expected_target)
        if metadata.get("source_phase") == "mini_recursive_route_contract":
            accepted_claims = [
                dict(item)
                for item in list(metadata.get("accepted_claims") or [])
                if isinstance(item, dict)
            ]
            root_assembly_claim_names = {
                str(name or "").strip()
                for name in list(metadata.get("root_assembly_claim_names") or [])
                if str(name or "").strip()
            }
            root_contract_identity = str(
                metadata.get("root_contract_identity") or ""
            ).strip()
            root_environment_hash = str(
                metadata.get("root_contract_identity_environment_hash") or ""
            ).strip()
            root_statement_key = str(
                metadata.get("root_contract_identity_statement_key") or ""
            ).strip()
            root_evidence_receipt = str(
                metadata.get("root_contract_identity_evidence_receipt") or ""
            ).strip()
            bound_root_identity = bool(
                has_lean_contract_identity(root_contract_identity)
                and root_statement_key
                and root_statement_key == expected_target_key
                and lean_contract_evidence_receipt_matches(
                    root_evidence_receipt,
                    identity=root_contract_identity,
                    statement_key=root_statement_key,
                    environment_hash=root_environment_hash,
                )
            )
            root_identity_evidence_present = any(
                str(metadata.get(field) or "").strip()
                for field in (
                    "root_contract_identity",
                    "root_contract_identity_statement_key",
                    "root_contract_identity_environment_hash",
                    "root_contract_identity_evidence_receipt",
                )
            )
            if root_identity_evidence_present and not bound_root_identity:
                return invalid_status({
                    "ready": False,
                    "verdict": "mini_recursive_route_contract_invalid_root_identity",
                    "route_id": clean_route_id,
                    "route_scope": effective_scope,
                    "dependency_node_ids": dependency_node_ids,
                })
            route_anchor_identities: Set[str] = set()
            route_anchor_statement_keys: Set[str] = set()
            invalid_route_anchor = False
            route_anchors_present = "route_anchor_contracts" in metadata
            raw_route_anchors = metadata.get("route_anchor_contracts")
            if not route_anchors_present:
                raw_route_anchors = []
            if not isinstance(raw_route_anchors, Sequence) or isinstance(
                raw_route_anchors,
                (str, bytes),
            ):
                raw_route_anchors = []
                invalid_route_anchor = True
            for anchor in list(raw_route_anchors):
                if not isinstance(anchor, Mapping):
                    invalid_route_anchor = True
                    continue
                anchor_identity = str(
                    anchor.get("contract_identity") or ""
                ).strip()
                anchor_statement_key = str(
                    anchor.get("contract_identity_statement_key") or ""
                ).strip()
                anchor_environment_hash = str(
                    anchor.get("contract_identity_environment_hash") or ""
                ).strip()
                if (
                    has_lean_contract_identity(anchor_identity)
                    and anchor_statement_key
                    == self._route_target_statement_key(
                        str(anchor.get("statement") or "").strip()
                    )
                    and anchor_environment_hash == root_environment_hash
                    and lean_contract_evidence_receipt_matches(
                        str(anchor.get("contract_identity_evidence_receipt") or ""),
                        identity=anchor_identity,
                        statement_key=anchor_statement_key,
                        environment_hash=anchor_environment_hash,
                    )
                ):
                    route_anchor_identities.add(anchor_identity)
                    route_anchor_statement_keys.add(anchor_statement_key)
                else:
                    invalid_route_anchor = True
            if invalid_route_anchor:
                return invalid_status({
                    "ready": False,
                    "verdict": "mini_recursive_route_contract_invalid_anchor_evidence",
                    "route_id": clean_route_id,
                    "route_scope": effective_scope,
                    "dependency_node_ids": dependency_node_ids,
                })
            current_anchor_identities = set(
                self.active_root_target_contract_identities
            )
            current_anchor_statement_keys = {
                self._route_target_statement_key(statement)
                for statement in self.active_root_target_statements
                if self._route_target_statement_key(statement)
            }
            if self.active_root_target_universe_observed and (
                (
                    route_anchor_statement_keys
                    and route_anchor_statement_keys != current_anchor_statement_keys
                )
                or (
                    route_anchor_identities
                    and route_anchor_identities != current_anchor_identities
                )
            ):
                return invalid_status({
                    "ready": False,
                    "verdict": "mini_recursive_route_contract_stale_anchor_universe",
                    "route_id": clean_route_id,
                    "route_scope": effective_scope,
                    "dependency_node_ids": dependency_node_ids,
                })

            def relation_anchor(item: Mapping[str, Any]) -> str:
                claim_identity = str(item.get("contract_identity") or "").strip()
                claim_statement_key = str(
                    item.get("contract_identity_statement_key") or ""
                ).strip()
                claim_environment_hash = str(
                    item.get("contract_identity_environment_hash") or ""
                ).strip()
                claim_receipt = str(
                    item.get("contract_identity_evidence_receipt") or ""
                ).strip()
                kind = str(
                    item.get("contract_route_relation_kind") or ""
                ).strip().lower()
                anchor_identity = str(
                    item.get("contract_route_relation_anchor_identity") or ""
                ).strip()
                relation_receipt = str(
                    item.get("contract_route_relation_evidence_receipt") or ""
                ).strip()
                if (
                    not bound_root_identity
                    or not has_lean_contract_identity(claim_identity)
                    or claim_statement_key
                    != self._route_target_statement_key(
                        str(item.get("statement") or "").strip()
                    )
                    or kind not in {"exact", "profile"}
                    or anchor_identity
                    not in {root_contract_identity, *route_anchor_identities}
                    or claim_environment_hash != root_environment_hash
                    or not lean_contract_evidence_receipt_matches(
                        claim_receipt,
                        identity=claim_identity,
                        statement_key=claim_statement_key,
                        environment_hash=claim_environment_hash,
                    )
                ):
                    return ""
                expected_receipt = (
                    "lean-contract-route-relation-v1:"
                    + graph_text_hash(
                        json.dumps(
                            {
                                "anchor_identity": anchor_identity,
                                "claim_evidence_receipt": claim_receipt,
                                "environment_hash": claim_environment_hash,
                                "kind": kind,
                            },
                            sort_keys=True,
                            separators=(",", ":"),
                            ensure_ascii=True,
                        )
                    )
                )
                return (
                    anchor_identity
                    if relation_receipt
                    and hmac.compare_digest(relation_receipt, expected_receipt)
                    else ""
                )

            def is_root_terminal_claim(item: Mapping[str, Any]) -> bool:
                name = str(
                    item.get("name") or item.get("claim_name") or ""
                ).strip()
                statement = str(item.get("statement") or "").strip()
                if not name or not statement:
                    return False
                claim_identity_evidence_present = any(
                    str(item.get(field) or "").strip()
                    for field in (
                        "contract_identity",
                        "contract_identity_statement_key",
                        "contract_identity_environment_hash",
                        "contract_identity_evidence_receipt",
                    )
                )
                claim_identity = str(item.get("contract_identity") or "").strip()
                claim_statement_key = str(
                    item.get("contract_identity_statement_key") or ""
                ).strip()
                claim_environment_hash = str(
                    item.get("contract_identity_environment_hash") or ""
                ).strip()
                if (
                    bound_root_identity
                    and has_lean_contract_identity(claim_identity)
                    and claim_identity != root_contract_identity
                    and not relation_anchor(item)
                ):
                    return False
                bound_claim_identity = bool(
                    has_lean_contract_identity(claim_identity)
                    and claim_statement_key
                    == self._route_target_statement_key(statement)
                    and claim_environment_hash == root_environment_hash
                    and lean_contract_evidence_receipt_matches(
                        str(
                            item.get("contract_identity_evidence_receipt") or ""
                        ),
                        identity=claim_identity,
                        statement_key=claim_statement_key,
                        environment_hash=claim_environment_hash,
                    )
                )
                if claim_identity_evidence_present and not bound_claim_identity:
                    return False
                if relation_anchor(item):
                    return True
                if any(
                    str(item.get(field) or "").strip()
                    for field in (
                        "contract_route_relation_kind",
                        "contract_route_relation_anchor_identity",
                        "contract_route_relation_evidence_receipt",
                    )
                ):
                    return False
                return bool(
                    graph_statement_root_equivalent(
                        statement,
                        expected_target,
                        active_target_statements=(expected_target,),
                    )
                    or graph_statement_is_root_bridge(statement, expected_target)
                )

            if not root_assembly_claim_names:
                root_assembly_claim_names = {
                    str(
                        item.get("name") or item.get("claim_name") or ""
                    ).strip()
                    for item in accepted_claims
                    if is_root_terminal_claim(item)
                }
            terminal_claims = [
                item
                for item in accepted_claims
                if str(item.get("name") or item.get("claim_name") or "").strip()
                in root_assembly_claim_names
                and is_root_terminal_claim(item)
            ]
            if terminal_claims:
                def terminal_order(item: Mapping[str, Any]) -> tuple[int, int]:
                    position = accepted_claims.index(item)
                    try:
                        selected = int(item.get("selected_index", position + 1))
                    except (TypeError, ValueError):
                        selected = position + 1
                    return selected, position

                terminal_claims = [min(terminal_claims, key=terminal_order)]
                root_assembly_claim_names = {
                    str(
                        terminal_claims[0].get("name")
                        or terminal_claims[0].get("claim_name")
                        or ""
                    ).strip()
                }
            terminal_relation_anchors = {
                relation_anchor(item) for item in terminal_claims
            }
            terminal_relation_anchors.discard("")
            if (
                not root_assembly_claim_names
                or not terminal_claims
                or (
                    route_anchor_identities
                    and root_contract_identity not in terminal_relation_anchors
                    and not route_anchor_identities.issubset(
                        terminal_relation_anchors
                    )
                )
            ):
                return invalid_status({
                    "ready": False,
                    "verdict": "mini_recursive_route_contract_missing_root_terminal",
                    "route_id": clean_route_id,
                    "route_scope": effective_scope,
                    "dependency_node_ids": dependency_node_ids,
                })
        expected_target_node_id = self.root_node_id
        contract_target_node_id = str(contract.get("target_node_id") or "").strip()
        if not contract_target_node_id:
            return invalid_status({
                "ready": False,
                "verdict": "route_assembly_contract_missing_target_node",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "target_node_id": expected_target_node_id,
                "dependency_node_ids": dependency_node_ids,
            })
        if contract_target_node_id != expected_target_node_id:
            return invalid_status({
                "ready": False,
                "verdict": "route_assembly_contract_target_node_mismatch",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "target_node_id": expected_target_node_id,
                "contract_target_node_id": contract_target_node_id,
                "dependency_node_ids": dependency_node_ids,
            })
        contract_target_key = str(contract.get("target_statement_key") or "").strip()
        if not contract_target_key:
            return invalid_status({
                "ready": False,
                "verdict": "route_assembly_contract_missing_target",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "dependency_node_ids": dependency_node_ids,
            })
        if expected_target_key and contract_target_key != expected_target_key:
            return invalid_status({
                "ready": False,
                "verdict": "route_assembly_target_mismatch",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "target_statement_key": expected_target_key,
                "contract_target_statement_key": contract_target_key,
                "dependency_node_ids": dependency_node_ids,
            })
        required_node_ids: List[str] = []
        for raw_id in list(contract.get("required_node_ids") or []):
            node_id = str(raw_id or "").strip()
            if node_id and node_id not in required_node_ids:
                required_node_ids.append(node_id)
        missing_helper_names: List[str] = []
        raw_required_helper_names = [
            str(raw_name or "").strip()
            for raw_name in list(contract.get("required_helper_names") or [])
            if str(raw_name or "").strip()
        ]
        for helper_name in raw_required_helper_names:
            helper_id = self.helper_name_to_node_id.get(helper_name)
            if helper_id:
                if helper_id not in required_node_ids:
                    required_node_ids.append(helper_id)
            elif helper_name not in missing_helper_names:
                missing_helper_names.append(helper_name)
        required_helper_source_hashes = {
            str(name or "").strip(): str(source_hash or "").strip()
            for name, source_hash in dict(
                contract.get("required_helper_source_hashes") or {}
            ).items()
            if str(name or "").strip() and str(source_hash or "").strip()
        }
        helper_source_mismatches: List[Dict[str, str]] = []
        for helper_name, expected_hash in required_helper_source_hashes.items():
            helper_id = self.helper_name_to_node_id.get(helper_name)
            helper = self.nodes.get(helper_id or "")
            actual_hash = str(getattr(helper, "source_hash", "") or "").strip()
            if helper is not None and actual_hash != expected_hash:
                helper_source_mismatches.append(
                    {
                        "helper_name": helper_name,
                        "expected_source_hash": expected_hash,
                        "actual_source_hash": actual_hash,
                    }
                )
        if helper_source_mismatches:
            return invalid_status({
                "ready": False,
                "verdict": "route_assembly_contract_helper_source_mismatch",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "dependency_node_ids": dependency_node_ids,
                "helper_source_mismatches": helper_source_mismatches,
            })
        if "required_obligation_count" in contract:
            try:
                required_count = int(contract.get("required_obligation_count") or 0)
            except (TypeError, ValueError):
                required_count = -1
            declared_items = set(required_node_ids) | {
                f"helper:{name}" for name in missing_helper_names
            }
            if required_count != len(declared_items):
                return invalid_status({
                    "ready": False,
                    "verdict": "route_assembly_contract_count_mismatch",
                    "route_id": clean_route_id,
                    "route_scope": effective_scope,
                    "dependency_node_ids": dependency_node_ids,
                    "required_node_ids": required_node_ids,
                    "missing_helper_names": missing_helper_names,
                    "required_obligation_count": required_count,
                    "declared_obligation_count": len(declared_items),
                })
        if not required_node_ids and not missing_helper_names:
            return invalid_status({
                "ready": False,
                "verdict": "empty_route_assembly_contract",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "dependency_node_ids": dependency_node_ids,
            })
        missing_dependency_edge_node_ids = [
            node_id
            for node_id in required_node_ids
            if node_id not in dependency_node_ids
        ]
        if missing_dependency_edge_node_ids:
            return invalid_status({
                "ready": False,
                "verdict": "route_assembly_contract_missing_dependency_edges",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "dependency_node_ids": dependency_node_ids,
                "required_node_ids": required_node_ids,
                "missing_dependency_edge_node_ids": missing_dependency_edge_node_ids,
            })
        uncontracted_dependency_ids = [
            node_id
            for node_id in dependency_node_ids
            if node_id not in required_node_ids
            # A PROVED uncontracted dependency (e.g. an ordinary obligation
            # recorded via record_missing_obligation(route_id=) on a contracted
            # route, then proved) is satisfied and cannot threaten readiness —
            # only an OPEN undeclared dependency is a closed-world violation.
            # This makes proving the obligation restore readiness instead of
            # requiring the contract to be expanded.
            and str(getattr(self.nodes.get(node_id), "status", "") or "")
            != "proved"
        ]
        if uncontracted_dependency_ids:
            return invalid_status({
                "ready": False,
                "verdict": "route_dependency_not_in_contract",
                "route_id": clean_route_id,
                "route_scope": effective_scope,
                "dependency_node_ids": dependency_node_ids,
                "required_node_ids": required_node_ids,
                "uncontracted_dependency_node_ids": uncontracted_dependency_ids,
            })
        all_required_ids = list(dict.fromkeys(required_node_ids + dependency_node_ids))
        missing_node_ids: List[str] = []
        unproved_node_ids: List[str] = []
        assembly_bridge_node_ids: List[str] = []
        candidate_assembly_bridge_node_ids: List[str] = []
        proved_nodes: Dict[str, ProofGraphNode] = {}
        contract_metadata = dict(contract.get("metadata") or {})

        def recorded_formalization_bridge_support(
            node: Optional[ProofGraphNode],
        ) -> bool:
            if node is None:
                return False
            if contract_metadata.get("source") != "formalization_bridge_support":
                return False
            if (
                str(contract_metadata.get("bridge_helper_node_id") or "").strip()
                != node.node_id
            ):
                return False
            obligation_id = str(
                contract_metadata.get("obligation_id") or ""
            ).strip()
            obligation = self.nodes.get(obligation_id)
            if obligation is None:
                return False
            obligation_metadata = (
                obligation.metadata if isinstance(obligation.metadata, dict) else {}
            )
            supports = [
                item
                for item in list(
                    obligation_metadata.get("formalization_bridge_supports") or []
                )
                if isinstance(item, dict)
            ]
            node_statement_key = graph_statement_key(str(node.statement or ""))
            for item in supports:
                if (
                    str(item.get("helper_node_id") or "").strip()
                    != node.node_id
                ):
                    continue
                support_statement = str(item.get("statement") or "").strip()
                support_statement_key = graph_statement_key(support_statement)
                if not support_statement or not support_statement_key:
                    continue
                if (
                    not node_statement_key
                    or node_statement_key != support_statement_key
                ):
                    continue
                support_hash = str(item.get("source_hash") or "").strip()
                accepted_hashes = {
                    str(node.source_hash or "").strip(),
                    str(node.proof_hash or "").strip(),
                    str(
                        (node.metadata or {}).get("verified_helper_source_hash")
                        or ""
                    ).strip(),
                }
                accepted_hashes.discard("")
                if not support_hash or support_hash not in accepted_hashes:
                    continue
                return True
            return False

        def route_contract_node_has_certificate(
            node: Optional[ProofGraphNode],
        ) -> bool:
            if node is None:
                return False
            route_local_bridge_helper = bool(
                node.kind == "helper"
                and (
                    (
                        contract_metadata.get("source")
                        == "formalization_bridge_support"
                        and str(
                            contract_metadata.get("bridge_helper_node_id") or ""
                        ).strip()
                        == node.node_id
                    )
                    or (
                        contract_metadata.get("source") == "root_exact_helper"
                        and str(
                            contract_metadata.get("root_exact_helper_node_id") or ""
                        ).strip()
                        == node.node_id
                    )
                    or (
                        contract_metadata.get("source")
                        == "active_root_exact_helper"
                        and str(
                            contract_metadata.get(
                                "active_root_exact_helper_node_id"
                            )
                            or ""
                        ).strip()
                        == node.node_id
                    )
                )
            )
            route_local_bridge_target = expected_target
            if route_local_bridge_helper and (
                contract_metadata.get("source") == "active_root_exact_helper"
            ):
                active_target = str(
                    contract_metadata.get("active_root_target_statement") or ""
                ).strip()
                if active_target:
                    route_local_bridge_target = active_target
            render_policy = str(
                (node.metadata or {}).get("verified_helper_render_policy") or ""
            ).strip()
            if (
                not route_local_bridge_helper
                and node.kind == "helper"
                and not _helper_render_policy_context_visible(render_policy)
                and graph_statement_is_root_bridge(node.statement, expected_target)
            ):
                route_local_bridge_helper = True
                route_local_bridge_target = expected_target
            if (
                self._proved_node_has_durable_certificate(node)
                and not route_local_bridge_helper
            ):
                return True
            if (
                node.status != "proved"
                or self.is_superseded_tombstone(node)
                or self._graph_native_source_is_superseded(node)
                or not str(node.proof_hash or "").strip()
            ):
                return False
            if (
                node.kind == "helper"
                and not _helper_render_policy_context_visible(render_policy)
                and not route_local_bridge_helper
            ):
                return False
            if self._node_open_root_reducer_premises(node):
                return False
            if self._formal_variant_crosses_parent_revision(node):
                return False
            if (
                route_local_bridge_helper
                and contract_metadata.get("source")
                == "formalization_bridge_support"
            ):
                return recorded_formalization_bridge_support(node)
            return bool(
                graph_statement_is_root_bridge(
                    node.statement,
                    route_local_bridge_target,
                )
            )

        def route_contract_node_is_branch_local_candidate(
            node: Optional[ProofGraphNode],
        ) -> bool:
            if (
                node is None
                or node.status != "proved"
                or self.is_superseded_tombstone(node)
                or self._graph_native_source_is_superseded(node)
                or not str(node.proof_hash or "").strip()
            ):
                return False
            if node.kind == "helper":
                render_policy = str(
                    (node.metadata or {}).get("verified_helper_render_policy") or ""
                ).strip()
                if render_policy not in {
                    "",
                    "root_authoritative",
                    "advisory_requires_unproved_premise",
                }:
                    return False
            if self._formal_variant_crosses_parent_revision(node):
                return False
            if not graph_statement_is_root_bridge(node.statement, expected_target):
                return False
            premises, _conclusion, _bound_names = (
                _graph_statement_premises_and_conclusion(node.statement)
            )
            return bool(premises)

        branch_local_candidate_node_ids: List[str] = []
        for node_id in all_required_ids:
            node = self.nodes.get(node_id)
            if node is None:
                missing_node_ids.append(node_id)
                continue
            certified = route_contract_node_has_certificate(node)
            branch_local_candidate = (
                not certified and route_contract_node_is_branch_local_candidate(node)
            )
            if not certified and not branch_local_candidate:
                # Reaching here means the node neither carries a certificate
                # nor bridges the target: ``route_contract_node_is_branch_local
                # _candidate`` already requires ``graph_statement_is_root_bridge``.
                # cf5ce8c9 admitted such a node as proved when its source was
                # hash-locked, but a hash lock only says "this is a real proved
                # object", never "this certifies the target". That made ``ready``
                # true for a non-bridging helper, a blank formalization-support
                # statement, and a hollow reducer without its premise. The
                # leftover-helper liveness case it was aiming at is handled
                # below, over ``branch_local_candidate_node_ids``, where the
                # node does bridge and only its premises are outstanding.
                unproved_node_ids.append(node_id)
                continue
            if branch_local_candidate:
                branch_local_candidate_node_ids.append(node_id)
            proved_nodes[node_id] = node
            if graph_statement_is_root_bridge(node.statement, expected_target):
                candidate_assembly_bridge_node_ids.append(node_id)
        root_support_candidates = _graph_support_candidates(
            expected_target,
            include_implication_premises=True,
            premises_are_assumptions=True,
        )

        def norm(text: str, names: Sequence[str] = ()) -> str:
            body, body_names = _graph_strip_leading_forall_binders_with_names(text)
            return _graph_contract_alpha_norm(
                body,
                context_bound_names=tuple(dict.fromkeys(tuple(names) + body_names)),
            )

        root_support_arguments: Dict[str, Dict[str, Any]] = {}
        for support, support_names, arg_index in _graph_root_forall_support_arguments(
            expected_target
        ):
            key = norm(support, support_names)
            if key and key not in root_support_arguments:
                root_support_arguments[key] = {
                    "statement": support,
                    "bound_names": tuple(support_names),
                    "root_arg_index": int(arg_index),
                }

        def explicit_helper_args_available(
            statement: str,
            *,
            exclude_proof_binders: bool = False,
        ) -> bool:
            return (
                _graph_forall_explicit_arity(
                    statement,
                    exclude_proof_binders=exclude_proof_binders,
                )
                <= target_forall_arity
            )

        def statement_supported_by_other_nodes(
            statement: str,
            *,
            bound_names: Sequence[str] = (),
            exclude_node_id: str = "",
        ) -> bool:
            statement_key = norm(statement, bound_names)
            if not statement_key:
                return False
            for support, support_names in root_support_candidates:
                if statement_key == norm(support, support_names):
                    return True
            for support_id, support_node in proved_nodes.items():
                if support_id == exclude_node_id:
                    continue
                for support, support_names in _graph_support_candidates(
                    support_node.statement
                ):
                    if statement_key == norm(support, support_names):
                        return True
            return False

        def support_for_statement(
            statement: str,
            *,
            bound_names: Sequence[str] = (),
            exclude_node_id: str = "",
        ) -> Dict[str, str]:
            statement_key = norm(statement, bound_names)
            if not statement_key:
                return {}
            for support_id, support_node in proved_nodes.items():
                if support_id == exclude_node_id:
                    continue
                for support, support_names in _graph_support_candidates(
                    support_node.statement
                ):
                    if statement_key == norm(support, support_names):
                        return {
                            "node_id": support_id,
                            "helper_name": self._node_helper_name(support_node),
                            "statement": support,
                            "full_statement": str(support_node.statement or ""),
                        }
            root_argument_support = root_support_arguments.get(statement_key)
            if root_argument_support:
                return {
                    "node_id": "",
                    "helper_name": "",
                    "statement": str(root_argument_support.get("statement") or ""),
                    "full_statement": str(
                        root_argument_support.get("statement") or ""
                    ),
                    "root_arg_index": str(
                        root_argument_support.get("root_arg_index") or ""
                    ),
                }
            for support, support_names in root_support_candidates:
                if statement_key == norm(support, support_names):
                    return {
                        "node_id": "",
                        "helper_name": "",
                        "statement": support,
                        "full_statement": support,
                    }
            return {}

        def branch_case_groups() -> List[Dict[str, Any]]:
            groups: List[Dict[str, Any]] = []
            seen: Set[Tuple[str, Tuple[str, ...]]] = set()
            for support_id, support_node in proved_nodes.items():
                if support_id in branch_local_candidate_node_ids:
                    continue
                if not route_contract_node_has_certificate(support_node):
                    continue
                case_support = _graph_case_disjunction_support(
                    support_node.statement
                )
                if not case_support:
                    continue
                support = str(case_support.get("statement") or "").strip()
                support_full = str(
                    case_support.get("full_statement") or support
                ).strip()
                support_names = tuple(case_support.get("bound_names") or ())
                leaves = [
                    dict(leaf)
                    for leaf in list(case_support.get("leaves") or [])
                    if isinstance(leaf, dict)
                ]
                branches: List[Dict[str, Any]] = []
                for branch_index, leaf in enumerate(leaves):
                    disjunct = str(leaf.get("statement") or "").strip()
                    path: List[int] = []
                    for raw_part in list(leaf.get("path") or []):
                        try:
                            direction = int(raw_part)
                        except (TypeError, ValueError):
                            continue
                        if direction in {0, 1}:
                            path.append(direction)
                    key = norm(disjunct, support_names)
                    if not key:
                        break
                    branches.append(
                        {
                            "branch_index": branch_index,
                            "branch_name": (
                                f"{self._node_helper_name(support_node) or 'case'}"
                                f"_branch_{branch_index + 1}"
                            ),
                            "assumption_statement": disjunct,
                            "assumption_key": key,
                            "case_branch_path": path,
                        }
                    )
                if len(branches) != len(leaves):
                    continue
                keys = tuple(branch["assumption_key"] for branch in branches)
                ordered = tuple(dict.fromkeys(keys))
                if len(keys) < 2 or len(ordered) != len(keys):
                    continue
                group_key = (support_id, ordered)
                if group_key in seen:
                    continue
                seen.add(group_key)
                groups.append(
                    {
                        "case_node_id": support_id,
                        "case_helper_name": self._node_helper_name(support_node),
                        "case_statement": support,
                        "case_full_statement": support_full,
                        "case_tree": dict(case_support.get("tree") or {}),
                        "assumption_keys": ordered,
                        "branches": branches,
                    }
                )
            return groups

        bridge_premise_entries: Dict[str, List[Dict[str, Any]]] = {}
        for node_id in candidate_assembly_bridge_node_ids:
            node = proved_nodes.get(node_id)
            if node is None:
                continue
            if graph_statement_root_equivalent(node.statement, expected_target):
                assembly_bridge_node_ids.append(node_id)
                continue
            premises, _conclusion, bound_names = (
                _graph_statement_premises_and_conclusion(node.statement)
            )
            entries: List[Dict[str, Any]] = []
            for premise in premises:
                premise_text, premise_names = (
                    _graph_strip_leading_forall_binders_with_names(premise)
                )
                premise_bound_names = tuple(
                    dict.fromkeys(tuple(bound_names) + tuple(premise_names))
                )
                key = norm(premise_text, premise_bound_names)
                if key:
                    entries.append(
                        {
                            "statement": premise_text,
                            "key": key,
                            "bound_names": premise_bound_names,
                        }
                    )
            bridge_premise_entries[node_id] = entries
            if premises and all(
                statement_supported_by_other_nodes(
                    premise,
                    bound_names=bound_names,
                    exclude_node_id=node_id,
                )
                for premise in premises
            ):
                assembly_bridge_node_ids.append(node_id)

        def reducer_for_branch(
            assumption_key: str,
            *,
            sibling_assumption_keys: Sequence[str],
        ) -> Dict[str, Any]:
            branch_key = str(assumption_key or "").strip()
            if not branch_key:
                return {}
            if branch_key == "false":
                return {
                    "reducer_id": "__branch_false_elim__",
                    "premise_bindings": [],
                }
            sibling_keys = {
                str(key or "").strip()
                for key in list(sibling_assumption_keys or [])
                if str(key or "").strip()
            }
            for node_id, entries in bridge_premise_entries.items():
                branch_entries = [
                    entry for entry in entries if entry.get("key") == branch_key
                ]
                if not branch_entries:
                    continue
                crosses_sibling = any(
                    entry.get("key") in sibling_keys and entry.get("key") != branch_key
                    for entry in entries
                )
                if crosses_sibling:
                    continue
                bindings: List[Dict[str, Any]] = []
                unsupported_extra = False
                for entry in entries:
                    entry_key = str(entry.get("key") or "").strip()
                    if entry_key == branch_key:
                        bindings.append({
                            "kind": "branch",
                            "statement": str(entry.get("statement") or ""),
                            "key": entry_key,
                        })
                        continue
                    support = support_for_statement(
                        str(entry.get("statement") or ""),
                        bound_names=tuple(entry.get("bound_names") or ()),
                        exclude_node_id=node_id,
                    )
                    if not support:
                        unsupported_extra = True
                        break
                    bindings.append({
                        "kind": "support",
                        "statement": str(entry.get("statement") or ""),
                        "key": entry_key,
                        "support_node_id": str(support.get("node_id") or ""),
                        "support_helper_name": str(
                            support.get("helper_name") or ""
                        ),
                        "support_statement": str(support.get("statement") or ""),
                        "support_full_statement": str(
                            support.get("full_statement")
                            or support.get("statement")
                            or ""
                        ),
                        "support_root_arg_index": str(
                            support.get("root_arg_index") or ""
                        ),
                    })
                if unsupported_extra:
                    continue
                return {
                    "reducer_id": node_id,
                    "premise_bindings": bindings,
                }
            return {}

        branch_frame_objects: List[ProofGraphBranchFrame] = []
        branch_frame_groups: List[Dict[str, Any]] = []
        for group in branch_case_groups():
            frame_ids: List[str] = []
            reducer_ids: List[str] = []
            case_helper_name = str(group.get("case_helper_name") or "").strip()
            case_node = proved_nodes.get(str(group.get("case_node_id") or ""))
            group_replayable = bool(case_helper_name) and (
                self._node_replay_materialization_helper(
                    case_node,
                    mutate=mutate,
                ) is None
            )
            if group_replayable and not explicit_helper_args_available(
                str(group.get("case_full_statement") or group.get("case_statement") or "")
            ):
                group_replayable = False
            group_keys = tuple(group.get("assumption_keys") or ())
            for branch in list(group.get("branches") or []):
                branch_index = int(branch.get("branch_index") or 0)
                assumption_key = str(branch.get("assumption_key") or "").strip()
                reducer_match = reducer_for_branch(
                    assumption_key,
                    sibling_assumption_keys=group_keys,
                )
                reducer_id = str(reducer_match.get("reducer_id") or "")
                false_branch_closed = reducer_id == "__branch_false_elim__"
                reducer_node = None if false_branch_closed else proved_nodes.get(reducer_id)
                reducer_helper_name = self._node_helper_name(reducer_node)
                reducer_statement = (
                    str(getattr(reducer_node, "statement", "") or "")
                    if reducer_node is not None
                    else ""
                )
                reducer_premise_bindings = list(
                    reducer_match.get("premise_bindings") or []
                )
                reducer_replayable = (
                    false_branch_closed
                    or (
                        self._node_replay_materialization_helper(
                            reducer_node,
                            mutate=mutate,
                        ) is None
                        and all(
                            item.get("kind") != "support"
                            or str(item.get("support_helper_name") or "").strip()
                            or str(item.get("support_root_arg_index") or "").strip()
                            for item in reducer_premise_bindings
                        )
                    )
                )
                if (
                    reducer_replayable
                    and not false_branch_closed
                    and not explicit_helper_args_available(
                        reducer_statement,
                        exclude_proof_binders=True,
                    )
                ):
                    reducer_replayable = False
                if reducer_replayable:
                    for binding in reducer_premise_bindings:
                        if str(binding.get("kind") or "").strip() != "support":
                            continue
                        if str(binding.get("support_root_arg_index") or "").strip():
                            continue
                        support_statement = str(
                            binding.get("support_full_statement")
                            or binding.get("support_statement")
                            or binding.get("statement")
                            or ""
                        )
                        if not explicit_helper_args_available(support_statement):
                            reducer_replayable = False
                            break
                if (
                    reducer_id
                    and not false_branch_closed
                    and (not reducer_helper_name or not reducer_replayable)
                ):
                    group_replayable = False
                frame_id = self.branch_frame_id(
                    clean_route_id,
                    str(group.get("case_node_id") or ""),
                    branch_index,
                    assumption_key,
                )
                frame = ProofGraphBranchFrame(
                    frame_id=frame_id,
                    route_id=clean_route_id,
                    case_node_id=str(group.get("case_node_id") or ""),
                    case_helper_name=str(group.get("case_helper_name") or ""),
                    case_statement=str(group.get("case_statement") or ""),
                    case_full_statement=str(
                        group.get("case_full_statement")
                        or group.get("case_statement")
                        or ""
                    ),
                    branch_name=str(branch.get("branch_name") or ""),
                    branch_index=branch_index,
                    assumption_statement=str(
                        branch.get("assumption_statement") or ""
                    ),
                    assumption_key=assumption_key,
                    reducer_node_id="" if false_branch_closed else reducer_id,
                    reducer_helper_name=reducer_helper_name,
                    reducer_statement=str(
                        getattr(reducer_node, "statement", "") if reducer_node else ""
                    ),
                    status="proved" if reducer_id else "open",
                    metadata={
                        "case_assumption_keys": list(group_keys),
                        "case_full_statement": str(
                            group.get("case_full_statement")
                            or group.get("case_statement")
                            or ""
                        ),
                        "case_branch_path": list(
                            branch.get("case_branch_path") or []
                        ),
                        "case_tree": dict(group.get("case_tree") or {}),
                        "branch_closed_by_false_elim": false_branch_closed,
                        "reducer_premise_bindings": copy.deepcopy(
                            reducer_premise_bindings
                        ),
                    },
                )
                branch_frame_objects.append(frame)
                frame_ids.append(frame.frame_id)
                if reducer_id and not false_branch_closed:
                    reducer_ids.append(reducer_id)
            branch_frame_groups.append(
                {
                    "case_node_id": str(group.get("case_node_id") or ""),
                    "case_helper_name": str(group.get("case_helper_name") or ""),
                    "case_statement": str(group.get("case_statement") or ""),
                    "case_full_statement": str(
                        group.get("case_full_statement")
                        or group.get("case_statement")
                        or ""
                    ),
                    "frame_ids": frame_ids,
                    "reducer_node_ids": list(dict.fromkeys(reducer_ids)),
                    "complete": bool(frame_ids)
                    and all(
                        frame.status == "proved"
                        for frame in branch_frame_objects
                        if frame.frame_id in set(frame_ids)
                    ),
                    "replayable": bool(group_replayable),
                }
            )
        persisted_branch_frames = (
            self._replace_route_branch_frames(
                clean_route_id,
                branch_frame_objects,
            )
            if mutate
            else sorted(
                branch_frame_objects,
                key=lambda frame: (frame.case_node_id, frame.branch_index),
            )
        )

        selected_branch_frame_ids: List[str] = []
        if not assembly_bridge_node_ids:
            for group in branch_frame_groups:
                if bool(group.get("complete")) and bool(group.get("replayable")):
                    assembly_bridge_node_ids.extend(
                        list(group.get("reducer_node_ids") or [])
                    )
                    selected_branch_frame_ids = list(group.get("frame_ids") or [])
                    break
        assembly_bridge_node_ids = list(dict.fromkeys(assembly_bridge_node_ids))
        selected_bridge_ids = set(assembly_bridge_node_ids)
        branch_frame_reducer_ids = {
            str(node_id or "").strip()
            for group in branch_frame_groups
            for node_id in list(group.get("reducer_node_ids") or [])
            if str(node_id or "").strip()
        }
        for node_id in branch_local_candidate_node_ids:
            if node_id in selected_bridge_ids or node_id in branch_frame_reducer_ids:
                continue
            candidate_node = proved_nodes.get(node_id)
            if self._helper_has_hash_locked_source(candidate_node):
                continue
            if branch_frame_groups:
                continue
            if node_id not in unproved_node_ids:
                unproved_node_ids.append(node_id)
        replay_materialization_node_ids = [
            node.node_id
            for node in self._route_replay_materialization_nodes(
                clean_route_id,
                mutate=mutate,
            )
        ]
        ready = not missing_helper_names and not missing_node_ids and not unproved_node_ids
        deterministic_ready = bool(
            ready
            and not replay_materialization_node_ids
            and (assembly_bridge_node_ids or selected_branch_frame_ids)
        )
        verdict = (
            "route_assembly_contract_ready"
            if deterministic_ready
            else (
                "route_assembly_contract_authoring_ready_missing_bridge"
                if ready
                else "route_assembly_contract_incomplete"
            )
        )
        return {
            "ready": ready,
            "authoring_ready": ready,
            "deterministic_ready": deterministic_ready,
            "verdict": verdict,
            "route_id": clean_route_id,
            "route_scope": effective_scope,
            "contract_metadata": dict(contract.get("metadata") or {}),
            "target_statement": expected_target,
            "target_node_id": expected_target_node_id,
            "contract_target_node_id": contract_target_node_id,
            "target_statement_key": expected_target_key,
            "contract_target_statement_key": contract_target_key,
            "dependency_node_ids": all_required_ids,
            "required_node_ids": required_node_ids,
            "assembly_bridge_node_ids": assembly_bridge_node_ids,
            "branch_local_candidate_node_ids": list(branch_local_candidate_node_ids),
            "branch_frame_ids": [frame.frame_id for frame in persisted_branch_frames],
            "branch_frames": [asdict(frame) for frame in persisted_branch_frames],
            "branch_frame_groups": branch_frame_groups,
            "selected_branch_frame_ids": selected_branch_frame_ids,
            "replay_materialization_node_ids": replay_materialization_node_ids,
            "missing_helper_names": missing_helper_names,
            "missing_node_ids": missing_node_ids,
            "unproved_node_ids": unproved_node_ids,
        }

    def ready_root_assembly_contract_status(
        self,
        *,
        target_statement: str = "",
        mutate: bool = True,
    ) -> Dict[str, Any]:
        """Return the first ready explicit root-assembly route contract."""

        checked: List[Dict[str, Any]] = []
        for route in self.nodes_by_kind("strategy_route"):
            metadata = dict(route.metadata or {})
            contract = metadata.get(_ROUTE_ASSEMBLY_CONTRACT_KEY)
            route_scope = str(metadata.get("route_scope") or "").strip()
            contract_scope = (
                str(contract.get("scope") or "").strip()
                if isinstance(contract, dict)
                else ""
            )
            if (
                route_scope != _ROUTE_SCOPE_ROOT_ASSEMBLY
                and contract_scope != _ROUTE_SCOPE_ROOT_ASSEMBLY
            ):
                continue
            status = self.route_assembly_contract_status(
                route.node_id,
                target_statement=target_statement,
                mutate=mutate,
            )
            if bool(status.get("ready")):
                out = dict(status)
                out.setdefault("route_id", route.node_id)
                return out
            checked.append(
                {
                    "route_id": route.node_id,
                    "verdict": str(status.get("verdict") or ""),
                    "dependency_node_ids": list(
                        status.get("dependency_node_ids") or []
                    ),
                }
            )
        return {
            "ready": False,
            "verdict": "missing_ready_root_assembly_contract",
            "checked_route_count": len(checked),
            "route_contract_verdicts": checked[:10],
        }

    def retarget_route_assembly_contract_requirement(
        self,
        route_id: str,
        *,
        old_node_id: str,
        new_node_id: str,
    ) -> bool:
        """Move a contracted root-route obligation to its repaired graph node."""

        clean_route_id = str(route_id or "").strip()
        old_id = str(old_node_id or "").strip()
        new_id = str(new_node_id or "").strip()
        if not clean_route_id or not old_id or not new_id or old_id == new_id:
            return False
        route = self.nodes.get(clean_route_id)
        if route is None or route.kind != "strategy_route":
            return False
        contract = (route.metadata or {}).get(_ROUTE_ASSEMBLY_CONTRACT_KEY)
        if not isinstance(contract, dict):
            return False
        required_ids: List[str] = []
        changed = False
        for raw_id in list(contract.get("required_node_ids") or []):
            node_id = str(raw_id or "").strip()
            if not node_id:
                continue
            if node_id == old_id:
                node_id = new_id
                changed = True
            if node_id not in required_ids:
                required_ids.append(node_id)
        if not changed:
            return False
        contract["required_node_ids"] = required_ids
        contract["required_obligation_count"] = len(required_ids)
        self._remove_route_dependency_edges(clean_route_id, old_id)
        self.attach_claim_to_route(clean_route_id, new_id)
        route.metadata.pop("route_assembly_contract_last_verdict", None)
        route.metadata.pop("route_assembly_contract_missing_node_ids", None)
        route.metadata.pop("route_assembly_contract_unproved_node_ids", None)
        route.metadata.pop(
            "route_assembly_contract_missing_dependency_edge_node_ids",
            None,
        )
        self._invalidate_strategy_route_assembly(
            clean_route_id,
            reason="route_assembly_contract_requirement_retargeted",
            dependency_node_id=old_id,
        )
        return True

    def _route_assembly_contract_signature(
        self,
        route: Optional[ProofGraphNode],
    ) -> Dict[str, Any]:
        if route is None or route.kind != "strategy_route":
            return {}
        metadata = dict(route.metadata or {})
        contract = metadata.get(_ROUTE_ASSEMBLY_CONTRACT_KEY)
        if not isinstance(contract, dict):
            return {}
        required_node_ids = [
            str(node_id or "").strip()
            for node_id in list(contract.get("required_node_ids") or [])
            if str(node_id or "").strip()
        ]
        required_helper_names = [
            str(name or "").strip()
            for name in list(contract.get("required_helper_names") or [])
            if str(name or "").strip()
        ]
        required_helper_source_hashes = {
            str(name or "").strip(): str(source_hash or "").strip()
            for name, source_hash in dict(
                contract.get("required_helper_source_hashes") or {}
            ).items()
            if str(name or "").strip() and str(source_hash or "").strip()
        }
        return {
            "route_scope": str(metadata.get("route_scope") or "").strip(),
            "contract_scope": str(contract.get("scope") or "").strip(),
            "target_node_id": str(contract.get("target_node_id") or "").strip(),
            "target_statement_key": str(
                contract.get("target_statement_key") or ""
            ).strip(),
            "required_node_ids": sorted(dict.fromkeys(required_node_ids)),
            "required_helper_names": sorted(dict.fromkeys(required_helper_names)),
            "required_helper_source_hashes": required_helper_source_hashes,
            "required_obligation_count": contract.get("required_obligation_count"),
        }

    def _route_dependency_targets_are_proved(self, route_id: str) -> bool:
        route_edges = self._route_dependency_edges(route_id)
        if not route_edges:
            return False
        for edge in route_edges:
            if not self._proved_node_has_durable_certificate(
                self.nodes.get(edge.target)
            ):
                return False
        return True

    def _route_missing_assembly_bridge_rescue_status(
        self,
        route_id: str,
        contract_status: Optional[Dict[str, Any]] = None,
        *,
        allow_deterministic_ready: bool = False,
        mutate: bool = True,
    ) -> Tuple[bool, str, Dict[str, Any]]:
        clean_route_id = str(route_id or "").strip()
        status = dict(
            contract_status
            if isinstance(contract_status, dict)
            else self.route_assembly_contract_status(
                clean_route_id,
                mutate=mutate,
            )
        )
        active = bool(status.get("ready")) and (
            allow_deterministic_ready
            or not bool(status.get("deterministic_ready"))
        )
        signature = ""
        if active:
            try:
                signature = str(
                    self.route_dependency_signature_hash(clean_route_id) or ""
                ).strip()
            except Exception:
                signature = ""
        return active, signature, status

    def _retire_route_missing_assembly_bridge_rescue_node(
        self,
        node: ProofGraphNode,
        *,
        current_signature_hash: str = "",
        contract_status: Optional[Dict[str, Any]] = None,
    ) -> None:
        metadata = node.metadata if isinstance(node.metadata, dict) else {}
        node.metadata = metadata
        old_signature = str(
            metadata.get("route_missing_assembly_bridge_signature_hash") or ""
        ).strip()
        metadata["route_missing_assembly_bridge_rescue_stale"] = True
        metadata["route_missing_assembly_bridge_rescue_stale_signature_hash"] = (
            old_signature
        )
        metadata["route_missing_assembly_bridge_rescue_current_signature_hash"] = str(
            current_signature_hash or ""
        ).strip()
        if isinstance(contract_status, dict):
            metadata["route_missing_assembly_bridge_rescue_stale_contract_status"] = (
                dict(contract_status)
            )
        metadata["schedulable"] = False
        if node.status != "proved":
            node.status = "obsolete"
        route_id = str(metadata.get("route_id") or "").strip()
        route = self.nodes.get(route_id) if route_id else None
        route_metadata = route.metadata if route is not None else None
        if isinstance(route_metadata, dict):
            if (
                str(
                    route_metadata.get(
                        "route_missing_assembly_bridge_rescue_obligation_id"
                    )
                    or ""
                ).strip()
                == node.node_id
            ):
                route_metadata.pop(
                    "route_missing_assembly_bridge_rescue_obligation_id",
                    None,
                )
            if (
                str(
                    route_metadata.get("route_missing_assembly_bridge_rescue_replan_id")
                    or ""
                ).strip()
                == node.node_id
            ):
                route_metadata.pop(
                    "route_missing_assembly_bridge_rescue_replan_id",
                    None,
                )
            if (
                old_signature
                and str(
                    route_metadata.get(
                        "route_missing_assembly_bridge_rescue_signature_hash"
                    )
                    or ""
                ).strip()
                == old_signature
            ):
                route_metadata.pop(
                    "route_missing_assembly_bridge_rescue_signature_hash",
                    None,
                )

    def _mark_route_missing_assembly_bridge_rescue_current(
        self,
        node: ProofGraphNode,
        *,
        signature_hash: str,
        contract_status: Dict[str, Any],
    ) -> None:
        metadata = node.metadata if isinstance(node.metadata, dict) else {}
        node.metadata = metadata
        stale_marker_present = any(
            key in metadata
            for key in (
                "route_missing_assembly_bridge_rescue_stale",
                "route_missing_assembly_bridge_rescue_stale_signature_hash",
                "route_missing_assembly_bridge_rescue_current_signature_hash",
                "route_missing_assembly_bridge_rescue_stale_contract_status",
            )
        )
        generation = int(
            self._coerce_float(
                metadata.get("route_missing_assembly_bridge_rescue_generation"),
                0.0,
            )
            or 0
        )
        if stale_marker_present:
            generation += 1
        metadata.pop("route_missing_assembly_bridge_rescue_stale", None)
        metadata.pop("route_missing_assembly_bridge_rescue_stale_signature_hash", None)
        metadata.pop(
            "route_missing_assembly_bridge_rescue_current_signature_hash",
            None,
        )
        metadata.pop(
            "route_missing_assembly_bridge_rescue_stale_contract_status",
            None,
        )
        if stale_marker_present and metadata.get("schedulable") is False:
            metadata.pop("schedulable", None)
        metadata["route_missing_assembly_bridge_rescue"] = True
        metadata["route_missing_assembly_bridge_signature_hash"] = str(
            signature_hash or ""
        ).strip()
        metadata["route_missing_assembly_bridge_rescue_generation"] = generation
        metadata["route_assembly_contract_status"] = dict(contract_status)
        # Signature-current means this rescue still represents the route; it
        # does not mean its causal blockers or terminal attempt state vanished.
        # Only an actual stale-signature retirement performed above owns an
        # automatic revival transition, and that retirement uses ``obsolete``.
        if stale_marker_present and node.status == "obsolete":
            unresolved_blocker = any(
                edge.source == node.node_id
                and edge.kind == "blocked_by"
                and not self._proved_node_has_durable_certificate(
                    self.nodes.get(edge.target)
                )
                for edge in self.edges
            )
            terminal_generation_memory = bool(
                metadata.get("retired_by_repeated_repair_failure")
                or metadata.get(
                    "formalization_repeated_unrelated_bridge_suppressed"
                )
                or metadata.get("proposal_invalidated")
                or graph_node_frontier_quarantined(node)
                or graph_node_frontier_promoted_to_proof_state(node)
            )
            if terminal_generation_memory:
                # Durable failure/delegation memory remains authoritative for
                # a semantically deduplicated rescue. Do not publish an OPEN
                # frontier item that session liveness will immediately reject.
                node.status = "obsolete"
            elif unresolved_blocker:
                # Spawned-claim blockers belong to the mathematical rescue,
                # not merely its exact certificate signature. Preserve their
                # causal conjunction across signature generations.
                node.status = "blocked"
            else:
                node.status = "open"

    def _route_missing_assembly_bridge_rescue_current(
        self,
        node: ProofGraphNode,
        *,
        contract_status: Optional[Dict[str, Any]] = None,
        mutate: bool = True,
    ) -> bool:
        metadata = dict(getattr(node, "metadata", {}) or {})
        if not metadata.get("route_missing_assembly_bridge_rescue"):
            return True
        route_id = str(metadata.get("route_id") or "").strip()
        if not route_id:
            if mutate:
                self._retire_route_missing_assembly_bridge_rescue_node(node)
            return False
        active, current_signature, status = (
            self._route_missing_assembly_bridge_rescue_status(
                route_id,
                contract_status=contract_status,
                allow_deterministic_ready=bool(
                    metadata.get("route_root_tactic_failure_rescue")
                ),
                mutate=mutate,
            )
        )
        rescue_signature = str(
            metadata.get("route_missing_assembly_bridge_signature_hash") or ""
        ).strip()
        if active and current_signature and current_signature == rescue_signature:
            if mutate and metadata.get("route_missing_assembly_bridge_rescue_stale"):
                self._mark_route_missing_assembly_bridge_rescue_current(
                    node,
                    signature_hash=current_signature,
                    contract_status=status,
                )
            return True
        if mutate:
            self._retire_route_missing_assembly_bridge_rescue_node(
                node,
                current_signature_hash=current_signature,
                contract_status=status,
            )
        return False

    def _retire_stale_route_missing_assembly_bridge_rescues(
        self,
        route_id: str,
        *,
        current_signature_hash: str = "",
        contract_status: Optional[Dict[str, Any]] = None,
        allow_deterministic_ready: bool = False,
    ) -> None:
        clean_route_id = str(route_id or "").strip()
        if not clean_route_id:
            return
        active, computed_signature, status = (
            self._route_missing_assembly_bridge_rescue_status(
                clean_route_id,
                contract_status=contract_status,
                allow_deterministic_ready=allow_deterministic_ready,
            )
        )
        current_signature = str(current_signature_hash or computed_signature).strip()
        for node in list(self.nodes.values()):
            metadata = dict(node.metadata or {})
            if not metadata.get("route_missing_assembly_bridge_rescue"):
                continue
            if str(metadata.get("route_id") or "").strip() != clean_route_id:
                continue
            rescue_signature = str(
                metadata.get("route_missing_assembly_bridge_signature_hash") or ""
            ).strip()
            if active and current_signature and rescue_signature == current_signature:
                continue
            self._retire_route_missing_assembly_bridge_rescue_node(
                node,
                current_signature_hash=current_signature,
                contract_status=status,
            )

    def _ensure_orphaned_route_missing_assembly_bridge_rescues(self) -> None:
        for route in list(self.nodes.values()):
            if route.kind != "strategy_route" or self.is_superseded_tombstone(route):
                continue
            if self._route_is_terminally_poisoned(route.node_id):
                continue
            metadata = route.metadata if isinstance(route.metadata, dict) else {}
            route.metadata = metadata
            marker_keys = (
                "route_missing_assembly_bridge_signature_hash",
                "route_root_tactic_failure_rescue_signature_hash",
                "route_root_tactic_failed_signature_hash",
                "route_root_assembly_author_failed_signature_hash",
            )
            marker_hashes = {
                key: str(metadata.get(key) or "").strip()
                for key in marker_keys
                if str(metadata.get(key) or "").strip()
            }
            if not marker_hashes:
                continue
            try:
                current_signature = str(
                    self.route_dependency_signature_hash(route.node_id) or ""
                ).strip()
            except Exception:
                current_signature = ""
            for key, marker_hash in marker_hashes.items():
                if current_signature and marker_hash == current_signature:
                    continue
                metadata.pop(key, None)
                if key == "route_root_tactic_failed_signature_hash":
                    metadata.pop("route_root_tactic_failed_hash", None)
                elif key == "route_root_assembly_author_failed_signature_hash":
                    metadata.pop(
                        "route_root_assembly_author_failed_hash",
                        None,
                    )
            current_marker_keys = {
                key
                for key, marker_hash in marker_hashes.items()
                if current_signature and marker_hash == current_signature
            }
            if not current_marker_keys:
                continue
            allow_deterministic_ready = any(
                key != "route_missing_assembly_bridge_signature_hash"
                for key in current_marker_keys
            )
            active, _computed_signature, status = (
                self._route_missing_assembly_bridge_rescue_status(
                    route.node_id,
                    allow_deterministic_ready=allow_deterministic_ready,
                )
            )
            if not active:
                continue
            current_rescue_found = False
            for node in list(self.nodes.values()):
                node_metadata = dict(node.metadata or {})
                if not node_metadata.get("route_missing_assembly_bridge_rescue"):
                    continue
                if str(node_metadata.get("route_id") or "").strip() != route.node_id:
                    continue
                if (
                    str(
                        node_metadata.get(
                            "route_missing_assembly_bridge_signature_hash"
                        )
                        or ""
                    ).strip()
                    != current_signature
                ):
                    continue
                if not self._route_missing_assembly_bridge_rescue_current(
                    node,
                    contract_status=status,
                ):
                    continue
                if node.kind == "missing_obligation":
                    metadata[
                        "route_missing_assembly_bridge_rescue_obligation_id"
                    ] = node.node_id
                elif node.kind == "replan_queue_item":
                    metadata["route_missing_assembly_bridge_rescue_replan_id"] = (
                        node.node_id
                    )
                current_rescue_found = True
            if current_rescue_found:
                continue
            rescue = self.ensure_route_missing_assembly_bridge_rescue(
                route.node_id,
                status,
                signature_hash=current_signature,
                phase="route_missing_assembly_bridge_orphan_recovery",
                allow_deterministic_ready=allow_deterministic_ready,
            )
            if rescue is None:
                metadata.pop("route_missing_assembly_bridge_signature_hash", None)
                metadata.pop(
                    "route_root_tactic_failure_rescue_signature_hash",
                    None,
                )
                metadata.pop("route_root_tactic_failed_hash", None)
                metadata.pop("route_root_tactic_failed_signature_hash", None)
                metadata.pop("route_root_assembly_author_failed_hash", None)
                metadata.pop(
                    "route_root_assembly_author_failed_signature_hash",
                    None,
                )
                metadata["route_missing_assembly_bridge_orphan_reopened"] = True

    def _route_is_terminally_poisoned(self, route_id: str) -> bool:
        route = self.nodes.get(str(route_id or "").strip())
        if route is None or route.kind != "strategy_route":
            return False
        metadata = dict(route.metadata or {})
        if bool(
            metadata.get("route_retired")
            or metadata.get("route_dependency_contradicted")
            or metadata.get("proposal_invalidated")
        ):
            return True
        status = str(getattr(route, "status", "") or "").strip()
        if status in {"failed", "obsolete", "superseded"}:
            return True
        if status == "rejected":
            return not self.node_has_new_rejection_evidence(route)
        return False

    def _node_route_ids(self, node: Any) -> Set[str]:
        metadata = dict(getattr(node, "metadata", {}) or {})
        route_id = str(metadata.get("route_id") or "").strip()
        route_ids: Set[str] = {route_id} if route_id else set()
        node_id = str(getattr(node, "node_id", "") or "").strip()
        if node_id:
            for edge in self.incoming(node_id):
                if edge.kind not in {"route_requires", "route_blocked_by", "route_replan"}:
                    continue
                route = self.nodes.get(edge.source)
                if route is not None and route.kind == "strategy_route":
                    route_ids.add(route.node_id)
        return route_ids

    def _node_route_is_terminally_poisoned(self, node: Any) -> bool:
        route_ids = self._node_route_ids(node)
        return bool(route_ids) and all(
            self._route_is_terminally_poisoned(route_id) for route_id in route_ids
        )

    def _revive_route_poisoned_node_for_live_route(
        self,
        node: ProofGraphNode,
        *,
        preferred_route_id: str = "",
    ) -> bool:
        metadata = node.metadata
        if (
            node.status != "rejected"
            or self.is_superseded_tombstone(node)
            or not (
                metadata.get("route_retired")
                or metadata.get("route_dependency_contradicted")
                or metadata.get("route_poisoned_descendant_suppressed")
            )
        ):
            return False
        live_route_ids = sorted(
            route_id
            for route_id in self._node_route_ids(node)
            if not self._route_is_terminally_poisoned(route_id)
        )
        if not live_route_ids:
            return False
        preferred = str(preferred_route_id or "").strip()
        metadata["route_id"] = (
            preferred if preferred in live_route_ids else live_route_ids[0]
        )
        for key in (
            "route_retired",
            "route_retired_reason",
            "route_retirement_verdict",
            "route_retired_dependency_node_id",
            "route_dependency_contradicted",
            "route_poisoned_descendant_suppressed",
        ):
            metadata.pop(key, None)
        metadata["route_poison_revived_for_live_route"] = True
        node.status = "open"
        return True

    def ensure_route_assembly_contract_replan(
        self,
        route_id: str,
        contract_status: Optional[Dict[str, Any]] = None,
    ) -> Optional[ProofGraphNode]:
        """Keep an incomplete root route in obligation-mining/replan mode."""

        clean_route_id = str(route_id or "").strip()
        route = self.nodes.get(clean_route_id)
        if route is None or route.kind != "strategy_route":
            return None
        if self._route_is_terminally_poisoned(clean_route_id):
            route.metadata["route_assembly_contract_replan_suppressed"] = True
            route.metadata["route_assembly_contract_last_verdict"] = str(
                (route.metadata or {}).get("route_retirement_verdict")
                or "route_retired"
            )
            return None
        existing_replan_id = str(
            (route.metadata or {}).get("route_assembly_contract_replan_id") or ""
        ).strip()
        existing_replan = self.nodes.get(existing_replan_id)
        if existing_replan is not None and existing_replan.status == "open":
            return existing_replan
        status = dict(
            contract_status
            if isinstance(contract_status, dict)
            else self.route_assembly_contract_status(clean_route_id)
        )
        verdict = str(status.get("verdict") or "route_assembly_contract_incomplete")
        reason = (
            "root route assembly contract incomplete; mine the missing "
            f"root obligations before assembling ({verdict})"
        )
        obligation = self.record_missing_obligation(
            statement="",
            reason=reason,
            source_node_id=clean_route_id,
            route_id=clean_route_id,
            phase="route_assembly_contract",
            error_type="route_assembly_contract_incomplete",
            metadata={
                "schedulable": False,
                "formalization_required": True,
                "root_equivalent_obligation_suppressed": True,
                "route_assembly_contract_verdict": verdict,
                "route_assembly_contract_status": status,
            },
        )
        replan = self.record_replan_item(
            source_node_id=clean_route_id,
            route_id=clean_route_id,
            obligation_id=obligation.node_id,
            reason=reason,
            phase="route_assembly_contract",
            priority=0.4,
            metadata={
                "schedulable": False,
                "formalization_required": True,
                "root_equivalent_obligation_suppressed": True,
                "route_assembly_contract_verdict": verdict,
                "route_assembly_contract_status": status,
            },
        )
        route.metadata["route_assembly_contract_replan_obligation_id"] = (
            obligation.node_id
        )
        route.metadata["route_assembly_contract_replan_id"] = replan.node_id
        return replan

    def ensure_route_missing_assembly_bridge_rescue(
        self,
        route_id: str,
        contract_status: Optional[Dict[str, Any]] = None,
        *,
        signature_hash: str = "",
        phase: str = "route_missing_assembly_bridge",
        turn_index: int = 0,
        allow_deterministic_ready: bool = False,
    ) -> Optional[ProofGraphNode]:
        """Create bridge-building work for a ready route with no replay bridge."""

        clean_route_id = str(route_id or "").strip()
        route = self.nodes.get(clean_route_id)
        if route is None or route.kind != "strategy_route":
            return None
        if self.is_superseded_tombstone(route) or self._route_is_terminally_poisoned(
            clean_route_id
        ):
            return None
        status = dict(
            contract_status
            if isinstance(contract_status, dict)
            else self.route_assembly_contract_status(clean_route_id)
        )
        if not bool(status.get("ready")) or (
            bool(status.get("deterministic_ready"))
            and not allow_deterministic_ready
        ):
            return None
        target_statement = str(
            status.get("target_statement") or self.root_statement or route.statement or ""
        ).strip()
        if not target_statement:
            return None
        clean_signature = str(signature_hash or "").strip()
        if not clean_signature:
            try:
                clean_signature = str(
                    self.route_dependency_signature_hash(clean_route_id) or ""
                ).strip()
            except Exception:
                clean_signature = ""
        if not clean_signature:
            clean_signature = graph_text_hash(
                json.dumps(status, sort_keys=True, default=str)
            )
        try:
            semantic_signature = str(
                self.route_semantic_dependency_signature_hash(clean_route_id) or ""
            ).strip()
        except Exception:
            semantic_signature = ""
        if not semantic_signature:
            semantic_signature = graph_text_hash(
                json.dumps(
                    {
                        "route_id": clean_route_id,
                        "target_statement_key": graph_statement_key(target_statement),
                        "contract_verdict": str(status.get("verdict") or ""),
                    },
                    sort_keys=True,
                )
            )
        self._retire_stale_route_missing_assembly_bridge_rescues(
            clean_route_id,
            current_signature_hash=clean_signature,
            contract_status=status,
            allow_deterministic_ready=allow_deterministic_ready,
        )
        identity_key = (
            (
                "route_root_tactic_failure_rescue:"
                if allow_deterministic_ready
                else "route_missing_assembly_bridge:"
            )
            + f"{clean_route_id}:{clean_signature}"
        )
        existing_id = str(
            (route.metadata or {}).get(
                "route_missing_assembly_bridge_rescue_obligation_id"
            )
            or ""
        ).strip()
        existing = self.nodes.get(existing_id) if existing_id else None
        if (
            existing is not None
            and existing.kind == "missing_obligation"
            and not self.is_superseded_tombstone(existing)
            and str((existing.metadata or {}).get("identity_key") or "").strip()
            == identity_key
        ):
            self._mark_route_missing_assembly_bridge_rescue_current(
                existing,
                signature_hash=clean_signature,
                contract_status=status,
            )
            return existing
        reason = (
            "Create a replayable Lean bridge for a ready route whose proved "
            "dependencies do not yet determine an assembly proof."
        )
        statement = (
            "Build a replayable assembly bridge for route "
            f"{graph_text_hash(clean_route_id)} with dependency signature "
            f"{clean_signature}."
        )
        shared_metadata = {
            "source": "route_missing_assembly_bridge",
            "identity_key": identity_key,
            "route_missing_assembly_bridge_rescue": True,
            "route_root_tactic_failure_rescue": bool(
                allow_deterministic_ready
            ),
            "route_missing_assembly_bridge_signature_hash": clean_signature,
            "route_missing_assembly_bridge_semantic_signature_hash": (
                semantic_signature
            ),
            "route_assembly_contract_status": status,
            "formalization_required": True,
            "materialization_required": True,
            "formalization_statement_pending": True,
            "formalization_bridge_contract": "strict_decomposition_bridge",
            "formalization_bridge_parent_statement": target_statement,
            "parent_repair_target_statement": target_statement,
            "requires_strict_smaller_bridge": True,
            "forbid_repair_target_statement": target_statement,
        }
        obligation = self.record_missing_obligation(
            statement=statement,
            reason=reason,
            source_node_id=clean_route_id,
            route_id=clean_route_id,
            phase=phase,
            turn_index=turn_index,
            error_type="route_missing_assembly_bridge",
            metadata=shared_metadata,
        )
        self._mark_route_missing_assembly_bridge_rescue_current(
            obligation,
            signature_hash=clean_signature,
            contract_status=status,
        )
        replan = self.record_replan_item(
            source_node_id=clean_route_id,
            route_id=clean_route_id,
            obligation_id=obligation.node_id,
            reason=reason,
            phase=phase,
            turn_index=turn_index,
            priority=0.35,
            metadata={
                **shared_metadata,
                "route_replan_requires_obligation": True,
                "target_statement": target_statement,
            },
        )
        self._mark_route_missing_assembly_bridge_rescue_current(
            replan,
            signature_hash=clean_signature,
            contract_status=status,
        )
        route.metadata["route_missing_assembly_bridge_rescue_obligation_id"] = (
            obligation.node_id
        )
        route.metadata["route_missing_assembly_bridge_rescue_replan_id"] = (
            replan.node_id
        )
        if allow_deterministic_ready:
            route.metadata[
                "route_root_tactic_failure_rescue_signature_hash"
            ] = clean_signature
            route.metadata.pop(
                "route_missing_assembly_bridge_signature_hash",
                None,
            )
        else:
            route.metadata[
                "route_missing_assembly_bridge_rescue_signature_hash"
            ] = clean_signature
        self.record_attempt(
            clean_route_id,
            phase=phase,
            turn_index=turn_index,
            proof="",
            verdict="route_missing_assembly_bridge_rescue_materialized",
            error_type="route_missing_assembly_bridge",
            metadata={
                "obligation_id": obligation.node_id,
                "replan_id": replan.node_id,
                "route_missing_assembly_bridge_signature_hash": clean_signature,
                "route_assembly_contract_status": status,
            },
        )
        return obligation

    def _ensure_route_assembly_contract_replans(self) -> None:
        for route in list(self.nodes.values()):
            if route.kind != "strategy_route" or self.is_superseded_tombstone(route):
                continue
            if (route.metadata or {}).get("assembled_route_proof_hash"):
                continue
            route_scope = str((route.metadata or {}).get("route_scope") or "").strip()
            if route_scope != _ROUTE_SCOPE_ROOT_ASSEMBLY:
                continue
            if not self._route_dependency_targets_are_proved(route.node_id):
                continue
            status = self.route_assembly_contract_status(route.node_id)
            if bool(status.get("ready")):
                continue
            self.ensure_route_assembly_contract_replan(route.node_id, status)

    def add_variant_relation(
        self,
        source_variant_id: str,
        target_variant_id: str,
        relation: str,
    ) -> None:
        source = str(source_variant_id or "").strip()
        target = str(target_variant_id or "").strip()
        raw = str(relation or "").strip()
        normalized = {
            "mutation": "mutates_to",
            "mutates": "mutates_to",
            "mutates_to": "mutates_to",
            "generalization": "generalizes_to",
            "generalizes": "generalizes_to",
            "generalizes_to": "generalizes_to",
            "specialization": "specializes_to",
            "specializes": "specializes_to",
            "specializes_to": "specializes_to",
        }.get(raw, raw)
        if normalized not in {"mutates_to", "generalizes_to", "specializes_to"}:
            normalized = "mutates_to"
        self._add_edge(source, target, normalized)

    def record_missing_obligation(
        self,
        *,
        statement: str = "",
        reason: str = "",
        source_node_id: str = "",
        route_id: str = "",
        phase: str = "",
        turn_index: int = 0,
        error_type: str = "",
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphNode:
        """Create a durable obligation mined from a failed/partial proof."""

        incoming_metadata = dict(metadata or {})
        raw_statement = str(statement or "").strip()
        statement_is_executable = graph_statement_is_executable(raw_statement)
        obligation_statement = (
            graph_formal_statement_text(raw_statement)
            if statement_is_executable
            else graph_identity_text(raw_statement)
        )
        reason_text = graph_identity_text(reason)
        source_id = str(source_node_id or "").strip()
        route = str(route_id or "").strip()
        identity_key = graph_identity_text(incoming_metadata.get("identity_key") or "")
        route_poisoned = self._route_is_terminally_poisoned(route)
        identity = "\n".join(
            item
            for item in [
                source_id,
                obligation_statement,
                reason_text,
                str(error_type or "").strip(),
                identity_key,
            ]
            if item
        )
        if not identity:
            raise ValueError("missing obligation requires a statement or reason")
        node_id = self.missing_obligation_node_id(identity)
        node_metadata: Dict[str, Any] = {
            "reason": reason_text,
            "source_node_id": source_id,
            "route_id": route,
            "error_type": str(error_type or "").strip(),
        }
        node_metadata.update(incoming_metadata)
        bind_graph_contract_identity_metadata(
            obligation_statement,
            node_metadata,
        )
        untrusted_generated_obligation = (
            node_metadata.get("certified_fact") is False
            or str(node_metadata.get("source") or "").strip()
            in {"post_failure_residual_work_item", "failed_proof_residual_work_item"}
        )
        if untrusted_generated_obligation:
            node_metadata["formalization_required"] = True
            node_metadata.setdefault(
                "obligation_trust",
                "untrusted_failed_proof_residual",
            )
        elif statement_is_executable:
            node_metadata.setdefault("formalization_required", False)
        elif raw_statement or reason_text or node_metadata.get("formalization_required"):
            node_metadata["formalization_required"] = True
        else:
            node_metadata["formalization_required"] = False
        if node_metadata.get("formalization_required") and not statement_is_executable:
            node_statement = obligation_statement if raw_statement else ""
        else:
            node_statement = obligation_statement or reason_text
        formalization_obligation_key = ""
        if node_metadata.get("formalization_required"):
            explicit_formalization_key = graph_identity_text(
                node_metadata.get("formalization_obligation_key") or ""
            )
            if explicit_formalization_key:
                formalization_obligation_key = explicit_formalization_key
            else:
                route_bridge_rescue = bool(
                    node_metadata.get("route_missing_assembly_bridge_rescue")
                )
                target_seed = str(
                    (
                        "route_missing_assembly_bridge"
                        if route_bridge_rescue
                        else node_metadata.get("materialization_seed")
                    )
                    or node_metadata.get("target_statement")
                    or node_metadata.get("decomposition_request_statement")
                    or obligation_statement
                    or reason_text
                    or ""
                ).strip()
                parent_text = str(
                    node_metadata.get("formalization_bridge_parent_statement")
                    or node_metadata.get("parent_repair_target_statement")
                    or node_metadata.get("materialization_parent_statement")
                    or ""
                ).strip()
                target_key = (
                    graph_statement_key(target_seed)
                    if target_seed and graph_statement_is_executable(target_seed)
                    else graph_text_hash(graph_identity_text(target_seed))
                    if target_seed
                    else ""
                )
                parent_key = (
                    graph_statement_key(parent_text)
                    if parent_text and graph_statement_is_executable(parent_text)
                    else graph_text_hash(graph_identity_text(parent_text))
                    if parent_text
                    else ""
                )
                bridge_contract = graph_identity_text(
                    node_metadata.get("formalization_bridge_contract") or ""
                )
                rescue_signature = ""
                if route_bridge_rescue:
                    rescue_signature = ":".join(
                        item
                        for item in [
                            graph_identity_text(node_metadata.get("route_id") or ""),
                            graph_identity_text(
                                node_metadata.get(
                                    "route_missing_assembly_bridge_semantic_signature_hash"
                                )
                                or node_metadata.get(
                                    "route_missing_assembly_bridge_signature_hash"
                                )
                                or ""
                            ),
                        ]
                        if item
                    )
                flavor_parts = [
                    "formalization_obligation",
                    "pending"
                    if (
                        node_metadata.get("formalization_statement_pending")
                        or not statement_is_executable
                    )
                    else "statement",
                    target_key,
                    parent_key,
                    bridge_contract,
                    rescue_signature,
                    "target_integrity"
                    if node_metadata.get("target_integrity_adjudication")
                    else "",
                ]
                canonical_seed = "\n".join(
                    item for item in flavor_parts if str(item or "").strip()
                )
                if canonical_seed:
                    formalization_obligation_key = (
                        "formalization:" + graph_text_hash(canonical_seed)
                    )
            if formalization_obligation_key:
                node_metadata["formalization_obligation_key"] = (
                    formalization_obligation_key
                )
        node_metadata = self._normalize_missing_obligation_metadata(node_metadata)
        duplicate_reused = False
        node = self.nodes.get(node_id)
        if formalization_obligation_key:
            for candidate in self.nodes.values():
                if candidate.kind != "missing_obligation":
                    continue
                candidate_key = str(
                    (candidate.metadata or {}).get("formalization_obligation_key")
                    or ""
                ).strip()
                if candidate_key != formalization_obligation_key:
                    continue
                node = candidate
                duplicate_reused = candidate.node_id != node_id
                break
        existing_node_reused = node is not None
        poisoned_duplicate_reuse = existing_node_reused and route_poisoned
        metadata_to_merge = node_metadata
        if poisoned_duplicate_reuse:
            metadata_to_merge = dict(node_metadata)
            for poisoned_route_key in (
                "route_id",
                "route_retired",
                "route_dependency_contradicted",
                "route_retirement_verdict",
                "route_retired_reason",
                "route_poisoned_descendant_suppressed",
            ):
                metadata_to_merge.pop(poisoned_route_key, None)
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="missing_obligation",
                name=f"obligation_{graph_text_hash(identity)}",
                statement=node_statement,
                status="open",
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                metadata=metadata_to_merge,
            )
            self.nodes[node_id] = node
        else:
            node.kind = "missing_obligation"
            if node_statement:
                existing_statement = str(node.statement or "").strip()
                existing_executable = graph_statement_is_executable(existing_statement)
                incoming_executable = graph_statement_is_executable(node_statement)
                if not (existing_executable and not incoming_executable):
                    node.statement = node_statement
            if phase:
                node.phase = str(phase or "")
            if turn_index:
                node.turn_index = int(turn_index or 0)
            self._merge_missing_obligation_metadata(node.metadata, metadata_to_merge)
        if duplicate_reused:
            node.metadata["formalization_duplicate_reused_last"] = True
            node.metadata["formalization_duplicate_reuse_count"] = (
                int(node.metadata.get("formalization_duplicate_reuse_count", 0) or 0)
                + 1
            )
            reuse_history = list(
                node.metadata.get("formalization_duplicate_reuse_history") or []
            )
            reuse_history.append({
                "source_node_id": source_id,
                "route_id": route,
                "statement": node_statement or raw_statement,
                "reason": reason_text,
                "error_type": str(error_type or "").strip(),
                "identity_key": identity_key,
                "turn_index": int(turn_index or 0),
                "rejected_root_failure_analysis": dict(
                    node_metadata.get("rejected_root_failure_analysis") or {}
                ),
            })
            node.metadata["formalization_duplicate_reuse_history"] = reuse_history[-12:]
        else:
            node.metadata["formalization_duplicate_reused_last"] = False
        if source_id:
            self._add_edge(source_id, node.node_id, "failure_requires")
        if route and not poisoned_duplicate_reuse:
            self._add_edge(route, node.node_id, "route_blocked_by")
        if not route_poisoned:
            self._revive_route_poisoned_node_for_live_route(
                node,
                preferred_route_id=route,
            )
        if route_poisoned:
            if poisoned_duplicate_reuse:
                node.metadata["route_poisoned_duplicate_reuse_ignored"] = True
                return node
            node.status = "rejected"
            node.proof_hash = ""
            node.metadata["route_retired"] = True
            node.metadata["route_dependency_contradicted"] = True
            node.metadata["route_retirement_verdict"] = str(
                (self.nodes.get(route).metadata or {}).get("route_retirement_verdict")
                if self.nodes.get(route) is not None
                else ""
            ) or "route_dependency_contradicted"
            node.metadata["route_retired_reason"] = str(
                (self.nodes.get(route).metadata or {}).get("route_retired_reason")
                if self.nodes.get(route) is not None
                else ""
            )
            node.metadata["route_poisoned_descendant_suppressed"] = True
            return node
        self._repair_revision_crossing_tombstones()
        source_ids, route_ids, obligation_ids = self._graph_native_source_links(node)
        source_superseded = self.is_superseded_tombstone(self.nodes.get(source_id))
        route_superseded = (
            self._route_links_are_primary_source(source_ids, obligation_ids)
            and self._all_route_links_have_superseded_dependencies(
                route_ids,
                ignore_node_id=node.node_id,
            )
        )
        if source_superseded or route_superseded:
            self._mark_node_superseded_by_source(
                node,
                source_node_id=source_id if source_superseded else route,
            )
        self._repair_graph_native_source_tombstones()
        helper = self._proved_helper_for_statement(
            node.statement,
            require_replayable_source=True,
            consumer_node=node,
        )
        if helper is not None:
            self.mark_obligation_proved_by_helper(
                node.node_id,
                helper.node_id,
                source_hash=helper.source_hash,
                proof_hash=helper.proof_hash or helper.source_hash,
            )
        return node

    @staticmethod
    def _metadata_sequence_items(value: Any) -> List[Any]:
        if isinstance(value, list):
            return list(value)
        if isinstance(value, tuple):
            return list(value)
        if isinstance(value, set):
            return sorted(value, key=str)
        if value:
            return [value]
        return []

    @staticmethod
    def _metadata_dedupe_key(value: Any) -> str:
        try:
            return json.dumps(value, sort_keys=True, default=str)
        except Exception:
            return repr(value)

    @classmethod
    def _merged_metadata_sequence(cls, *values: Any) -> List[Any]:
        merged: List[Any] = []
        seen: Set[str] = set()
        for value in values:
            for item in cls._metadata_sequence_items(value):
                if item is None:
                    continue
                if isinstance(item, str):
                    item = item.strip()
                    if not item:
                        continue
                elif not item:
                    continue
                key = cls._metadata_dedupe_key(item)
                if key in seen:
                    continue
                seen.add(key)
                merged.append(item)
        return merged

    @classmethod
    def _latest_metadata_sequence_item(cls, *values: Any) -> Any:
        latest: Any = None
        for value in values:
            for item in cls._metadata_sequence_items(value):
                if item is None:
                    continue
                if isinstance(item, str):
                    item = item.strip()
                    if not item:
                        continue
                elif not item:
                    continue
                latest = item
        return latest

    @classmethod
    def _bounded_metadata_sequence(
        cls,
        values: Sequence[Any],
        *,
        limit: int = 16,
    ) -> List[Any]:
        items = list(values or [])
        if limit <= 0 or len(items) <= limit:
            return items
        return [items[0], *items[-(limit - 1) :]]

    @classmethod
    def _normalize_missing_obligation_metadata(
        cls,
        metadata: Dict[str, Any],
    ) -> Dict[str, Any]:
        normalized: Dict[str, Any] = {}
        cls._merge_missing_obligation_metadata(normalized, dict(metadata or {}))
        return normalized

    @classmethod
    def _merge_missing_obligation_metadata(
        cls,
        existing: Dict[str, Any],
        incoming: Dict[str, Any],
    ) -> None:
        merged = dict(incoming or {})
        for scalar_key, list_key in (
            ("rejected_root_unknown_identifier", "rejected_root_unknown_identifiers"),
            ("rejected_root_missing_instance", "rejected_root_missing_instances"),
        ):
            existing_scalar = existing.get(scalar_key)
            incoming_scalar = merged.get(scalar_key)
            values = cls._merged_metadata_sequence(
                existing.get(list_key),
                existing_scalar,
                merged.get(list_key),
                incoming_scalar,
            )
            latest = cls._latest_metadata_sequence_item(
                existing.get(list_key),
                existing_scalar,
                merged.get(list_key),
                incoming_scalar,
            )
            if values:
                merged[list_key] = cls._bounded_metadata_sequence(values)
            if latest:
                merged[scalar_key] = latest

        for list_key in ("forbidden_materialization_fragments",):
            values = cls._merged_metadata_sequence(
                existing.get(list_key),
                merged.get(list_key),
            )
            if values:
                merged[list_key] = cls._bounded_metadata_sequence(values)

        failure_analyses = cls._merged_metadata_sequence(
            existing.get("rejected_root_first_failure_analysis"),
            existing.get("rejected_root_failure_analyses"),
            existing.get("rejected_root_failure_analysis"),
            existing.get("rejected_root_latest_failure_analysis"),
            merged.get("rejected_root_first_failure_analysis"),
            merged.get("rejected_root_failure_analyses"),
            merged.get("rejected_root_failure_analysis"),
            merged.get("rejected_root_latest_failure_analysis"),
        )
        latest_failure_analysis = cls._latest_metadata_sequence_item(
            existing.get("rejected_root_failure_analyses"),
            existing.get("rejected_root_failure_analysis"),
            existing.get("rejected_root_latest_failure_analysis"),
            merged.get("rejected_root_failure_analyses"),
            merged.get("rejected_root_failure_analysis"),
            merged.get("rejected_root_latest_failure_analysis"),
        )
        if failure_analyses:
            merged["rejected_root_failure_analyses"] = cls._bounded_metadata_sequence(
                failure_analyses
            )
            merged["rejected_root_first_failure_analysis"] = (
                existing.get("rejected_root_first_failure_analysis")
                or merged.get("rejected_root_first_failure_analysis")
                or failure_analyses[0]
            )
            merged["rejected_root_latest_failure_analysis"] = (
                latest_failure_analysis or failure_analyses[-1]
            )
            merged["rejected_root_failure_analysis"] = (
                latest_failure_analysis or failure_analyses[-1]
            )

        existing.update(merged)

    def record_replan_item(
        self,
        *,
        source_node_id: str = "",
        route_id: str = "",
        obligation_id: str = "",
        reason: str = "",
        phase: str = "",
        turn_index: int = 0,
        priority: float = 0.0,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphNode:
        """Queue graph-native replay/replan work after a failed route/node."""

        source_id = str(source_node_id or "").strip()
        route = str(route_id or "").strip()
        obligation = str(obligation_id or "").strip()
        reason_text = graph_identity_text(reason)
        route_poisoned = self._route_is_terminally_poisoned(route)
        identity = "\n".join(
            item for item in [source_id, route, obligation, reason_text, phase] if item
        )
        if not identity:
            raise ValueError("replan item requires a source, route, obligation, or reason")
        node_id = self.replan_node_id(identity)
        node_metadata: Dict[str, Any] = {
            "source_node_id": source_id,
            "route_id": route,
            "obligation_id": obligation,
            "reason": reason_text,
            "priority": self._coerce_float(priority),
        }
        node_metadata.update(dict(metadata or {}))
        node = self.nodes.get(node_id)
        existing_reused = node is not None
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="replan_queue_item",
                name=f"replan_{graph_text_hash(identity)}",
                statement=reason_text,
                status="open",
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                metadata=node_metadata,
            )
            self.nodes[node_id] = node
        else:
            node.kind = "replan_queue_item"
            if reason_text:
                node.statement = reason_text
            if phase:
                node.phase = str(phase or "")
            if turn_index:
                node.turn_index = int(turn_index or 0)
            node.metadata.update(node_metadata)
        if source_id:
            self._add_edge(source_id, node.node_id, "needs_replan")
        if route:
            self._add_edge(route, node.node_id, "route_replan")
        if obligation:
            self._add_edge(obligation, node.node_id, "obligation_replan")
        if route_poisoned:
            if existing_reused:
                # Re-recording through a now-poisoned route must not wipe a
                # previously queued item.  Frontier already skips terminally
                # poisoned routes; destroying the node made revival impossible.
                return node
            node.status = "rejected"
            node.proof_hash = ""
            node.metadata["route_retired"] = True
            node.metadata["route_dependency_contradicted"] = True
            node.metadata["route_retirement_verdict"] = str(
                (self.nodes.get(route).metadata or {}).get("route_retirement_verdict")
                if self.nodes.get(route) is not None
                else ""
            ) or "route_dependency_contradicted"
            node.metadata["route_retired_reason"] = str(
                (self.nodes.get(route).metadata or {}).get("route_retired_reason")
                if self.nodes.get(route) is not None
                else ""
            )
            node.metadata["route_poisoned_descendant_suppressed"] = True
            return node
        self._repair_revision_crossing_tombstones()
        if obligation:
            self._sync_replan_with_obligation_status(node, obligation)
        source_ids, route_ids, obligation_ids = self._graph_native_source_links(node)
        source_superseded = self.is_superseded_tombstone(self.nodes.get(source_id))
        route_superseded = (
            self._route_links_are_primary_source(source_ids, obligation_ids)
            and self._all_route_links_have_superseded_dependencies(
                route_ids,
                ignore_node_id=node.node_id,
            )
        )
        obligation_superseded = self.is_superseded_tombstone(
            self.nodes.get(obligation)
        )
        if source_superseded or route_superseded or obligation_superseded:
            self._mark_node_superseded_by_source(
                node,
                source_node_id=(
                    source_id
                    if source_superseded
                    else obligation
                    if obligation_superseded
                    else route
                ),
            )
        self._repair_graph_native_source_tombstones()
        return node

    def _proved_helper_for_statement(
        self,
        statement: str,
        *,
        require_replayable_source: bool = False,
        consumer_node: Optional[ProofGraphNode] = None,
    ) -> Optional[ProofGraphNode]:
        statement_key = graph_statement_key(statement)
        if not statement_key:
            return None
        for node in self.nodes_by_kind("helper"):
            if node.status != "proved":
                continue
            structurally_vacuous = "structurally_vacuous_helper" in {
                str(tag or "").strip()
                for tag in list(
                    (node.metadata or {}).get("verified_helper_quality_tags")
                    or []
                )
            }
            exact_scope_authorized = bool(
                consumer_node is not None
                and consumer_node.kind
                in {"proposed_claim", "formal_variant", "missing_obligation"}
                and (consumer_node.metadata or {}).get(
                    "allow_structurally_vacuous_helper"
                )
                is True
            )
            if structurally_vacuous and not exact_scope_authorized:
                continue
            if require_replayable_source and not self._helper_has_replayable_source(
                node,
                allow_advisory_negative_evidence_exact=True,
                exact_statement_key=statement_key,
            ):
                continue
            if graph_statement_key(node.statement) == statement_key:
                if not require_replayable_source:
                    metadata = dict(node.metadata or {})
                    source_recorded = bool(
                        str(metadata.get("verified_helper_source") or "").strip()
                        or str(metadata.get("verified_helper_source_hash") or "").strip()
                        or str(metadata.get("verified_helper_render_policy") or "").strip()
                    )
                    if source_recorded and not self._helper_has_replayable_source(
                        node,
                        allow_advisory_negative_evidence_exact=True,
                        exact_statement_key=statement_key,
                    ):
                        continue
                return node
        return None

    def _helper_has_hash_locked_source(
        self,
        helper: Optional[ProofGraphNode],
    ) -> bool:
        """Return whether a proved helper's source is hash-locked, without
        requiring a formalization-bridge admission receipt.

        Used to keep leftover branch-local helpers out of ``unproved_node_ids``
        without treating a stale or mismatched ``verified_helper_source``
        string as authority.
        """

        if self._helper_has_replayable_source(helper):
            return True
        if (
            helper is None
            or helper.kind != "helper"
            or helper.status != "proved"
            or self.is_superseded_tombstone(helper)
        ):
            return False
        metadata = dict(helper.metadata or {})
        source = str(metadata.get("verified_helper_source") or "").strip()
        if not source:
            return False
        declared_name = helper_decl_name(source)
        if declared_name != helper.name:
            return False
        source_body = helper_decl_body(source)
        if not source_body or has_sorry_or_admit(source_body):
            return False
        source_hash = graph_text_hash(source)
        recorded_hash = str(metadata.get("verified_helper_source_hash") or "").strip()
        if recorded_hash and recorded_hash != source_hash:
            return False
        return bool(
            helper.source_hash == source_hash and helper.proof_hash == source_hash
        )

    def _helper_has_replayable_source(
        self,
        helper: Optional[ProofGraphNode],
        *,
        allow_advisory_negative_evidence_exact: bool = False,
        allow_formalization_bridge_support: bool = False,
        exact_statement_key: str = "",
    ) -> bool:
        if (
            helper is None
            or helper.kind != "helper"
            or helper.status != "proved"
            or self.is_superseded_tombstone(helper)
        ):
            return False
        metadata = dict(helper.metadata or {})
        render_policy = str(metadata.get("verified_helper_render_policy") or "").strip()
        if not _helper_render_policy_context_visible(render_policy):
            helper_statement_key = graph_statement_key(helper.statement)
            bridge_support_allowed = bool(
                allow_formalization_bridge_support
                and render_policy
                in {
                    "advisory_requires_unproved_premise",
                    "advisory_route_support_only",
                    "advisory_root_equivalent",
                    # A negative-conclusion lemma can be legitimate route
                    # support without refuting the bridge parent (for
                    # example, an oddness/divisibility exclusion).  The
                    # record-time exact-parent-negation guard handles the
                    # contradictory case; this path still requires complete
                    # replayable source and the source-bound admission
                    # receipt below.
                    "advisory_negative_evidence",
                }
            )
            exact_advisory_allowed = bool(
                render_policy
                in {"advisory_negative_evidence", "advisory_root_equivalent"}
                and (allow_advisory_negative_evidence_exact or exact_statement_key)
                and exact_statement_key
                and helper_statement_key
                == str(exact_statement_key or "").strip()
            )
            if not (bridge_support_allowed or exact_advisory_allowed):
                return False
        source = str(metadata.get("verified_helper_source") or "").strip()
        if not source:
            return False
        declared_name = helper_decl_name(source)
        if declared_name != helper.name:
            return False
        source_statement = helper_decl_statement(source)
        if not source_statement:
            return False
        if graph_statement_key(source_statement) != graph_statement_key(
            helper.statement
        ):
            return False
        source_body = helper_decl_body(source)
        if not source_body or has_sorry_or_admit(source_body):
            return False
        source_hash = graph_text_hash(source)
        recorded_hash = str(metadata.get("verified_helper_source_hash") or "").strip()
        if recorded_hash and recorded_hash != source_hash:
            return False
        if not helper.source_hash or helper.source_hash != source_hash:
            return False
        if not helper.proof_hash or helper.proof_hash != source_hash:
            return False
        source_mentions_solution = _helper_source_mentions_solution(source)
        if source_mentions_solution:
            # Never let an admission receipt introduce a solution-bearing
            # declaration name or a *new* solution symbol through the proof
            # body. A visible-answer proof may legitimately unfold the exact
            # target constant already present in its statement (as B1 does),
            # but the receipt cannot launder any additional answer reference.
            statement_solution_refs = _helper_source_solution_references(
                source_statement
            )
            if _helper_source_solution_references(declared_name or ""):
                return False
            if not _helper_source_solution_references(source_body).issubset(
                statement_solution_refs
            ):
                return False
            admission_policy = str(
                metadata.get("verified_helper_answer_safety_policy") or ""
            ).strip()
            if admission_policy != "official_answer_visible":
                return False
        if source_mentions_solution or allow_formalization_bridge_support:
            # Bridge support is an authority-producing path: a verified helper
            # can cause a new open premise to be scheduled. Require the
            # dossier's source-bound admission receipt even for ordinary
            # non-solution declarations, rather than treating graph-local
            # source text and matching hashes as independent Lean authority.
            admission_policy = str(
                metadata.get("verified_helper_answer_safety_policy") or ""
            ).strip()
            if not graph_helper_answer_safety_receipt_matches(
                str(
                    metadata.get("verified_helper_answer_safety_receipt")
                    or ""
                ),
                source_hash=source_hash,
                source_digest=hashlib.sha256(
                    source.encode("utf-8", errors="replace")
                ).hexdigest(),
                statement_key=graph_statement_key(source_statement),
                environment_hash=str(
                    metadata.get("verified_helper_environment_hash") or ""
                ).strip(),
                render_policy=render_policy,
                visibility_policy=str(
                    metadata.get("verified_helper_visibility_policy") or ""
                ).strip(),
                admission_policy=admission_policy,
            ):
                return False
        return True

    def _helper_has_graph_only_certificate(
        self,
        helper: Optional[ProofGraphNode],
        node: Optional[ProofGraphNode],
    ) -> bool:
        """Return whether ``helper`` may unlock search but still needs source."""

        if (
            helper is None
            or helper.kind != "helper"
            or helper.status != "proved"
            or self.is_superseded_tombstone(helper)
            or node is None
            or node.kind not in {"proposed_claim", "formal_variant"}
        ):
            return False
        helper_key = graph_statement_key(getattr(helper, "statement", "") or "")
        node_key = graph_statement_key(getattr(node, "statement", "") or "")
        if not (helper_key and node_key and helper_key == node_key):
            return False
        if self._helper_has_replayable_source(helper):
            return False
        metadata = dict(helper.metadata or {})
        render_policy = str(metadata.get("verified_helper_render_policy") or "").strip()
        if not _helper_render_policy_context_visible(render_policy):
            return False
        source_recorded = bool(
            str(metadata.get("verified_helper_source") or "").strip()
            or str(metadata.get("verified_helper_source_hash") or "").strip()
        )
        if source_recorded:
            return False
        return bool(helper.proof_hash or helper.source_hash)

    def _helper_needs_replay_materialization(
        self,
        helper: Optional[ProofGraphNode],
    ) -> bool:
        """Return whether a directly cited helper has graph evidence only."""

        if (
            helper is None
            or helper.kind != "helper"
            or helper.status != "proved"
            or self.is_superseded_tombstone(helper)
        ):
            return False
        if self._helper_has_replayable_source(helper):
            return False
        metadata = dict(helper.metadata or {})
        if not _helper_render_policy_context_visible(
            str(metadata.get("verified_helper_render_policy") or "")
        ):
            return False
        source_recorded = bool(
            str(metadata.get("verified_helper_source") or "").strip()
            or str(metadata.get("verified_helper_source_hash") or "").strip()
        )
        if source_recorded:
            return False
        return bool(helper.proof_hash or helper.source_hash)

    @staticmethod
    def _clear_replay_materialization_metadata(node: Optional[ProofGraphNode]) -> None:
        if node is None:
            return
        for key in _REPLAY_MATERIALIZATION_METADATA_KEYS:
            node.metadata.pop(key, None)

    def _mark_replay_materialization_needed(
        self,
        node: Optional[ProofGraphNode],
        helper: Optional[ProofGraphNode],
        *,
        reason: str = "graph_only_helper_certificate",
    ) -> None:
        if node is None or helper is None:
            return
        statement_key = graph_statement_key(getattr(node, "statement", "") or "")
        node.metadata["needs_replay_materialization"] = True
        node.metadata["replay_materialization_reason"] = str(reason or "")
        node.metadata["replay_materialization_helper_name"] = str(helper.name or "")
        node.metadata["replay_materialization_helper_node_id"] = str(
            helper.node_id or ""
        )
        node.metadata["replay_materialization_statement_key"] = statement_key
        node.metadata["replay_materialization_helper_proof_hash"] = str(
            helper.proof_hash or ""
        )
        node.metadata["replay_materialization_helper_source_hash"] = str(
            helper.source_hash or ""
        )

    def _node_replay_materialization_helper(
        self,
        node: Optional[ProofGraphNode],
        *,
        mutate: bool = True,
    ) -> Optional[ProofGraphNode]:
        """Return the graph-only helper whose source blocks final citation.

        ``mutate=False`` is the scheduler-quotation contract: compute the same
        eligibility result without repairing or recording materialization debt.
        """

        if (
            node is None
            or node.status != "proved"
            or self.is_superseded_tombstone(node)
            or self._graph_native_source_is_superseded(node)
        ):
            return None
        if node.kind == "helper":
            if self._helper_has_replayable_source(node):
                if mutate:
                    self._clear_replay_materialization_metadata(node)
                return None
            if self._helper_needs_replay_materialization(node):
                if mutate:
                    self._mark_replay_materialization_needed(
                        node,
                        node,
                        reason="direct_graph_only_helper_citation",
                    )
                return node
            return None
        if node.kind not in {"proposed_claim", "formal_variant"}:
            return None
        helper_edges = {
            "proposed_claim": {"claim_verified_by"},
            "formal_variant": {"variant_verified_by"},
        }.get(node.kind, set())
        candidates: List[ProofGraphNode] = []
        seen: Set[str] = set()

        def add(helper: Optional[ProofGraphNode]) -> None:
            if (
                helper is None
                or helper.kind != "helper"
                or helper.node_id in seen
            ):
                return
            seen.add(helper.node_id)
            candidates.append(helper)

        metadata = dict(node.metadata or {})
        add(self.nodes.get(str(metadata.get("verified_by_helper_node_id") or "")))
        helper_name = str(metadata.get("verified_by_helper_name") or "").strip()
        if helper_name:
            add(self.nodes.get(self.helper_name_to_node_id.get(helper_name, "")))
        for edge in self.outgoing(node.node_id):
            if edge.kind in helper_edges:
                add(self.nodes.get(edge.target))
        node_key = graph_statement_key(node.statement)
        if node_key:
            for helper in self.nodes_by_kind("helper"):
                if graph_statement_key(helper.statement) == node_key:
                    add(helper)
        for helper in candidates:
            if self._helper_has_replayable_source(helper):
                if mutate:
                    self._clear_replay_materialization_metadata(node)
                return None
        for helper in candidates:
            if self._helper_has_graph_only_certificate(helper, node):
                if mutate:
                    self._mark_replay_materialization_needed(node, helper)
                return helper
        return None

    def _route_replay_materialization_nodes(
        self,
        route_id: str,
        *,
        mutate: bool = True,
    ) -> List[ProofGraphNode]:
        nodes: List[ProofGraphNode] = []
        seen: Set[str] = set()
        for edge in self._route_dependency_edges(route_id):
            node = self.nodes.get(edge.target)
            if node is None or node.node_id in seen:
                continue
            if self._node_replay_materialization_helper(
                node,
                mutate=mutate,
            ) is None:
                continue
            seen.add(node.node_id)
            nodes.append(node)
        return nodes

    def _route_dependency_edges(self, route_id: str) -> List[ProofGraphEdge]:
        route = str(route_id or "").strip()
        if not route:
            return []
        route_node = self.nodes.get(route)
        route_metadata = dict(getattr(route_node, "metadata", {}) or {})
        current_internal_ids = {
            str(
                route_metadata.get("route_assembly_contract_replan_id") or ""
            ).strip(),
            str(
                route_metadata.get(
                    "route_assembly_contract_replan_obligation_id"
                )
                or ""
            ).strip(),
        }
        current_internal_ids.discard("")

        def is_internal_contract_control(edge: ProofGraphEdge) -> bool:
            target_id = str(edge.target or "").strip()
            if target_id in current_internal_ids:
                return True
            target = self.nodes.get(target_id)
            if target is None or target.kind not in {
                "missing_obligation",
                "replan_queue_item",
            }:
                return False
            metadata = dict(target.metadata or {})
            return bool(
                str(target.phase or "").strip() == "route_assembly_contract"
                and metadata.get("schedulable") is False
                and metadata.get("formalization_required") is True
                and metadata.get("root_equivalent_obligation_suppressed") is True
            )

        return [
            edge
            for edge in self.outgoing(route)
            if edge.kind in _ROUTE_DEPENDENCY_EDGE_KINDS
            and not is_internal_contract_control(edge)
            and not bool(
                (
                    getattr(self.nodes.get(str(edge.target or "")), "metadata", {})
                    or {}
                ).get("route_missing_assembly_bridge_rescue")
            )
        ]

    def _route_dependency_helper_nodes(
        self,
        target: Optional[ProofGraphNode],
    ) -> List[ProofGraphNode]:
        if target is None:
            return []
        seen: Set[str] = set()
        helpers: List[ProofGraphNode] = []

        def add(helper: Optional[ProofGraphNode]) -> None:
            if (
                helper is None
                or helper.kind != "helper"
                or helper.node_id in seen
            ):
                return
            seen.add(helper.node_id)
            helpers.append(helper)

        if target.kind == "helper":
            add(target)
        metadata = dict(target.metadata or {})
        helper_node_id = str(metadata.get("verified_by_helper_node_id") or "").strip()
        if helper_node_id:
            add(self.nodes.get(helper_node_id))
        helper_name = str(metadata.get("verified_by_helper_name") or "").strip()
        if helper_name:
            add(self.nodes.get(self.helper_name_to_node_id.get(helper_name, "")))
        resolved_helper_node_id = str(
            metadata.get("resolved_by_helper_node_id") or ""
        ).strip()
        if resolved_helper_node_id:
            add(self.nodes.get(resolved_helper_node_id))
        resolved_helper_name = str(
            metadata.get("resolved_by_helper_name") or ""
        ).strip()
        if resolved_helper_name:
            add(self.nodes.get(self.helper_name_to_node_id.get(resolved_helper_name, "")))
        target_statement_key = graph_statement_key(target.statement)
        if target_statement_key:
            for helper in self.nodes_by_kind("helper"):
                if helper.status != "proved" or self.is_superseded_tombstone(helper):
                    continue
                if graph_statement_key(helper.statement) == target_statement_key:
                    add(helper)
        return helpers

    def _route_dependency_helper_fingerprints(
        self,
        target: Optional[ProofGraphNode],
    ) -> List[Dict[str, str]]:
        fingerprints: List[Dict[str, str]] = []
        for helper in self._route_dependency_helper_nodes(target):
            metadata = dict(helper.metadata or {})
            fingerprints.append(
                {
                    "helper_node_id": str(helper.node_id or ""),
                    "helper_name": str(helper.name or ""),
                    "helper_status": str(helper.status or ""),
                    "helper_source_hash": str(helper.source_hash or ""),
                    "helper_proof_hash": str(helper.proof_hash or ""),
                    "helper_statement_key": graph_statement_key(helper.statement),
                    "verified_helper_source_hash": str(
                        metadata.get("verified_helper_source_hash") or ""
                    ),
                    "verified_helper_render_policy": str(
                        metadata.get("verified_helper_render_policy") or ""
                    ),
                    "replayable_source": (
                        "1" if self._helper_has_replayable_source(helper) else "0"
                    ),
                }
            )
        return sorted(
            fingerprints,
            key=lambda item: (item["helper_node_id"], item["helper_name"]),
        )

    def route_dependency_signature(self, route_id: str) -> List[Dict[str, Any]]:
        signature: List[Dict[str, Any]] = []
        route = self.nodes.get(str(route_id or "").strip())
        for edge in sorted(
            self._route_dependency_edges(route_id),
            key=lambda item: (str(item.kind or ""), str(item.target or "")),
        ):
            target = self.nodes.get(edge.target)
            metadata = dict(target.metadata or {}) if target is not None else {}
            signature.append(
                {
                    "edge_kind": str(edge.kind or ""),
                    "node_id": str(edge.target or ""),
                    "kind": str(getattr(target, "kind", "") or "")
                    if target
                    else "",
                    "statement": str(getattr(target, "statement", "") or "")
                    if target
                    else "",
                    "statement_key": graph_statement_key(
                        getattr(target, "statement", "") if target else ""
                    ),
                    "status": str(getattr(target, "status", "") or "")
                    if target
                    else "",
                    "source_hash": str(getattr(target, "source_hash", "") or "")
                    if target
                    else "",
                    "proof_hash": str(getattr(target, "proof_hash", "") or "")
                    if target
                    else "",
                    "verified_helper_source_hash": str(
                        metadata.get("verified_helper_source_hash") or ""
                    ),
                    "verified_by_helper_name": str(
                        metadata.get("verified_by_helper_name") or ""
                    ),
                    "verified_by_helper_node_id": str(
                        metadata.get("verified_by_helper_node_id") or ""
                    ),
                    "resolved_by_helper_name": str(
                        metadata.get("resolved_by_helper_name") or ""
                    ),
                    "resolved_by_helper_node_id": str(
                        metadata.get("resolved_by_helper_node_id") or ""
                    ),
                    "proposal_revision": str(metadata.get("proposal_revision") or ""),
                    "helper_replayability": self._route_dependency_helper_fingerprints(
                        target
                    ),
                }
            )
        contract_signature = self._route_assembly_contract_signature(route)
        if contract_signature:
            signature.append(
                {
                    "edge_kind": "route_assembly_contract",
                    "node_id": str(getattr(route, "node_id", "") or ""),
                    "kind": "strategy_route_contract",
                    **contract_signature,
                }
            )
        return signature

    def route_dependency_signature_hash(self, route_id: str) -> str:
        return graph_text_hash(
            json.dumps(self.route_dependency_signature(route_id), sort_keys=True)
        )

    def route_semantic_dependency_signature(self, route_id: str) -> List[Dict[str, Any]]:
        """Return mathematical route state without replay/provenance identity.

        Generated helper names, node ids, and certificate hashes are necessary
        for exact replay invalidation, but they must not make an alpha-equivalent
        route look like new mathematical work.  Rescue/formalization dedupe uses
        this projection while assembly replay keeps using
        :meth:`route_dependency_signature`.
        """

        signature: List[Dict[str, Any]] = []
        route = self.nodes.get(str(route_id or "").strip())
        for edge in sorted(
            self._route_dependency_edges(route_id),
            key=lambda item: (
                str(item.kind or ""),
                graph_statement_key(
                    str(getattr(self.nodes.get(item.target), "statement", "") or "")
                ),
            ),
        ):
            target = self.nodes.get(edge.target)
            statement = str(getattr(target, "statement", "") or "")
            signature.append(
                {
                    "edge_kind": str(edge.kind or ""),
                    "kind": str(getattr(target, "kind", "") or "") if target else "",
                    "statement_key": graph_statement_key(statement)
                    or graph_text_hash(graph_identity_text(statement)),
                    "status": str(getattr(target, "status", "") or "")
                    if target
                    else "",
                }
            )
        contract_signature = self._route_assembly_contract_signature(route)
        if contract_signature:
            required_statement_keys = []
            for node_id in list(contract_signature.get("required_node_ids") or []):
                node = self.nodes.get(str(node_id or "").strip())
                statement = str(getattr(node, "statement", "") or "")
                key = graph_statement_key(statement) or (
                    graph_text_hash(graph_identity_text(statement)) if statement else ""
                )
                if key:
                    required_statement_keys.append(key)
            signature.append(
                {
                    "edge_kind": "route_assembly_contract",
                    "kind": "strategy_route_contract",
                    "route_scope": str(contract_signature.get("route_scope") or ""),
                    "contract_scope": str(
                        contract_signature.get("contract_scope") or ""
                    ),
                    "target_statement_key": str(
                        contract_signature.get("target_statement_key") or ""
                    ),
                    "required_statement_keys": sorted(
                        dict.fromkeys(required_statement_keys)
                    ),
                }
            )
        by_semantic_key = {
            json.dumps(item, sort_keys=True, default=str): item for item in signature
        }
        return [by_semantic_key[key] for key in sorted(by_semantic_key)]

    def route_semantic_dependency_signature_hash(self, route_id: str) -> str:
        return graph_text_hash(
            json.dumps(
                self.route_semantic_dependency_signature(route_id),
                sort_keys=True,
            )
        )

    def _helper_certifies_node(
        self,
        helper: Optional[ProofGraphNode],
        node: Optional[ProofGraphNode],
    ) -> bool:
        if (
            helper is None
            or helper.kind != "helper"
            or helper.status != "proved"
            or self.is_superseded_tombstone(helper)
            or node is None
        ):
            return False
        helper_metadata = dict(getattr(helper, "metadata", {}) or {})
        node_metadata = dict(getattr(node, "metadata", {}) or {})
        if (
            "structurally_vacuous_helper"
            in {
                str(tag or "").strip()
                for tag in list(
                    helper_metadata.get("verified_helper_quality_tags") or []
                )
            }
            and node.kind
            in {"proposed_claim", "formal_variant", "missing_obligation"}
            and node_metadata.get("allow_structurally_vacuous_helper") is not True
        ):
            return False
        helper_environment_hash = str(
            helper_metadata.get("verified_helper_environment_hash") or ""
        ).strip()
        node_environment_hash = str(
            node_metadata.get("statement_environment_hash") or ""
        ).strip()
        # Retirement is an exact-environment operation. A monotone extension
        # preserves old declarations, but can change notation, instances, and
        # elaboration of a newly-created target. Structural similarity does
        # not authorize crossing that boundary. Blank/legacy targets likewise
        # remain fail-closed against normally stamped helpers.
        if helper_environment_hash != node_environment_hash:
            return False
        exact_graph_native = node.kind in {
            "proposed_claim",
            "formal_variant",
            "missing_obligation",
            "proof_state_root",
            "proof_state_child_goal",
        }
        helper_key = ""
        node_key = ""
        if exact_graph_native:
            helper_key = graph_statement_key(getattr(helper, "statement", "") or "")
            node_key = graph_statement_key(getattr(node, "statement", "") or "")
            helper_contract_identity = graph_helper_bound_contract_identity(helper)
            node_contract_identity = graph_node_bound_contract_identity(node)
            helper_parsed_identity = parse_lean_contract_identity(
                helper_contract_identity
            )
            node_parsed_identity = parse_lean_contract_identity(
                node_contract_identity
            )
            structural_match = bool(
                helper_parsed_identity is not None
                and node_parsed_identity is not None
                and helper_parsed_identity[0] == node_parsed_identity[0]
            )
            structural_conflict = bool(
                helper_parsed_identity is not None
                and node_parsed_identity is not None
                and not structural_match
            )
            if structural_conflict:
                return False
            # Unbound format-valid litter is not authority, but it is still a
            # conflict signal against a helper's bound identity. Bind strips
            # every alias key, so legacy reinject may land on any of them.
            if (
                helper_parsed_identity is not None
                and any(
                    parse_lean_contract_identity(raw) is not None
                    and parse_lean_contract_identity(raw)[0]
                    != helper_parsed_identity[0]
                    for raw in _graph_metadata_raw_lean_identities(node_metadata)
                )
                and not structural_match
            ):
                return False
            if not (
                structural_match
                or (helper_key and node_key and helper_key == node_key)
            ):
                return False
        metadata = dict(helper.metadata or {})
        render_policy = str(metadata.get("verified_helper_render_policy") or "").strip()
        allow_advisory_negative_evidence_exact = bool(
            render_policy == "advisory_negative_evidence"
            and exact_graph_native
            and node_key
            and not graph_node_frontier_quarantined(node)
        )
        allow_hidden_exact_certificate = bool(
            exact_graph_native
            and node.kind == "missing_obligation"
            and node_key
            and helper_key == node_key
            and render_policy in {
                "advisory_root_equivalent",
                "advisory_negative_evidence",
            }
            and not graph_node_frontier_quarantined(node)
        )
        has_decl_source = bool(
            str(metadata.get("verified_helper_source") or "").strip()
            or str(metadata.get("verified_helper_source_hash") or "").strip()
        )
        if self._helper_has_graph_only_certificate(helper, node):
            return True
        if exact_graph_native or has_decl_source:
            return self._helper_has_replayable_source(
                helper,
                allow_advisory_negative_evidence_exact=allow_advisory_negative_evidence_exact,
                exact_statement_key=(
                    node_key
                    if allow_advisory_negative_evidence_exact
                    or allow_hidden_exact_certificate
                    else ""
                ),
            )
        return bool(helper.proof_hash or helper.source_hash)

    def _repair_non_theorem_graph_targets(self) -> None:
        """Reapply theorem-target invariants to rehydrated legacy graph nodes."""

        for node in list(self.nodes.values()):
            if node.kind in {"proposed_claim", "formal_variant"}:
                reason = graph_statement_non_theorem_reason(node.statement)
                if not reason:
                    continue
                _mark_non_theorem_graph_target(
                    node,
                    reason=reason,
                    raw_statement=node.statement,
                )
                continue
            if node.kind != "missing_obligation":
                continue
            statement = str(node.statement or "").strip()
            if not statement:
                continue
            reason = graph_statement_non_theorem_reason(statement)
            if not reason:
                continue
            node.metadata["formalization_required"] = True
            node.metadata["schedulable"] = False
            node.metadata["graph_statement_non_theorem"] = True
            node.metadata["graph_statement_non_theorem_reason"] = reason
            if node.status == "proved":
                node.status = "open"
                node.proof_hash = ""
                node.metadata[
                    "rehydration_status_repair"
                ] = "proved_non_theorem_obligation_requires_formalization"

    def resolve_existing_proved_helper_matches(self) -> None:
        """Repair graph-native nodes that duplicate already proved helpers."""

        for claim in self.nodes_by_kind("proposed_claim"):
            helper = self._proved_helper_for_statement(
                claim.statement,
                require_replayable_source=False,
                consumer_node=claim,
            )
            if helper is None:
                continue
            self.mark_claim_proved_by_helper(
                claim.node_id,
                helper.node_id,
                source_hash=helper.source_hash,
                proof_hash=helper.proof_hash or helper.source_hash,
            )
        for variant in self.nodes_by_kind("formal_variant"):
            helper = self._proved_helper_for_statement(
                variant.statement,
                require_replayable_source=False,
                consumer_node=variant,
            )
            if helper is None:
                continue
            self.mark_variant_proved_by_helper(
                variant.node_id,
                helper.node_id,
                source_hash=helper.source_hash,
                proof_hash=helper.proof_hash or helper.source_hash,
            )
        for obligation in self.nodes_by_kind("missing_obligation"):
            helper = self._proved_helper_for_statement(
                obligation.statement,
                require_replayable_source=True,
                consumer_node=obligation,
            )
            if helper is None:
                continue
            self.mark_obligation_proved_by_helper(
                obligation.node_id,
                helper.node_id,
                source_hash=helper.source_hash,
                proof_hash=helper.proof_hash or helper.source_hash,
            )
        for replan in self.nodes_by_kind("replan_queue_item"):
            obligation_id = str(
                (replan.metadata or {}).get("obligation_id") or ""
            ).strip()
            if obligation_id:
                self._sync_replan_with_obligation_status(replan, obligation_id)
                continue
            for edge in self.incoming(replan.node_id, kind="obligation_replan"):
                self._sync_replan_with_obligation_status(replan, edge.source)
                break

    def _supersede_unmatched_child_variants_for_claim(
        self,
        *,
        claim_node_id: str,
        active_statement: str,
        helper_node_id: str = "",
        helper_name: str = "",
    ) -> None:
        claim_id = str(claim_node_id or "").strip()
        active_key = graph_statement_key(active_statement)
        if not claim_id or not active_key:
            return
        variant_ids = {
            edge.target
            for edge in self.outgoing(claim_id, kind="claim_formalized_as")
        }
        for variant in self.nodes_by_kind("formal_variant"):
            parent_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
            if parent_id == claim_id:
                variant_ids.add(variant.node_id)
        changed = False
        for variant_id in variant_ids:
            variant = self.nodes.get(variant_id)
            if variant is None or variant.kind != "formal_variant":
                continue
            if self.is_superseded_tombstone(variant):
                continue
            if graph_statement_key(variant.statement) == active_key:
                continue
            if self._proved_node_has_durable_certificate(variant):
                variant.metadata["proved_variant_preserved_from_claim_supersession"] = (
                    active_key
                )
                continue
            if helper_node_id:
                self._add_edge(variant.node_id, helper_node_id, "proposal_superseded_by")
            variant.metadata["superseded_active_statement_key"] = active_key
            variant.metadata["verified_by_helper_name"] = str(helper_name or "")
            self._mark_node_superseded_by_source(
                variant,
                source_node_id=claim_id,
            )
            self.record_attempt(
                variant.node_id,
                phase="variant_superseded_by_verified_claim",
                turn_index=0,
                proof="",
                verdict="proof_policy_rejected",
                error_type="proposal_superseded",
                metadata={
                    "claim_node_id": claim_id,
                    "helper_name": str(helper_name or ""),
                    "active_statement_key": active_key,
                },
            )
            changed = True
        if changed:
            self.enforce_superseded_tombstones()

    def repair_proved_claim_child_variant_tombstones(self) -> None:
        """Repair legacy graphs with proved claims and stale child variants."""

        for claim in self.nodes_by_kind("proposed_claim"):
            if claim.status != "proved" or self.is_superseded_tombstone(claim):
                continue
            self._supersede_unmatched_child_variants_for_claim(
                claim_node_id=claim.node_id,
                active_statement=claim.statement,
            )

    def mark_claim_proved_by_helper(
        self,
        claim_id: str,
        helper_node_id: str = "",
        *,
        source_hash: str = "",
        proof_hash: str = "",
        support_names: Optional[Iterable[str]] = None,
    ) -> None:
        claim = self.nodes.get(str(claim_id or "").strip())
        if claim is None or claim.kind != "proposed_claim":
            return
        if bool((claim.metadata or {}).get("proposal_superseded")):
            return
        helper = self.nodes.get(str(helper_node_id or "").strip())
        if helper is None:
            claim.metadata["uncertified_claim_proved_ignored"] = True
            return
        if not self._helper_certifies_node(helper, claim):
            claim.metadata["uncertified_claim_proved_ignored"] = True
            return
        self._add_edge(claim.node_id, helper.node_id, "claim_verified_by")
        claim.metadata["verified_by_helper_name"] = helper.name
        claim.metadata["verified_by_helper_node_id"] = helper.node_id
        if self._helper_has_graph_only_certificate(helper, claim):
            self._mark_replay_materialization_needed(claim, helper)
        else:
            self._clear_replay_materialization_metadata(claim)
        self.mark_node_proved(
            claim.node_id,
            source_hash=source_hash or helper.source_hash,
            proof_hash=proof_hash
            or helper.proof_hash
            or helper.source_hash,
            support_names=support_names,
        )
        self._supersede_unmatched_child_variants_for_claim(
            claim_node_id=claim.node_id,
            active_statement=claim.statement,
            helper_node_id=helper.node_id,
            helper_name=helper.name,
        )

    def mark_variant_proved_by_helper(
        self,
        variant_id: str,
        helper_node_id: str = "",
        *,
        source_hash: str = "",
        proof_hash: str = "",
        support_names: Optional[Iterable[str]] = None,
    ) -> None:
        variant = self.nodes.get(str(variant_id or "").strip())
        if variant is None or variant.kind != "formal_variant":
            return
        if bool((variant.metadata or {}).get("proposal_superseded")):
            return
        helper = self.nodes.get(str(helper_node_id or "").strip())
        if helper is None:
            variant.metadata["uncertified_variant_proved_ignored"] = True
            return
        if not self._helper_certifies_node(helper, variant):
            variant.metadata["uncertified_variant_proved_ignored"] = True
            return
        self._add_edge(variant.node_id, helper.node_id, "variant_verified_by")
        variant.metadata["verified_by_helper_name"] = helper.name
        variant.metadata["verified_by_helper_node_id"] = helper.node_id
        if self._helper_has_graph_only_certificate(helper, variant):
            self._mark_replay_materialization_needed(variant, helper)
        else:
            self._clear_replay_materialization_metadata(variant)
        self.mark_node_proved(
            variant.node_id,
            source_hash=source_hash or helper.source_hash,
            proof_hash=proof_hash
            or helper.proof_hash
            or helper.source_hash,
            support_names=support_names,
        )
        claim_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
        claim = self.nodes.get(claim_id)
        if (
            claim is not None
            and claim.kind == "proposed_claim"
            and graph_statement_key(claim.statement)
            and graph_statement_key(claim.statement) == graph_statement_key(variant.statement)
        ):
            self.mark_claim_proved_by_helper(
                claim_id,
                helper_node_id,
                source_hash=source_hash,
                proof_hash=proof_hash,
                support_names=support_names,
            )

    def record_obligation_bridge_support(
        self,
        obligation_id: str,
        helper_node_id: str = "",
        *,
        formal_statement: str = "",
        bridge_reason: str = "",
        parent_statement: str = "",
        phase: str = "",
        turn_index: int = 0,
        source_hash: str = "",
        support_names: Optional[Iterable[str]] = None,
        parent_proof_binder_structural_hashes: Optional[Iterable[str]] = None,
        helper_proof_binder_structural_hashes: Optional[Iterable[str]] = None,
    ) -> bool:
        """Record a verified helper as support for, not proof of, an obligation.

        A decomposition bridge can be useful route evidence without certifying
        the selected informal/abstract obligation.  This keeps the parent open
        for assembly while preserving the Lean-checked helper as graph support.
        """

        obligation = self.nodes.get(str(obligation_id or "").strip())
        if obligation is None or obligation.kind != "missing_obligation":
            return False
        if self.is_superseded_tombstone(obligation):
            self._enforce_superseded_tombstone(obligation)
            return False
        helper = self.nodes.get(str(helper_node_id or "").strip())
        if helper is None or helper.kind != "helper" or helper.status != "proved":
            obligation.metadata["uncertified_bridge_support_ignored"] = True
            return False
        accepted_hashes = {
            str(helper.source_hash or "").strip(),
            str(helper.proof_hash or "").strip(),
            str(
                (helper.metadata or {}).get("verified_helper_source_hash") or ""
            ).strip(),
        }
        accepted_hashes.discard("")
        supplied_source_hash = str(source_hash or "").strip()
        if supplied_source_hash and supplied_source_hash not in accepted_hashes:
            obligation.metadata["stale_bridge_support_source_hash_ignored"] = True
            obligation.metadata["stale_bridge_support_helper_node_id"] = (
                helper.node_id
            )
            obligation.metadata["stale_bridge_support_source_hash"] = (
                supplied_source_hash
            )
            return False
        helper_is_negative_evidence = (
            str((helper.metadata or {}).get("verified_helper_render_policy") or "")
            == "advisory_negative_evidence"
            or "negative_evidence_helper"
            in list((helper.metadata or {}).get("verified_helper_quality_tags") or [])
        )
        statement = str(formal_statement or helper.statement or "").strip()
        has_lean_contract_evidence = (
            bool(graph_helper_bound_contract_identity(helper))
            and graph_statement_key(statement)
            == graph_statement_key(str(helper.statement or ""))
        )
        ambiguous_binder_types = (
            ()
            if has_lean_contract_evidence
            else graph_statement_contract_ambiguities(statement)
        )
        if ambiguous_binder_types:
            obligation.metadata[
                "formalization_bridge_ambiguous_contract_ignored"
            ] = True
            obligation.metadata[
                "formalization_bridge_ambiguous_binder_types"
            ] = list(ambiguous_binder_types)
            obligation.metadata["formalization_bridge_support_progress_earned"] = False
            return False
        negated_statement_key = graph_negated_statement_key(statement)
        if (
            (helper_is_negative_evidence or negated_statement_key)
            and negated_statement_key
            and negated_statement_key == graph_statement_key(parent_statement)
        ):
            obligation.metadata["negative_evidence_bridge_support_ignored"] = True
            obligation.metadata["negative_evidence_bridge_helper_node_id"] = (
                helper.node_id
            )
            return False
        if not self._helper_has_replayable_source(
            helper,
            allow_formalization_bridge_support=True,
        ):
            # Recording bridge support can immediately mint a schedulable
            # premise and parent route. Keep malformed/stale-contract
            # diagnostics above precise, but do not let a graph-local proved
            # bit and hashes cross this authority boundary.
            obligation.metadata["nonreplayable_bridge_support_ignored"] = True
            obligation.metadata["nonreplayable_bridge_support_helper_node_id"] = (
                helper.node_id
            )
            return False

        entry = {
            "helper_name": str(helper.name or ""),
            "helper_node_id": helper.node_id,
            "statement": statement,
            "bridge_reason": str(bridge_reason or ""),
            "parent_statement": str(parent_statement or "").strip(),
            "phase": str(phase or ""),
            "turn_index": int(turn_index or 0),
            "source_hash": str(
                supplied_source_hash
                or helper.source_hash
                or helper.proof_hash
                or ""
            ),
            "support_names": [
                str(name or "").strip()
                for name in list(support_names or [])
                if str(name or "").strip()
            ],
            "parent_proof_binder_structural_hashes": [
                str(value or "").strip()
                for value in list(
                    parent_proof_binder_structural_hashes or []
                )
                if str(value or "").strip()
            ],
            "helper_proof_binder_structural_hashes": [
                str(value or "").strip()
                for value in list(
                    helper_proof_binder_structural_hashes or []
                )
                if str(value or "").strip()
            ],
        }
        supports = [
            dict(item)
            for item in list(obligation.metadata.get("formalization_bridge_supports") or [])
            if isinstance(item, dict)
        ]
        parent_work_was_materialized = bool(
            obligation.metadata.get("formalization_bridge_parent_work_materialized")
        )
        # Mathematical novelty is the proposition supported for this parent,
        # not the generated declaration name or the source/proof certificate.
        # Keep those fields in ``entry`` as replay provenance, but do not let a
        # renamed copy of the same theorem manufacture new graph progress.
        entry_key = (
            graph_statement_key(entry["statement"])
            or graph_text_hash(entry["statement"]),
            graph_statement_key(entry["parent_statement"])
            or graph_text_hash(entry["parent_statement"]),
        )
        entry_fingerprint = graph_text_hash(
            json.dumps(entry_key, sort_keys=True, default=str)
        )
        support_identity_version = int(
            obligation.metadata.get("formalization_bridge_support_identity_version", 0)
            or 0
        )
        seen_fingerprints = {
            str(value or "").strip()
            for value in list(
                obligation.metadata.get("formalization_bridge_support_seen_keys")
                or []
            )
            if str(value or "").strip()
        }
        if support_identity_version < 2:
            seen_fingerprints = set()
        if not seen_fingerprints:
            for item in supports:
                legacy_key = (
                    graph_statement_key(str(item.get("statement") or ""))
                    or graph_text_hash(str(item.get("statement") or "")),
                    graph_statement_key(str(item.get("parent_statement") or ""))
                    or graph_text_hash(str(item.get("parent_statement") or "")),
                )
                seen_fingerprints.add(
                    graph_text_hash(
                        json.dumps(legacy_key, sort_keys=True, default=str)
                    )
                )
        deduped: List[Dict[str, Any]] = []
        replaced = False
        for item in supports:
            item_key = (
                graph_statement_key(str(item.get("statement") or ""))
                or graph_text_hash(str(item.get("statement") or "")),
                graph_statement_key(str(item.get("parent_statement") or ""))
                or graph_text_hash(str(item.get("parent_statement") or "")),
            )
            if item_key == entry_key:
                if not replaced:
                    deduped.append(entry)
                    replaced = True
                continue
            deduped.append(item)
        if not replaced:
            deduped.append(entry)
        support_added = entry_fingerprint not in seen_fingerprints
        seen_fingerprints.add(entry_fingerprint)
        obligation.metadata["formalization_bridge_support_seen_keys"] = sorted(
            seen_fingerprints
        )
        obligation.metadata["formalization_bridge_support_identity_version"] = 2
        obligation.metadata["formalization_bridge_supports"] = deduped[-8:]
        obligation.metadata["formalization_bridge_support_recorded"] = True
        obligation.metadata["formalization_bridge_parent_assembly_required"] = True
        obligation.metadata["materialization_required"] = True
        if statement:
            obligation.metadata["last_bridge_support_statement"] = statement
        if parent_statement:
            obligation.metadata.setdefault(
                "formalization_bridge_parent_statement",
                str(parent_statement or "").strip(),
            )
        self._add_edge(helper.node_id, obligation.node_id, "supports")
        self._add_edge(obligation.node_id, helper.node_id, "obligation_bridge_support")
        parent_work_materialized = self._materialize_bridge_parent_work(
            obligation=obligation,
            helper=helper,
            parent_statement=parent_statement,
            phase=phase,
            turn_index=turn_index,
        )
        if parent_work_materialized:
            obligation.metadata["formalization_bridge_parent_work_materialized"] = True
            obligation.metadata.pop("formalization_bridge_parent_work_missing", None)
            obligation.metadata["formalization_required"] = False
            obligation.metadata.pop("formalization_statement_pending", None)
            # A later success supersedes an earlier non-universal refusal.
            # Leaving the flag set makes run-metrics mining over-count refusals
            # on obligations that went on to materialize.
            obligation.metadata.pop(
                "formalization_bridge_parent_non_universal_telescope",
                None,
            )
        elif not obligation.metadata.get("formalization_bridge_parent_work_materialized"):
            obligation.metadata["formalization_bridge_parent_work_missing"] = True
            obligation.metadata["formalization_required"] = True
        if obligation.status in {"failed", "rejected", "blocked"}:
            obligation.status = "open"
        contract_reduced = bool(
            obligation.metadata.get("formalization_bridge_parent_contract_reduced")
        )
        obligation.metadata["formalization_bridge_support_semantically_novel"] = bool(
            support_added
        )
        obligation.metadata["formalization_bridge_support_progress_earned"] = bool(
            support_added and parent_work_materialized and contract_reduced
        )
        return bool(
            support_added
            or (parent_work_materialized and not parent_work_was_materialized)
        )

    def retire_formalization_bridge_open_premises(
        self,
        parent_obligation_id: str,
        *,
        reason: str = "parent_contract_lean_closed",
    ) -> List[str]:
        """Retire stale projected premise debt after the parent is proved.

        A later formalization can Lean-check the entire parent contract even
        when an earlier support-only pass projected local proof binders into
        standalone obligations.  Those projections are no longer part of any
        executable route and must not remain schedulable after parent closure.
        """

        obligation_id = str(parent_obligation_id or "").strip()
        if not obligation_id:
            return []
        stale_ids: List[str] = []
        for premise_node in self.nodes_by_kind("missing_obligation"):
            premise_metadata = (
                premise_node.metadata
                if isinstance(premise_node.metadata, dict)
                else {}
            )
            if str(
                premise_metadata.get(
                    "formalization_bridge_parent_obligation_id"
                )
                or ""
            ).strip() != obligation_id:
                continue
            if premise_node.status not in {"open", "blocked"}:
                continue
            premise_node.status = "obsolete"
            premise_metadata["schedulable"] = False
            premise_metadata["formalization_bridge_open_premise_retired"] = str(
                reason or "parent_contract_lean_closed"
            )
            stale_ids.append(premise_node.node_id)
        if not stale_ids:
            return []

        stale_id_set = set(stale_ids)
        for route in list(self.nodes_by_kind("strategy_route")):
            route_metadata = route.metadata if isinstance(route.metadata, dict) else {}
            contract = route_metadata.get(_ROUTE_ASSEMBLY_CONTRACT_KEY)
            if not isinstance(contract, dict):
                for stale_id in stale_ids:
                    self._remove_route_dependency_edges(route.node_id, stale_id)
                continue
            prior_required_ids = list(contract.get("required_node_ids") or [])
            required_ids = [
                str(node_id or "").strip()
                for node_id in prior_required_ids
                if str(node_id or "").strip()
                and str(node_id or "").strip() not in stale_id_set
            ]
            if len(required_ids) == len(prior_required_ids):
                continue
            contract_metadata = (
                dict(contract.get("metadata") or {})
                if isinstance(contract.get("metadata"), dict)
                else {}
            )
            for metadata_key in (
                "bridge_open_premise_node_ids",
                "formalization_bridge_parent_open_premise_node_ids",
            ):
                if metadata_key not in contract_metadata:
                    continue
                contract_metadata[metadata_key] = [
                    str(node_id or "").strip()
                    for node_id in list(contract_metadata.get(metadata_key) or [])
                    if str(node_id or "").strip()
                    and str(node_id or "").strip() not in stale_id_set
                ]
            self.set_route_assembly_contract(
                route.node_id,
                required_node_ids=required_ids,
                required_helper_names=list(
                    contract.get("required_helper_names") or []
                ),
                required_helper_source_hashes=dict(
                    contract.get("required_helper_source_hashes") or {}
                ),
                target_statement=str(contract.get("target_statement") or ""),
                scope=str(contract.get("scope") or _ROUTE_SCOPE_ROOT_ASSEMBLY),
                phase=str(contract.get("phase") or route.phase or ""),
                turn_index=int(
                    contract.get("turn_index") or route.turn_index or 0
                ),
                metadata=contract_metadata or None,
            )
        parent = self.nodes.get(obligation_id)
        if parent is not None and isinstance(parent.metadata, dict):
            parent.metadata.pop(
                "formalization_bridge_parent_open_premise_node_ids",
                None,
            )
            parent.metadata[
                "formalization_bridge_retired_open_premise_node_ids"
            ] = list(stale_ids)
        return stale_ids

    def _materialize_bridge_parent_work(
        self,
        *,
        obligation: ProofGraphNode,
        helper: ProofGraphNode,
        parent_statement: str = "",
        phase: str = "",
        turn_index: int = 0,
    ) -> bool:
        """Convert non-closing bridge support into executable parent work."""

        metadata = obligation.metadata if isinstance(obligation.metadata, dict) else {}
        route_id = str(metadata.get("route_id") or "").strip()
        if not route_id:
            return False
        route = self.nodes.get(route_id)
        if route is None or route.kind != "strategy_route":
            return False
        route_metadata = route.metadata if isinstance(route.metadata, dict) else {}
        if self._route_is_terminally_poisoned(route_id):
            metadata["formalization_bridge_parent_work_route_poisoned"] = True
            return False
        target_statement = str(
            parent_statement
            or metadata.get("formalization_bridge_parent_statement")
            or metadata.get("parent_repair_target_statement")
            or self.root_statement
            or ""
        ).strip()
        if not target_statement:
            return False
        allow_scoped_parent = bool(
            metadata.get("auxiliary_bridge_allow_non_root_parent_assembly")
            or route_metadata.get("auxiliary_bridge_allow_non_root_parent_assembly")
        )
        if self.root_statement and not allow_scoped_parent and not graph_statement_root_equivalent(
            target_statement,
            self.root_statement,
            active_target_statements=(),
        ):
            metadata["formalization_bridge_parent_work_not_root_equivalent"] = True
            return False
        if allow_scoped_parent:
            metadata["formalization_bridge_parent_work_scoped_to_parent"] = True
        supports = [
            dict(item)
            for item in list(metadata.get("formalization_bridge_supports") or [])
            if isinstance(item, dict)
        ]
        helper_node_ids = [
            str(item.get("helper_node_id") or "").strip()
            for item in supports
            if str(item.get("helper_node_id") or "").strip()
        ]
        helper_node_ids.append(helper.node_id)
        helper_node_ids = list(dict.fromkeys(helper_node_ids))
        circular_open_premise_keys: Set[str] = set()
        if not graph_statement_leading_telescope_is_universal(target_statement):
            # The parent is existential-headed, so its closed
            # premise set certifies nothing and every helper premise would be
            # promoted as a standalone goal.  Under an existential parent that
            # goal is strictly stronger than anything the parent asserts — it
            # drops the witness the premise was conditional on — so it is
            # typically false and unprovable.
            #
            # Scope the refusal to the case that can actually manufacture one:
            # a helper with no closed premises projects nothing, so refusing it
            # is pure liveness loss.  Roughly one root in ten is existentially
            # headed, so the premise-free path is worth keeping.
            projecting_helpers = [
                helper_id
                for helper_id in helper_node_ids
                if graph_statement_closed_premises(
                    str(getattr(self.nodes.get(helper_id), "statement", "") or "")
                )
            ]
            if projecting_helpers:
                metadata["formalization_bridge_parent_contract_reduced"] = False
                metadata[
                    "formalization_bridge_parent_non_universal_telescope"
                ] = True
                metadata["formalization_bridge_parent_work_missing"] = True
                return False
            metadata.pop(
                "formalization_bridge_parent_non_universal_telescope",
                None,
            )
        parent_contract_premise_keys = {
            graph_statement_key(premise) or graph_text_hash(premise)
            for premise in graph_statement_closed_premises(target_statement)
        }
        helper_conclusion_keys = {
            helper_id: graph_statement_key(
                graph_statement_closed_conclusion(
                    str(getattr(self.nodes.get(helper_id), "statement", "") or "")
                )
            )
            for helper_id in helper_node_ids
        }
        helper_premises: Dict[str, List[Tuple[str, str]]] = {}
        premise_records: Dict[str, Tuple[str, str]] = {}
        for helper_id in helper_node_ids:
            helper_node = self.nodes.get(helper_id)
            helper_statement = str(getattr(helper_node, "statement", "") or "")
            if not graph_statement_leading_telescope_is_universal(
                helper_statement
            ):
                # The premise walker only sees a universal telescope, so for
                # this helper an empty premise list means "cannot analyze", not
                # "has no premises".  Treating it as premise-free would call the
                # helper fully grounded and let the bridge materialize on
                # obligations nobody checked, and its degenerate conclusion key
                # would also disable the circular-premise fail-closed below.
                metadata["formalization_bridge_parent_contract_reduced"] = False
                metadata[
                    "formalization_bridge_helper_non_universal_telescope"
                ] = True
                metadata["formalization_bridge_parent_work_missing"] = True
                return False
            helper_conclusion_key = helper_conclusion_keys.get(helper_id, "")
            helper_premises[helper_id] = []
            for premise_statement in graph_statement_closed_premises(helper_statement):
                premise_key = (
                    graph_statement_key(premise_statement)
                    or graph_text_hash(premise_statement)
                )
                helper_premises[helper_id].append((premise_key, premise_statement))
                premise_records.setdefault(
                    premise_key,
                    (premise_statement, helper_id),
                )
                if premise_key and premise_key == helper_conclusion_key:
                    circular_open_premise_keys.add(premise_key)

        if circular_open_premise_keys:
            metadata["formalization_bridge_parent_contract_reduced"] = False
            metadata["formalization_bridge_circular_open_premise_keys"] = (
                sorted(circular_open_premise_keys)
            )
            metadata["formalization_bridge_parent_work_missing"] = True
            return False

        support_by_helper_id = {
            str(item.get("helper_node_id") or "").strip(): item
            for item in supports
            if str(item.get("helper_node_id") or "").strip()
        }
        parent_proof_binder_structural_hashes = {
            str(value or "").strip()
            for item in supports
            for value in list(
                item.get("parent_proof_binder_structural_hashes") or []
            )
            if str(value or "").strip()
        }
        helper_premise_structural_hashes: Dict[
            Tuple[str, str], str
        ] = {}
        for helper_id, premises in helper_premises.items():
            support = support_by_helper_id.get(helper_id, {})
            hashes = [
                str(value or "").strip()
                for value in list(
                    support.get("helper_proof_binder_structural_hashes") or []
                )
            ]
            if len(hashes) != len(premises):
                continue
            for (premise_key, _premise_statement), structural_hash in zip(
                premises,
                hashes,
            ):
                if structural_hash:
                    helper_premise_structural_hashes[
                        (helper_id, premise_key)
                    ] = structural_hash
        structurally_parent_supplied_premise_keys = {
            premise_key
            for helper_id, premises in helper_premises.items()
            for premise_key, _premise_statement in premises
            if parent_proof_binder_structural_hashes
            and helper_premise_structural_hashes.get(
                (helper_id, premise_key),
                "",
            )
            in parent_proof_binder_structural_hashes
        }
        produced_premise_keys = {
            key for key in helper_conclusion_keys.values() if key
        }
        external_premise_keys = {
            premise_key
            for premises in helper_premises.values()
            for premise_key, _premise_statement in premises
            if premise_key not in parent_contract_premise_keys
            and premise_key
            not in structurally_parent_supplied_premise_keys
            and premise_key not in produced_premise_keys
        }
        # Promoting an unmet helper premise as a standalone goal closes it over
        # the DATA binders only, silently dropping the parent's own hypotheses.
        # That is exact for an independent side condition, but wrong when the
        # premise is a VARIANT of something the parent already granted: for
        # parent `forall i j, i <= j -> ...` and helper `forall i j, j <= i ->
        # ...` it manufactures `forall i j, j <= i`, which is simply false. The
        # honest obligation would carry the parent's antecedents, and that
        # cannot be synthesized reliably from pretty-printed surface text.
        #
        # Detect the variant case narrowly: same ingredients as a parent
        # premise (identical identifier/operator token set) but a different
        # key, i.e. the helper wants a rearrangement of the parent's own
        # hypothesis rather than a new fact.
        # Tokenize the same alpha-normalized key used to decide premise
        # membership.  Surface tokens retain binder spellings, so a parent
        # premise over ``i j`` and its reversed helper variant over ``a b``
        # almost never collide even though the layer directly beneath this
        # discriminator has already normalized them to ``__b0 __b1``.
        parent_premise_token_profiles = []
        for parent_premise in graph_statement_closed_premises(target_statement):
            parent_premise_key = graph_statement_key(parent_premise)
            parent_premise_token_profiles.append(
                (
                    _graph_contract_key_discriminator_tokens(parent_premise_key),
                    _graph_bridge_variant_rejection_tokens(parent_premise_key),
                    _graph_bridge_key_uses_explicit_operator_scaffolding(
                        parent_premise_key
                    ),
                )
            )

        def parent_premise_variant(
            helper_id: str,
            premise_key: str,
        ) -> bool:
            """Fail closed on elaboration-refined parent hypotheses.

            A verified helper often prints inferred local-binder types that
            were absent from the selected parent target.  The strict graph key
            must retain those annotations (erasing them is unsound for proof
            identity), but that same strictness must not turn a local parent
            hypothesis into a standalone universal theorem.  In that case the
            parent's discriminator tokens are a subset of the elaborated
            helper premise (or conversely when the parent is the elaborated
            side).  Treat the shape as an unattributed parent-hypothesis
            variant and refuse bridge materialization.  Refusal can lose a
            route; promoting the premise can manufacture a false proposition.

            Exact keys were removed from ``external_premise_keys`` above, so
            this guard handles only non-exact variants.  Subset matching is
            deliberately used only as a rejection predicate, never as proof
            equivalence or falsification authority.
            """

            premise_structural_hash = helper_premise_structural_hashes.get(
                (helper_id, premise_key),
                "",
            )
            if (
                premise_structural_hash
                and parent_proof_binder_structural_hashes
            ):
                return (
                    premise_structural_hash
                    in parent_proof_binder_structural_hashes
                )
            premise_tokens = _graph_contract_key_discriminator_tokens(
                premise_key
            )
            if not premise_tokens:
                return False
            premise_rejection_tokens = _graph_bridge_variant_rejection_tokens(
                premise_key
            )
            premise_uses_explicit_scaffolding = (
                _graph_bridge_key_uses_explicit_operator_scaffolding(premise_key)
            )
            for (
                parent_tokens,
                parent_rejection_tokens,
                parent_uses_explicit_scaffolding,
            ) in parent_premise_token_profiles:
                if parent_tokens and (
                    premise_tokens.issubset(parent_tokens)
                    or parent_tokens.issubset(premise_tokens)
                ):
                    return True
                # Notation-insensitive matching is a rejection-only fallback
                # and is activated only when one side came from Lean's explicit
                # printer.  Ordinary surface propositions retain the stricter
                # discriminator behavior above.
                if not (
                    parent_uses_explicit_scaffolding
                    or premise_uses_explicit_scaffolding
                ):
                    continue
                if parent_rejection_tokens and premise_rejection_tokens and (
                    premise_rejection_tokens.issubset(parent_rejection_tokens)
                    or parent_rejection_tokens.issubset(premise_rejection_tokens)
                ):
                    return True
                # Unknown pp.explicit core applications cannot safely be
                # distinguished from a differently printed parent hypothesis
                # using surface text alone. Exact keys were already handled;
                # fail closed rather than globalizing an unverified premise.
                return True
            return False

        variant_premise_statements = [
            premise_statement
            for helper_id, premises in helper_premises.items()
            for premise_key, premise_statement in premises
            if premise_key in external_premise_keys
            and parent_premise_variant(helper_id, premise_key)
        ]
        variant_premise_keys = {
            premise_key
            for helper_id, premises in helper_premises.items()
            for premise_key, _premise_statement in premises
            if premise_key in external_premise_keys
            and parent_premise_variant(helper_id, premise_key)
        }
        parent_supplied_premise_keys = {
            premise_key
            for premises in helper_premises.values()
            for premise_key, _premise_statement in premises
            if premise_key in parent_contract_premise_keys
            or premise_key in structurally_parent_supplied_premise_keys
        }

        def obsolete_legacy_bridge_premises(
            premise_keys: Set[str],
            *,
            keep_parent_obligation: bool,
            reason: str,
        ) -> List[str]:
            """Remove stale globally projected premises and route debt.

            A restored dossier can contain bridge-premise nodes created before
            parent-context/variant classification improved.  Merely declining
            to create another node leaves those old false goals schedulable and
            referenced by route contracts.  Reconcile the durable topology at
            the same boundary that now recognizes the premise shape.
            """

            clean_keys = {str(key or "").strip() for key in premise_keys if key}
            if not clean_keys:
                return []
            stale_ids: List[str] = []
            for premise_node in self.nodes_by_kind("missing_obligation"):
                premise_metadata = premise_node.metadata or {}
                stored_premise_key = str(
                    premise_metadata.get(
                        "formalization_bridge_open_premise_key"
                    )
                    or ""
                ).strip()
                current_premise_key = graph_statement_key(
                    str(getattr(premise_node, "statement", "") or "")
                )
                if (
                    str(
                        premise_metadata.get(
                            "formalization_bridge_parent_obligation_id"
                        )
                        or ""
                    )
                    != obligation.node_id
                    or not (
                        stored_premise_key in clean_keys
                        or current_premise_key in clean_keys
                    )
                ):
                    continue
                if current_premise_key:
                    premise_metadata[
                        "formalization_bridge_open_premise_key"
                    ] = current_premise_key
                premise_node.status = "obsolete"
                premise_metadata["schedulable"] = False
                premise_metadata[
                    "formalization_bridge_open_premise_reclassified"
                ] = str(reason or "parent_context")
                stale_ids.append(premise_node.node_id)
            if not stale_ids:
                return []

            stale_id_set = set(stale_ids)
            for consumer_route in list(self.nodes_by_kind("strategy_route")):
                consumer_metadata = (
                    consumer_route.metadata
                    if isinstance(consumer_route.metadata, dict)
                    else {}
                )
                contract = consumer_metadata.get(_ROUTE_ASSEMBLY_CONTRACT_KEY)
                if not isinstance(contract, dict):
                    had_stale_dependency = any(
                        str(getattr(edge, "target", "") or "") in stale_id_set
                        for edge in self._route_dependency_edges(
                            consumer_route.node_id
                        )
                    )
                    for stale_id in stale_ids:
                        self._remove_route_dependency_edges(
                            consumer_route.node_id,
                            stale_id,
                        )
                    if keep_parent_obligation and had_stale_dependency:
                        self.attach_claim_to_route(
                            consumer_route.node_id,
                            obligation.node_id,
                        )
                    continue
                required_ids = [
                    str(node_id or "").strip()
                    for node_id in list(contract.get("required_node_ids") or [])
                    if str(node_id or "").strip()
                    and str(node_id or "").strip() not in stale_id_set
                ]
                contract_changed = len(required_ids) != len(
                    list(contract.get("required_node_ids") or [])
                )
                if (
                    keep_parent_obligation
                    and contract_changed
                    and obligation.node_id not in required_ids
                ):
                    required_ids.append(obligation.node_id)
                    contract_changed = True
                if not contract_changed:
                    continue
                contract_metadata = (
                    dict(contract.get("metadata") or {})
                    if isinstance(contract.get("metadata"), dict)
                    else {}
                )
                for metadata_key in (
                    "bridge_open_premise_node_ids",
                    "formalization_bridge_parent_open_premise_node_ids",
                ):
                    if metadata_key in contract_metadata:
                        contract_metadata[metadata_key] = [
                            str(node_id or "").strip()
                            for node_id in list(
                                contract_metadata.get(metadata_key) or []
                            )
                            if str(node_id or "").strip()
                            and str(node_id or "").strip() not in stale_id_set
                        ]
                    if metadata_key in consumer_metadata:
                        consumer_metadata[metadata_key] = [
                            str(node_id or "").strip()
                            for node_id in list(
                                consumer_metadata.get(metadata_key) or []
                            )
                            if str(node_id or "").strip()
                            and str(node_id or "").strip() not in stale_id_set
                        ]
                self.set_route_assembly_contract(
                    consumer_route.node_id,
                    required_node_ids=required_ids,
                    required_helper_names=list(
                        contract.get("required_helper_names") or []
                    ),
                    required_helper_source_hashes=dict(
                        contract.get("required_helper_source_hashes") or {}
                    ),
                    target_statement=str(contract.get("target_statement") or ""),
                    scope=str(
                        contract.get("scope") or _ROUTE_SCOPE_ROOT_ASSEMBLY
                    ),
                    phase=str(contract.get("phase") or consumer_route.phase or ""),
                    turn_index=int(
                        contract.get("turn_index")
                        or consumer_route.turn_index
                        or 0
                    ),
                    metadata=contract_metadata or None,
                )
            for metadata_key in (
                "formalization_bridge_parent_open_premise_node_ids",
                "bridge_open_premise_node_ids",
            ):
                if metadata_key in metadata:
                    metadata[metadata_key] = [
                        str(node_id or "").strip()
                        for node_id in list(metadata.get(metadata_key) or [])
                        if str(node_id or "").strip()
                        and str(node_id or "").strip() not in stale_id_set
                    ]
            metadata["formalization_bridge_retired_open_premise_node_ids"] = list(
                dict.fromkeys(
                    [
                        *list(
                            metadata.get(
                                "formalization_bridge_retired_open_premise_node_ids"
                            )
                            or []
                        ),
                        *stale_ids,
                    ]
                )
            )
            if keep_parent_obligation and route_id in self.nodes:
                self.attach_claim_to_route(route_id, obligation.node_id)
                metadata.pop(
                    "formalization_bridge_parent_obligation_detached_from_route",
                    None,
                )
                metadata["formalization_bridge_parent_work_materialized"] = False
                metadata["formalization_bridge_parent_work_missing"] = True
                metadata["formalization_required"] = True
            return stale_ids

        obsolete_legacy_bridge_premises(
            set(parent_supplied_premise_keys),
            keep_parent_obligation=False,
            reason="supplied_by_parent_context",
        )
        metadata.pop(
            "formalization_bridge_parent_hypothesis_variant_premise",
            None,
        )
        if variant_premise_statements:
            obsolete_legacy_bridge_premises(
                set(variant_premise_keys),
                keep_parent_obligation=True,
                reason="parent_hypothesis_variant",
            )
            metadata["formalization_bridge_parent_contract_reduced"] = False
            metadata[
                "formalization_bridge_parent_hypothesis_variant_premise"
            ] = sorted(set(variant_premise_statements))
            metadata["formalization_bridge_parent_work_missing"] = True
            return False
        available_premise_keys = {
            *parent_contract_premise_keys,
            *structurally_parent_supplied_premise_keys,
            *external_premise_keys,
        }
        grounded_helper_ids: Set[str] = set()
        while True:
            newly_grounded = {
                helper_id
                for helper_id, premises in helper_premises.items()
                if helper_id not in grounded_helper_ids
                and all(
                    premise_key in available_premise_keys
                    for premise_key, _premise_statement in premises
                )
            }
            if not newly_grounded:
                break
            grounded_helper_ids.update(newly_grounded)
            available_premise_keys.update(
                helper_conclusion_keys.get(helper_id, "")
                for helper_id in newly_grounded
                if helper_conclusion_keys.get(helper_id, "")
            )
        cyclic_premise_keys = {
            premise_key
            for helper_id, premises in helper_premises.items()
            if helper_id not in grounded_helper_ids
            for premise_key, _premise_statement in premises
            if premise_key not in parent_supplied_premise_keys
        }
        open_premise_keys = external_premise_keys | cyclic_premise_keys
        internalized_premise_keys = {
            premise_key
            for premises in helper_premises.values()
            for premise_key, _premise_statement in premises
            if premise_key not in parent_supplied_premise_keys
            and premise_key not in open_premise_keys
        }
        open_premises = [
            (premise_key, *premise_records[premise_key])
            for premise_key in sorted(open_premise_keys)
            if premise_key in premise_records
        ]
        for premise_node in self.nodes_by_kind("missing_obligation"):
            premise_metadata = premise_node.metadata or {}
            premise_key = str(
                premise_metadata.get("formalization_bridge_open_premise_key") or ""
            )
            if (
                str(premise_metadata.get("route_id") or "") == route_id
                and premise_key in internalized_premise_keys
                and premise_node.status in {"open", "blocked"}
            ):
                premise_node.status = "obsolete"
                premise_metadata["schedulable"] = False
                premise_metadata[
                    "formalization_bridge_open_premise_internalized"
                ] = True

        open_premise_node_ids: List[str] = []
        parent_environment_ancestors = [
            str(item or "").strip()
            for item in list(
                metadata.get("statement_environment_ancestor_hashes") or []
            )
            if str(item or "").strip()
        ]
        for premise_key, premise_statement, premise_helper_id in open_premises:
            premise_helper = self.nodes.get(premise_helper_id)
            premise_helper_metadata = dict(
                getattr(premise_helper, "metadata", {}) or {}
            )
            bridge_environment_hash = str(
                premise_helper_metadata.get("verified_helper_environment_hash")
                or ""
            ).strip()
            bridge_environment_ancestors = [
                str(item or "").strip()
                for item in list(
                    premise_helper_metadata.get(
                        "statement_environment_ancestor_hashes"
                    )
                    or parent_environment_ancestors
                )
                if str(item or "").strip()
            ]
            premise_metadata: Dict[str, Any] = {
                "source": "formalization_bridge_open_premise",
                "obligation_trust": FORMALIZATION_BRIDGE_OPEN_PREMISE_TRUST,
                "identity_key": (
                    f"formalization_bridge_open_premise:{route_id}:{premise_key}"
                ),
                "formalization_required": False,
                "formalization_bridge_parent_statement": target_statement,
                "formalization_bridge_parent_obligation_id": obligation.node_id,
                "formalization_bridge_helper_node_id": premise_helper_id,
                "formalization_bridge_open_premise_key": premise_key,
            }
            if bridge_environment_hash:
                premise_metadata["statement_environment_hash"] = (
                    bridge_environment_hash
                )
                premise_metadata["statement_environment_ancestor_hashes"] = list(
                    bridge_environment_ancestors
                )
                premise_metadata["statement_environment_stamp_source"] = (
                    "formalization_bridge_open_premise_verified_bridge"
                )
            premise_node = self.record_missing_obligation(
                statement=premise_statement,
                reason=(
                    "Discharge an explicit open premise of a verified "
                    "formalization bridge before parent assembly."
                ),
                source_node_id=premise_helper_id,
                route_id=route_id,
                phase=phase or "formalization_bridge_open_premise",
                turn_index=turn_index,
                error_type="formalization_bridge_open_premise",
                metadata=premise_metadata,
            )
            if premise_node.node_id not in open_premise_node_ids:
                open_premise_node_ids.append(premise_node.node_id)
        existing_dependency_node_ids: List[str] = []
        deferred_dependency_node_ids: List[str] = []
        for edge in self._route_dependency_edges(route_id):
            dependency_id = str(edge.target or "").strip()
            if not dependency_id or dependency_id == obligation.node_id:
                continue
            dependency = self.nodes.get(dependency_id)
            if self._proved_node_has_durable_certificate(dependency):
                existing_dependency_node_ids.append(dependency_id)
            else:
                deferred_dependency_node_ids.append(dependency_id)
        existing_dependency_node_ids = list(dict.fromkeys(existing_dependency_node_ids))
        deferred_dependency_node_ids = list(dict.fromkeys(deferred_dependency_node_ids))
        required_node_ids = list(
            dict.fromkeys(
                [
                    *existing_dependency_node_ids,
                    *helper_node_ids,
                    *open_premise_node_ids,
                ]
            )
        )
        if not required_node_ids:
            return False
        source_route_id = route_id
        if deferred_dependency_node_ids:
            bridge_route_key = "\n".join(
                [
                    "formalization_bridge_parent_work",
                    source_route_id,
                    obligation.node_id,
                    helper.node_id,
                    graph_statement_key(target_statement)
                    or graph_text_hash(target_statement),
                    "\n".join(required_node_ids),
                    "\n".join(deferred_dependency_node_ids),
                ]
            )
            bridge_route = self.record_strategy_route(
                name=f"bridge_parent_{graph_text_hash(bridge_route_key)[:12]}",
                description=(
                    "Formalization bridge parent assembly route with only "
                    "proved route dependencies and bridge helpers."
                ),
                route_key=bridge_route_key,
                score=self._coerce_float(route_metadata.get("score", 0.0)),
                phase=phase,
                turn_index=turn_index,
                metadata={
                    "route_scope": _ROUTE_SCOPE_ROOT_ASSEMBLY,
                    "source": "formalization_bridge_parent_work",
                    "formalization_bridge_parent_source_route_id": source_route_id,
                    "formalization_bridge_parent_obligation_id": obligation.node_id,
                    "formalization_bridge_parent_helper_node_id": helper.node_id,
                    "formalization_bridge_parent_deferred_dependency_node_ids": (
                        list(deferred_dependency_node_ids)
                    ),
                },
            )
            route_id = bridge_route.node_id
            route = bridge_route
            route_metadata = (
                route.metadata if isinstance(route.metadata, dict) else {}
            )
            metadata["formalization_bridge_parent_source_route_id"] = source_route_id
            metadata["formalization_bridge_parent_fresh_route_created"] = True
        else:
            metadata.pop("formalization_bridge_parent_source_route_id", None)
            metadata.pop("formalization_bridge_parent_fresh_route_created", None)
        before_edge_count = len(self.edges)
        self.edges = [
            edge
            for edge in self.edges
            if not (
                edge.source == source_route_id
                and edge.target == obligation.node_id
                and edge.kind in _ROUTE_DEPENDENCY_EDGE_KINDS
            )
        ]
        if len(self.edges) != before_edge_count:
            self._rebuild_edge_index()
            metadata["formalization_bridge_parent_obligation_detached_from_route"] = True
        contract = self.set_route_assembly_contract(
            route_id,
            required_node_ids=required_node_ids,
            target_statement=target_statement
            if allow_scoped_parent
            else self.root_statement or target_statement,
            phase=phase,
            turn_index=turn_index,
            metadata={
                "source": "formalization_bridge_support",
                "obligation_id": obligation.node_id,
                "parent_statement": target_statement,
                "bridge_helper_node_id": helper.node_id,
                "bridge_open_premise_node_ids": list(open_premise_node_ids),
                "auxiliary_bridge_allow_non_root_parent_assembly": allow_scoped_parent,
            },
        )
        metadata["formalization_bridge_parent_route_id"] = route_id
        metadata["formalization_bridge_parent_work_type"] = "assemble_route"
        metadata["formalization_bridge_parent_required_node_ids"] = required_node_ids
        metadata["formalization_bridge_parent_open_premise_node_ids"] = list(
            open_premise_node_ids
        )
        metadata["formalization_bridge_parent_open_premise_keys"] = [
            premise_key
            for premise_key, _premise_statement, _premise_helper_id in open_premises
        ]
        metadata["formalization_bridge_parent_discharged_open_premise_keys"] = sorted(
            internalized_premise_keys
        )
        metadata["formalization_bridge_parent_context_premise_keys"] = sorted(
            parent_supplied_premise_keys
        )
        # Making previously implicit antecedents explicit completes the route
        # contract; it does not discharge any mathematics.  The actions that
        # later prove these nodes, or successfully assemble the route, own the
        # corresponding progress signal.
        metadata["formalization_bridge_parent_open_premise_contract_materialized"] = bool(
            open_premise_node_ids
        )
        metadata["formalization_bridge_parent_contract_reduced"] = False
        if existing_dependency_node_ids:
            metadata["formalization_bridge_parent_preserved_dependency_node_ids"] = (
                list(dict.fromkeys(existing_dependency_node_ids))
            )
        else:
            metadata.pop(
                "formalization_bridge_parent_preserved_dependency_node_ids",
                None,
            )
        if deferred_dependency_node_ids:
            metadata["formalization_bridge_parent_deferred_dependency_node_ids"] = (
                list(deferred_dependency_node_ids)
            )
        else:
            metadata.pop(
                "formalization_bridge_parent_deferred_dependency_node_ids",
                None,
            )
        metadata["formalization_bridge_parent_contract"] = dict(contract)
        try:
            self.record_attempt(
                route_id,
                phase=phase or "formalization_bridge_support",
                turn_index=turn_index,
                proof="",
                verdict="formalization_bridge_parent_assembly_scheduled",
                error_type="formalization_bridge_parent_assembly_required",
                metadata={
                    "obligation_id": obligation.node_id,
                    "helper_node_id": helper.node_id,
                    "required_node_ids": required_node_ids,
                    "source_route_id": source_route_id,
                    "deferred_dependency_node_ids": list(
                        deferred_dependency_node_ids
                    ),
                    "target_statement": target_statement
                    if allow_scoped_parent
                    else self.root_statement or target_statement,
                },
            )
        except Exception:
            pass
        return True

    def formalization_bridge_open_premise_is_trusted(
        self,
        premise_node: Optional[ProofGraphNode],
    ) -> bool:
        """Validate a bridge-premise stamp against its durable graph origin.

        The metadata marker is intentionally insufficient by itself.  A
        promotable premise must be an exact closed premise of a proved helper,
        belong to that helper's recorded bridge support, and be required by
        the bridge assembly contract.  This prevents arbitrary or legacy
        missing-obligation nodes from self-authorizing through a copied tag.
        """

        if premise_node is None or premise_node.kind != "missing_obligation":
            return False
        premise_metadata = (
            premise_node.metadata if isinstance(premise_node.metadata, dict) else {}
        )
        if (
            premise_node.status != "open"
            or self.is_superseded_tombstone(premise_node)
            or self._graph_native_source_is_superseded(premise_node)
            or premise_metadata.get("authoritative_falsification_terminal") is True
            or premise_metadata.get("proposal_invalidated") is True
        ):
            return False
        if (
            str(premise_metadata.get("source") or "").strip()
            != "formalization_bridge_open_premise"
            or str(premise_metadata.get("obligation_trust") or "").strip()
            != FORMALIZATION_BRIDGE_OPEN_PREMISE_TRUST
        ):
            return False
        premise_key = str(
            premise_metadata.get("formalization_bridge_open_premise_key") or ""
        ).strip()
        if not premise_key or premise_key != (
            graph_statement_key(premise_node.statement)
            or graph_text_hash(premise_node.statement)
        ):
            return False
        helper_id = str(
            premise_metadata.get("formalization_bridge_helper_node_id") or ""
        ).strip()
        helper = self.nodes.get(helper_id)
        if (
            helper is None
            or helper.kind != "helper"
            or helper.status != "proved"
            or self.is_superseded_tombstone(helper)
            or self._graph_native_source_is_superseded(helper)
            or not self._helper_has_replayable_source(
                helper,
                allow_formalization_bridge_support=True,
            )
        ):
            return False
        premise_environment_hash = str(
            premise_metadata.get("statement_environment_hash") or ""
        ).strip()
        helper_environment_hash = str(
            (helper.metadata or {}).get("verified_helper_environment_hash") or ""
        ).strip()
        # A bridge premise is an elaborated obligation in one exact Lean
        # environment.  Re-recording its stable graph identity after a
        # preamble change must not let an older helper authorize the new
        # interpretation.  Legacy/unstamped evidence remains fail-closed.
        if (
            not premise_environment_hash
            or not helper_environment_hash
            or premise_environment_hash != helper_environment_hash
        ):
            return False
        helper_premise_keys = {
            graph_statement_key(statement) or graph_text_hash(statement)
            for statement in graph_statement_closed_premises(helper.statement)
        }
        if premise_key not in helper_premise_keys:
            return False
        obligation_id = str(
            premise_metadata.get("formalization_bridge_parent_obligation_id") or ""
        ).strip()
        obligation = self.nodes.get(obligation_id)
        if obligation is None or obligation.kind != "missing_obligation":
            return False
        obligation_metadata = (
            obligation.metadata if isinstance(obligation.metadata, dict) else {}
        )
        helper_statement_key = graph_statement_key(helper.statement)
        accepted_hashes = {
            str(helper.source_hash or "").strip(),
            str(helper.proof_hash or "").strip(),
            str(
                (helper.metadata or {}).get("verified_helper_source_hash") or ""
            ).strip(),
        }
        accepted_hashes.discard("")
        recorded_support = any(
            str(item.get("helper_node_id") or "").strip() == helper_id
            and graph_statement_key(str(item.get("statement") or ""))
            == helper_statement_key
            and str(item.get("source_hash") or "").strip() in accepted_hashes
            for item in list(
                obligation_metadata.get("formalization_bridge_supports") or []
            )
            if isinstance(item, dict)
        )
        if not recorded_support:
            return False
        support_edges = {
            (str(edge.source or ""), str(edge.target or ""), str(edge.kind or ""))
            for edge in self.edges
        }
        if (
            (helper_id, obligation_id, "supports") not in support_edges
            or (obligation_id, helper_id, "obligation_bridge_support")
            not in support_edges
        ):
            return False
        for route in self.nodes_by_kind("strategy_route"):
            contract = dict(
                (route.metadata or {}).get(_ROUTE_ASSEMBLY_CONTRACT_KEY) or {}
            )
            contract_metadata = dict(contract.get("metadata") or {})
            if (
                contract_metadata.get("source") == "formalization_bridge_support"
                and str(contract_metadata.get("obligation_id") or "").strip()
                == obligation_id
                and premise_node.node_id
                in set(contract.get("required_node_ids") or [])
                and premise_node.node_id
                in set(contract_metadata.get("bridge_open_premise_node_ids") or [])
                and (route.node_id, premise_node.node_id, "route_requires")
                in support_edges
            ):
                return True
        return False

    def mark_obligation_proved_by_helper(
        self,
        obligation_id: str,
        helper_node_id: str = "",
        *,
        source_hash: str = "",
        proof_hash: str = "",
        support_names: Optional[Iterable[str]] = None,
    ) -> None:
        obligation = self.nodes.get(str(obligation_id or "").strip())
        if obligation is None or obligation.kind != "missing_obligation":
            return
        if self.is_superseded_tombstone(obligation):
            self._enforce_superseded_tombstone(obligation)
            return
        helper = self.nodes.get(str(helper_node_id or "").strip())
        if helper is None or not self._helper_certifies_node(helper, obligation):
            obligation.metadata["uncertified_obligation_proved_ignored"] = True
            return
        prior_helper_name = obligation.metadata.get("verified_by_helper_name")
        prior_helper_node_id = obligation.metadata.get("verified_by_helper_node_id")
        obligation.metadata["verified_by_helper_name"] = helper.name
        obligation.metadata["verified_by_helper_node_id"] = helper.node_id
        self.mark_node_proved(
            obligation.node_id,
            source_hash=source_hash or helper.source_hash,
            proof_hash=proof_hash
            or helper.proof_hash
            or helper.source_hash,
            support_names=support_names,
        )
        if obligation.status != "proved":
            if prior_helper_name is None:
                obligation.metadata.pop("verified_by_helper_name", None)
            else:
                obligation.metadata["verified_by_helper_name"] = prior_helper_name
            if prior_helper_node_id is None:
                obligation.metadata.pop("verified_by_helper_node_id", None)
            else:
                obligation.metadata["verified_by_helper_node_id"] = prior_helper_node_id
            return
        self._add_edge(obligation.node_id, helper.node_id, "obligation_verified_by")
        self._resolve_replans_for_obligation(obligation, helper)

    def mark_proof_state_node_proved_by_helper(
        self,
        node_id: str,
        helper_node_id: str,
        *,
        source_hash: str = "",
        proof_hash: str = "",
        support_names: Optional[Iterable[str]] = None,
    ) -> None:
        """Retire exact receipt-bound proof-state work with a replayable fact."""

        node = self.nodes.get(str(node_id or "").strip())
        helper = self.nodes.get(str(helper_node_id or "").strip())
        if (
            node is None
            or node.kind not in {"proof_state_root", "proof_state_child_goal"}
            or helper is None
            or not self._helper_certifies_node(helper, node)
        ):
            return
        node.metadata["verified_by_helper_name"] = helper.name
        node.metadata["verified_by_helper_node_id"] = helper.node_id
        self.mark_node_proved(
            node.node_id,
            source_hash=source_hash or helper.source_hash,
            proof_hash=proof_hash or helper.proof_hash or helper.source_hash,
            support_names=support_names,
        )
        if node.status == "proved":
            self._add_edge(node.node_id, helper.node_id, "proof_state_verified_by")

    def _resolve_replans_for_obligation(
        self,
        obligation: ProofGraphNode,
        helper: Optional[ProofGraphNode] = None,
    ) -> None:
        for edge in self.outgoing(obligation.node_id, kind="obligation_replan"):
            replan = self.nodes.get(edge.target)
            if replan is None or replan.kind != "replan_queue_item":
                continue
            self._mark_replan_resolved_by_obligation(replan, obligation, helper)

    def _resolve_replan_if_obligation_proved(
        self,
        replan: ProofGraphNode,
        obligation_id: str,
    ) -> None:
        self._sync_replan_with_obligation_status(replan, obligation_id)

    def _sync_replan_with_obligation_status(
        self,
        replan: ProofGraphNode,
        obligation_id: str,
    ) -> None:
        obligation = self.nodes.get(str(obligation_id or "").strip())
        if (
            obligation is None
            or obligation.kind != "missing_obligation"
        ):
            return
        if obligation.status in {"failed", "rejected"}:
            self._mark_replan_closed_by_obligation(replan, obligation)
            return
        if obligation.status != "proved":
            return
        helper = None
        for edge in self.outgoing(obligation.node_id, kind="obligation_verified_by"):
            candidate = self.nodes.get(edge.target)
            if candidate is not None and candidate.kind == "helper":
                helper = candidate
                break
        self._mark_replan_resolved_by_obligation(replan, obligation, helper)

    def _mark_replan_resolved_by_obligation(
        self,
        replan: ProofGraphNode,
        obligation: ProofGraphNode,
        helper: Optional[ProofGraphNode] = None,
    ) -> None:
        if replan.status == "proved":
            return
        replan.metadata["resolved_by_obligation_id"] = obligation.node_id
        if helper is not None:
            self._add_edge(replan.node_id, helper.node_id, "replan_resolved_by")
            replan.metadata["resolved_by_helper_name"] = helper.name
            replan.metadata["resolved_by_helper_node_id"] = helper.node_id
        self.mark_node_proved(
            replan.node_id,
            source_hash=obligation.source_hash,
            proof_hash=obligation.proof_hash,
        )

    def _close_replans_for_obligation_terminal_status(
        self,
        obligation: ProofGraphNode,
    ) -> None:
        if (
            obligation is None
            or obligation.kind != "missing_obligation"
            or obligation.status not in {"failed", "rejected"}
        ):
            return
        for edge in self.outgoing(obligation.node_id, kind="obligation_replan"):
            replan = self.nodes.get(edge.target)
            if replan is None or replan.kind != "replan_queue_item":
                continue
            self._mark_replan_closed_by_obligation(replan, obligation)

    def _mark_replan_closed_by_obligation(
        self,
        replan: ProofGraphNode,
        obligation: ProofGraphNode,
    ) -> None:
        if replan is None or obligation is None:
            return
        if replan.kind != "replan_queue_item" or obligation.kind != "missing_obligation":
            return
        if replan.status == "proved" or obligation.status not in {"failed", "rejected"}:
            return
        replan.status = "failed" if obligation.status == "failed" else "rejected"
        replan.metadata["closed_by_obligation_id"] = obligation.node_id
        replan.metadata["closed_by_obligation_status"] = obligation.status
        replan.metadata["closed_reason"] = "linked_obligation_terminal"


    def _set_supports(
        self,
        node: ProofGraphNode,
        support_names: Iterable[str],
        *,
        replace: bool = False,
    ) -> None:
        names = [
            str(name or "").strip()
            for name in support_names
            if str(name or "").strip()
        ]
        if replace:
            old_names = set(node.support_names)
            new_names = set(names)
            removed = old_names - new_names
            if removed:
                self.edges = [
                    edge
                    for edge in self.edges
                    if not (
                        edge.kind == "supports"
                        and edge.target == node.node_id
                        and self.nodes.get(edge.source)
                        and self.nodes[edge.source].name in removed
                    )
                ]
                self._rebuild_edge_index()
            node.support_names = list(dict.fromkeys(names))
        elif names:
            node.support_names = list(dict.fromkeys(node.support_names + names))
        for support in names:
            support_id = self.helper_name_to_node_id.get(support)
            if support_id is not None and support_id != node.node_id:
                self._add_edge(support_id, node.node_id, "supports")

    def _backfill_support_edges(self, helper_name: str, helper_id: str) -> None:
        """Connect existing nodes that named this helper before it existed."""

        for node in self.nodes.values():
            if node.node_id == helper_id:
                continue
            if helper_name in node.support_names:
                self._add_edge(helper_id, node.node_id, "supports")

    def _add_edge(self, source: str, target: str, kind: str) -> None:
        if not source or not target or source == target:
            return
        triple = (source, target, kind)
        if triple in self._edge_keys:
            return
        self.edges.append(ProofGraphEdge(source=source, target=target, kind=kind))
        self._edge_keys.add(triple)

    def _rebuild_edge_index(self) -> None:
        self._edge_keys = {
            (edge.source, edge.target, edge.kind)
            for edge in self.edges
            if edge.source and edge.target and edge.source != edge.target
        }

    def add_edge(self, source: str, target: str, kind: str) -> None:
        """Add a graph edge after applying the same dedup policy as internals."""

        self._add_edge(source, target, kind)

    def mark_node_blocked(
        self,
        node_id: str,
        *,
        reason: str = "",
        blocker_node_ids: Iterable[str] = (),
    ) -> None:
        """Mark a node blocked by explicit blocker nodes.

        Generic ``proof_state_dependency`` edges are provenance, not blockers.
        Only ``blocked_by`` edges participate in graph-readiness scheduling.
        """

        node = self.nodes.get(str(node_id or "").strip())
        if node is None or node.status == "proved":
            return
        if self.is_superseded_tombstone(node):
            self._enforce_superseded_tombstone(node)
            return
        node.status = "blocked"
        if reason:
            node.metadata["blocker"] = str(reason or "")
        for blocker_id in blocker_node_ids:
            blocker = str(blocker_id or "").strip()
            if blocker:
                self._add_edge(node.node_id, blocker, "blocked_by")

    def reopen_node(self, node_id: str, *, reason: str = "") -> bool:
        """Reopen a non-proved node for explicit retry/replan scheduling."""

        node = self.nodes.get(str(node_id or "").strip())
        if node is None or node.status == "proved":
            return False
        if self.is_superseded_tombstone(node):
            self._enforce_superseded_tombstone(node)
            return False
        node.status = "open"
        if reason:
            node.metadata["reopen_reason"] = str(reason or "")
        return True

    def incoming(
        self,
        node_id: str,
        *,
        kind: Optional[str] = None,
    ) -> List[ProofGraphEdge]:
        """Return incoming edges, optionally filtered by exact edge kind."""

        target = str(node_id or "").strip()
        edge_kind = str(kind or "").strip()
        if not target:
            return []
        return [
            edge
            for edge in self.edges
            if edge.target == target and (not edge_kind or edge.kind == edge_kind)
        ]

    def outgoing(
        self,
        node_id: str,
        *,
        kind: Optional[str] = None,
    ) -> List[ProofGraphEdge]:
        """Return outgoing edges, optionally filtered by exact edge kind."""

        source = str(node_id or "").strip()
        edge_kind = str(kind or "").strip()
        if not source:
            return []
        return [
            edge
            for edge in self.edges
            if edge.source == source and (not edge_kind or edge.kind == edge_kind)
        ]

    def nodes_by_kind(self, kind: str) -> List[ProofGraphNode]:
        node_kind = str(kind or "").strip()
        if not node_kind:
            return []
        return [node for node in self.nodes.values() if node.kind == node_kind]

    def nodes_by_status(self, status: str) -> List[ProofGraphNode]:
        node_status = str(status or "").strip()
        if not node_status:
            return []
        return [node for node in self.nodes.values() if node.status == node_status]

    @staticmethod
    def is_superseded_tombstone(node: Optional[ProofGraphNode]) -> bool:
        """Return whether a graph node is a durable superseded proposal tombstone."""

        if node is None:
            return False
        return bool((node.metadata or {}).get("proposal_superseded"))

    @staticmethod
    def _proposal_revision(node: Optional[ProofGraphNode]) -> int:
        if node is None:
            return 0
        try:
            revision = int((node.metadata or {}).get("proposal_revision") or 0)
        except (AttributeError, TypeError, ValueError):
            revision = 0
        return revision if revision > 0 else 0

    def _effective_proposal_revision(self, node: Optional[ProofGraphNode]) -> int:
        """Return the proposal generation that should guard route rewrites."""

        own_revision = self._proposal_revision(node)
        if own_revision or node is None or node.kind != "formal_variant":
            return own_revision

        origin_revisions: List[int] = []
        parent_id = str((node.metadata or {}).get("claim_node_id") or "").strip()
        parent_revision = self._proposal_revision(self.nodes.get(parent_id))
        revisionless_source_origin = False
        reparented_from = str(
            (node.metadata or {}).get("reparented_from_superseded_claim_id") or ""
        ).strip()
        if reparented_from:
            origin_parent = self.nodes.get(reparented_from)
            if self._superseded_parent_points_to(origin_parent, parent_id):
                revision = self._proposal_revision(origin_parent)
                if revision:
                    origin_revisions.append(revision)
                else:
                    revisionless_source_origin = True
        for edge in self.incoming(node.node_id, kind="claim_formalized_as"):
            parent = self.nodes.get(edge.source)
            if not self.is_superseded_tombstone(parent):
                continue
            if not self._superseded_parent_points_to(parent, parent_id):
                continue
            revision = self._proposal_revision(parent)
            if revision:
                origin_revisions.append(revision)
            else:
                revisionless_source_origin = True
        if revisionless_source_origin:
            return parent_revision - 1 if parent_revision > 1 else 0
        if origin_revisions:
            return min(origin_revisions)
        if own_revision:
            return own_revision

        return parent_revision

    def _superseded_source_chain_reaches(
        self,
        source_node_id: str,
        target_node_id: str,
    ) -> bool:
        """Return whether a superseded-source chain reaches ``target_node_id``."""

        target = str(target_node_id or "").strip()
        start = str(source_node_id or "").strip()
        frontier = [start]
        queued: Set[str] = {start} if start else set()
        seen: Set[str] = set()
        max_steps = max(1, len(self.nodes) + 1)
        for _ in range(max_steps):
            if not frontier:
                return False
            current = frontier.pop(0)
            if not current or current in seen:
                continue
            seen.add(current)
            node = self.nodes.get(current)
            if not self.is_superseded_tombstone(node):
                continue
            metadata = dict(node.metadata if node is not None else {})
            for key in (
                "superseded_source_node_id",
                "duplicate_same_name_generation_superseded_by",
            ):
                next_id = str(metadata.get(key) or "").strip()
                if next_id == target:
                    return True
                if next_id and next_id not in seen and next_id not in queued:
                    queued.add(next_id)
                    frontier.append(next_id)
        return False

    def _live_superseded_source_candidates(
        self,
        source_node_id: str,
        *,
        kind: str = "",
        statement_key: str = "",
    ) -> List[ProofGraphNode]:
        """Return live nodes reached through superseded-source metadata."""

        start = str(source_node_id or "").strip()
        frontier = [start]
        queued: Set[str] = {start} if start else set()
        seen: Set[str] = set()
        candidates: List[ProofGraphNode] = []
        max_steps = max(1, len(self.nodes) + 1)
        for _ in range(max_steps):
            if not frontier:
                break
            current = frontier.pop(0)
            if not current or current in seen:
                continue
            seen.add(current)
            node = self.nodes.get(current)
            if node is None:
                continue
            if not self.is_superseded_tombstone(node):
                if (
                    (not kind or node.kind == kind)
                    and (
                        not statement_key
                        or graph_statement_key(node.statement) == statement_key
                    )
                ):
                    candidates.append(node)
                continue
            metadata = dict(node.metadata or {})
            for key in (
                "superseded_source_node_id",
                "duplicate_same_name_generation_superseded_by",
            ):
                next_id = str(metadata.get(key) or "").strip()
                if next_id and next_id not in seen and next_id not in queued:
                    queued.add(next_id)
                    frontier.append(next_id)
        return sorted(
            candidates,
            key=lambda node: (
                self._proposal_revision(node),
                int(node.turn_index or 0),
                node.node_id,
            ),
            reverse=True,
        )

    def _live_superseded_source_candidate(
        self,
        source_node_id: str,
        *,
        kind: str = "",
        statement_key: str = "",
    ) -> Optional[ProofGraphNode]:
        """Return the highest-ranked live node reached through source metadata."""

        candidates = self._live_superseded_source_candidates(
            source_node_id,
            kind=kind,
            statement_key=statement_key,
        )
        return candidates[0] if candidates else None

    def _enforce_superseded_tombstone(self, node: ProofGraphNode) -> None:
        """Keep superseded proposal artifacts terminal and non-certifying."""

        if not self.is_superseded_tombstone(node):
            return
        metadata = dict(node.metadata or {})
        successor_ids = [
            str(metadata.get("duplicate_same_name_generation_superseded_by") or ""),
            str(metadata.get("superseded_source_node_id") or ""),
        ]
        statement_key = graph_statement_key(node.statement)
        for source_node_id in dict.fromkeys(
            candidate.strip() for candidate in successor_ids if candidate.strip()
        ):
            source_candidates = self._live_superseded_source_candidates(
                source_node_id,
                kind=node.kind,
                statement_key=statement_key,
            )
            retargeted = False
            for source in source_candidates:
                if (
                    source is None
                    or source.kind != node.kind
                    or self.is_superseded_tombstone(source)
                    or graph_statement_key(source.statement) != statement_key
                ):
                    continue
                retargeted = self._retarget_equivalent_route_dependencies(
                    node,
                    source_node_id=source.node_id,
                    allow_newer_revision=not bool(
                        metadata.get("route_retarget_revision_guarded")
                    ),
                )
                if retargeted:
                    break
            if retargeted:
                break
        if self._graph_native_certifying_kind(node):
            if node.proof_hash:
                node.metadata.setdefault(
                    "superseded_previous_proof_hash",
                    node.proof_hash,
                )
            if node.source_hash:
                node.metadata.setdefault(
                    "superseded_previous_source_hash",
                    node.source_hash,
                )
        node.status = "rejected"
        node.proof_hash = ""
        node.metadata["tombstone_status"] = "proposal_superseded"

    @staticmethod
    def _graph_native_certifying_kind(node: Optional[ProofGraphNode]) -> bool:
        return node is not None and node.kind in {
            "proposed_claim",
            "formal_variant",
            "missing_obligation",
            "replan_queue_item",
        }

    def _superseded_parent_points_to(
        self,
        node: Optional[ProofGraphNode],
        target_id: str,
    ) -> bool:
        if node is None:
            return False
        return self._superseded_source_chain_reaches(node.node_id, target_id)

    def _formal_variant_crosses_parent_revision(
        self,
        node: Optional[ProofGraphNode],
    ) -> bool:
        if node is None or node.kind != "formal_variant":
            return False
        parent_id = str((node.metadata or {}).get("claim_node_id") or "").strip()
        parent_revision = self._proposal_revision(self.nodes.get(parent_id))
        own_revision = self._proposal_revision(node)
        if own_revision > 0 and parent_revision > 0:
            return own_revision < parent_revision
        origin_revisions: List[int] = []
        reparented_from = str(
            (node.metadata or {}).get("reparented_from_superseded_claim_id") or ""
        ).strip()
        if reparented_from:
            origin_parent = self.nodes.get(reparented_from)
            if self._superseded_parent_points_to(origin_parent, parent_id):
                revision = self._proposal_revision(origin_parent)
                if revision:
                    origin_revisions.append(revision)
                elif parent_revision > 0:
                    return True
        for edge in self.incoming(node.node_id, kind="claim_formalized_as"):
            origin_parent = self.nodes.get(edge.source)
            if not self.is_superseded_tombstone(origin_parent):
                continue
            if not self._superseded_parent_points_to(origin_parent, parent_id):
                continue
            revision = self._proposal_revision(origin_parent)
            if revision:
                origin_revisions.append(revision)
            elif parent_revision > 0 and self._superseded_parent_points_to(
                origin_parent,
                parent_id,
            ):
                return True
        if origin_revisions:
            origin_revision = min(origin_revisions)
            if parent_revision > 0 and parent_revision > origin_revision:
                return True
        variant_revision = self._effective_proposal_revision(node)
        return bool(
            variant_revision > 0
            and parent_revision > 0
            and parent_revision > variant_revision
        )

    def _reject_revision_crossing_formal_variants(self) -> Set[str]:
        """Tombstone legacy variants whose proof state crosses claim revisions."""

        rejected: Set[str] = set()
        for variant in self.nodes_by_kind("formal_variant"):
            if self.is_superseded_tombstone(variant):
                continue
            if not self._formal_variant_crosses_parent_revision(variant):
                continue
            parent_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
            variant.metadata["superseded_parent_revision_crossing"] = True
            self._mark_node_superseded_by_source(
                variant,
                source_node_id=parent_id,
            )
            rejected.add(variant.node_id)
        return rejected

    def _repair_revision_crossing_tombstones(self, *, cascade_all: bool = False) -> None:
        """Repair stale-origin variants without running global proposal dedupe."""

        frontier: Set[str] = set()
        max_iterations = max(8, len(self.nodes) + len(self.edges) + 1)
        for _ in range(max_iterations):
            before = self._superseded_repair_signature()
            rejected = self._reject_revision_crossing_formal_variants()
            cascade_sources = set(frontier)
            cascade_sources.update(rejected)
            if cascade_sources:
                frontier = self._cascade_superseded_downstream(
                    tombstone_ids=cascade_sources,
                )
            elif cascade_all:
                frontier = self._cascade_superseded_downstream()
            else:
                frontier = set()
            for node in self.nodes.values():
                self._enforce_superseded_tombstone(node)
            if self._superseded_repair_signature() == before:
                break

    def _root_reducer_support_statements(
        self,
        *,
        skip_node_id: str = "",
    ) -> List[Tuple[str, Tuple[str, ...]]]:
        support: List[Tuple[str, Tuple[str, ...]]] = []
        root = self.nodes.get(self.root_node_id)
        if root is not None:
            support.extend(
                _graph_support_candidates(
                    root.statement,
                    include_implication_premises=True,
                    premises_are_assumptions=True,
                )
            )
        skip = str(skip_node_id or "").strip()
        for node in list(self.nodes.values()):
            if node.node_id == skip or node.status != "proved":
                continue
            if self.is_superseded_tombstone(node):
                continue
            if self._graph_native_source_is_superseded(node):
                continue
            if node.kind == "helper":
                if not self._helper_has_replayable_source(node):
                    continue
            elif self._graph_native_certifying_kind(node):
                if not node.proof_hash:
                    continue
            elif not (node.proof_hash or node.source_hash):
                continue
            statement = str(node.statement or "").strip()
            if statement:
                support.extend(_graph_support_candidates(statement))
        return support

    def _node_open_root_reducer_premises(
        self,
        node: ProofGraphNode,
    ) -> List[str]:
        statement = str(getattr(node, "statement", "") or "").strip()
        if not statement:
            return []
        root = self.nodes.get(self.root_node_id)
        if root is None:
            return []
        premises, conclusion, bound_names = _graph_statement_premises_and_conclusion(
            statement
        )
        if not premises or not _graph_statement_root_adjacent(
            conclusion,
            root.statement,
            conclusion_bound_names=bound_names,
        ):
            node.metadata.pop("graph_open_root_reducer_premise_keys", None)
            node.metadata.pop("graph_open_root_reducer_premises", None)
            return []
        support_keys: Set[str] = set()
        support_candidates = self._root_reducer_support_statements(
            skip_node_id=node.node_id
        )
        support_alpha_norms: Set[str] = set()
        for support, support_bound_names in support_candidates:
            key = graph_statement_key(support)
            if key:
                support_keys.add(key)
            norm = _graph_contract_norm(support)
            if norm:
                support_keys.add(norm)
            alpha_norm = _graph_contract_alpha_norm(
                support,
                context_bound_names=support_bound_names,
            )
            if alpha_norm:
                support_alpha_norms.add(alpha_norm)
        open_premises: List[str] = []
        open_keys: List[str] = []
        for premise in premises:
            premise_text, premise_names = _graph_strip_leading_forall_binders_with_names(
                premise
            )
            premise_bound_names = tuple(dict.fromkeys(bound_names + premise_names))
            key = graph_statement_key(premise_text)
            norm = _graph_contract_norm(premise_text)
            alpha_norm = _graph_contract_alpha_norm(
                premise_text,
                context_bound_names=premise_bound_names,
            )
            if not (key or norm or alpha_norm):
                continue
            if (
                key in support_keys
                or norm in support_keys
                or alpha_norm in support_alpha_norms
            ):
                continue
            open_key = key or norm
            if open_key not in open_keys:
                open_keys.append(open_key)
                open_premises.append(str(premise_text or "").strip())
        if open_keys:
            node.metadata["graph_open_root_reducer_premise_keys"] = list(open_keys)
            node.metadata["graph_open_root_reducer_premises"] = list(open_premises)
            node.metadata["graph_hollow_root_reducer_certificate_blocked"] = True
            return open_premises
        node.metadata.pop("graph_open_root_reducer_premise_keys", None)
        node.metadata.pop("graph_open_root_reducer_premises", None)
        node.metadata.pop("graph_hollow_root_reducer_certificate_blocked", None)
        return []

    def _proved_node_has_durable_certificate(
        self,
        node: Optional[ProofGraphNode],
        *,
        _seen: Optional[Set[str]] = None,
    ) -> bool:
        """Return whether a proved graph node has non-replay proof evidence."""

        if node is None or node.status != "proved" or self.is_superseded_tombstone(node):
            return False
        if node.kind in _GRAPH_FORMAL_STATEMENT_KINDS and graph_statement_non_theorem_reason(
            node.statement
        ):
            return False
        if self._graph_native_source_is_superseded(node):
            return False
        if self._node_open_root_reducer_premises(node):
            return False
        if node.kind == "helper" and not _helper_render_policy_context_visible(
            str((node.metadata or {}).get("verified_helper_render_policy") or "")
        ):
            return False
        helper_certified_proof_state = bool(
            node.kind in {"proof_state_root", "proof_state_child_goal"}
            and (
                str((node.metadata or {}).get("verified_by_helper_node_id") or "").strip()
                or any(
                    edge.kind == "proof_state_verified_by"
                    for edge in self.outgoing(node.node_id)
                )
            )
        )
        if not self._graph_native_certifying_kind(node) and not helper_certified_proof_state:
            return True
        if self._formal_variant_crosses_parent_revision(node):
            return False
        seen = set(_seen or set())
        if node.node_id in seen:
            return False
        seen.add(node.node_id)

        if helper_certified_proof_state:
            helper_ids = {
                str((node.metadata or {}).get("verified_by_helper_node_id") or "").strip()
            }
            helper_ids.update(
                str(edge.target or "").strip()
                for edge in self.outgoing(node.node_id)
                if edge.kind == "proof_state_verified_by"
            )
            helper_ids.discard("")
            return any(
                self._helper_certifies_node(self.nodes.get(helper_id), node)
                for helper_id in helper_ids
            )

        if node.kind in {"proposed_claim", "formal_variant"}:
            has_helper_ref = bool(
                str((node.metadata or {}).get("verified_by_helper_node_id") or "").strip()
            ) or any(
                edge.kind in {"claim_verified_by", "variant_verified_by"}
                for edge in self.outgoing(node.node_id)
            )
            if has_helper_ref and not any(
                self._helper_certifies_node(self.nodes.get(edge.target), node)
                for edge in self.outgoing(node.node_id)
                if edge.kind in {"claim_verified_by", "variant_verified_by"}
            ):
                helper_id = str(
                    (node.metadata or {}).get("verified_by_helper_node_id") or ""
                ).strip()
                if not self._helper_certifies_node(self.nodes.get(helper_id), node):
                    return False

        if node.kind == "replan_queue_item":
            _source_ids, _route_ids, obligation_ids = (
                self._graph_native_source_links(node)
            )
            live_obligation_ids = [
                obligation_id
                for obligation_id in dict.fromkeys(obligation_ids)
                if obligation_id
            ]
            if live_obligation_ids:
                return all(
                    self._proved_node_has_durable_certificate(
                        self.nodes.get(obligation_id),
                        _seen=seen,
                    )
                    for obligation_id in live_obligation_ids
                )
        if node.kind != "missing_obligation" and node.proof_hash:
            return True

        helper_edge_kinds = {
            "claim_verified_by",
            "variant_verified_by",
            "obligation_verified_by",
            "replan_resolved_by",
            "proof_state_verified_by",
        }
        for edge in self.outgoing(node.node_id):
            if edge.kind not in helper_edge_kinds:
                continue
            helper = self.nodes.get(edge.target)
            if self._helper_certifies_node(helper, node):
                return True

        metadata = dict(node.metadata or {})
        helper_ids = [
            str(metadata.get("verified_by_helper_node_id") or "").strip(),
            str(metadata.get("resolved_by_helper_node_id") or "").strip(),
        ]
        for helper_id in helper_ids:
            if not helper_id:
                continue
            helper = self.nodes.get(helper_id)
            if self._helper_certifies_node(helper, node):
                return True
        return False

    def _reopen_uncertified_graph_native_node(
        self,
        node: ProofGraphNode,
        *,
        reason: str,
    ) -> None:
        node.status = "open"
        node.source_hash = ""
        node.proof_hash = ""
        for key in (
            "verified_by_helper_name",
            "verified_by_helper_node_id",
            "resolved_by_helper_name",
            "resolved_by_helper_node_id",
            "verified_fact_id",
            "verified_statement_identity",
        ):
            node.metadata.pop(key, None)
        node.metadata["rehydration_status_repair"] = reason
        helper_edge_kinds = {
            "claim_verified_by",
            "variant_verified_by",
            "obligation_verified_by",
            "replan_resolved_by",
            "proof_state_verified_by",
        }
        self.edges = [
            edge
            for edge in self.edges
            if not (edge.source == node.node_id and edge.kind in helper_edge_kinds)
        ]
        if node.kind == "proposed_claim":
            active_key = graph_statement_key(node.statement)
            for variant in self.nodes_by_kind("formal_variant"):
                metadata = variant.metadata
                if (
                    not self.is_superseded_tombstone(variant)
                    or str(metadata.get("claim_node_id") or "").strip()
                    != node.node_id
                    or str(metadata.get("superseded_source_node_id") or "").strip()
                    != node.node_id
                    or str(metadata.get("superseded_active_statement_key") or "")
                    != active_key
                ):
                    continue
                previous_status = str(
                    metadata.pop("superseded_previous_status", "") or ""
                )
                previous_proof_hash = str(
                    metadata.pop("superseded_previous_proof_hash", "") or ""
                ).strip()
                previous_source_hash = str(
                    metadata.pop("superseded_previous_source_hash", "") or ""
                ).strip()
                for key in (
                    "proposal_superseded",
                    "tombstone_status",
                    "superseded_source_node_id",
                    "route_retarget_revision_guarded",
                    "superseded_active_statement_key",
                    "verified_by_helper_name",
                    "verified_by_helper_node_id",
                ):
                    metadata.pop(key, None)
                variant.status = "proved" if previous_status == "proved" else "open"
                variant.proof_hash = previous_proof_hash
                if previous_source_hash:
                    variant.source_hash = previous_source_hash
                if (
                    variant.status == "proved"
                    and not self._proved_node_has_durable_certificate(variant)
                ):
                    variant.status = "open"
                    variant.proof_hash = ""
                metadata[
                    "claim_certificate_tombstone_revived"
                ] = "parent_claim_certificate_revoked"
                self.edges = [
                    edge
                    for edge in self.edges
                    if not (
                        edge.source == variant.node_id
                        and edge.kind == "proposal_superseded_by"
                    )
                ]
        self._rebuild_edge_index()

    def _repair_uncertified_graph_native_proved_nodes(self) -> None:
        """Reopen serialized graph-native proved nodes that lack a certificate."""

        self._repair_graph_native_source_tombstones()
        for node in self.nodes.values():
            if self._reject_graph_native_node_from_superseded_source(node):
                continue
            if (
                (
                    self._graph_native_certifying_kind(node)
                    or (
                        node.kind
                        in {"proof_state_root", "proof_state_child_goal"}
                        and bool(
                            str(
                                (node.metadata or {}).get(
                                    "verified_by_helper_node_id"
                                )
                                or ""
                            ).strip()
                        )
                    )
                )
                and node.status == "proved"
                and not self.is_superseded_tombstone(node)
                and not self._proved_node_has_durable_certificate(node)
            ):
                self._reopen_uncertified_graph_native_node(
                    node,
                    reason="proved_graph_native_missing_certificate",
                )

    def _repair_graph_native_proof_hashes_from_attempts(self) -> None:
        """Backfill legacy proved proposal certificates from attached attempts."""

        attempts_by_id = {attempt.attempt_id: attempt for attempt in self.attempts}
        attempts_by_node: Dict[str, List[ProofGraphAttempt]] = {}
        for attempt in self.attempts:
            attempts_by_node.setdefault(attempt.node_id, []).append(attempt)
        for node in self.nodes.values():
            if (
                not self._graph_native_certifying_kind(node)
                or node.status != "proved"
                or node.proof_hash
                or self.is_superseded_tombstone(node)
            ):
                continue
            candidate_attempts: List[ProofGraphAttempt] = []
            for attempt_id in list(node.attempt_ids or []):
                attempt = attempts_by_id.get(str(attempt_id or ""))
                if attempt is not None and attempt.node_id == node.node_id:
                    candidate_attempts.append(attempt)
            for attempt in attempts_by_node.get(node.node_id, []):
                if attempt not in candidate_attempts:
                    candidate_attempts.append(attempt)
            for attempt in candidate_attempts:
                if (
                    str(attempt.verdict or "").lower()
                    not in _PROOF_GRAPH_REHYDRATION_VERDICTS
                ):
                    continue
                if not attempt.proof_hash:
                    continue
                node.proof_hash = attempt.proof_hash
                node.metadata["rehydration_certificate_repair"] = "attempt_proof_hash"
                break

    def _repair_formal_variant_parent_metadata_from_edges(self) -> None:
        """Backfill replayed variant parent metadata before same-name dedupe."""

        for variant in self.nodes_by_kind("formal_variant"):
            parent_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
            edge_parent_ids: List[str] = []
            for edge in self.incoming(variant.node_id, kind="claim_formalized_as"):
                edge_parent = self.nodes.get(edge.source)
                if edge_parent is not None and edge_parent.kind == "proposed_claim":
                    edge_parent_ids.append(edge.source)
            if not edge_parent_ids:
                continue
            parent = self.nodes.get(parent_id)
            if (
                parent is not None
                and parent.kind == "proposed_claim"
                and parent_id in edge_parent_ids
            ):
                continue
            live_parent_ids = [
                edge_parent_id
                for edge_parent_id in edge_parent_ids
                if not self.is_superseded_tombstone(self.nodes.get(edge_parent_id))
            ]
            parent_key = graph_statement_key(parent.statement) if parent else ""
            variant_key = graph_statement_key(variant.statement)
            if (
                not live_parent_ids
                and parent is not None
                and parent.kind == "proposed_claim"
                and not self.is_superseded_tombstone(parent)
                and parent_key
                and parent_key == variant_key
            ):
                stale_parent_ids = []
                for edge_parent_id in edge_parent_ids:
                    edge_parent = self.nodes.get(edge_parent_id)
                    if (
                        self.is_superseded_tombstone(edge_parent)
                        and self._superseded_source_chain_reaches(
                            edge_parent_id,
                            parent.node_id,
                        )
                    ):
                        stale_parent_ids.append(edge_parent_id)
                if stale_parent_ids:
                    existing_origin_id = str(
                        (variant.metadata or {}).get(
                            "reparented_from_superseded_claim_id"
                        )
                        or ""
                    ).strip()
                    origin_candidates = list(stale_parent_ids)
                    if self._superseded_parent_points_to(
                        self.nodes.get(existing_origin_id),
                        parent.node_id,
                    ):
                        origin_candidates.append(existing_origin_id)
                    variant.metadata["reparented_from_superseded_claim_id"] = min(
                        origin_candidates,
                        key=lambda node_id: (
                            self._proposal_revision(self.nodes.get(node_id)) or 0,
                            node_id,
                        ),
                    )
                    variant.metadata["rehydration_stale_parent_origin_repair"] = (
                        "claim_formalized_as"
                    )
                variant.metadata["claim_node_id"] = parent.node_id
                variant.metadata["rehydration_parent_metadata_repair"] = (
                    "claim_node_id_live_without_edge"
                )
                remove_keys = {
                    (edge.source, edge.target, edge.kind)
                    for edge in self.incoming(
                        variant.node_id,
                        kind="claim_formalized_as",
                    )
                    if edge.source != parent.node_id
                }
                if remove_keys:
                    self.edges = [
                        edge
                        for edge in self.edges
                        if (edge.source, edge.target, edge.kind) not in remove_keys
                    ]
                    self._rebuild_edge_index()
                self._add_edge(parent.node_id, variant.node_id, "claim_formalized_as")
                continue
            variant.metadata["claim_node_id"] = (
                live_parent_ids[0] if live_parent_ids else edge_parent_ids[0]
            )
            variant.metadata["rehydration_parent_metadata_repair"] = (
                "claim_formalized_as_mismatch"
                if parent_id
                else "claim_formalized_as"
            )

    def _repair_graph_native_metadata_edges(self) -> None:
        """Backfill durable graph-native edges from replayed node metadata."""

        for obligation in self.nodes_by_kind("missing_obligation"):
            metadata = dict(obligation.metadata or {})
            source_id = str(metadata.get("source_node_id") or "").strip()
            route_id = str(metadata.get("route_id") or "").strip()
            if source_id in self.nodes:
                self._add_edge(source_id, obligation.node_id, "failure_requires")
            route_dependency_replaced_by_bridge = bool(
                metadata.get("formalization_bridge_parent_obligation_detached_from_route")
                or metadata.get("formalization_bridge_parent_work_materialized")
            )
            if route_id in self.nodes and not route_dependency_replaced_by_bridge:
                self._add_edge(route_id, obligation.node_id, "route_blocked_by")
        for replan in self.nodes_by_kind("replan_queue_item"):
            metadata = dict(replan.metadata or {})
            source_id = str(metadata.get("source_node_id") or "").strip()
            route_id = str(metadata.get("route_id") or "").strip()
            obligation_ids = (
                str(metadata.get("obligation_id") or "").strip(),
                str(metadata.get("resolved_by_obligation_id") or "").strip(),
            )
            if source_id in self.nodes:
                self._add_edge(source_id, replan.node_id, "needs_replan")
            if route_id in self.nodes:
                self._add_edge(route_id, replan.node_id, "route_replan")
            for obligation_id in obligation_ids:
                if obligation_id in self.nodes:
                    self._add_edge(obligation_id, replan.node_id, "obligation_replan")
                    self._sync_replan_with_obligation_status(replan, obligation_id)

    def _graph_native_source_links(
        self,
        node: Optional[ProofGraphNode],
    ) -> Tuple[List[str], List[str], List[str]]:
        source_ids: List[str] = []
        route_ids: List[str] = []
        obligation_ids: List[str] = []

        def append_unique(values: List[str], value: str) -> None:
            clean = str(value or "").strip()
            if clean and clean not in values:
                values.append(clean)

        if node is None or node.kind not in {"missing_obligation", "replan_queue_item"}:
            return source_ids, route_ids, obligation_ids
        metadata = dict(node.metadata or {})
        append_unique(source_ids, str(metadata.get("source_node_id") or ""))
        append_unique(route_ids, str(metadata.get("route_id") or ""))
        if node.kind == "missing_obligation":
            for edge in self.incoming(node.node_id):
                if edge.kind == "failure_requires":
                    append_unique(source_ids, edge.source)
                elif edge.kind == "route_blocked_by":
                    append_unique(route_ids, edge.source)
            return source_ids, route_ids, obligation_ids

        append_unique(obligation_ids, str(metadata.get("obligation_id") or ""))
        append_unique(
            obligation_ids,
            str(metadata.get("resolved_by_obligation_id") or ""),
        )
        for edge in self.incoming(node.node_id):
            if edge.kind == "needs_replan":
                append_unique(source_ids, edge.source)
            elif edge.kind == "route_replan":
                append_unique(route_ids, edge.source)
            elif edge.kind == "obligation_replan":
                append_unique(obligation_ids, edge.source)
        return source_ids, route_ids, obligation_ids

    def _route_has_superseded_dependency(
        self,
        route_id: str,
        *,
        ignore_node_id: str = "",
    ) -> bool:
        route = str(route_id or "").strip()
        if not route:
            return False
        ignored = str(ignore_node_id or "").strip()
        for edge in self.outgoing(route):
            if edge.kind not in {"route_requires", "route_blocked_by", "route_replan"}:
                continue
            if ignored and edge.target == ignored:
                continue
            if self.is_superseded_tombstone(self.nodes.get(edge.target)):
                return True
        return False

    @staticmethod
    def _route_links_are_primary_source(
        source_ids: Iterable[str],
        obligation_ids: Iterable[str],
    ) -> bool:
        return not any(str(item or "").strip() for item in source_ids) and not any(
            str(item or "").strip() for item in obligation_ids
        )

    def _all_route_links_have_superseded_dependencies(
        self,
        route_ids: Iterable[str],
        *,
        ignore_node_id: str = "",
    ) -> bool:
        routes = [str(route_id or "").strip() for route_id in route_ids]
        routes = [route_id for route_id in routes if route_id]
        return bool(routes) and all(
            self._route_has_superseded_dependency(
                route_id,
                ignore_node_id=ignore_node_id,
            )
            for route_id in routes
        )

    def _graph_native_source_is_superseded(
        self,
        node: Optional[ProofGraphNode],
    ) -> bool:
        if node is None or node.kind not in {"missing_obligation", "replan_queue_item"}:
            return False
        source_ids, route_ids, obligation_ids = self._graph_native_source_links(node)
        if any(
            source_id and self.is_superseded_tombstone(self.nodes.get(source_id))
            for source_id in source_ids
        ):
            return True
        if (
            self._route_links_are_primary_source(source_ids, obligation_ids)
            and self._all_route_links_have_superseded_dependencies(
                route_ids,
                ignore_node_id=node.node_id,
            )
        ):
            return True
        return any(
            obligation_id
            and self.is_superseded_tombstone(self.nodes.get(obligation_id))
            for obligation_id in obligation_ids
        )

    def _reject_graph_native_node_from_superseded_source(
        self,
        node: Optional[ProofGraphNode],
    ) -> bool:
        if not self._graph_native_source_is_superseded(node):
            return False
        source_ids, route_ids, obligation_ids = self._graph_native_source_links(node)
        source_node_id = ""
        for source_id in source_ids:
            if source_id and self.is_superseded_tombstone(self.nodes.get(source_id)):
                source_node_id = source_id
                break
        if not source_node_id:
            if self._route_links_are_primary_source(source_ids, obligation_ids):
                if self._all_route_links_have_superseded_dependencies(
                    route_ids,
                    ignore_node_id=node.node_id,
                ):
                    for route_id in route_ids:
                        if self._route_has_superseded_dependency(
                            route_id,
                            ignore_node_id=node.node_id,
                        ):
                            source_node_id = route_id
                            break
        if not source_node_id:
            for obligation_id in obligation_ids:
                if obligation_id and self.is_superseded_tombstone(
                    self.nodes.get(obligation_id)
                ):
                    source_node_id = obligation_id
                    break
        self._mark_node_superseded_by_source(
            node,
            source_node_id=source_node_id,
        )
        return True

    def _revive_graph_native_node_if_sources_clean(
        self,
        node: Optional[ProofGraphNode],
    ) -> bool:
        if (
            node is None
            or node.kind not in {"missing_obligation", "replan_queue_item"}
            or not self.is_superseded_tombstone(node)
            or self._graph_native_source_is_superseded(node)
        ):
            return False
        source_ids, route_ids, obligation_ids = self._graph_native_source_links(node)
        if not source_ids and not route_ids and not obligation_ids:
            return False
        metadata = node.metadata
        previous_status = str(metadata.pop("superseded_previous_status", "") or "")
        previous_proof_hash = str(
            metadata.pop("superseded_previous_proof_hash", "") or ""
        ).strip()
        previous_source_hash = str(
            metadata.pop("superseded_previous_source_hash", "") or ""
        ).strip()
        metadata.pop("proposal_superseded", None)
        metadata.pop("tombstone_status", None)
        metadata.pop("superseded_source_node_id", None)
        metadata.pop("route_retarget_revision_guarded", None)
        metadata["graph_native_tombstone_revived"] = "source_links_clean"
        if previous_status == "proved":
            if previous_proof_hash:
                node.proof_hash = previous_proof_hash
            if previous_source_hash and not node.source_hash:
                node.source_hash = previous_source_hash
            node.status = "proved"
            if not self._proved_node_has_durable_certificate(node):
                node.status = "open"
                node.proof_hash = ""
        elif node.status == "rejected":
            node.status = "open"
        return True

    def revive_verified_helper_node(self, node_id: str) -> bool:
        """Clear proposal tombstones when a helper has fresh Lean evidence."""

        node = self.nodes.get(str(node_id or "").strip())
        if node is None or node.kind != "helper":
            return False
        metadata = node.metadata
        tombstone_keys = (
            "proposal_superseded",
            "proposal_invalidated",
            "invalidated_statement_key",
            "invalid_reason",
            "tombstone_status",
            "superseded_source_node_id",
            "route_retarget_revision_guarded",
            "superseded_previous_status",
            "superseded_previous_proof_hash",
            "superseded_previous_source_hash",
        )
        changed = False
        for key in tombstone_keys:
            if key in metadata:
                metadata.pop(key, None)
                changed = True
        if node.status in {"rejected", "failed", "blocked"}:
            node.status = "open"
            changed = True
        if changed:
            metadata["verified_helper_tombstone_revived"] = True
        return changed

    def _repair_graph_native_source_tombstones(self) -> None:
        """Reject graph-native work whose source chain now points at tombstones."""

        max_iterations = max(8, len(self.nodes) + len(self.edges) + 1)
        for _ in range(max_iterations):
            before = self._superseded_repair_signature()
            for node in self.nodes.values():
                self._revive_graph_native_node_if_sources_clean(node)
            for node in self.nodes.values():
                self._reject_graph_native_node_from_superseded_source(node)
            for node in self.nodes.values():
                self._enforce_superseded_tombstone(node)
            if self._superseded_repair_signature() == before:
                break

    def _mark_node_superseded_by_source(
        self,
        node: ProofGraphNode,
        *,
        source_node_id: str = "",
    ) -> None:
        self._retarget_equivalent_route_dependencies(
            node,
            source_node_id=source_node_id,
        )
        node.metadata["proposal_superseded"] = True
        if source_node_id:
            node.metadata["superseded_source_node_id"] = source_node_id
            node.metadata["route_retarget_revision_guarded"] = True
        if node.status == "proved":
            node.metadata["superseded_previous_status"] = "proved"
        self._enforce_superseded_tombstone(node)

    def _invalidate_strategy_route_assembly(
        self,
        route_id: str,
        *,
        reason: str,
        dependency_node_id: str = "",
    ) -> bool:
        route = self.nodes.get(str(route_id or "").strip())
        if route is None or route.kind != "strategy_route":
            return False
        had_assembly = (
            route.status == "proved"
            or bool(route.proof_hash)
            or bool((route.metadata or {}).get("assembled_dependency_node_ids"))
        )
        if not had_assembly:
            return False
        previous_dependencies = list(
            (route.metadata or {}).get("assembled_dependency_node_ids") or []
        )
        route.status = "open"
        route.proof_hash = ""
        route.metadata.pop("assembled_dependency_node_ids", None)
        route.metadata.pop("assembled_by_action", None)
        route.metadata.pop("assembled_route_proof_hash", None)
        route.metadata.pop("assembled_dependency_signature_hash", None)
        route.metadata.pop("assembled_branch_frame_ids", None)
        route.metadata.pop("route_cases_assembly_helper_names", None)
        route.metadata["route_assembly_invalidated_reason"] = str(reason or "")
        if dependency_node_id:
            route.metadata["route_assembly_invalidated_dependency_node_id"] = (
                dependency_node_id
            )
        if previous_dependencies:
            route.metadata["invalidated_assembled_dependency_node_ids"] = (
                previous_dependencies
            )
        return True

    def retire_strategy_route(
        self,
        route_id: str,
        *,
        reason: str,
        dependency_node_id: str = "",
        verdict: str = "route_dependency_contradicted",
    ) -> bool:
        """Terminally retire a route whose required dependency is invalidated."""

        clean_route_id = str(route_id or "").strip()
        route = self.nodes.get(clean_route_id)
        if route is None or route.kind != "strategy_route":
            return False
        was_terminally_retired = bool(
            (route.metadata or {}).get("route_retired")
            or (route.metadata or {}).get("route_dependency_contradicted")
        )
        if was_terminally_retired:
            return False
        reason_text = str(reason or "").strip()
        dependency_id = str(dependency_node_id or "").strip()
        self._invalidate_strategy_route_assembly(
            clean_route_id,
            reason=reason_text or verdict,
            dependency_node_id=dependency_id,
        )
        route.status = "rejected"
        route.proof_hash = ""
        route.metadata["activation_status"] = "archived"
        route.metadata["route_retired"] = True
        route.metadata["route_dependency_contradicted"] = True
        route.metadata["route_retirement_verdict"] = str(
            verdict or "route_dependency_contradicted"
        )
        route.metadata["route_retired_reason"] = reason_text
        if dependency_id:
            route.metadata["route_retired_dependency_node_id"] = dependency_id
        route.metadata.pop("assembled_route_proof_hash", None)
        route.metadata.pop("assembled_dependency_signature_hash", None)
        route.metadata.pop("assembled_dependency_node_ids", None)
        route.metadata.pop("assembled_branch_frame_ids", None)
        route.metadata.pop("route_cases_assembly_helper_names", None)
        route.metadata["route_assembly_contract_last_verdict"] = "route_retired"
        self._replace_route_branch_frames(clean_route_id, [])
        for node in list(self.nodes.values()):
            if clean_route_id not in self._node_route_ids(node):
                continue
            if node.kind not in {"missing_obligation", "replan_queue_item"}:
                continue
            if str(getattr(node, "status", "") or "") == "proved":
                continue
            remaining_live_route_ids = sorted(
                route_id
                for route_id in self._node_route_ids(node)
                if route_id != clean_route_id
                and not self._route_is_terminally_poisoned(route_id)
            )
            if remaining_live_route_ids:
                node.metadata["route_id"] = remaining_live_route_ids[0]
                retired_route_ids = list(node.metadata.get("retired_route_ids") or [])
                if clean_route_id not in retired_route_ids:
                    retired_route_ids.append(clean_route_id)
                node.metadata["retired_route_ids"] = retired_route_ids[-32:]
                for key in (
                    "route_retired",
                    "route_retired_reason",
                    "route_retirement_verdict",
                    "route_retired_dependency_node_id",
                    "route_dependency_contradicted",
                    "route_poisoned_descendant_suppressed",
                ):
                    node.metadata.pop(key, None)
                continue
            node.status = "rejected"
            node.proof_hash = ""
            node.metadata["route_retired"] = True
            node.metadata["route_retired_reason"] = reason_text
            node.metadata["route_retirement_verdict"] = str(
                verdict or "route_dependency_contradicted"
            )
            if dependency_id:
                node.metadata["route_retired_dependency_node_id"] = dependency_id
        self.record_attempt(
            clean_route_id,
            phase="route_retirement",
            turn_index=0,
            proof="",
            verdict=str(verdict or "route_dependency_contradicted"),
            error_type="route_retired",
            metadata={
                "reason": reason_text,
                "dependency_node_id": dependency_id,
            },
        )
        return not was_terminally_retired

    def _repair_invalid_route_assemblies(self) -> None:
        """Reopen assembled routes whose serialized dependency certificate is stale."""

        for route in self.nodes_by_kind("strategy_route"):
            metadata = dict(route.metadata or {})
            kernel_finalization_hash = str(
                metadata.get("kernel_finalized_root_proof_hash") or ""
            ).strip()
            if (
                kernel_finalization_hash
                and route.status == "proved"
                and route.proof_hash == kernel_finalization_hash
            ):
                # A root proof accepted by the kernel is an independent route
                # certificate. Graph dependencies remain provenance, not a
                # second authority capable of revoking that exact proof.
                continue
            assembled_ids = [
                str(node_id or "").strip()
                for node_id in list(metadata.get("assembled_dependency_node_ids") or [])
                if str(node_id or "").strip()
            ]
            if route.status != "proved" and not route.proof_hash and not assembled_ids:
                continue
            current_deps = [
                edge.target
                for edge in self._route_dependency_edges(route.node_id)
            ]
            stale_dependency_id = next(
                (
                    node_id
                    for node_id in [*assembled_ids, *current_deps]
                    if self.is_superseded_tombstone(self.nodes.get(node_id))
                ),
                "",
            )
            dependency_mismatch = bool(assembled_ids) and set(assembled_ids) != set(
                current_deps
            )
            signature_hash = str(
                metadata.get("assembled_dependency_signature_hash") or ""
            ).strip()
            missing_signature = bool(
                metadata.get("assembled_route_proof_hash")
                or metadata.get("assembled_dependency_node_ids")
            ) and not signature_hash
            signature_mismatch = bool(signature_hash) and (
                signature_hash != self.route_dependency_signature_hash(route.node_id)
            )
            missing_dependencies = route.status == "proved" and not current_deps
            # Wipe for a dependency that stopped being proved, never for
            # "this contract is not assemblable yet". ``ready`` is also false
            # while a leftover helper or an unsatisfied hollow reducer is
            # outstanding, and using it here cleared the status and proof of an
            # already-assembled route -- turning a not-ready-yet contract into
            # a teardown of live work. Only kernel-finalized roots were spared.
            unproved_assembled_dependency = any(
                (self.nodes.get(node_id) is None)
                or (self.nodes.get(node_id).status != "proved")
                for node_id in assembled_ids
            )
            if not (
                stale_dependency_id
                or dependency_mismatch
                or missing_signature
                or signature_mismatch
                or missing_dependencies
                or unproved_assembled_dependency
            ):
                continue
            self._invalidate_strategy_route_assembly(
                route.node_id,
                reason=(
                    "serialized_route_assembly_stale"
                    if stale_dependency_id or dependency_mismatch or missing_dependencies
                    else "serialized_route_dependency_signature_stale"
                    if signature_mismatch
                    else "serialized_route_dependency_signature_missing"
                    if missing_signature
                    else "serialized_route_assembled_dependency_unproved"
                ),
                dependency_node_id=stale_dependency_id
                or (assembled_ids[0] if assembled_ids else ""),
            )

    def _retarget_equivalent_route_dependencies(
        self,
        node: ProofGraphNode,
        *,
        source_node_id: str = "",
        allow_newer_revision: bool = False,
    ) -> bool:
        source = self.nodes.get(str(source_node_id or "").strip())
        if (
            source is None
            or source.node_id == node.node_id
            or source.kind != node.kind
            or self.is_superseded_tombstone(source)
        ):
            return False
        source_key = graph_statement_key(source.statement)
        node_key = graph_statement_key(node.statement)
        if not source_key or source_key != node_key:
            return False
        node_revision = self._effective_proposal_revision(node)
        source_revision = self._effective_proposal_revision(source)
        if (
            not allow_newer_revision
            and source_revision > node_revision
        ):
            return False
        route_edge_kinds = {"route_requires", "route_blocked_by", "route_replan"}
        remove_keys: Set[Tuple[str, str, str]] = set()
        redirects: List[Tuple[str, str, str]] = []
        for edge in self.incoming(node.node_id):
            if edge.kind not in route_edge_kinds:
                continue
            route = self.nodes.get(edge.source)
            if route is None or route.kind != "strategy_route":
                continue
            remove_keys.add((edge.source, edge.target, edge.kind))
            redirects.append((edge.source, source.node_id, edge.kind))
        if not remove_keys:
            return False
        self.edges = [
            edge
            for edge in self.edges
            if (edge.source, edge.target, edge.kind) not in remove_keys
        ]
        self._rebuild_edge_index()
        for source_id, target_id, kind in redirects:
            contract_retargeted = self.retarget_route_assembly_contract_requirement(
                source_id,
                old_node_id=node.node_id,
                new_node_id=target_id,
            )
            if not contract_retargeted:
                self._add_edge(source_id, target_id, kind)
                self._invalidate_strategy_route_assembly(
                    source_id,
                    reason="route_dependency_retargeted",
                    dependency_node_id=node.node_id,
                )
        return True

    def _reparent_equivalent_child_variant_from_superseded_claim(
        self,
        variant: ProofGraphNode,
        *,
        parent_id: str = "",
    ) -> bool:
        if (
            variant.kind != "formal_variant"
            or self.is_superseded_tombstone(variant)
        ):
            return False
        old_parent_id = str(parent_id or "").strip()
        if not old_parent_id:
            for edge in self.incoming(variant.node_id, kind="claim_formalized_as"):
                if self.is_superseded_tombstone(self.nodes.get(edge.source)):
                    old_parent_id = edge.source
                    break
        old_parent = self.nodes.get(old_parent_id)
        if old_parent is None or not self.is_superseded_tombstone(old_parent):
            return False
        old_parent_key = graph_statement_key(old_parent.statement)
        source = self._live_superseded_source_candidate(
            old_parent_id,
            kind="proposed_claim",
            statement_key=old_parent_key,
        )
        if (
            source is None
            or source.kind != "proposed_claim"
            or self.is_superseded_tombstone(source)
        ):
            return False
        source_key = graph_statement_key(source.statement)
        variant_key = graph_statement_key(variant.statement)
        if (
            not source_key
            or source_key != old_parent_key
            or source_key != variant_key
        ):
            return False
        old_revision = self._proposal_revision(old_parent)
        source_revision = self._proposal_revision(source)
        own_variant_revision = self._proposal_revision(variant)
        variant_revision = self._effective_proposal_revision(variant)
        variant_is_current = (
            own_variant_revision > 0
            and source_revision > 0
            and own_variant_revision >= source_revision
        )
        if (
            old_revision > 0
            and source_revision > old_revision
            and not variant_is_current
        ):
            return False
        if variant_revision > 0 and source_revision > variant_revision:
            return False
        remove_keys = {
            (edge.source, edge.target, edge.kind)
            for edge in self.incoming(variant.node_id, kind="claim_formalized_as")
            if edge.source == old_parent_id
        }
        if remove_keys:
            self.edges = [
                edge
                for edge in self.edges
                if (edge.source, edge.target, edge.kind) not in remove_keys
            ]
            self._rebuild_edge_index()
        variant.metadata["claim_node_id"] = source.node_id
        variant.metadata["reparented_from_superseded_claim_id"] = old_parent_id
        self._add_edge(source.node_id, variant.node_id, "claim_formalized_as")
        return True

    def _remove_stale_superseded_parent_edges_for_variant(
        self,
        variant: ProofGraphNode,
        *,
        tombstone_ids: Set[str],
    ) -> bool:
        parent_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
        parent = self.nodes.get(parent_id)
        if (
            variant.kind != "formal_variant"
            or not parent_id
            or parent is None
            or self.is_superseded_tombstone(parent)
        ):
            return False
        parent_key = graph_statement_key(parent.statement)
        variant_key = graph_statement_key(variant.statement)
        if not parent_key or parent_key != variant_key:
            return False
        stale_parent_ids = {
            edge.source
            for edge in self.incoming(variant.node_id, kind="claim_formalized_as")
            if edge.source in tombstone_ids and edge.source != parent_id
        }
        if not stale_parent_ids:
            return False
        parent_revision = self._proposal_revision(parent)
        variant_revision = self._effective_proposal_revision(variant)
        if variant_revision > 0 and parent_revision > variant_revision:
            return False
        remove_keys = {
            (edge.source, edge.target, edge.kind)
            for edge in self.incoming(variant.node_id, kind="claim_formalized_as")
            if edge.source in stale_parent_ids
        }
        self.edges = [
            edge
            for edge in self.edges
            if (edge.source, edge.target, edge.kind) not in remove_keys
        ]
        self._rebuild_edge_index()
        self._add_edge(parent_id, variant.node_id, "claim_formalized_as")
        return True

    @staticmethod
    def _spawned_claim_blocked_work_kind(node: Optional[ProofGraphNode]) -> bool:
        return node is not None and node.kind in {
            "proposed_claim",
            "formal_variant",
            "missing_obligation",
            "replan_queue_item",
            "strategy_route",
        }

    def _reopen_work_blocked_by_superseded_spawned_claims(
        self,
        tombstone_ids: Set[str],
    ) -> Set[str]:
        """Requeue graph-native work whose spawned proposal was superseded."""

        tombstones = {
            str(node_id or "").strip()
            for node_id in tombstone_ids
            if self.is_superseded_tombstone(self.nodes.get(str(node_id or "").strip()))
        }
        if not tombstones:
            return set()
        work_to_tombstones: Dict[str, Set[str]] = {}
        for tombstone_id in tombstones:
            for edge in self.incoming(tombstone_id, kind="replan_spawned_claim"):
                work_node = self.nodes.get(edge.source)
                if (
                    not self._spawned_claim_blocked_work_kind(work_node)
                    or work_node.status != "blocked"
                    or self.is_superseded_tombstone(work_node)
                ):
                    continue
                work_to_tombstones.setdefault(work_node.node_id, set()).add(
                    tombstone_id
                )
        if not work_to_tombstones:
            return set()
        remove_keys = {
            (work_node_id, tombstone_id, "blocked_by")
            for work_node_id, blocked_tombstones in work_to_tombstones.items()
            for tombstone_id in blocked_tombstones
        }
        if remove_keys:
            self.edges = [
                edge
                for edge in self.edges
                if (edge.source, edge.target, edge.kind) not in remove_keys
            ]
            self._rebuild_edge_index()
        reopened: Set[str] = set()
        for work_node_id, blocked_tombstones in work_to_tombstones.items():
            work_node = self.nodes.get(work_node_id)
            if work_node is None or work_node.status != "blocked":
                continue
            remaining_blockers = [
                edge
                for edge in self.outgoing(work_node_id, kind="blocked_by")
                if edge.target not in blocked_tombstones
            ]
            if remaining_blockers:
                continue
            if self.reopen_node(
                work_node_id,
                reason="spawned_claim_superseded",
            ):
                work_node.metadata["spawned_claim_superseded_reopen_ids"] = sorted(
                    blocked_tombstones
                )
                reopened.add(work_node_id)
        return reopened

    def _cascade_superseded_downstream(
        self,
        *,
        tombstone_ids: Optional[Set[str]] = None,
    ) -> Set[str]:
        """Propagate superseded proposal tombstones to dependent work nodes."""

        initial_tombstone_ids = {
            node.node_id
            for node in self.nodes.values()
            if self.is_superseded_tombstone(node)
        }
        tombstone_ids = set(
            tombstone_ids
            if tombstone_ids is not None
            else {
                node.node_id
                for node in self.nodes.values()
                if self.is_superseded_tombstone(node)
            }
        )
        if not tombstone_ids:
            return set()
        variant_ids: Set[str] = set()
        for source_id in list(tombstone_ids):
            variant_ids.update(
                edge.target
                for edge in self.outgoing(source_id, kind="claim_formalized_as")
            )
        for variant in self.nodes_by_kind("formal_variant"):
            parent_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
            if parent_id in tombstone_ids:
                variant_ids.add(variant.node_id)
        for variant_id in variant_ids:
            variant = self.nodes.get(variant_id)
            if variant is None or variant.kind != "formal_variant":
                continue
            parent_id = str((variant.metadata or {}).get("claim_node_id") or "").strip()
            if self._remove_stale_superseded_parent_edges_for_variant(
                variant,
                tombstone_ids=tombstone_ids,
            ):
                continue
            if self._reparent_equivalent_child_variant_from_superseded_claim(
                variant,
                parent_id=parent_id,
            ):
                continue
            self._mark_node_superseded_by_source(
                variant,
                source_node_id=parent_id if parent_id in tombstone_ids else "",
            )
            tombstone_ids.add(variant.node_id)
        self._reopen_work_blocked_by_superseded_spawned_claims(tombstone_ids)
        obligation_ids: Set[str] = set()
        replan_ids: Set[str] = set()
        route_ids: Set[str] = set()
        changed = True
        while changed:
            changed = False
            for source_id in list(tombstone_ids):
                obligation_ids.update(
                    edge.target
                    for edge in self.outgoing(source_id, kind="failure_requires")
                )
                replan_ids.update(
                    edge.target for edge in self.outgoing(source_id, kind="needs_replan")
                )
                replan_ids.update(
                    edge.target
                    for edge in self.outgoing(source_id, kind="obligation_replan")
                )
                route_ids.update(
                    edge.source
                    for edge in self.incoming(source_id)
                    if edge.kind in {"route_requires", "route_blocked_by", "route_replan"}
                )
            for route_id in list(route_ids):
                for edge in self.outgoing(route_id):
                    if edge.kind not in {
                        "route_requires",
                        "route_blocked_by",
                        "route_replan",
                    }:
                        continue
                    if edge.target not in tombstone_ids and not self.is_superseded_tombstone(
                        self.nodes.get(edge.target)
                    ):
                        continue
                    if self._invalidate_strategy_route_assembly(
                        route_id,
                        reason="route_dependency_superseded",
                        dependency_node_id=edge.target,
                    ):
                        changed = True
                    break
            for route_id in list(route_ids):
                for edge in self.outgoing(route_id, kind="route_blocked_by"):
                    obligation = self.nodes.get(edge.target)
                    source_links, route_links, obligation_links = (
                        self._graph_native_source_links(obligation)
                    )
                    if self._route_links_are_primary_source(
                        source_links,
                        obligation_links,
                    ) and self._all_route_links_have_superseded_dependencies(
                        route_links,
                        ignore_node_id=edge.target,
                    ):
                        obligation_ids.add(edge.target)
                for edge in self.outgoing(route_id, kind="route_replan"):
                    replan = self.nodes.get(edge.target)
                    source_links, route_links, obligation_links = (
                        self._graph_native_source_links(replan)
                    )
                    if self._route_links_are_primary_source(
                        source_links,
                        obligation_links,
                    ) and self._all_route_links_have_superseded_dependencies(
                        route_links,
                        ignore_node_id=edge.target,
                    ):
                        replan_ids.add(edge.target)
            for obligation in self.nodes_by_kind("missing_obligation"):
                source_ids, route_link_ids, _obligation_ids = (
                    self._graph_native_source_links(obligation)
                )
                if any(source in tombstone_ids for source in source_ids) or (
                    any(route in route_ids for route in route_link_ids)
                    and self._route_links_are_primary_source(
                        source_ids,
                        _obligation_ids,
                    )
                    and self._all_route_links_have_superseded_dependencies(
                        route_link_ids,
                        ignore_node_id=obligation.node_id,
                    )
                ):
                    obligation_ids.add(obligation.node_id)
            for obligation_id in list(obligation_ids):
                obligation = self.nodes.get(obligation_id)
                if obligation is None or obligation.kind != "missing_obligation":
                    continue
                source_ids, _route_link_ids, _obligation_ids = (
                    self._graph_native_source_links(obligation)
                )
                source = next(
                    (candidate for candidate in source_ids if candidate in tombstone_ids),
                    "",
                )
                was_tombstone = obligation.node_id in tombstone_ids
                self._mark_node_superseded_by_source(
                    obligation,
                    source_node_id=source if source in tombstone_ids else "",
                )
                if not was_tombstone:
                    tombstone_ids.add(obligation.node_id)
                    changed = True
                replan_ids.update(
                    edge.target
                    for edge in self.outgoing(obligation.node_id, kind="obligation_replan")
                )
            for replan in self.nodes_by_kind("replan_queue_item"):
                source_ids, route_link_ids, replan_obligation_ids = (
                    self._graph_native_source_links(replan)
                )
                if (
                    any(source in tombstone_ids for source in source_ids)
                    or (
                        any(route in route_ids for route in route_link_ids)
                        and self._route_links_are_primary_source(
                            source_ids,
                            replan_obligation_ids,
                        )
                        and self._all_route_links_have_superseded_dependencies(
                            route_link_ids,
                            ignore_node_id=replan.node_id,
                        )
                    )
                    or any(
                        obligation in obligation_ids or obligation in tombstone_ids
                        for obligation in replan_obligation_ids
                    )
                ):
                    replan_ids.add(replan.node_id)
            for replan_id in list(replan_ids):
                replan = self.nodes.get(replan_id)
                if replan is None or replan.kind != "replan_queue_item":
                    continue
                source_ids, route_link_ids, replan_obligation_ids = (
                    self._graph_native_source_links(replan)
                )
                superseded_source = ""
                for candidate in [*source_ids, *replan_obligation_ids, *route_link_ids]:
                    if candidate and (
                        candidate in tombstone_ids
                        or candidate in obligation_ids
                        or candidate in route_ids
                    ):
                        superseded_source = candidate
                        break
                was_tombstone = replan.node_id in tombstone_ids
                self._mark_node_superseded_by_source(
                    replan,
                    source_node_id=superseded_source,
                )
                if not was_tombstone:
                    tombstone_ids.add(replan.node_id)
                    changed = True
        return {
            node.node_id
            for node in self.nodes.values()
            if self.is_superseded_tombstone(node)
        } - initial_tombstone_ids

    def _guarded_route_fallback_successor_ids(self) -> Set[str]:
        """Live same-revision successors that guarded route repair must preserve."""

        protected: Set[str] = set()
        route_edge_kinds = {"route_requires", "route_blocked_by", "route_replan"}
        for node in self.nodes.values():
            metadata = dict(node.metadata or {})
            tombstone_has_route_edge = any(
                edge.kind in route_edge_kinds for edge in self.incoming(node.node_id)
            )
            if (
                not self.is_superseded_tombstone(node)
                or not metadata.get("route_retarget_revision_guarded")
            ):
                continue
            statement_key = graph_statement_key(node.statement)
            if not statement_key:
                continue
            node_revision = self._effective_proposal_revision(node)
            successor_ids = [
                str(metadata.get("superseded_source_node_id") or ""),
                str(metadata.get("duplicate_same_name_generation_superseded_by") or ""),
            ]
            for successor_id in dict.fromkeys(
                candidate.strip() for candidate in successor_ids if candidate.strip()
            ):
                for candidate in self._live_superseded_source_candidates(
                    successor_id,
                    kind=node.kind,
                    statement_key=statement_key,
                ):
                    candidate_has_route_edge = any(
                        edge.kind in route_edge_kinds
                        for edge in self.incoming(candidate.node_id)
                    )
                    if (
                        candidate.node_id != node.node_id
                        and (tombstone_has_route_edge or candidate_has_route_edge)
                        and self._effective_proposal_revision(candidate)
                        <= node_revision
                    ):
                        protected.add(candidate.node_id)
        return protected

    def _dedupe_live_same_name_statement_generations(self) -> None:
        """On replay, keep only the newest live same-name proposal statement."""

        node_order = {
            node.node_id: index for index, node in enumerate(self.nodes.values())
        }
        guarded_fallback_successor_ids = self._guarded_route_fallback_successor_ids()

        def proposal_name(node: ProofGraphNode) -> str:
            return self._proposal_generation_name(
                node_name=node.name,
                metadata=node.metadata,
                prefer_variant_name=node.kind == "formal_variant",
            )

        def route_is_ready_with_node(route: ProofGraphNode, node: ProofGraphNode) -> bool:
            for edge in self.outgoing(route.node_id):
                if edge.kind not in {
                    "route_requires",
                    "route_blocked_by",
                    "route_replan",
                }:
                    continue
                if edge.target == node.node_id:
                    continue
                target = self.nodes.get(edge.target)
                if (
                    target is None
                    or not self._proved_node_has_durable_certificate(target)
                ):
                    return False
            return True

        def direct_proved_route_dependency_counts(
            node: ProofGraphNode,
        ) -> Tuple[int, int]:
            if not self._proved_node_has_durable_certificate(node):
                return (0, 0)
            ready_count = 0
            open_count = 0
            for edge in self.incoming(node.node_id):
                if edge.kind not in {
                    "route_requires",
                    "route_blocked_by",
                    "route_replan",
                }:
                    continue
                route = self.nodes.get(edge.source)
                if (
                    route is not None
                    and route.kind == "strategy_route"
                    and route.status == "open"
                    and not self.is_superseded_tombstone(route)
                ):
                    open_count += 1
                    if route_is_ready_with_node(route, node):
                        ready_count += 1
            return (ready_count, open_count)

        def proved_route_dependency_counts(node: ProofGraphNode) -> Tuple[int, int]:
            ready_count, open_count = direct_proved_route_dependency_counts(node)
            if node.kind != "proposed_claim":
                return (ready_count, open_count)
            claim_statement_key = graph_statement_key(node.statement)
            if not claim_statement_key:
                return (ready_count, open_count)
            variant_ids = {
                edge.target
                for edge in self.outgoing(node.node_id, kind="claim_formalized_as")
            }
            for variant in self.nodes_by_kind("formal_variant"):
                parent_id = str(
                    (variant.metadata or {}).get("claim_node_id") or ""
                ).strip()
                if parent_id == node.node_id:
                    variant_ids.add(variant.node_id)
            for variant_id in variant_ids:
                variant = self.nodes.get(variant_id)
                if (
                    variant is None
                    or variant.kind != "formal_variant"
                    or self.is_superseded_tombstone(variant)
                    or graph_statement_key(variant.statement) != claim_statement_key
                ):
                    continue
                child_ready, child_open = direct_proved_route_dependency_counts(variant)
                ready_count += child_ready
                open_count += child_open
            return (ready_count, open_count)

        def proposal_score(
            node: ProofGraphNode,
        ) -> Tuple[int, int, int, int, int, int, int, int]:
            proposal_revision = self._effective_proposal_revision(node)
            ready_route_count, open_route_count = proved_route_dependency_counts(node)
            proved_with_certificate = self._proved_node_has_durable_certificate(node)
            return (
                1 if graph_statement_key(node.statement) else 0,
                0 if self._formal_variant_crosses_parent_revision(node) else 1,
                1 if proved_with_certificate else 0,
                proposal_revision,
                ready_route_count,
                open_route_count,
                int(node.turn_index or 0),
                int(node_order.get(node.node_id, 0)),
            )

        for kind in ("proposed_claim", "formal_variant"):
            groups: Dict[Tuple[str, str], List[ProofGraphNode]] = {}
            for node in self.nodes_by_kind(kind):
                if self.is_superseded_tombstone(node):
                    continue
                name = proposal_name(node)
                if not name:
                    continue
                groups.setdefault((name, graph_statement_key(node.statement)), []).append(
                    node
                )
            for nodes in groups.values():
                if len(nodes) <= 1:
                    continue
                active = max(nodes, key=proposal_score)
                active_statement_key = graph_statement_key(active.statement)
                for node in nodes:
                    if (
                        node.node_id == active.node_id
                        or node.node_id in guarded_fallback_successor_ids
                    ):
                        continue
                    node.metadata["proposal_superseded"] = True
                    node.metadata["superseded_active_statement_key"] = (
                        active_statement_key
                    )
                    node.metadata["duplicate_same_name_generation_superseded_by"] = (
                        active.node_id
                    )
                    self._mark_node_superseded_by_source(
                        node,
                        source_node_id=active.node_id,
                    )

    def _superseded_repair_signature(
        self,
    ) -> Tuple[
        Tuple[Tuple[str, str, str, str, str, str], ...],
        Tuple[Tuple[str, str, str], ...],
    ]:
        node_items = tuple(
            sorted(
                (
                    node.node_id,
                    node.status,
                    node.proof_hash,
                    "1" if self.is_superseded_tombstone(node) else "0",
                    str((node.metadata or {}).get("claim_node_id") or ""),
                    str(
                        (node.metadata or {}).get(
                            "duplicate_same_name_generation_superseded_by"
                        )
                        or (node.metadata or {}).get("superseded_source_node_id")
                        or ""
                    ),
                )
                for node in self.nodes.values()
                if node.kind
                in {
                    "proposed_claim",
                    "formal_variant",
                    "missing_obligation",
                    "replan_queue_item",
                    "strategy_route",
                }
            )
        )
        edge_items = tuple(
            sorted((edge.source, edge.target, edge.kind) for edge in self.edges)
        )
        return node_items, edge_items

    def enforce_superseded_tombstones(self) -> None:
        """Repair superseded proposal state until dedupe/cascade reaches a fixed point."""

        max_iterations = max(8, len(self.nodes) + len(self.edges) + 1)
        for _ in range(max_iterations):
            before = self._superseded_repair_signature()
            self._reject_revision_crossing_formal_variants()
            self._dedupe_live_same_name_statement_generations()
            for node in self.nodes.values():
                self._enforce_superseded_tombstone(node)
            self._cascade_superseded_downstream()
            self._reject_revision_crossing_formal_variants()
            for node in self.nodes.values():
                self._enforce_superseded_tombstone(node)
            if self._superseded_repair_signature() == before:
                break

    def blocked_by_resolved(self, node_id: str) -> bool:
        blockers = self.outgoing(node_id, kind="blocked_by")
        if not blockers:
            return False
        for edge in blockers:
            blocker_node = self.nodes.get(edge.target)
            if not self._proved_node_has_durable_certificate(blocker_node):
                return False
        return True

    def repair_terminal_blockers(self) -> Dict[str, List[str]]:
        """Detach blockers that can no longer become proved.

        A ``blocked_by`` edge is a wait condition, not a permanent dependency
        certificate. Once its existing target is terminally unproved, the
        blocked node must be allowed to pursue another proof route instead of
        waiting forever on an impossible transition. Missing targets remain
        attached because they may be forward references restored later.
        """

        terminal_statuses = {"failed", "rejected", "obsolete", "superseded"}
        detached_by_node: Dict[str, List[str]] = {}
        remove_keys: Set[Tuple[str, str, str]] = set()
        for edge in self.edges:
            if edge.kind != "blocked_by":
                continue
            blocker = self.nodes.get(edge.target)
            if blocker is None or (
                str(blocker.status or "") not in terminal_statuses
                and not self.is_superseded_tombstone(blocker)
            ):
                continue
            remove_keys.add((edge.source, edge.target, edge.kind))
            detached_by_node.setdefault(edge.source, []).append(edge.target)
        if not remove_keys:
            return {}
        self.edges = [
            edge
            for edge in self.edges
            if (edge.source, edge.target, edge.kind) not in remove_keys
        ]
        self._rebuild_edge_index()
        for node_id, blocker_ids in detached_by_node.items():
            node = self.nodes.get(node_id)
            if node is None:
                continue
            detached = set(blocker_ids)
            node.metadata["blocked_by_node_ids"] = [
                blocker_id
                for blocker_id in list(node.metadata.get("blocked_by_node_ids") or [])
                if str(blocker_id or "").strip() not in detached
            ]
            node_record = node.metadata.get("proof_state_node")
            if isinstance(node_record, dict):
                node_record["blocked_by_node_ids"] = [
                    blocker_id
                    for blocker_id in list(node_record.get("blocked_by_node_ids") or [])
                    if str(blocker_id or "").strip() not in detached
                ]
            history = list((node.metadata or {}).get("terminal_blocker_history") or [])
            history.extend(blocker_ids)
            node.metadata["terminal_blocker_history"] = list(dict.fromkeys(history))[-32:]
            if node.status == "blocked" and not self.outgoing(
                node_id,
                kind="blocked_by",
            ):
                self.reopen_node(node_id, reason="terminal_blocker_detached")
        return {
            node_id: list(dict.fromkeys(blocker_ids))
            for node_id, blocker_ids in detached_by_node.items()
        }

    def retrieval_evidence_for_node(self, node_id: str) -> Tuple[List[str], List[str]]:
        """Return safe retrieval evidence attached to a node.

        This deliberately excludes proof status. Retrieved declarations/facts
        can justify retrying work, but never certify a proof.
        """

        graph_node_id = str(node_id or "").strip()
        if not graph_node_id:
            return [], []
        decls: List[str] = []
        facts: List[str] = []
        for edge in self.outgoing(graph_node_id):
            if edge.kind not in {"retrieved_declaration", "retrieved_fact"}:
                continue
            retrieval_node = self.nodes.get(edge.target)
            if retrieval_node is None:
                continue
            metadata = dict(retrieval_node.metadata or {})
            if edge.kind == "retrieved_declaration":
                decl = str(
                    metadata.get("decl_name")
                    or retrieval_node.name
                    or retrieval_node.statement
                    or ""
                ).strip()
                if decl:
                    decls.append(decl)
            else:
                fact = str(
                    metadata.get("retrieved_fact")
                    or retrieval_node.statement
                    or retrieval_node.name
                    or ""
                ).strip()
                if fact:
                    facts.append(fact[:1000])
        node = self.nodes.get(graph_node_id)
        metadata = dict(getattr(node, "metadata", {}) or {}) if node is not None else {}
        node_record = metadata.get("proof_state_node")
        if isinstance(node_record, dict):
            for decl in list(node_record.get("retrieved_decl_names") or []):
                clean = str(decl or "").strip()
                if clean:
                    decls.append(clean)
            for fact in list(node_record.get("retrieved_facts") or []):
                clean = str(fact or "").strip()
                if clean:
                    facts.append(clean[:1000])
        return list(dict.fromkeys(decls)), list(dict.fromkeys(facts))

    def evidence_hash_for_node(self, node_id: str) -> str:
        decls, facts = self.retrieval_evidence_for_node(node_id)
        blockers = [
            edge.target
            for edge in self.outgoing(node_id, kind="blocked_by")
            if self._proved_node_has_durable_certificate(self.nodes.get(edge.target))
        ]
        if not decls and not facts and not blockers:
            return ""
        payload = {
            "retrieved_decl_names": sorted(decls),
            "retrieved_facts": sorted(facts),
            "proved_blockers": sorted(blockers),
        }
        return graph_text_hash(json.dumps(payload, sort_keys=True))

    def node_has_new_rejection_evidence(self, node_or_id: Any) -> bool:
        """Return whether a rejected graph node has evidence not seen at rejection."""

        node = (
            self.nodes.get(str(node_or_id or "").strip())
            if not isinstance(node_or_id, ProofGraphNode)
            else node_or_id
        )
        if node is None or node.status != "rejected":
            return False
        evidence_hash = self.evidence_hash_for_node(node.node_id)
        if not evidence_hash:
            return False
        metadata = dict(node.metadata or {})
        node_record = metadata.get("proof_state_node")
        old_hash = str(
            metadata.get("last_rejection_evidence_hash")
            or (
                node_record.get("rejection_evidence_hash")
                if isinstance(node_record, dict)
                else ""
            )
            or ""
        ).strip()
        return evidence_hash != old_hash

    def replan_queue_item_frontier_quarantined(self, node: Any) -> bool:
        """Return whether a replan item is unschedulable by quarantine policy."""

        if graph_node_frontier_quarantined(node):
            return True
        if getattr(node, "kind", "") != "replan_queue_item":
            return False
        obligation_id = self._replan_queue_item_obligation_id(node)
        obligation = self.nodes.get(obligation_id) if obligation_id else None
        return bool(
            obligation is not None
            and obligation.kind == "missing_obligation"
            and graph_node_frontier_quarantined(obligation)
        )

    def replan_queue_item_frontier_promoted_to_proof_state(self, node: Any) -> bool:
        """Return whether a replan item is delegated through a promoted obligation."""

        if graph_node_frontier_promoted_to_proof_state(node):
            return True
        if getattr(node, "kind", "") != "replan_queue_item":
            return False
        obligation_id = self._replan_queue_item_obligation_id(node)
        obligation = self.nodes.get(obligation_id) if obligation_id else None
        return bool(
            obligation is not None
            and obligation.kind == "missing_obligation"
            and graph_node_frontier_promoted_to_proof_state(obligation)
        )

    def _replan_queue_item_obligation_id(self, node: Any) -> str:
        if getattr(node, "kind", "") != "replan_queue_item":
            return ""
        metadata = dict(getattr(node, "metadata", {}) or {})
        obligation_id = str(metadata.get("obligation_id") or "").strip()
        if not obligation_id:
            obligation_id = str(
                metadata.get("resolved_by_obligation_id") or ""
            ).strip()
        if obligation_id:
            return obligation_id
        for edge in self.incoming(getattr(node, "node_id", ""), kind="obligation_replan"):
            return str(edge.source or "").strip()
        return ""

    def consumer_bindings_for_node(
        self,
        graph_node_id: str,
        record: Optional[Mapping[str, Any]] = None,
        *,
        route_ids: Sequence[str] = (),
        binding_graph_node_id: str = "",
    ) -> List[Dict[str, Any]]:
        """Return every cognitive consumer of one executable graph unit.

        Scheduler packets and fact-lifecycle reconciliation share this one
        ownership projection so a node consumed by several routes cannot be
        attributed only to the lineage written directly on the node.  A
        scheduler/control node may supply lineage for a distinct executable
        target through ``binding_graph_node_id``; the resulting bindings then
        authorize that target without discarding the source node's lineage.
        """

        graph_node = self.nodes.get(str(graph_node_id or "").strip())
        if graph_node is None:
            return []
        work_record = dict(record or {})
        node_metadata = dict(graph_node.metadata or {})
        try:
            node_lineage = ProofLineageEnvelope.from_metadata(node_metadata)
        except (TypeError, ValueError):
            node_lineage = ProofLineageEnvelope()
        candidate_route_ids = {
            str(item or "").strip()
            for item in route_ids
            if str(item or "").strip()
        }
        record_route_id = str(work_record.get("route_id") or "").strip()
        if record_route_id:
            candidate_route_ids.add(record_route_id)
        if node_lineage.route_id:
            candidate_route_ids.add(node_lineage.route_id)
        candidate_route_ids.update(
            str(edge.source or "").strip()
            for edge in self.incoming(graph_node.node_id)
            if edge.kind in _ROUTE_DEPENDENCY_EDGE_KINDS
            and self.nodes.get(edge.source) is not None
            and self.nodes[edge.source].kind == "strategy_route"
        )
        if not candidate_route_ids:
            candidate_route_ids.add("")

        bindings: List[Dict[str, Any]] = []
        for route_id in sorted(candidate_route_ids):
            route = self.nodes.get(route_id) if route_id else None
            route_metadata = dict(getattr(route, "metadata", {}) or {})
            try:
                route_lineage = ProofLineageEnvelope.from_metadata(route_metadata)
            except (TypeError, ValueError):
                route_lineage = ProofLineageEnvelope()
            route_owned_fields = {
                "proof_idea_id",
                "strategy_lineage_id",
                "parent_lineage_id",
            }
            lineage_values: Dict[str, str] = {}
            for field_name in ProofLineageEnvelope.__dataclass_fields__:
                node_value = str(getattr(node_lineage, field_name) or "")
                route_value = str(getattr(route_lineage, field_name) or "")
                if field_name in route_owned_fields:
                    lineage_values[field_name] = route_value or node_value
                elif (
                    field_name == "claim_id"
                    and node_value in self.nodes
                    and route_value
                ):
                    # Legacy graph producers wrote the executable occurrence
                    # ID (proposed claim / obligation node) into claim_id.  A
                    # registered route stores the conserved lifecycle claim;
                    # prefer it while retaining the occurrence independently
                    # in graph_node_ids.
                    lineage_values[field_name] = route_value
                else:
                    lineage_values[field_name] = node_value or route_value
            if route_id:
                lineage_values["route_id"] = route_id
            claim_id = str(work_record.get("claim_id") or "").strip()
            if claim_id and not lineage_values["claim_id"]:
                lineage_values["claim_id"] = claim_id
            elif (
                graph_node.kind == "proposed_claim"
                and not lineage_values["claim_id"]
            ):
                lineage_values["claim_id"] = graph_node.node_id
            if (
                not lineage_values["proof_candidate_id"]
                and graph_node.kind == "formal_variant"
            ):
                lineage_values["proof_candidate_id"] = graph_node.node_id
            assembly_id = str(work_record.get("assembly_id") or "").strip()
            if assembly_id:
                lineage_values["assembly_id"] = assembly_id
            if not lineage_values["statement_identity"]:
                lineage_values["statement_identity"] = (
                    graph_node_bound_contract_identity(graph_node)
                    or graph_statement_key(graph_node.statement)
                )
            envelope = ProofLineageEnvelope(**lineage_values)
            if not envelope.proof_idea_id:
                continue
            branch_id = str(
                # A shared executable node retains its creation branch, while
                # each consuming route owns the lifecycle branch of that
                # consumption. Prefer route ownership whenever a route exists;
                # node ownership remains the graph-only fallback.
                route_metadata.get("branch_id")
                or node_metadata.get("branch_id")
                or ""
            ).strip()
            reason_parts: List[str] = []
            for value in (
                node_metadata.get("reason")
                or work_record.get("obligation_reason"),
                route_metadata.get("reason")
                or route_metadata.get("strategy")
                or getattr(route, "statement", ""),
            ):
                clean_value = str(value or "").strip()
                if clean_value and clean_value not in reason_parts:
                    reason_parts.append(clean_value)
            bound_graph_node_id = str(binding_graph_node_id or "").strip()
            identity_payload = {
                "proof_lineage": envelope.to_record(),
                "branch_id": branch_id,
                "reason": "; route purpose: ".join(reason_parts),
                "graph_node_id": bound_graph_node_id or graph_node.node_id,
            }
            binding_id = hashlib.sha256(
                json.dumps(
                    identity_payload,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                ).encode("utf-8")
            ).hexdigest()
            bindings.append(
                {
                    "consumer_binding_id": "consumer-binding:" + binding_id,
                    **identity_payload,
                }
            )
        return bindings

    def work_frontier(
        self,
        *,
        max_items: int = 8,
        mutate: bool = True,
    ) -> List[Dict[str, Any]]:
        """Return graph-derived scheduler hints for proof-state work.

        Mutating dispatch applies stale-origin and lifecycle reconciliation
        before projection. Observational callers quote the current reconciled
        state directly and never clone or repair the graph. The graph may make
        work schedulable, but it does not certify proof closure: callers must
        map these records back through ``ProofSearchState`` and Lean/dossier
        verification before accepting anything as proved.
        """

        if mutate:
            self._repair_graph_native_metadata_edges()
            self._repair_revision_crossing_tombstones(cascade_all=True)
            self._repair_graph_native_source_tombstones()
            self.repair_terminal_blockers()
            self._repair_invalid_route_assemblies()
            self._ensure_route_assembly_contract_replans()
            self._ensure_orphaned_route_missing_assembly_bridge_rescues()
        items: List[Dict[str, Any]] = []
        seen: Set[Tuple[str, str, str]] = set()
        search_values: Dict[str, float] = {}
        route_materialization_node_ids: Dict[str, List[str]] = {}
        incoming_by_node: Dict[str, List[ProofGraphEdge]] = {}
        outgoing_by_node: Dict[str, List[ProofGraphEdge]] = {}
        for edge in self.edges:
            incoming_by_node.setdefault(edge.target, []).append(edge)
            outgoing_by_node.setdefault(edge.source, []).append(edge)

        def incoming_edges(node_id: str, kind: str = "") -> List[ProofGraphEdge]:
            edge_kind = str(kind or "")
            return [
                edge
                for edge in incoming_by_node.get(str(node_id or ""), [])
                if not edge_kind or edge.kind == edge_kind
            ]

        def outgoing_edges(node_id: str, kind: str = "") -> List[ProofGraphEdge]:
            edge_kind = str(kind or "")
            return [
                edge
                for edge in outgoing_by_node.get(str(node_id or ""), [])
                if not edge_kind or edge.kind == edge_kind
            ]

        def blocked_by_resolved_local(node_id: str) -> bool:
            blockers = outgoing_edges(node_id, "blocked_by")
            if not blockers:
                return False
            for edge in blockers:
                blocker_node = self.nodes.get(edge.target)
                if not self._proved_node_has_durable_certificate(blocker_node):
                    return False
            return True

        def state_node_id(graph_node: Optional[ProofGraphNode]) -> str:
            if graph_node is None:
                return ""
            metadata = dict(graph_node.metadata or {})
            explicit = str(metadata.get("proof_state_node_id") or "").strip()
            if explicit:
                return explicit
            name = str(graph_node.name or "").strip()
            if name:
                return name
            node_id = str(graph_node.node_id or "").strip()
            return node_id.removeprefix("proof_state:")

        def target_hash_for(graph_node: ProofGraphNode) -> str:
            metadata = dict(graph_node.metadata or {})
            node_record = metadata.get("proof_state_node")
            if isinstance(node_record, dict):
                goal = node_record.get("normalized_goal") or node_record.get("goal")
                if isinstance(goal, dict):
                    target_hash = str(goal.get("normalized_statement_hash") or "").strip()
                    if target_hash:
                        return target_hash
            return graph_text_hash(graph_node.statement)

        def rejected_has_new_evidence(graph_node: ProofGraphNode) -> bool:
            return self.node_has_new_rejection_evidence(graph_node)

        def dependencies_for(graph_node: ProofGraphNode) -> List[str]:
            metadata = dict(graph_node.metadata or {})
            node_record = metadata.get("proof_state_node")
            if isinstance(node_record, dict):
                deps = node_record.get("dependencies")
                if isinstance(deps, list):
                    return [str(item) for item in deps if str(item or "").strip()]
            return []

        def packet_digest(value: Any) -> str:
            encoded = json.dumps(
                value,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ).encode("utf-8")
            return hashlib.sha256(encoded).hexdigest()

        def attach_execution_packet(
            graph_node: ProofGraphNode,
            record: Dict[str, Any],
            *,
            route_ids: Sequence[str] = (),
        ) -> None:
            """Attach lossless execution identity and cognitive ownership."""

            exact_target = str(record.get("target_statement") or "")
            target_node = graph_node
            target_node_ids = [
                str(record.get(key) or "").strip()
                for key in ("obligation_id", "variant_id", "claim_id")
            ]
            if str(record.get("work_type") or "") == "assemble_route":
                target_node_ids.insert(0, self.root_node_id)
            for target_node_id in target_node_ids:
                candidate = self.nodes.get(target_node_id)
                if candidate is None:
                    continue
                if exact_target and str(candidate.statement or "").strip() != exact_target:
                    continue
                target_node = candidate
                break
            metadata = dict(target_node.metadata or {})
            execution_target_sha256 = hashlib.sha256(
                exact_target.encode("utf-8")
            ).hexdigest()
            environment_hash = str(
                metadata.get("statement_environment_hash") or ""
            ).strip()
            contract_identity = graph_node_bound_contract_identity(target_node)
            parsed_contract_identity = parse_lean_contract_identity(
                contract_identity
            )
            proposition_identity = (
                "lean-full-expr:" + parsed_contract_identity[0]
                if parsed_contract_identity is not None
                else contract_identity
            )
            materialization_seed = str(
                record.get("materialization_seed") or ""
            )
            materialization_seed_sha256 = hashlib.sha256(
                materialization_seed.encode("utf-8")
            ).hexdigest()
            raw_helper_receipts = (
                record.get("required_helper_source_hashes")
                or metadata.get("required_helper_source_hashes")
                or {}
            )
            helper_receipts = (
                dict(raw_helper_receipts)
                if isinstance(raw_helper_receipts, Mapping)
                else {}
            )
            helper_context_hash = str(
                record.get("helper_context_hash")
                or metadata.get("helper_context_hash")
                or ""
            )
            execution_identity = {
                "schema_version": 1,
                "target_identity": (
                    proposition_identity or execution_target_sha256
                ),
                "target_available": bool(exact_target),
                "materialization_seed_sha256": materialization_seed_sha256,
                "environment_hash": environment_hash,
                "helper_context_hash": helper_context_hash,
                "required_helper_source_hashes": {
                    str(key): str(value)
                    for key, value in sorted(helper_receipts.items())
                },
            }
            execution_scope_digest = packet_digest(execution_identity)
            record.update(
                {
                    "execution_scope_schema_version": 1,
                    "execution_scope_id": (
                        "execution-scope:" + execution_scope_digest
                    ),
                    "execution_scope_digest": execution_scope_digest,
                    "execution_target_sha256": execution_target_sha256,
                    "execution_target_available": bool(exact_target),
                    "execution_materialization_seed_sha256": (
                        materialization_seed_sha256
                    ),
                    "execution_target_graph_node_id": target_node.node_id,
                    "execution_environment_hash": environment_hash,
                    "execution_contract_identity": contract_identity,
                    "execution_proposition_identity": proposition_identity,
                    "execution_helper_context_hash": helper_context_hash,
                    "exact_target_statement": exact_target,
                    "execution_scope": {
                        "target_statement": exact_target,
                        "statement_identity": contract_identity,
                        "proposition_identity": proposition_identity,
                        "environment_hash": environment_hash,
                        "helper_context_hash": helper_context_hash,
                        "graph_revision": "",
                    },
                }
            )
            # A replan queue item supplies the selected lineage, while the
            # linked obligation is the executable target that lineage
            # authorizes.  Preserve both sides of that distinction.
            binding_graph_node_id = (
                target_node.node_id
                if str(record.get("work_type") or "") == "route_replan"
                else ""
            )
            bindings = self.consumer_bindings_for_node(
                graph_node.node_id,
                record,
                route_ids=route_ids,
                binding_graph_node_id=binding_graph_node_id,
            )
            if bindings:
                record["consumer_bindings"] = bindings
                record["primary_consumer_binding"] = next(
                    (
                        binding
                        for binding in bindings
                        if str(
                            binding.get("proof_lineage", {}).get("route_id") or ""
                        ).strip()
                        == str(record.get("route_id") or "").strip()
                    ),
                    bindings[0],
                )

        def finalize_packet(record: Dict[str, Any]) -> None:
            """Seal scope digests after semantic-consumer coalescing."""

            raw_bindings = [
                dict(item)
                for item in list(record.get("consumer_bindings") or [])
                if isinstance(item, Mapping)
            ]
            unique_bindings: Dict[str, Dict[str, Any]] = {}
            for binding in raw_bindings:
                binding_id = str(binding.get("consumer_binding_id") or "").strip()
                if not binding_id:
                    binding_id = "consumer-binding:" + packet_digest(binding)
                    binding["consumer_binding_id"] = binding_id
                unique_bindings[binding_id] = binding
            bindings = [unique_bindings[key] for key in sorted(unique_bindings)]
            if bindings:
                record["consumer_bindings"] = bindings
                primary = record.get("primary_consumer_binding")
                primary_id = (
                    str(primary.get("consumer_binding_id") or "").strip()
                    if isinstance(primary, Mapping)
                    else ""
                )
                primary = unique_bindings.get(primary_id) or bindings[0]
                record["primary_consumer_binding"] = primary
                try:
                    primary_lineage = ProofLineageEnvelope.from_metadata(primary)
                except (TypeError, ValueError):
                    primary_lineage = ProofLineageEnvelope()
                record.update(primary_lineage.merged_metadata(record))
            else:
                record.pop("consumer_bindings", None)
                record.pop("primary_consumer_binding", None)
            cognition_identity = {
                "schema_version": 1,
                "consumer_bindings": bindings,
                "primary_consumer_binding_id": str(
                    (
                        record.get("primary_consumer_binding") or {}
                    ).get("consumer_binding_id")
                    or ""
                ),
            }
            cognition_scope_digest = packet_digest(cognition_identity)
            record["cognition_scope_digest"] = cognition_scope_digest
            currentness = {
                "projection_turn_index": int(
                    record.get("projection_turn_index") or 0
                ),
                "evidence_hash": str(record.get("evidence_hash") or ""),
                "reopened_by_new_evidence": bool(
                    record.get("reopened_by_new_evidence")
                ),
            }
            record["execution_currentness_digest"] = packet_digest(
                {
                    "execution_scope_digest": str(
                        record.get("execution_scope_digest") or ""
                    ),
                    **currentness,
                }
            )
            record["cognition_currentness_digest"] = packet_digest(
                {
                    "cognition_scope_digest": cognition_scope_digest,
                    **currentness,
                }
            )

        def graph_work_payload(
            graph_node: ProofGraphNode,
            work_type: str = "",
        ) -> Dict[str, Any]:
            metadata = dict(graph_node.metadata or {})
            statement = str(graph_node.statement or "").strip()
            formalization_required = bool(metadata.get("formalization_required"))
            statement_executable = graph_statement_is_executable(statement)
            formalization_work = str(work_type or "").strip() in {
                "formalize_claim",
                "formalize_missing_obligation",
            }
            payload: Dict[str, Any] = {
                "obligation_reason": str(metadata.get("reason") or ""),
                "source_phase": str(graph_node.phase or metadata.get("phase") or ""),
                "missing_dependency": str(metadata.get("missing_dependency") or ""),
            }
            if (
                statement
                and (
                    statement_executable
                    or (
                        not formalization_work
                        and (
                            not formalization_required
                            or graph_node.kind != "missing_obligation"
                        )
                    )
                )
            ):
                payload["target_statement"] = statement
            elif statement and formalization_work and not statement_executable:
                payload["formalization_statement_pending"] = True
                payload["formalization_required"] = True
                payload["materialization_seed"] = statement
            elif formalization_required and graph_node.kind == "missing_obligation":
                payload["formalization_statement_pending"] = True
                if statement:
                    payload["materialization_seed"] = statement
            if metadata.get("target_integrity_adjudication"):
                payload["target_integrity_adjudication"] = True
            if metadata.get("allow_root_equivalent_target_integrity_adjudication"):
                payload["allow_root_equivalent_target_integrity_adjudication"] = True
            if formalization_required:
                payload["formalization_required"] = True
            if metadata.get("materialization_required"):
                payload["materialization_required"] = True
            for key in (
                "formalization_bridge_contract",
                "formalization_bridge_parent_statement",
                "formalization_obligation_key",
                "parent_repair_target_statement",
                "materialization_parent_statement",
                "bridge_relevance_required",
                "forbidden_materialization_fragments",
                "rejected_root_failure_analysis",
                "rejected_root_first_failure_analysis",
                "rejected_root_latest_failure_analysis",
                "rejected_root_failure_analyses",
                "rejected_root_error_type",
                "rejected_root_unknown_identifier",
                "rejected_root_unknown_identifiers",
                "rejected_root_missing_instance",
                "rejected_root_missing_instances",
                "decomposition_request_statement",
                "requires_strict_smaller_bridge",
                "forbid_repair_target_statement",
                "route_missing_assembly_bridge_rescue",
                "route_missing_assembly_bridge_signature_hash",
                "route_missing_assembly_bridge_rescue_generation",
                "retired_target_statement_hash",
                "formalization_bridge_support_recorded",
                "formalization_bridge_parent_assembly_required",
                "formalization_bridge_parent_work_missing",
            ):
                value = metadata.get(key)
                if value:
                    payload[key] = value
            if metadata.get("needs_replay_materialization"):
                payload["requires_replay_source"] = True
                payload["replay_materialization_reason"] = str(
                    metadata.get("replay_materialization_reason") or ""
                )
                payload["helper_name"] = str(
                    metadata.get("replay_materialization_helper_name") or ""
                )
                payload["helper_node_id"] = str(
                    metadata.get("replay_materialization_helper_node_id") or ""
                )
            return {key: value for key, value in payload.items() if value}

        def add(
            graph_node: ProofGraphNode,
            work_type: str,
            *,
            assembly_node: Optional[ProofGraphNode] = None,
            child_state_node_ids: Optional[List[str]] = None,
            unblocked_by_graph: bool = False,
            reopened_by_new_evidence: bool = False,
        ) -> None:
            sid = state_node_id(graph_node)
            wtype = str(work_type or "").strip()
            if not sid or not wtype:
                return
            assembly_id = ""
            if assembly_node is not None:
                assembly_metadata = dict(assembly_node.metadata or {})
                assembly_record = assembly_metadata.get("proof_state_assembly")
                if isinstance(assembly_record, dict):
                    assembly_id = str(
                        assembly_record.get("assembly_id") or assembly_node.name or ""
                    )
                else:
                    assembly_id = str(assembly_node.name or "")
            metadata = dict(graph_node.metadata or {})
            dedupe_sid = sid
            if wtype in {"formalize_claim", "formalize_missing_obligation"}:
                formalization_key = str(
                    metadata.get("formalization_obligation_key") or ""
                ).strip()
                if formalization_key:
                    dedupe_sid = f"formalization:{formalization_key}"
            key = (dedupe_sid, wtype, assembly_id if wtype == "assembly" else "")
            if key in seen:
                return
            seen.add(key)
            search_value = self._coerce_float(
                search_values.get(
                    graph_node.node_id,
                    metadata.get("search_value", 0.0),
                )
            )
            priority = self._coerce_float(metadata.get("priority", 0.0)) + search_value
            record: Dict[str, Any] = {
                "node_id": sid,
                "graph_node_id": graph_node.node_id,
                "work_type": wtype,
                "action": str(metadata.get("action") or ""),
                "priority": priority,
                "target_hash": target_hash_for(graph_node),
                "blocker": str(metadata.get("blocker") or ""),
                "dependencies": dependencies_for(graph_node),
                "node_kind": graph_node.kind,
                "node_status": graph_node.status,
                "projection_turn_index": int(graph_node.turn_index or 0),
                "search_value": search_value,
            }
            record.update(graph_work_payload(graph_node, wtype))
            if unblocked_by_graph:
                record["unblocked_by_graph"] = True
            evidence_hash = self.evidence_hash_for_node(graph_node.node_id)
            if evidence_hash:
                record["evidence_hash"] = evidence_hash
            if reopened_by_new_evidence:
                record["reopened_by_new_evidence"] = True
            if assembly_node is not None:
                assembly_metadata = dict(assembly_node.metadata or {})
                assembly_record = assembly_metadata.get("proof_state_assembly")
                if isinstance(assembly_record, dict):
                    record["assembly_id"] = assembly_id
                    proof_stub = str(assembly_record.get("proof_stub") or "")
                    if proof_stub:
                        record["proof_stub_hash"] = graph_text_hash(proof_stub)
                else:
                    record["assembly_id"] = assembly_id
                record["assembly_graph_node_id"] = assembly_node.node_id
                record["child_state_node_ids"] = list(child_state_node_ids or [])
            attach_execution_packet(graph_node, record)
            finalize_packet(record)
            items.append(record)

        def graph_native_ids(graph_node: ProofGraphNode) -> Dict[str, Any]:
            metadata = dict(graph_node.metadata or {})
            route_id = str(metadata.get("route_id") or "").strip()
            route_scope_blocked = False
            claim_id = str(metadata.get("claim_node_id") or "").strip()
            variant_id = ""
            obligation_id = ""
            replan_id = ""
            source_ids: List[str] = []
            source_route_ids: List[str] = []
            source_obligation_ids: List[str] = []
            if graph_node.kind in {"missing_obligation", "replan_queue_item"}:
                source_ids, source_route_ids, source_obligation_ids = (
                    self._graph_native_source_links(graph_node)
                )
                if not route_id and source_route_ids:
                    route_id = source_route_ids[0]
                elif route_id and route_id not in source_route_ids:
                    source_route_ids.insert(0, route_id)
                clean_route_id = next(
                    (
                        candidate
                        for candidate in source_route_ids
                        if self.nodes.get(candidate) is not None
                        and self.nodes[candidate].kind == "strategy_route"
                        and not self._route_has_superseded_dependency(
                            candidate,
                            ignore_node_id=graph_node.node_id,
                        )
                    ),
                    "",
                )
                if clean_route_id:
                    route_id = clean_route_id
                elif source_route_ids:
                    route_id = ""
                    route_scope_blocked = True
            if graph_node.kind == "strategy_route":
                route_id = graph_node.node_id
            elif graph_node.kind == "proposed_claim":
                claim_id = graph_node.node_id
            elif graph_node.kind == "formal_variant":
                variant_id = graph_node.node_id
            elif graph_node.kind == "missing_obligation":
                obligation_id = graph_node.node_id
            elif graph_node.kind == "replan_queue_item":
                replan_id = graph_node.node_id
                obligation_id = str(metadata.get("obligation_id") or "").strip()
                if not obligation_id:
                    obligation_id = str(
                        metadata.get("resolved_by_obligation_id") or ""
                    ).strip()
                if not obligation_id and source_obligation_ids:
                    obligation_id = source_obligation_ids[0]
            return {
                "route_id": route_id,
                "claim_id": claim_id,
                "variant_id": variant_id,
                "obligation_id": obligation_id,
                "replan_id": replan_id,
                "search_value": self._coerce_float(
                    search_values.get(
                        graph_node.node_id,
                        metadata.get("search_value", 0.0),
                    )
                ),
                "route_scope_blocked": route_scope_blocked,
            }

        def claim_has_active_formal_variant(claim_node: ProofGraphNode) -> bool:
            semantic_claim_ids = {claim_node.node_id}
            semantic_claim_key = graph_node_semantic_work_key(
                self,
                claim_node,
                allow_exact_surface_identity=True,
                normalize_schedulable_status=True,
            )
            if semantic_claim_key is not None:
                for peer in self.nodes_by_kind("proposed_claim"):
                    if peer.node_id == claim_node.node_id:
                        continue
                    peer_key = graph_node_semantic_work_key(
                        self,
                        peer,
                        allow_exact_surface_identity=True,
                        normalize_schedulable_status=True,
                    )
                    if peer_key == semantic_claim_key:
                        semantic_claim_ids.add(peer.node_id)
            candidate_ids: Set[str] = set()
            for semantic_claim_id in semantic_claim_ids:
                for edge in outgoing_edges(
                    semantic_claim_id,
                    "claim_formalized_as",
                ):
                    candidate_ids.add(str(edge.target or ""))
            for variant in self.nodes_by_kind("formal_variant"):
                metadata = dict(variant.metadata or {})
                if (
                    str(metadata.get("claim_node_id") or "").strip()
                    in semantic_claim_ids
                ):
                    candidate_ids.add(variant.node_id)
            for candidate_id in candidate_ids:
                variant = self.nodes.get(candidate_id)
                if variant is None or variant.kind != "formal_variant":
                    continue
                if self.is_superseded_tombstone(variant):
                    continue
                if variant.status in {"open", "blocked"} or rejected_has_new_evidence(
                    variant
                ):
                    return True
            return False

        def add_graph_native(graph_node: ProofGraphNode, work_type: str) -> None:
            wtype = str(work_type or "").strip()
            if not wtype:
                return
            metadata = dict(graph_node.metadata or {})
            native_ids = graph_native_ids(graph_node)
            route_backed_work = bool(native_ids.get("route_id")) and not bool(
                native_ids.get("route_scope_blocked")
            )
            root_suppression = graph_root_equivalent_suppression_decision(
                graph_node.statement,
                self.root_statement,
                active_target_statements=tuple(self.active_root_target_statements),
                route_backed_work=route_backed_work,
                allow_route_backed_work=graph_node.kind == "missing_obligation",
                reopened_after_superseded_spawn=bool(
                    metadata.get("spawned_claim_superseded_reopen_ids")
                ),
            )
            if (
                graph_node.kind
                in {"proposed_claim", "formal_variant", "missing_obligation"}
                and wtype
                in {
                    "formalize_claim",
                    "prove_claim_variant",
                    "mine_missing_obligation",
                    "formalize_missing_obligation",
                }
                and root_suppression.suppress
                and not bool(
                    metadata.get("allow_root_equivalent_target_integrity_adjudication")
                    and metadata.get("target_integrity_adjudication")
                )
            ):
                if mutate:
                    graph_node.metadata["root_equivalent_work_suppressed"] = True
                return
            value = self._coerce_float(
                search_values.get(
                    graph_node.node_id,
                    metadata.get("search_value", 0.0),
                )
            )
            priority = self._coerce_float(
                metadata.get("priority", metadata.get("score", 0.0))
            ) + value
            key = (graph_node.node_id, wtype, graph_text_hash(str(value)))
            if key in seen:
                return
            seen.add(key)
            reopened_by_new_evidence = rejected_has_new_evidence(graph_node)
            record: Dict[str, Any] = {
                "node_id": graph_node.node_id,
                "graph_node_id": graph_node.node_id,
                "work_type": wtype,
                "action": str(metadata.get("action") or wtype),
                "priority": priority,
                "target_hash": target_hash_for(graph_node),
                "blocker": str(metadata.get("blocker") or ""),
                "dependencies": dependencies_for(graph_node),
                "node_kind": graph_node.kind,
                "node_status": graph_node.status,
                "projection_turn_index": int(graph_node.turn_index or 0),
                "value_hash": graph_text_hash(str(value)),
            }
            record.update(graph_work_payload(graph_node, wtype))
            if (
                graph_node.kind == "replan_queue_item"
                and wtype == "route_replan"
                and not native_ids.get("obligation_id")
            ):
                return
            if native_ids.pop("route_scope_blocked", False):
                return
            if graph_node.kind == "replan_queue_item":
                obligation_id = str(native_ids.get("obligation_id") or "").strip()
                obligation = self.nodes.get(obligation_id) if obligation_id else None
                if obligation is not None and obligation.kind == "missing_obligation":
                    obligation_metadata = dict(obligation.metadata or {})
                    obligation_statement = str(obligation.statement or "").strip()
                    obligation_reason = str(
                        obligation_metadata.get("reason") or ""
                    ).strip()
                    if graph_node_frontier_quarantined(obligation):
                        return
                    if graph_node_frontier_promoted_to_proof_state(obligation):
                        return
                    if obligation_metadata.get(
                        "formalization_required"
                    ) or not graph_statement_is_executable(obligation_statement):
                        return
                    obligation_suppression = graph_root_equivalent_suppression_decision(
                        obligation_statement,
                        self.root_statement,
                        active_target_statements=tuple(
                            self.active_root_target_statements
                        ),
                        route_backed_work=route_backed_work,
                        allow_route_backed_work=True,
                    )
                    if obligation_suppression.suppress:
                        if bool(
                            obligation_metadata.get(
                                "allow_root_equivalent_target_integrity_adjudication"
                            )
                            and obligation_metadata.get("target_integrity_adjudication")
                        ):
                            pass
                        else:
                            if mutate:
                                graph_node.metadata[
                                    "root_equivalent_work_suppressed"
                                ] = True
                                obligation.metadata[
                                    "root_equivalent_work_suppressed"
                                ] = True
                            return
                    if obligation_statement:
                        record["target_statement"] = obligation_statement
                    if obligation_reason:
                        record["obligation_reason"] = obligation_reason
                    record.pop("formalization_required", None)
                    record.pop("route_replan_requires_obligation", None)
                else:
                    return
            record.update(native_ids)
            if wtype == "materialize_replay_source":
                helper = self._node_replay_materialization_helper(
                    graph_node,
                    mutate=mutate,
                )
                if helper is None:
                    return
                record["requires_replay_source"] = True
                record["helper_node_id"] = str(helper.node_id or "")
                record["helper_name"] = str(helper.name or "")
                record["replay_materialization_reason"] = str(
                    metadata.get("replay_materialization_reason")
                    or "graph_only_helper_certificate"
                )
            if graph_node.kind == "strategy_route" and wtype == "assemble_route":
                contract_status = self.route_assembly_contract_status(
                    graph_node.node_id,
                    mutate=mutate,
                )
                route_description = str(record.get("target_statement") or "").strip()
                if route_description:
                    record["route_description"] = route_description
                target_statement = str(
                    contract_status.get("target_statement")
                    or self.root_statement
                    or ""
                ).strip()
                if target_statement:
                    record["target_statement"] = target_statement
                    record["target_hash"] = graph_text_hash(target_statement)
                record["route_scope"] = str(
                    contract_status.get("route_scope") or ""
                )
                record["route_assembly_contract_verdict"] = str(
                    contract_status.get("verdict") or ""
                )
                record["route_assembly_authoring_ready"] = bool(
                    contract_status.get("authoring_ready")
                    or contract_status.get("ready")
                )
                record["route_assembly_deterministic_ready"] = bool(
                    contract_status.get("deterministic_ready")
                )
                replay_materialization_node_ids = [
                    str(node_id or "").strip()
                    for node_id in route_materialization_node_ids.get(
                        graph_node.node_id,
                        list(
                            (graph_node.metadata or {}).get(
                                "route_no_replayable_helper_dependency_node_ids"
                            )
                            or []
                        ),
                    )
                    if str(node_id or "").strip()
                ]
                if replay_materialization_node_ids:
                    record["route_dependency_needs_replay_materialization"] = True
                    record[
                        "route_no_replayable_helper_dependency_node_ids"
                    ] = replay_materialization_node_ids
                    record[
                        "route_assembly_requires_authoring_due_to_graph_only_helpers"
                    ] = True
                record["route_assembly_required_node_ids"] = list(
                    contract_status.get("required_node_ids") or []
                )
                record["route_assembly_bridge_node_ids"] = list(
                    contract_status.get("assembly_bridge_node_ids") or []
                )
                record["route_branch_frame_ids"] = list(
                    contract_status.get("selected_branch_frame_ids")
                    or contract_status.get("branch_frame_ids")
                    or []
                )
            evidence_hash = self.evidence_hash_for_node(graph_node.node_id)
            if evidence_hash:
                record["evidence_hash"] = evidence_hash
            if reopened_by_new_evidence:
                record["reopened_by_new_evidence"] = True
            if graph_node.kind in {
                "missing_obligation",
                "formal_variant",
                "proposed_claim",
                "proof_state_root",
                "proof_state_child_goal",
            }:
                semantic_key = graph_node_semantic_work_key(
                    self,
                    graph_node,
                    allow_exact_surface_identity=True,
                    normalize_schedulable_status=True,
                )
                if semantic_key is not None:
                    record["_semantic_work_owner_key"] = (wtype, semantic_key)
                    semantic_route_ids = sorted(
                        {
                            edge.source
                            for edge in incoming_edges(graph_node.node_id)
                            if edge.kind in _ROUTE_DEPENDENCY_EDGE_KINDS
                            and self.nodes.get(edge.source) is not None
                            and self.nodes[edge.source].kind == "strategy_route"
                        }
                    )
                    record["_semantic_consumer_route_ids"] = semantic_route_ids
                else:
                    semantic_route_ids = []
            else:
                semantic_route_ids = []
            attach_execution_packet(
                graph_node,
                record,
                route_ids=semantic_route_ids,
            )
            items.append(record)

        def retrieval_attempted(graph_node: ProofGraphNode) -> bool:
            if outgoing_edges(graph_node.node_id, "retrieved_declaration"):
                return True
            if outgoing_edges(graph_node.node_id, "retrieved_fact"):
                return True
            metadata = dict(graph_node.metadata or {})
            node_record = metadata.get("proof_state_node")
            return bool(
                isinstance(node_record, dict)
                and node_record.get("retrieval_attempted")
            )

        def retrieved_decl_names(graph_node: ProofGraphNode) -> List[str]:
            names: List[str] = []
            for edge in outgoing_edges(graph_node.node_id, "retrieved_declaration"):
                retrieval_node = self.nodes.get(edge.target)
                if retrieval_node is None:
                    continue
                metadata = dict(retrieval_node.metadata or {})
                name = str(
                    metadata.get("decl_name")
                    or retrieval_node.name
                    or retrieval_node.statement
                    or ""
                ).strip()
                if name:
                    names.append(name)
            metadata = dict(graph_node.metadata or {})
            node_record = metadata.get("proof_state_node")
            if isinstance(node_record, dict):
                for name in list(node_record.get("retrieved_decl_names") or []):
                    clean = str(name or "").strip()
                    if clean:
                        names.append(clean)
            return list(dict.fromkeys(names))

        def route_ready_for_assembly(graph_node: ProofGraphNode) -> bool:
            if graph_node.kind != "strategy_route":
                return False
            metadata = dict(graph_node.metadata or {})
            frontier_metadata = (
                graph_node.metadata if mutate else dict(graph_node.metadata or {})
            )
            if metadata.get("assembled_route_proof_hash"):
                return False
            contract_status = self.route_assembly_contract_status(
                graph_node.node_id,
                mutate=mutate,
            )
            frontier_metadata["route_assembly_contract_last_verdict"] = str(
                contract_status.get("verdict") or ""
            )
            for key in (
                "missing_node_ids",
                "unproved_node_ids",
                "uncontracted_dependency_node_ids",
                "missing_dependency_edge_node_ids",
                "missing_helper_names",
            ):
                metadata_key = f"route_assembly_contract_{key}"
                values = list(contract_status.get(key) or [])
                if values:
                    frontier_metadata[metadata_key] = values
                else:
                    frontier_metadata.pop(metadata_key, None)
            if not bool(contract_status.get("ready")):
                return False
            # ``ready`` only means the unproved set is empty. When it is only
            # true because a branch-local reducer was admitted with its
            # premises still open, the route has no satisfied bridge and must
            # not be assembled -- the contract already names that state,
            # route_assembly_contract_authoring_ready_missing_bridge. Routes
            # with no branch-local candidates at all are certified directly and
            # are unaffected.
            if list(contract_status.get("branch_local_candidate_node_ids") or []) and not (
                list(contract_status.get("assembly_bridge_node_ids") or [])
                or list(contract_status.get("selected_branch_frame_ids") or [])
            ):
                return False
            route_edges = [
                edge
                for edge in outgoing_edges(graph_node.node_id)
                if edge.kind in _ROUTE_DEPENDENCY_EDGE_KINDS
            ]
            if not route_edges:
                return False
            current_route_signature_hash = self.route_dependency_signature_hash(
                graph_node.node_id
            )
            materialization_nodes = self._route_replay_materialization_nodes(
                graph_node.node_id,
                mutate=mutate,
            )
            route_materialization_node_ids[graph_node.node_id] = [
                node.node_id for node in materialization_nodes
            ]
            if materialization_nodes:
                frontier_metadata[
                    "route_no_replayable_helper_signature_hash"
                ] = current_route_signature_hash
                frontier_metadata[
                    "route_no_replayable_helper_dependency_node_ids"
                ] = [node.node_id for node in materialization_nodes]
                frontier_metadata[
                    "route_assembly_requires_authoring_due_to_graph_only_helpers"
                ] = True
                return False
            else:
                frontier_metadata.pop(
                    "route_no_replayable_helper_signature_hash",
                    None,
                )
                frontier_metadata.pop(
                    "route_no_replayable_helper_dependency_node_ids",
                    None,
                )
                frontier_metadata.pop(
                    "route_assembly_requires_authoring_due_to_graph_only_helpers",
                    None,
                )
            contract_metadata = dict(contract_status.get("contract_metadata") or {})
            replayable_bridge_available = bool(
                contract_status.get("deterministic_ready")
                or contract_status.get("assembly_bridge_node_ids")
                or contract_status.get("selected_branch_frame_ids")
                or (
                    contract_metadata.get("source") == "formalization_bridge_support"
                    and contract_metadata.get("bridge_helper_node_id")
                )
            )
            if (
                contract_metadata.get("source") == "active_root_exact_helper"
                and not replayable_bridge_available
            ):
                frontier_metadata[
                    "route_assembly_missing_replayable_bridge_signature_hash"
                ] = current_route_signature_hash
                frontier_metadata[
                    "route_assembly_missing_replayable_bridge_verdict"
                ] = str(contract_status.get("verdict") or "")
                return False
            frontier_metadata.pop(
                "route_assembly_missing_replayable_bridge_signature_hash",
                None,
            )
            frontier_metadata.pop(
                "route_assembly_missing_replayable_bridge_verdict",
                None,
            )
            missing_bridge_hash = str(
                metadata.get("route_missing_assembly_bridge_signature_hash") or ""
            ).strip()
            if missing_bridge_hash:
                if current_route_signature_hash == missing_bridge_hash:
                    return False
                frontier_metadata.pop(
                    "route_missing_assembly_bridge_signature_hash",
                    None,
                )
            tactic_failure_rescue_hash = str(
                metadata.get("route_root_tactic_failure_rescue_signature_hash") or ""
            ).strip()
            if tactic_failure_rescue_hash:
                if current_route_signature_hash == tactic_failure_rescue_hash:
                    return False
                frontier_metadata.pop(
                    "route_root_tactic_failure_rescue_signature_hash",
                    None,
                )
            author_failed_hash = str(
                metadata.get("route_root_assembly_author_failed_signature_hash") or ""
            ).strip()
            if author_failed_hash:
                if current_route_signature_hash == author_failed_hash:
                    return False
                frontier_metadata.pop(
                    "route_root_assembly_author_failed_hash",
                    None,
                )
                frontier_metadata.pop(
                    "route_root_assembly_author_failed_signature_hash",
                    None,
                )
                frontier_metadata.pop(
                    "route_root_tactic_authoring_ready_hash",
                    None,
                )
                frontier_metadata.pop(
                    "route_root_tactic_authoring_ready_signature_hash",
                    None,
                )
            author_ready_hash = str(
                metadata.get("route_root_tactic_authoring_ready_signature_hash") or ""
            ).strip()
            if author_ready_hash and current_route_signature_hash != author_ready_hash:
                frontier_metadata.pop(
                    "route_root_tactic_authoring_ready_hash",
                    None,
                )
                frontier_metadata.pop(
                    "route_root_tactic_authoring_ready_signature_hash",
                    None,
                )
            failed_hash = str(
                metadata.get("route_root_tactic_failed_signature_hash") or ""
            ).strip()
            if failed_hash:
                if current_route_signature_hash == failed_hash:
                    return False
                frontier_metadata.pop("route_root_tactic_failed_hash", None)
                frontier_metadata.pop("route_root_tactic_failed_signature_hash", None)
                frontier_metadata.pop("route_root_tactic_deferred_hash", None)
                frontier_metadata.pop("route_root_tactic_continued_hash", None)
                frontier_metadata.pop("route_root_tactic_continuation_hash", None)
                frontier_metadata.pop("route_root_tactic_suppressed_proofs", None)
                frontier_metadata.pop(
                    "route_root_tactic_suppressed_proof_records",
                    None,
                )
                frontier_metadata.pop("route_root_tactic_suppressed_count", None)
                frontier_metadata.pop("route_root_tactic_last_attempt_count", None)
                frontier_metadata.pop("route_root_tactic_last_candidate_count", None)
                frontier_metadata.pop("route_root_tactic_timeout_continuation_hash", None)
            return True

        search_values = self.propagate_values(mutate=mutate)

        # Assembly is the only graph-native readiness rule in this first
        # causal scheduling pass: an explicit assembly artifact with all of
        # its required proof-state children proved is executable.
        for assembly_node in self.nodes_by_kind("proof_state_assembly"):
            if assembly_node.status != "open":
                continue
            assembly_metadata = dict(assembly_node.metadata or {})
            assembly_record = assembly_metadata.get("proof_state_assembly")
            if isinstance(assembly_record, dict):
                if str(assembly_record.get("status") or "open") != "open":
                    continue
                if int(assembly_record.get("attempt_count") or 0) > 0:
                    continue
            parents = incoming_edges(assembly_node.node_id, "proof_state_assembly")
            if not parents:
                continue
            parent_node = self.nodes.get(parents[0].source)
            parent_unblocked = (
                parent_node is not None
                and parent_node.status == "blocked"
                and blocked_by_resolved_local(parent_node.node_id)
            )
            parent_retry = (
                parent_node is not None and rejected_has_new_evidence(parent_node)
            )
            if parent_node is None or (
                parent_node.status != "open" and not parent_unblocked and not parent_retry
            ):
                continue
            child_edges = [
                edge
                for edge in outgoing_edges(assembly_node.node_id)
                if edge.kind == "assembly_requires"
                or edge.kind.startswith("assembly_requires_slot:")
            ]
            child_ids: List[str] = []
            all_children_proved = bool(child_edges)
            for edge in child_edges:
                child_node = self.nodes.get(edge.target)
                if not self._proved_node_has_durable_certificate(child_node):
                    all_children_proved = False
                    break
                child_ids.append(state_node_id(child_node))
            if all_children_proved:
                add(
                    parent_node,
                    "assembly",
                    assembly_node=assembly_node,
                    child_state_node_ids=list(dict.fromkeys(child_ids)),
                    unblocked_by_graph=parent_unblocked,
                    reopened_by_new_evidence=parent_retry,
                )

        for graph_node in self.nodes.values():
            if self.is_superseded_tombstone(graph_node):
                continue
            if self._node_route_is_terminally_poisoned(graph_node):
                continue
            unblocked = (
                graph_node.status == "blocked"
                and blocked_by_resolved_local(graph_node.node_id)
            )
            retry_rejected = rejected_has_new_evidence(graph_node)
            if graph_node.status != "open" and not unblocked and not retry_rejected:
                continue
            if graph_node.kind in {"proposed_claim", "formal_variant"} and (
                graph_node_frontier_quarantined(graph_node)
                or bool((graph_node.metadata or {}).get("graph_statement_non_theorem"))
            ):
                continue
            if graph_node.kind == "proposed_claim":
                if not claim_has_active_formal_variant(graph_node):
                    add_graph_native(graph_node, "formalize_claim")
            elif graph_node.kind == "formal_variant":
                add_graph_native(graph_node, "prove_claim_variant")
            elif graph_node.kind == "missing_obligation":
                metadata = dict(graph_node.metadata or {})
                if not self._route_missing_assembly_bridge_rescue_current(
                    graph_node,
                    mutate=mutate,
                ):
                    continue
                if graph_node_frontier_quarantined(graph_node):
                    continue
                if graph_node_frontier_promoted_to_proof_state(graph_node):
                    continue
                if (
                    metadata.get("formalization_bridge_support_recorded")
                    and metadata.get("formalization_bridge_parent_assembly_required")
                    and metadata.get("formalization_bridge_parent_work_materialized")
                    and (
                        metadata.get("formalization_bridge_parent_work_type")
                        == "assemble_route"
                    )
                ):
                    continue
                statement = str(graph_node.statement or "").strip()
                statement_executable = graph_statement_is_executable(statement)
                if (
                    metadata.get("target_integrity_adjudication")
                    and statement_executable
                ):
                    add_graph_native(graph_node, "target_integrity_adjudication")
                elif metadata.get("formalization_required"):
                    if statement_executable:
                        add_graph_native(graph_node, "formalize_claim")
                    else:
                        add_graph_native(
                            graph_node,
                            "formalize_missing_obligation",
                        )
                else:
                    add_graph_native(graph_node, "mine_missing_obligation")
            elif graph_node.kind == "replan_queue_item":
                if not self._route_missing_assembly_bridge_rescue_current(
                    graph_node,
                    mutate=mutate,
                ):
                    continue
                if self.replan_queue_item_frontier_quarantined(graph_node):
                    continue
                if self.replan_queue_item_frontier_promoted_to_proof_state(graph_node):
                    continue
                add_graph_native(graph_node, "route_replan")
            elif graph_node.kind == "strategy_route":
                if route_ready_for_assembly(graph_node):
                    add_graph_native(graph_node, "assemble_route")
                    for node_id in route_materialization_node_ids.get(
                        graph_node.node_id,
                        list(
                            (graph_node.metadata or {}).get(
                                "route_no_replayable_helper_dependency_node_ids"
                            )
                            or []
                        ),
                    ):
                        materialization_node = self.nodes.get(
                            str(node_id or "").strip()
                        )
                        if materialization_node is None:
                            continue
                        add_graph_native(
                            materialization_node,
                            "materialize_replay_source",
                        )
                else:
                    materialization_required = False
                    for node_id in route_materialization_node_ids.get(
                        graph_node.node_id,
                        list(
                            (graph_node.metadata or {}).get(
                                "route_no_replayable_helper_dependency_node_ids"
                            )
                            or []
                        ),
                    ):
                        materialization_node = self.nodes.get(
                            str(node_id or "").strip()
                        )
                        if materialization_node is None:
                            continue
                        materialization_required = True
                        add_graph_native(
                            materialization_node,
                            "materialize_replay_source",
                        )
                    if (
                        materialization_required
                    ):
                        add_graph_native(graph_node, "assemble_route")
            elif graph_node.kind == "proof_state_decomposition_task":
                add(
                    graph_node,
                    "lemma_dag_decomposition",
                    unblocked_by_graph=unblocked,
                    reopened_by_new_evidence=retry_rejected,
                )
            elif graph_node.kind == "proof_state_child_goal":
                if not retrieval_attempted(graph_node):
                    add(
                        graph_node,
                        "retrieval",
                        unblocked_by_graph=unblocked,
                        reopened_by_new_evidence=retry_rejected,
                    )
                if retrieved_decl_names(graph_node):
                    add(
                        graph_node,
                        "decl_probe",
                        unblocked_by_graph=unblocked,
                        reopened_by_new_evidence=retry_rejected,
                    )
                add(
                    graph_node,
                    "tactic_swarm",
                    unblocked_by_graph=unblocked,
                    reopened_by_new_evidence=retry_rejected,
                )
                # B8 fix (2026-05-11): emit ``child_llm_prove`` from the
                # graph-source path. Previously only the legacy local
                # frontier in proof_state.work_frontier could surface
                # this work_type, so the recursive helper prover starved
                # whenever the graph view took precedence over local
                # (B6 territory — graph blocked/rejected/failed with a
                # later sync-pending local-open transition). The
                # consumer in proof_state.work_frontier applies the
                # attempt + giveup caps so a turn-budget-exhausted
                # node won't dispatch.
                add(
                    graph_node,
                    "child_llm_prove",
                    unblocked_by_graph=unblocked,
                    reopened_by_new_evidence=retry_rejected,
                )
            elif graph_node.kind == "proof_state_root":
                add(
                    graph_node,
                    "root_repair",
                    unblocked_by_graph=unblocked,
                    reopened_by_new_evidence=retry_rejected,
                )

        def work_order(item: Mapping[str, Any]) -> int:
            work_type = str(item.get("work_type") or "")
            if (
                work_type == "formalize_missing_obligation"
                and bool(item.get("formalization_statement_pending"))
                and not str(item.get("target_statement") or "").strip()
            ):
                return 6
            return {
                "materialize_replay_source": -1,
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
                "root_repair": 6,
            }.get(work_type, 4)

        items.sort(
            key=lambda item: (
                work_order(item),
                -float(item.get("priority") or 0.0),
                str(item.get("node_id") or ""),
                str(item.get("work_type") or ""),
            )
        )
        # Multiple lifecycle nodes may consume the same exact formal work.
        # Keep those aliases and route edges in the graph, but dispatch only
        # the highest-priority scheduler owner and expose all consumers on it.
        coalesced_items: List[Dict[str, Any]] = []
        semantic_owners: Dict[Tuple[Any, ...], Dict[str, Any]] = {}
        for item in items:
            semantic_key = item.pop("_semantic_work_owner_key", None)
            item_consumer_route_ids = [
                str(route_id or "").strip()
                for route_id in list(
                    item.pop("_semantic_consumer_route_ids", []) or []
                )
                if str(route_id or "").strip()
            ]
            if semantic_key is None:
                coalesced_items.append(item)
                continue
            graph_node_id = str(item.get("graph_node_id") or "").strip()
            route_id = str(item.get("route_id") or "").strip()
            if route_id:
                item_consumer_route_ids.append(route_id)
            owner = semantic_owners.get(semantic_key)
            if owner is None:
                item["semantic_equivalent_graph_node_ids"] = (
                    [graph_node_id] if graph_node_id else []
                )
                item["semantic_consumer_route_ids"] = sorted(
                    set(item_consumer_route_ids)
                )
                semantic_owners[semantic_key] = item
                coalesced_items.append(item)
                continue
            equivalent_ids = list(
                owner.get("semantic_equivalent_graph_node_ids") or []
            )
            if graph_node_id:
                equivalent_ids.append(graph_node_id)
            owner["semantic_equivalent_graph_node_ids"] = sorted(
                set(equivalent_ids)
            )
            route_ids = list(owner.get("semantic_consumer_route_ids") or [])
            route_ids.extend(item_consumer_route_ids)
            owner["semantic_consumer_route_ids"] = sorted(set(route_ids))
            owner_bindings = list(owner.get("consumer_bindings") or [])
            owner_bindings.extend(list(item.get("consumer_bindings") or []))
            owner["consumer_bindings"] = owner_bindings
        for item in coalesced_items:
            finalize_packet(item)
        return coalesced_items[: max(0, int(max_items or 0))]

    def prune_proof_state_projection(self) -> None:
        """Remove the ephemeral proof-state scheduler projection from the graph.

        Verified helpers, root proof status, scratch checks, and declaration
        applications are durable graph facts.  The proof-state scheduler nodes
        are a refreshed projection of the current search frontier, so stale
        state nodes/edges should not survive a later sync.
        """

        # Any projection prune invalidates the associated in-memory scheduler
        # snapshot as well.  ``ProofSearchState.sync_to_graph`` writes a new
        # one after rebuilding the projection.
        if hasattr(self, "_proof_state_execution_record"):
            delattr(self, "_proof_state_execution_record")
        if hasattr(self, "_proof_state_execution_snapshot_fingerprint"):
            delattr(self, "_proof_state_execution_snapshot_fingerprint")
        if hasattr(self, "_proof_state_falsification_authorities"):
            delattr(self, "_proof_state_falsification_authorities")

        removed_node_ids = {
            node_id
            for node_id, node in self.nodes.items()
            if str(node_id or "").startswith("proof_state")
            or str(node.kind or "").startswith("proof_state")
        }
        if not removed_node_ids:
            return
        for node_id in removed_node_ids:
            self.nodes.pop(node_id, None)
        self.edges = [
            edge
            for edge in self.edges
            if edge.source not in removed_node_ids and edge.target not in removed_node_ids
        ]
        self._rebuild_edge_index()

    def ensure_state_node(
        self,
        node_id: str,
        *,
        kind: str,
        name: str,
        statement: str = "",
        status: str = "open",
        phase: str = "",
        turn_index: int = 0,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphNode:
        """Create or refresh a non-helper controller/search-state node."""

        graph_node_id = str(node_id or "").strip()
        if not graph_node_id:
            raise ValueError("state node requires a non-empty node_id")
        node_kind = str(kind or "state").strip() or "state"
        node_name = str(name or graph_node_id).strip() or graph_node_id
        node = self.nodes.get(graph_node_id)
        if node is None:
            node = ProofGraphNode(
                node_id=graph_node_id,
                kind=node_kind,
                name=node_name,
                statement=str(statement or "").strip(),
                status=str(status or "open"),
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                metadata=dict(metadata or {}),
            )
            self.nodes[graph_node_id] = node
        else:
            node.kind = node_kind
            node.name = node_name
            if statement:
                node.statement = str(statement or "").strip()
            node.status = str(status or node.status or "open")
            if phase:
                node.phase = str(phase or "")
            if turn_index:
                node.turn_index = int(turn_index or 0)
            if metadata is not None:
                node.metadata = dict(metadata or {})
        return node

    def remove_helper(self, name: str) -> None:
        helper_name = str(name or "").strip()
        node_id = self.helper_name_to_node_id.pop(helper_name, None)
        if node_id is None:
            return
        self.nodes.pop(node_id, None)
        self.edges = [
            edge
            for edge in self.edges
            if edge.source != node_id and edge.target != node_id
        ]
        self._rebuild_edge_index()
        removed_attempt_ids = {
            attempt.attempt_id for attempt in self.attempts if attempt.node_id == node_id
        }
        if removed_attempt_ids:
            self.attempts = [
                attempt for attempt in self.attempts if attempt.node_id != node_id
            ]
            self._rebuild_attempt_index()
            for node in self.nodes.values():
                node.attempt_ids = [
                    attempt_id
                    for attempt_id in node.attempt_ids
                    if attempt_id not in removed_attempt_ids
                ]
        for node in self.nodes.values():
            if helper_name in node.support_names:
                node.support_names = [
                    support for support in node.support_names if support != helper_name
                ]
            metadata = dict(node.metadata or {})
            if metadata.get("verified_by_helper_node_id") == node_id or metadata.get(
                "verified_by_helper_name"
            ) == helper_name or metadata.get(
                "resolved_by_helper_node_id"
            ) == node_id or metadata.get(
                "resolved_by_helper_name"
            ) == helper_name:
                if self._graph_native_certifying_kind(node) or node.kind in {
                    "proof_state_root",
                    "proof_state_child_goal",
                }:
                    self._reopen_uncertified_graph_native_node(
                        node,
                        reason="proved_graph_native_helper_removed",
                    )
        self._repair_uncertified_graph_native_proved_nodes()

    def mark_node_proved(
        self,
        node_id: str,
        *,
        source_hash: str = "",
        proof_hash: str = "",
        support_names: Optional[Iterable[str]] = None,
    ) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        self._repair_revision_crossing_tombstones()
        self._repair_graph_native_source_tombstones()
        if self.is_superseded_tombstone(node):
            self._enforce_superseded_tombstone(node)
            return
        if self._reject_graph_native_node_from_superseded_source(node):
            return
        if (
            self._graph_native_certifying_kind(node)
            and not proof_hash
            and not node.proof_hash
            and not self._proved_node_has_durable_certificate(node)
        ):
            node.status = "open"
            node.metadata["uncertified_proved_status_ignored"] = True
            return
        if node.kind == "missing_obligation":
            helper_node_id = str(
                (node.metadata or {}).get("verified_by_helper_node_id") or ""
            ).strip()
            helper = self.nodes.get(helper_node_id)
            if helper is None:
                for edge in self.outgoing(node.node_id, kind="obligation_verified_by"):
                    candidate = self.nodes.get(edge.target)
                    if candidate is not None and candidate.kind == "helper":
                        helper = candidate
                        break
            if (
                helper is None
                or not self._helper_certifies_node(helper, node)
            ):
                node.status = "open"
                node.metadata["uncertified_obligation_proved_ignored"] = True
                return
        node.status = "proved"
        if source_hash:
            node.source_hash = source_hash
        if proof_hash:
            node.proof_hash = proof_hash
        if support_names is not None:
            self._set_supports(node, support_names, replace=True)
        if node.kind == "proposed_claim":
            helper_node_id = str(
                (node.metadata or {}).get("verified_by_helper_node_id") or ""
            ).strip()
            helper = self.nodes.get(helper_node_id)
            self._supersede_unmatched_child_variants_for_claim(
                claim_node_id=node.node_id,
                active_statement=node.statement,
                helper_node_id=helper_node_id,
                helper_name=helper.name if helper is not None else "",
            )

    def mark_node_failed(self, node_id: str, *, status: str = "failed") -> None:
        node = self.nodes.get(node_id)
        if node is None or node.status == "proved":
            return
        node.status = str(status or "failed")
        if node.kind == "missing_obligation":
            self._close_replans_for_obligation_terminal_status(node)

    def _value_propagation_signature(self, iterations: int) -> Tuple[Any, ...]:
        def metadata_value_signature(metadata: Dict[str, Any], key: str) -> Tuple[bool, str]:
            return key in metadata, repr(metadata.get(key))

        node_items = tuple(
            sorted(
                (
                    node.node_id,
                    node.kind,
                    node.status,
                    node.proof_hash,
                    "1" if self.is_superseded_tombstone(node) else "0",
                    metadata_value_signature(node.metadata or {}, "score"),
                    metadata_value_signature(node.metadata or {}, "base_score"),
                    metadata_value_signature(node.metadata or {}, "priority"),
                )
                for node in self.nodes.values()
            )
        )
        edge_items = tuple(
            sorted((edge.source, edge.target, edge.kind) for edge in self.edges)
        )
        return (int(iterations or 0), node_items, edge_items)

    def _store_search_values(self, values: Dict[str, float]) -> None:
        for node_id, value in values.items():
            node = self.nodes.get(node_id)
            if node is not None:
                node.metadata["search_value"] = self._bounded_search_value(value)

    def propagate_values(
        self,
        *,
        iterations: int = 3,
        mutate: bool = True,
    ) -> Dict[str, float]:
        """Propagate coarse search value from variants/obligations to routes.

        This value is scheduler guidance only. It never certifies proof truth;
        Lean-checked attempts still control ``proved`` status.
        """

        requested_iterations = max(1, int(iterations or 1))
        max_iterations = max(
            requested_iterations,
            min(64, max(1, len(self.nodes) + len(self.edges))),
        )
        signature = self._value_propagation_signature(max_iterations)
        if (
            self._value_propagation_cache_signature == signature
            and self._value_propagation_cache_values
        ):
            if mutate:
                self._store_search_values(self._value_propagation_cache_values)
            return dict(self._value_propagation_cache_values)

        values: Dict[str, float] = {}
        for node in self.nodes.values():
            metadata = dict(node.metadata or {})
            if self.is_superseded_tombstone(node):
                base = -1.0
            elif node.status == "proved":
                base = 1.0
            elif node.status in {"failed", "rejected"}:
                base = -0.5
            elif node.status == "blocked":
                base = -0.2
            else:
                base = self._coerce_float(
                    metadata.get("score", metadata.get("base_score", 0.1))
                )
            if node.kind == "missing_obligation" and node.status != "proved":
                base = min(base, -0.1)
            values[node.node_id] = self._bounded_search_value(base)

        route_edge_kinds = {"route_requires", "route_blocked_by", "route_replan"}
        outgoing_by_node: Dict[str, List[ProofGraphEdge]] = {}
        for edge in self.edges:
            outgoing_by_node.setdefault(edge.source, []).append(edge)
        for _ in range(max_iterations):
            next_values = dict(values)
            for node in self.nodes.values():
                outgoing = outgoing_by_node.get(node.node_id, [])
                if node.kind == "proposed_claim":
                    child_values = [
                        values.get(edge.target, 0.0)
                        for edge in outgoing
                        if edge.kind == "claim_formalized_as"
                    ]
                    if child_values:
                        next_values[node.node_id] = self._bounded_search_value(
                            max(child_values)
                        )
                elif node.kind == "missing_obligation":
                    replan_values = [
                        values.get(edge.target, 0.0)
                        for edge in outgoing
                        if edge.kind == "obligation_replan"
                    ]
                    if replan_values:
                        base = values.get(node.node_id, 0.0)
                        next_values[node.node_id] = self._bounded_search_value(
                            max(base, max(replan_values))
                        )
                elif node.kind == "replan_queue_item":
                    spawned_values = [
                        values.get(edge.target, 0.0)
                        for edge in outgoing
                        if edge.kind in {"replan_spawned_claim", "blocked_by"}
                    ]
                    if spawned_values:
                        base = values.get(node.node_id, 0.0)
                        next_values[node.node_id] = self._bounded_search_value(
                            max(base, max(spawned_values))
                        )
                elif node.kind == "strategy_route":
                    required_values = [
                        values.get(edge.target, 0.0)
                        for edge in outgoing
                        if edge.kind in route_edge_kinds
                    ]
                    if required_values:
                        base = self._coerce_float(node.metadata.get("base_score", 0.0))
                        next_values[node.node_id] = self._bounded_search_value(
                            base + sum(required_values) / max(1, len(required_values))
                        )
            if all(
                abs(next_values.get(node_id, 0.0) - values.get(node_id, 0.0)) < 1e-9
                for node_id in set(values) | set(next_values)
            ):
                values = next_values
                break
            values = next_values

        values = {
            node_id: self._bounded_search_value(value)
            for node_id, value in values.items()
            if node_id in self.nodes
        }
        if mutate:
            self._store_search_values(values)
            self._value_propagation_cache_signature = signature
            self._value_propagation_cache_values = dict(values)
        return dict(values)

    def record_attempt(
        self,
        node_id: str,
        *,
        phase: str,
        turn_index: int,
        proof: str = "",
        helper_names: Iterable[str] = (),
        verdict: str,
        error_type: str = "",
        source: str = "",
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProofGraphAttempt:
        if node_id not in self.nodes:
            raise ValueError(f"unknown proof graph node id: {node_id}")
        attempt_id = self._allocate_attempt_id()
        proof_hash = graph_text_hash(proof) if proof else ""
        node = self.nodes[node_id]
        attempt_metadata = dict(metadata or {})
        try:
            node_lineage = ProofLineageEnvelope.from_metadata(node.metadata)
        except (TypeError, ValueError):
            node_lineage = ProofLineageEnvelope()
        try:
            attempt_lineage = ProofLineageEnvelope.from_metadata(
                attempt_metadata
            )
        except (TypeError, ValueError):
            attempt_lineage = ProofLineageEnvelope()
        from ensemble_prover.proof_lineage import (
            lean_residual_identity,
            proof_candidate_identity,
        )

        canonical_candidate_id = (
            proof_candidate_identity(
                target_id=node_id,
                proof_hash=proof_hash,
            )
            if proof_hash
            else ""
        )
        failure_signature = str(
            attempt_metadata.get("lean_failure_signature")
            or attempt_metadata.get("failure_signature")
            or ""
        ).strip()
        success_verdict = str(verdict or "").strip().lower() in {
            "accepted",
            "solved",
            "proved",
            "helper_accepted",
            "scratch_ok",
            "tactic_solved",
        }
        canonical_residual_id = (
            ""
            if success_verdict
            else lean_residual_identity(
                proof_candidate_id=canonical_candidate_id,
                error_type=str(error_type or ""),
                failure_signature=failure_signature,
                proof_attempt_id=attempt_id,
                target_id=node_id,
            )
        )
        predecessor_residual_id = (
            attempt_lineage.lean_residual_id
            if success_verdict and attempt_lineage.repair_ticket_id
            else ""
        )
        lineage = node_lineage.updated(
            **{
                field_name: getattr(attempt_lineage, field_name)
                for field_name in attempt_lineage.__dataclass_fields__
                if field_name not in {"proof_candidate_id", "lean_residual_id"}
                if getattr(attempt_lineage, field_name)
            },
            proof_candidate_id=canonical_candidate_id,
            lean_residual_id=(
                canonical_residual_id
                or predecessor_residual_id
                or (
                    attempt_lineage.lean_residual_id
                    or node_lineage.lean_residual_id
                    if not success_verdict
                    else ""
                )
            ),
        )
        attempt_metadata = lineage.merged_metadata(attempt_metadata)
        attempt_metadata["proof_attempt_id"] = attempt_id
        attempt = ProofGraphAttempt(
            attempt_id=attempt_id,
            node_id=node_id,
            phase=str(phase or ""),
            turn_index=int(turn_index or 0),
            verdict=str(verdict or ""),
            proof_hash=proof_hash,
            error_type=str(error_type or ""),
            helper_names=[
                str(name or "").strip()
                for name in helper_names
                if str(name or "").strip()
            ],
            source=str(source or ""),
            metadata=attempt_metadata,
        )
        self.attempts.append(attempt)
        self._attempt_ids.add(attempt.attempt_id)
        self.nodes[node_id].attempt_ids.append(attempt.attempt_id)
        self._update_status_from_verdict(
            node_id,
            attempt.verdict,
            proof_hash=attempt.proof_hash,
            helper_names=attempt.helper_names,
            error_type=attempt.error_type,
        )
        if (
            node_id == self.root_node_id
            and self.nodes.get(node_id)
            and self.nodes[node_id].status == "proved"
        ):
            for name in attempt.helper_names:
                helper_id = self.helper_name_to_node_id.get(str(name or "").strip())
                if helper_id is not None:
                    self._add_edge(helper_id, self.root_node_id, "supports_root")
        self._compact_attempt_history()
        return attempt

    def _update_status_from_verdict(
        self,
        node_id: str,
        verdict: str,
        *,
        proof_hash: str = "",
        helper_names: Iterable[str] = (),
        error_type: str = "",
    ) -> None:
        node = self.nodes.get(node_id)
        if node is None:
            return
        self._repair_revision_crossing_tombstones()
        self._repair_graph_native_source_tombstones()
        if self.is_superseded_tombstone(node):
            self._enforce_superseded_tombstone(node)
            return
        if self._reject_graph_native_node_from_superseded_source(node):
            return
        if node.status == "proved":
            if proof_hash and not node.proof_hash:
                node.proof_hash = proof_hash
            return
        v = str(verdict or "").lower()
        proved_verdicts = {"solved", "proved", "helper_accepted", "scratch_ok"}
        root_proved_verdicts = {"solved", "proved", "tactic_solved"}
        failed_verdicts = {
            "claim_exhausted",
            "claim_llm_failed",
            "frontier_work_no_progress",
            "graph_work_exception",
            "plan_call_failed",
            "plan_parse_failed",
            "parallel_sample_all_failed",
        }
        blocked_verdicts = {"claim_dependency_blocked"}
        rejected_verdicts = {
            "lean_rejected",
            "tactic_rejected",
            "variant_falsified_by_sample",
            "variant_type_rejected",
            "proof_policy_rejected",
            "scratch_rejected",
            "no_proof_extracted",
            "lean_infra_error",
            "llm_call_failed",
            "claim_invalidated_by_child",
            "claim_skipped_previous_child_invalidation",
            "claim_skipped_repaired_previous_child_invalidation",
            "proposed_helper_skipped_child_invalidated",
            "variant_skipped_context_free_raw",
        }
        is_proof_state_projection = (
            str(node.kind or "").startswith("proof_state_")
            and str(node.kind or "") not in {
                "proof_state_transition",
                "proof_state_attempt",
                "proof_state_retrieval",
                "proof_state_assembly",
            }
        )
        if is_proof_state_projection and v in (
            failed_verdicts | blocked_verdicts | rejected_verdicts
        ):
            # Projection nodes mirror ProofSearchState; scheduler attempts are
            # evidence attached to that mirror, not an authoritative state
            # transition.  Letting a no-progress/rejection verdict close the
            # projection creates a feedback loop: graph failure is hydrated
            # into local state, which then deletes the structured frontier.
            # Explicit graph status edits can still be ingested by
            # ProofSearchState.refresh_graph_readiness, and sync_to_graph
            # remains the owner of normal projection status.
            node.metadata["last_projection_attempt_verdict"] = v
            node.metadata["projection_attempt_status_ignored_count"] = int(
                node.metadata.get("projection_attempt_status_ignored_count", 0)
                or 0
            ) + 1
            return
        if node.kind == "root" and v in root_proved_verdicts and not proof_hash:
            node.status = "open"
        elif (
            self._graph_native_certifying_kind(node)
            and v in proved_verdicts
            and not proof_hash
            and not self._proved_node_has_durable_certificate(node)
        ):
            node.status = "open"
            node.metadata["uncertified_proved_verdict_ignored"] = v
        elif node.kind == "missing_obligation" and v in proved_verdicts:
            node.status = "open"
            node.metadata["uncertified_obligation_attempt_ignored"] = v
        elif v in (root_proved_verdicts if node.kind == "root" else proved_verdicts):
            node.status = "proved"
            if proof_hash:
                node.proof_hash = proof_hash
            if node.kind == "proposed_claim":
                self._supersede_unmatched_child_variants_for_claim(
                    claim_node_id=node.node_id,
                    active_statement=node.statement,
                )
        elif node.kind == "root":
            node.status = "open"
        elif (
            node.kind == "missing_obligation"
            and v in rejected_verdicts
            and str(error_type or "") == "graph_native_helper_record_failed"
        ):
            node.status = "open"
            node.metadata["uncertified_obligation_rejection_ignored"] = error_type
        elif v in blocked_verdicts:
            node.status = "blocked"
        elif v in failed_verdicts:
            node.status = "failed"
        elif v in rejected_verdicts:
            node.status = "rejected"
            node.metadata["last_rejection_evidence_hash"] = self.evidence_hash_for_node(
                node.node_id
            )
        if node.kind == "missing_obligation":
            self._close_replans_for_obligation_terminal_status(node)

    def record_scratch(
        self,
        *,
        turn_index: int,
        tool_call_index: int,
        ok: bool,
        summary: str,
        code: str,
        label: str = "try_lean",
    ) -> ProofGraphNode:
        code_hash = graph_text_hash(code)
        node_id = f"scratch:{int(turn_index or 0)}:{int(tool_call_index or 0)}:{code_hash}"
        node = self.nodes.get(node_id)
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="scratch",
                name=f"{label}:{int(turn_index or 0)}:{int(tool_call_index or 0)}",
                statement=str(summary or "")[:500],
                status="proved" if ok else "rejected",
                phase="try_lean",
                turn_index=int(turn_index or 0),
                proof_hash=code_hash,
                metadata={"tool_call_index": int(tool_call_index or 0)},
            )
            self.nodes[node_id] = node
        else:
            node.statement = str(summary or "")[:500]
            node.status = "proved" if ok else "rejected"
            node.proof_hash = code_hash
            node.metadata["tool_call_index"] = int(tool_call_index or 0)
        self._add_edge(self.root_node_id, node_id, "scratch_check")
        self.record_attempt(
            node_id,
            phase="try_lean",
            turn_index=turn_index,
            proof=code,
            verdict="scratch_ok" if ok else "scratch_rejected",
            error_type="" if ok else "scratch_rejected",
            metadata={"summary": str(summary or "")[:500]},
        )
        self.prune_scratch_nodes()
        return node

    def prune_scratch_nodes(
        self,
        *,
        max_nodes: int = _MAX_PROOF_GRAPH_SCRATCH_NODES,
    ) -> int:
        """Bound diagnostic scratch nodes and their graph-local WAL records."""

        limit = max(0, int(max_nodes or 0))
        scratch_ids = [
            node.node_id for node in self.nodes.values() if node.kind == "scratch"
        ]
        remove_ids = set(scratch_ids[: max(0, len(scratch_ids) - limit)])
        if not remove_ids:
            return 0
        for node_id in remove_ids:
            self.nodes.pop(node_id, None)
        self.edges = [
            edge
            for edge in self.edges
            if edge.source not in remove_ids and edge.target not in remove_ids
        ]
        self.attempts = [
            attempt for attempt in self.attempts if attempt.node_id not in remove_ids
        ]
        self._rebuild_attempt_index()
        self._rebuild_edge_index()
        self._value_propagation_cache_signature = ()
        self._value_propagation_cache_values = {}
        return len(remove_ids)

    def record_decl_application(
        self,
        *,
        turn_index: int,
        tool_call_index: int,
        statement: str,
        decl_name: str,
        applicable: bool,
        proof_stub: str = "",
        remaining_goals: Iterable[Any] = (),
        error_kind: str = "",
        error_text: str = "",
        decl_type: str = "",
    ) -> ProofGraphNode:
        raw_target_statement = str(statement or "").strip()
        raw_name = str(decl_name or "").strip() or "<unknown>"
        target_statement = _graph_prompt_safe_decl_application_preview(
            raw_target_statement,
            limit=1000,
        )
        name = (
            _graph_prompt_safe_decl_application_preview(raw_name, limit=160)
            or "<unknown>"
        )
        goals = [str(goal or "") for goal in (remaining_goals or [])]
        proof_stub_text = str(proof_stub or "").strip()
        safe_proof_stub = (
            "" if _helper_source_mentions_solution(proof_stub_text) else proof_stub_text
        )
        closed = bool(applicable) and bool(safe_proof_stub) and not goals
        node_hash = graph_text_hash(f"{name}\n{target_statement}")
        node_id = (
            f"decl_app:{int(turn_index or 0)}:"
            f"{int(tool_call_index or 0)}:{node_hash}"
        )
        node = self.nodes.get(node_id)
        metadata = {
            "decl_name": name,
            "applicable": bool(applicable),
            "closed": closed,
            "proof_stub": safe_proof_stub[:500],
            "remaining_goal_count": len(goals),
            "remaining_goals": [
                _graph_prompt_safe_decl_application_preview(goal, limit=500)
                for goal in goals[:5]
            ],
            "error_kind": str(error_kind or ""),
            "error_preview": _graph_prompt_safe_decl_application_preview(
                error_text,
                limit=500,
            ),
            "decl_type": _graph_prompt_safe_decl_application_preview(
                decl_type,
                limit=500,
            ),
            "tool_call_index": int(tool_call_index or 0),
        }
        status = "proved" if closed else ("open" if applicable else "rejected")
        if node is None:
            node = ProofGraphNode(
                node_id=node_id,
                kind="decl_application",
                name=name,
                statement=target_statement[:1000],
                status=status,
                phase="apply_decl_to_goal",
                turn_index=int(turn_index or 0),
                proof_hash=graph_text_hash(safe_proof_stub) if safe_proof_stub else "",
                metadata=metadata,
            )
            self.nodes[node_id] = node
        else:
            node.name = name
            node.statement = target_statement[:1000]
            node.status = status
            node.proof_hash = graph_text_hash(safe_proof_stub) if safe_proof_stub else ""
            node.metadata.update(metadata)
        self._add_edge(self.root_node_id, node_id, "decl_application")
        helper_id = self.helper_name_to_node_id.get(name)
        if helper_id is not None:
            self._add_edge(helper_id, node_id, "supports")
        verdict = (
            "decl_app_closed"
            if closed
            else ("decl_app_partial" if applicable else "decl_app_rejected")
        )
        self.record_attempt(
            node_id,
            phase="apply_decl_to_goal",
            turn_index=turn_index,
            proof=safe_proof_stub,
            helper_names=[name] if helper_id is not None else [],
            verdict=verdict,
            error_type=str(error_kind or ""),
            metadata={
                "tool_call_index": int(tool_call_index or 0),
                "remaining_goal_count": len(goals),
            },
        )
        return node

    def mark_root_solved(
        self,
        *,
        proof: str,
        replay_helper_names: Iterable[str] = (),
        support_helper_names: Optional[Iterable[str]] = None,
    ) -> None:
        root = self.ensure_root(self.root_statement)
        root.status = "proved"
        root.proof_hash = graph_text_hash(proof)
        root.metadata["final_proof"] = str(proof or "")
        root.metadata["proof_state_root_status"] = "proved"
        replay_names = [
            str(name or "").strip()
            for name in replay_helper_names
            if str(name or "").strip()
        ]
        root.metadata["final_replay_helper_names"] = [
            name for name in replay_names if name
        ]
        support_names = (
            [
                str(name or "").strip()
                for name in list(support_helper_names or ())
                if str(name or "").strip()
            ]
            if support_helper_names is not None
            else replay_names
        )
        root.metadata["final_support_helper_names"] = [
            name for name in support_names if name
        ]
        self.edges = [
            edge
            for edge in self.edges
            if not (edge.kind == "supports_root" and edge.target == self.root_node_id)
        ]
        self._rebuild_edge_index()
        for name in support_names:
            helper_id = self.helper_name_to_node_id.get(str(name or "").strip())
            if helper_id is not None:
                self._add_edge(helper_id, self.root_node_id, "supports_root")

    def mark_strategy_route_solved_by_kernel(
        self,
        route_id: str,
        *,
        proof: str,
        dependency_node_ids: Iterable[str] = (),
        turn_index: int = 0,
    ) -> bool:
        """Close one exact route from an already kernel-accepted root proof.

        The caller owns kernel verification.  This method records that
        certificate on only the named strategy route and is idempotent for the
        same proof.  Dependency IDs are provenance; when omitted they are
        derived from the route's current dependency edges.
        """

        clean_route_id = str(route_id or "").strip()
        proof_text = str(proof or "").strip()
        route = self.nodes.get(clean_route_id)
        if route is None or route.kind != "strategy_route" or not proof_text:
            return False
        proof_hash = graph_text_hash(proof_text)
        supplied_dependencies = [
            str(node_id or "").strip()
            for node_id in dependency_node_ids
            if str(node_id or "").strip()
        ]
        dependencies = supplied_dependencies or [
            edge.target for edge in self._route_dependency_edges(clean_route_id)
        ]
        dependencies = sorted(dict.fromkeys(dependencies))
        if any(node_id not in self.nodes for node_id in dependencies):
            return False
        route.status = "proved"
        route.proof_hash = proof_hash
        route.turn_index = max(int(route.turn_index or 0), int(turn_index or 0))
        route.metadata["kernel_finalized_root_proof_hash"] = proof_hash
        route.metadata["assembled_route_proof_hash"] = proof_hash
        route.metadata["assembled_dependency_node_ids"] = dependencies
        route.metadata["assembled_dependency_signature_hash"] = (
            self.route_dependency_signature_hash(clean_route_id)
        )
        route.metadata["assembled_by_action"] = "root_finalization"
        route.metadata["route_assembly_contract_last_verdict"] = (
            "kernel_verified_root_finalization"
        )
        route.metadata.pop("activation_status", None)
        return True

    def clear_root_solved(self) -> None:
        root = self.ensure_root(self.root_statement)
        root.status = "open"
        root.proof_hash = ""
        root.metadata.pop("final_proof", None)
        root.metadata["proof_state_root_status"] = "open"
        root.metadata.pop("final_replay_helper_names", None)
        root.metadata.pop("final_support_helper_names", None)
        root.metadata.pop("root_finalization_route_id", None)
        root.metadata.pop("root_finalization_dependency_node_ids", None)
        root.metadata.pop("root_finalization_helper_names", None)
        root.metadata.pop("root_finalization_dependency_helper_names", None)
        root.metadata.pop("root_finalization_require_route_contract", None)
        root.metadata.pop("root_finalization_contract_status", None)
        root.metadata.pop("root_finalization_verification_status", None)
        root.metadata.pop("root_finalization_verification_certificate", None)
        self.edges = [edge for edge in self.edges if edge.kind != "supports_root"]
        self._rebuild_edge_index()

    def merge_verified_helpers_from(self, other: "ProofGraph") -> None:
        for name, node_id in getattr(other, "helper_name_to_node_id", {}).items():
            node = other.nodes.get(node_id)
            if (
                node is None
                or node.status != "proved"
                or not other._helper_has_replayable_source(node)
            ):
                continue
            existing_id = self.helper_name_to_node_id.get(name)
            if existing_id is not None:
                existing = self.nodes.get(existing_id)
                if existing is not None and self._helper_has_replayable_source(existing):
                    continue
                existing_key = graph_statement_key(
                    getattr(existing, "statement", "") if existing is not None else ""
                )
                incoming_key = graph_statement_key(node.statement)
                if existing_key and incoming_key and existing_key != incoming_key:
                    continue
            copied = self.ensure_helper(
                name,
                statement=node.statement,
                phase=node.phase,
                turn_index=node.turn_index,
                # E4 fix (2026-05-08): use deep copy so nested dicts/lists
                # in metadata are NOT shared between source and merged
                # graphs. Without this, a parallel sample's post-merge
                # mutation would leak across to other samples sharing the
                # base graph (latent under current code paths but a
                # fragile invariant — explicit copy is the structural
                # fix).
                support_names=list(node.support_names),
                metadata=copy.deepcopy(node.metadata),
            )
            copied.status = "proved"
            copied.source_hash = node.source_hash
            copied.proof_hash = node.proof_hash

    def summary(self) -> Dict[str, int]:
        self.propagate_values()
        self.refresh_route_branch_frames()
        nodes = list(self.nodes.values())
        branch_frames = list(self.branch_frames.values())
        proof_state_artifact_kinds = {
            "proof_state_transition",
            "proof_state_retrieval",
            "proof_state_assembly",
            "proof_state_attempt",
        }
        proof_state_search_nodes = [
            n
            for n in nodes
            if n.kind.startswith("proof_state")
            and n.kind not in proof_state_artifact_kinds
        ]
        open_obligation_nodes = [
            n for n in nodes if n.kind == "missing_obligation" and n.status == "open"
        ]
        open_replan_queue_nodes = [
            n for n in nodes if n.kind == "replan_queue_item" and n.status == "open"
        ]
        open_quarantined_obligation_nodes = [
            n for n in open_obligation_nodes if graph_node_frontier_quarantined(n)
        ]
        open_promoted_obligation_nodes = [
            n
            for n in open_obligation_nodes
            if graph_node_frontier_promoted_to_proof_state(n)
        ]
        open_quarantined_replan_queue_nodes = [
            n
            for n in open_replan_queue_nodes
            if self.replan_queue_item_frontier_quarantined(n)
        ]
        open_promoted_replan_queue_nodes = [
            n
            for n in open_replan_queue_nodes
            if self.replan_queue_item_frontier_promoted_to_proof_state(n)
        ]
        open_attackable_obligation_nodes = [
            n
            for n in open_obligation_nodes
            if n not in open_quarantined_obligation_nodes
            and n not in open_promoted_obligation_nodes
        ]
        open_attackable_replan_queue_nodes = [
            n
            for n in open_replan_queue_nodes
            if n not in open_quarantined_replan_queue_nodes
            and n not in open_promoted_replan_queue_nodes
        ]
        return {
            "nodes": len(nodes),
            "edges": len(self.edges),
            "attempts": len(self.attempts),
            "helper_nodes": sum(1 for n in nodes if n.kind == "helper"),
            "proved_helpers": sum(
                1 for n in nodes if n.kind == "helper" and n.status == "proved"
            ),
            "open_helpers": sum(
                1 for n in nodes if n.kind == "helper" and n.status == "open"
            ),
            "failed_helpers": sum(
                1
                for n in nodes
                if n.kind == "helper" and n.status in {"failed", "rejected", "blocked"}
            ),
            "blocked_helpers": sum(
                1 for n in nodes if n.kind == "helper" and n.status == "blocked"
            ),
            "claim_nodes": sum(1 for n in nodes if n.kind == "proposed_claim"),
            "open_claim_nodes": sum(
                1 for n in nodes if n.kind == "proposed_claim" and n.status == "open"
            ),
            "proved_claim_nodes": sum(
                1
                for n in nodes
                if n.kind == "proposed_claim" and n.status == "proved"
            ),
            "rejected_claim_nodes": sum(
                1
                for n in nodes
                if n.kind == "proposed_claim" and n.status == "rejected"
            ),
            "variant_nodes": sum(1 for n in nodes if n.kind == "formal_variant"),
            "open_variant_nodes": sum(
                1 for n in nodes if n.kind == "formal_variant" and n.status == "open"
            ),
            "proved_variant_nodes": sum(
                1
                for n in nodes
                if n.kind == "formal_variant" and n.status == "proved"
            ),
            "rejected_variant_nodes": sum(
                1
                for n in nodes
                if n.kind == "formal_variant" and n.status == "rejected"
            ),
            "non_theorem_statement_nodes": sum(
                1
                for n in nodes
                if (n.metadata or {}).get("graph_statement_non_theorem") is True
            ),
            "route_nodes": sum(1 for n in nodes if n.kind == "strategy_route"),
            "open_route_nodes": sum(
                1 for n in nodes if n.kind == "strategy_route" and n.status == "open"
            ),
            "obligation_nodes": sum(1 for n in nodes if n.kind == "missing_obligation"),
            "open_obligation_nodes": len(open_obligation_nodes),
            "open_attackable_obligation_nodes": len(open_attackable_obligation_nodes),
            "open_quarantined_obligation_nodes": len(
                open_quarantined_obligation_nodes
            ),
            "open_promoted_obligation_nodes": len(open_promoted_obligation_nodes),
            "replan_queue_nodes": sum(
                1 for n in nodes if n.kind == "replan_queue_item"
            ),
            "open_replan_queue_nodes": len(open_replan_queue_nodes),
            "open_attackable_replan_queue_nodes": len(
                open_attackable_replan_queue_nodes
            ),
            "open_quarantined_replan_queue_nodes": len(
                open_quarantined_replan_queue_nodes
            ),
            "open_promoted_replan_queue_nodes": len(
                open_promoted_replan_queue_nodes
            ),
            "proof_state_nodes": len(proof_state_search_nodes),
            "open_proof_state_nodes": sum(
                1
                for n in proof_state_search_nodes
                if n.status == "open"
            ),
            "proved_proof_state_nodes": sum(
                1
                for n in proof_state_search_nodes
                if n.status == "proved"
            ),
            "proof_state_artifact_nodes": sum(
                1 for n in nodes if n.kind in proof_state_artifact_kinds
            ),
            "proof_state_transition_nodes": sum(
                1 for n in nodes if n.kind == "proof_state_transition"
            ),
            "proof_state_retrieval_nodes": sum(
                1 for n in nodes if n.kind == "proof_state_retrieval"
            ),
            "proof_state_assembly_nodes": sum(
                1 for n in nodes if n.kind == "proof_state_assembly"
            ),
            "proof_state_attempt_nodes": sum(
                1 for n in nodes if n.kind == "proof_state_attempt"
            ),
            "branch_frames": len(branch_frames),
            "open_branch_frames": sum(
                1 for frame in branch_frames if frame.status == "open"
            ),
            "proved_branch_frames": sum(
                1 for frame in branch_frames if frame.status == "proved"
            ),
            "scratch_nodes": sum(1 for n in nodes if n.kind == "scratch"),
            "decl_application_nodes": sum(
                1 for n in nodes if n.kind == "decl_application"
            ),
            "closed_decl_applications": sum(
                1
                for n in nodes
                if n.kind == "decl_application" and n.status == "proved"
            ),
            "partial_decl_applications": sum(
                1
                for n in nodes
                if n.kind == "decl_application" and n.status == "open"
            ),
            "rejected_decl_applications": sum(
                1
                for n in nodes
                if n.kind == "decl_application" and n.status == "rejected"
            ),
            "root_proved": 1
            if self.nodes.get(self.root_node_id)
            and self.nodes[self.root_node_id].status == "proved"
            else 0,
        }

    def _reconcile_recorded_bridge_parent_work_on_rehydrate(self) -> None:
        """Revalidate persisted bridge projections under current identity rules.

        Older checkpoints may already contain globally projected helper
        premises and therefore never call ``record_obligation_bridge_support``
        again after resume.  Replay the pure graph materializer from the
        authoritative stored support receipt so safety migrations can retire
        those stale nodes before the frontier is exposed.
        """

        def fail_closed(obligation: ProofGraphNode, reason: str) -> None:
            if obligation.status in {"proved", "obsolete"}:
                return
            metadata = obligation.metadata
            metadata["formalization_bridge_parent_work_materialized"] = False
            metadata["formalization_bridge_parent_work_missing"] = True
            metadata["formalization_required"] = True
            metadata["formalization_bridge_rehydrate_rejected"] = str(reason)

        for obligation in list(self.nodes.values()):
            metadata = (
                obligation.metadata
                if isinstance(obligation.metadata, dict)
                else {}
            )
            if (
                obligation.kind != "missing_obligation"
                or not metadata.get("formalization_bridge_support_recorded")
            ):
                continue
            supports = [
                dict(item)
                for item in list(
                    metadata.get("formalization_bridge_supports") or []
                )
                if isinstance(item, dict)
            ]
            live_parent_values = [
                str(metadata.get(key) or "").strip()
                for key in (
                    "formalization_bridge_parent_statement",
                    "parent_repair_target_statement",
                )
                if str(metadata.get(key) or "").strip()
            ]
            if not live_parent_values and graph_statement_is_executable(
                obligation.statement
            ):
                live_parent_values.append(str(obligation.statement or "").strip())
            live_parent_keys = {
                graph_statement_key(value) or graph_text_hash(value)
                for value in live_parent_values
                if value
            }
            if len(live_parent_keys) != 1:
                fail_closed(obligation, "parent_identity_missing_or_split")
                continue
            live_parent_key = next(iter(live_parent_keys))
            valid_supports: List[Dict[str, Any]] = []
            rejection_reasons: List[str] = []
            for candidate in supports:
                candidate_helper = self.nodes.get(
                    str(candidate.get("helper_node_id") or "").strip()
                )
                if (
                    candidate_helper is None
                    or candidate_helper.kind != "helper"
                    or candidate_helper.status != "proved"
                ):
                    rejection_reasons.append("helper_missing_or_unproved")
                    continue
                candidate_parent = str(
                    candidate.get("parent_statement") or ""
                ).strip()
                candidate_parent_key = (
                    graph_statement_key(candidate_parent)
                    or graph_text_hash(candidate_parent)
                )
                if candidate_parent_key != live_parent_key:
                    rejection_reasons.append("parent_identity_stale")
                    continue
                support_statement = str(
                    candidate.get("statement") or ""
                ).strip()
                helper_statement = str(candidate_helper.statement or "").strip()
                if (
                    graph_statement_key(support_statement)
                    or graph_text_hash(support_statement)
                ) != (
                    graph_statement_key(helper_statement)
                    or graph_text_hash(helper_statement)
                ):
                    rejection_reasons.append("helper_statement_stale")
                    continue
                support_source_hash = str(
                    candidate.get("source_hash") or ""
                ).strip()
                live_source_hashes = {
                    str(value or "").strip()
                    for value in (
                        candidate_helper.source_hash,
                        candidate_helper.proof_hash,
                    )
                    if str(value or "").strip()
                }
                if (
                    not support_source_hash
                    or not live_source_hashes
                    or support_source_hash not in live_source_hashes
                ):
                    rejection_reasons.append("helper_source_stale")
                    continue
                valid_supports.append(candidate)
            if not valid_supports:
                metadata["formalization_bridge_rehydrate_support_rejections"] = (
                    sorted(set(rejection_reasons))
                )
                fail_closed(obligation, "no_live_bound_support")
                continue
            # Exclude stale receipts from the materializer's helper/premise
            # closure. They remain summarized in rejection telemetry but may
            # not contribute proof authority after rehydration.
            metadata["formalization_bridge_supports"] = valid_supports
            if rejection_reasons:
                metadata["formalization_bridge_rehydrate_support_rejections"] = (
                    sorted(set(rejection_reasons))
                )
            helper = None
            support: Dict[str, Any] = {}
            for candidate in reversed(valid_supports):
                candidate_helper = self.nodes.get(
                    str(candidate.get("helper_node_id") or "").strip()
                )
                if (
                    candidate_helper is not None
                    and candidate_helper.kind == "helper"
                    and candidate_helper.status == "proved"
                ):
                    helper = candidate_helper
                    support = candidate
                    break
            if helper is None:
                metadata["formalization_bridge_rehydrate_support_missing"] = True
                fail_closed(obligation, "helper_missing_or_unproved")
                continue
            materialized = self._materialize_bridge_parent_work(
                obligation=obligation,
                helper=helper,
                parent_statement=str(
                    support.get("parent_statement")
                    or metadata.get("formalization_bridge_parent_statement")
                    or ""
                ),
                phase=str(support.get("phase") or "checkpoint_rehydrate"),
                turn_index=int(support.get("turn_index") or 0),
            )
            if materialized:
                metadata["formalization_bridge_parent_work_materialized"] = True
                metadata.pop("formalization_bridge_parent_work_missing", None)
                metadata["formalization_required"] = False
            else:
                fail_closed(obligation, "parent_work_revalidation_failed")
                if metadata.get(
                    "formalization_bridge_parent_hypothesis_variant_premise"
                ):
                    metadata[
                        "formalization_bridge_rehydrate_reclassified"
                    ] = True

    def to_record(self) -> Dict[str, Any]:
        self.prune_scratch_nodes()
        self.refresh_route_branch_frames()
        return {
            "schema_version": 1,
            "theorem_name": self.theorem_name,
            "root_statement": self.root_statement,
            "root_node_id": self.root_node_id,
            "summary": self.summary(),
            "nodes": [asdict(node) for node in self.nodes.values()],
            "edges": [asdict(edge) for edge in self.edges],
            "attempts": [asdict(attempt) for attempt in self.attempts],
            "attempt_history_pruned": int(self.attempt_history_pruned),
            "next_attempt_index": int(self._next_attempt_index),
            "helper_name_to_node_id": dict(self.helper_name_to_node_id),
            "branch_frames": [asdict(frame) for frame in self.branch_frames.values()],
            "active_root_target_statements": list(self.active_root_target_statements),
            "active_root_target_contract_identities": list(
                self.active_root_target_contract_identities
            ),
            "active_root_target_universe_observed": bool(
                self.active_root_target_universe_observed
            ),
        }

    @classmethod
    def from_record(
        cls,
        record: Dict[str, Any],
        *,
        resolve_helper_matches: bool = True,
    ) -> "ProofGraph":
        """Rehydrate a proof graph from ``to_record`` JSON-compatible data."""

        data = dict(record or {})
        if "schema_version" in data:
            try:
                schema_version = int(data.get("schema_version"))
            except (TypeError, ValueError) as exc:
                raise ValueError("invalid proof-graph schema_version") from exc
            if schema_version != 1:
                raise ValueError(
                    f"unsupported proof-graph schema_version={schema_version}; expected 1"
                )
        nodes: Dict[str, ProofGraphNode] = {}
        for raw in list(data.get("nodes") or []):
            if not isinstance(raw, dict):
                continue
            kind = str(raw.get("kind") or "state")
            name = str(raw.get("name") or "")
            statement = _rehydrate_graph_node_statement(
                kind,
                str(raw.get("statement") or ""),
            )
            metadata = copy.deepcopy(dict(raw.get("metadata") or {}))
            if kind == "decl_application":
                name = _graph_prompt_safe_decl_application_preview(name, limit=160)
                statement = _graph_prompt_safe_decl_application_preview(
                    statement,
                    limit=1000,
                )
                metadata = _sanitize_decl_application_metadata(metadata)
            node = ProofGraphNode(
                node_id=str(raw.get("node_id") or ""),
                kind=kind,
                name=name,
                statement=statement,
                status=str(raw.get("status") or "open"),
                phase=str(raw.get("phase") or ""),
                turn_index=int(raw.get("turn_index") or 0),
                source_hash=str(raw.get("source_hash") or ""),
                proof_hash=str(raw.get("proof_hash") or ""),
                support_names=[
                    str(item or "").strip()
                    for item in list(raw.get("support_names") or [])
                    if str(item or "").strip()
                ],
                attempt_ids=[
                    str(item or "").strip()
                    for item in list(raw.get("attempt_ids") or [])
                    if str(item or "").strip()
                ],
                metadata=metadata,
            )
            if node.node_id:
                nodes[node.node_id] = node
        edges = [
            ProofGraphEdge(
                source=str(raw.get("source") or ""),
                target=str(raw.get("target") or ""),
                kind=str(raw.get("kind") or ""),
            )
            for raw in list(data.get("edges") or [])
            if isinstance(raw, dict)
        ]
        attempts = []
        for raw in list(data.get("attempts") or []):
            if not isinstance(raw, dict):
                continue
            phase = str(raw.get("phase") or "")
            metadata = copy.deepcopy(dict(raw.get("metadata") or {}))
            source = str(raw.get("source") or "")
            helper_names = [
                str(item or "").strip()
                for item in list(raw.get("helper_names") or [])
                if str(item or "").strip()
            ]
            if phase == "apply_decl_to_goal":
                source = _graph_prompt_safe_decl_application_preview(source, limit=1000)
                metadata = _sanitize_decl_application_metadata(metadata)
                helper_names = [
                    _graph_prompt_safe_decl_application_preview(name, limit=160)
                    for name in helper_names
                ]
            attempts.append(
                ProofGraphAttempt(
                    attempt_id=str(raw.get("attempt_id") or ""),
                    node_id=str(raw.get("node_id") or ""),
                    phase=phase,
                    turn_index=int(raw.get("turn_index") or 0),
                    verdict=str(raw.get("verdict") or ""),
                    proof_hash=str(raw.get("proof_hash") or ""),
                    error_type=str(raw.get("error_type") or ""),
                    helper_names=helper_names,
                    source=source,
                    metadata=metadata,
                )
            )
        # Attempt ids are graph-local primary keys. Corrupt/legacy records can
        # contain duplicates (or blanks), which make set-based compaction retain
        # an unbounded number of rows under one id. Preserve every diagnostic
        # row, but mint deterministic fresh numeric ids for collisions before
        # any certificate repair or history compaction sees them.
        used_attempt_ids: Set[str] = set()
        max_numeric_attempt_id = 0
        for attempt in attempts:
            raw_id = str(attempt.attempt_id or "").strip()
            if raw_id.startswith("attempt:"):
                try:
                    max_numeric_attempt_id = max(
                        max_numeric_attempt_id,
                        int(raw_id.split(":", 1)[1]),
                    )
                except ValueError:
                    pass
        next_rehydrated_attempt_id = max_numeric_attempt_id + 1
        for attempt in attempts:
            original_attempt_id = str(attempt.attempt_id or "")
            attempt_id = original_attempt_id.strip()
            if not attempt_id or attempt_id in used_attempt_ids:
                while True:
                    attempt_id = f"attempt:{next_rehydrated_attempt_id}"
                    next_rehydrated_attempt_id += 1
                    if attempt_id not in used_attempt_ids:
                        break
            attempt.attempt_id = attempt_id
            if (
                isinstance(attempt.metadata, dict)
                and (
                    attempt_id != original_attempt_id
                    or "proof_attempt_id" in attempt.metadata
                )
            ):
                attempt.metadata["proof_attempt_id"] = attempt_id
            used_attempt_ids.add(attempt_id)
        branch_frames: Dict[str, ProofGraphBranchFrame] = {}
        for raw in list(data.get("branch_frames") or []):
            if not isinstance(raw, dict):
                continue
            frame = ProofGraphBranchFrame(
                frame_id=str(raw.get("frame_id") or ""),
                route_id=str(raw.get("route_id") or ""),
                case_node_id=str(raw.get("case_node_id") or ""),
                case_helper_name=str(raw.get("case_helper_name") or ""),
                case_statement=str(raw.get("case_statement") or ""),
                case_full_statement=str(
                    raw.get("case_full_statement")
                    or (dict(raw.get("metadata") or {})).get("case_full_statement")
                    or raw.get("case_statement")
                    or ""
                ),
                branch_name=str(raw.get("branch_name") or ""),
                branch_index=int(raw.get("branch_index") or 0),
                assumption_statement=str(raw.get("assumption_statement") or ""),
                assumption_key=str(raw.get("assumption_key") or ""),
                reducer_node_id=str(raw.get("reducer_node_id") or ""),
                reducer_helper_name=str(raw.get("reducer_helper_name") or ""),
                reducer_statement=str(raw.get("reducer_statement") or ""),
                status=str(raw.get("status") or "open"),
                metadata=copy.deepcopy(dict(raw.get("metadata") or {})),
            )
            if frame.frame_id:
                branch_frames[frame.frame_id] = frame
        root_node_id = str(data.get("root_node_id") or "root")
        root_statement = str(data.get("root_statement") or "")
        if not root_statement and root_node_id in nodes:
            root_statement = str(nodes[root_node_id].statement or "")
        graph = cls(
            theorem_name=str(data.get("theorem_name") or ""),
            root_statement=root_statement,
            root_node_id=root_node_id,
            nodes=nodes,
            edges=edges,
            helper_name_to_node_id=dict(data.get("helper_name_to_node_id") or {}),
            attempts=attempts,
            attempt_history_pruned=max(
                0,
                int(data.get("attempt_history_pruned") or 0),
            ),
            branch_frames=branch_frames,
            active_root_target_statements=[
                str(item or "").strip()
                for item in list(data.get("active_root_target_statements") or [])
                if str(item or "").strip()
            ],
            active_root_target_contract_identities=[
                str(item or "").strip()
                for item in list(
                    data.get("active_root_target_contract_identities") or []
                )
                if has_lean_contract_identity(str(item or "").strip())
            ],
            active_root_target_universe_observed=(
                data.get("active_root_target_universe_observed") is True
                or bool(data.get("active_root_target_statements"))
                or bool(data.get("active_root_target_contract_identities"))
            ),
        )
        # Node-side attempt references are a projection of the sanitized
        # attempt ledger, never independent deserialized authority.
        attempts_by_node: Dict[str, List[str]] = {}
        for attempt in graph.attempts:
            if attempt.node_id in graph.nodes:
                attempts_by_node.setdefault(attempt.node_id, []).append(
                    attempt.attempt_id
                )
        for node in graph.nodes.values():
            node.attempt_ids = attempts_by_node.get(node.node_id, [])
        root = graph.nodes.get(graph.root_node_id)
        if root is not None and root.status == "proved" and not root.proof_hash:
            root.status = "open"
            root.metadata["rehydration_status_repair"] = "proved_root_missing_proof_hash"
            graph.edges = [
                edge for edge in graph.edges if edge.kind != "supports_root"
            ]
        graph._rebuild_edge_index()
        graph._repair_graph_native_proof_hashes_from_attempts()
        graph._repair_formal_variant_parent_metadata_from_edges()
        graph._repair_graph_native_metadata_edges()
        graph._repair_revived_claim_child_variants_for_all()
        graph._repair_revived_claim_route_dependencies_for_all()
        graph._repair_revived_variant_route_dependencies_for_all()
        graph._repair_non_theorem_graph_targets()
        graph._reconcile_recorded_bridge_parent_work_on_rehydrate()
        if resolve_helper_matches:
            graph.resolve_existing_proved_helper_matches()
        if resolve_helper_matches:
            graph.repair_proved_claim_child_variant_tombstones()
        graph.enforce_superseded_tombstones()
        graph._repair_invalid_route_assemblies()
        if resolve_helper_matches:
            graph.resolve_existing_proved_helper_matches()
        graph._repair_uncertified_graph_native_proved_nodes()
        graph.refresh_route_branch_frames()
        graph.prune_scratch_nodes()
        graph._next_attempt_index = max(
            graph._next_attempt_index,
            int(data.get("next_attempt_index") or 1),
        )
        graph._sync_next_attempt_index()
        return graph
