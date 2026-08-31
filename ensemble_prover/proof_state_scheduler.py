"""Proof-state scheduling and type-directed retrieval."""

from __future__ import annotations

import copy
import re
import time
from dataclasses import dataclass
from types import SimpleNamespace
from typing import TYPE_CHECKING, Any, Dict, List, Optional, Sequence, Set, Tuple

from .proof_dossier import (
    _prompt_safe_helper_name,
    _prompt_safe_inline_text,
    helper_decl_name,
    text_hash,
)
from .proof_graph import helper_decl_statement
from .proof_state import (
    PROOF_STATE_DECL_EXECUTION_POLICY_VERSION,
    ProofSearchState,
    ProofStateNode,
    _CHECK_TERM_RE,
    _GOAL_OPERATOR_TAGS,
    _LEAN_IDENTIFIER_RE,
    _LEAN_TYPE_SYMBOLS,
    _MATHLIB_SHAPE_KEYWORDS,
    _blank_lean_quoted_identifier_contents,
    _has_goal_operator,
    _compact_search_text,
    canonicalize_lean_statement_for_identity,
    lean_statement_bound_names,
    lean_statement_conclusion,
    lean_statement_forall_body,
    proof_state_decl_application_page_is_current,
)

if TYPE_CHECKING:
    from .mathlib_api_search import MathlibApiSearcher


_PROOF_STATE_RETRIEVAL_INDEX_VERSION = "proof_state_type_shape_v4"
_TYPE_DIRECTED_GENERIC_TERMS = {
    "",
    "Nat",
    "Int",
    "Rat",
    "Real",
    "Complex",
    "Set",
    "Finset",
    "List",
    "Prop",
    "Sort",
    "Type",
    "True",
    "False",
    "Eq",
    "Iff",
    "Filter",
    "Filter.atTop",
    "atTop",
}

_TYPE_DIRECTED_OPERATOR_TAGS = {
    "equality rewrite",
    "iff",
    "inequality le",
    "inequality ge",
    "inequality lt",
    "inequality gt",
    "membership set",
    "subset set",
    "divisibility dvd",
    "negation",
    "exists",
}


_UNIVERSE_LEVEL_SPACE_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(?:Sort|Type)\s+([uvw](?:\d+)?)(?![A-Za-z0-9_'])"
)
_UNIVERSE_LEVEL_DOT_BRACE_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(?:Sort|Type)\.\{([^}]+)\}"
)
_UNIVERSE_LEVEL_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_'])([uvw](?:\d+)?)(?![A-Za-z0-9_'])"
)
_UNEXPECTED_SEARCH_KEYWORD_RE = re.compile(
    r"unexpected keyword argument ['\"]([^'\"]+)['\"]"
)


def _universe_level_identifiers(type_text: str) -> Set[str]:
    text = str(type_text or "")
    levels = set(_UNIVERSE_LEVEL_SPACE_RE.findall(text))
    for blob in _UNIVERSE_LEVEL_DOT_BRACE_RE.findall(text):
        levels.update(_UNIVERSE_LEVEL_TOKEN_RE.findall(blob))
    return levels


def _canonical_decl_name(name: str) -> str:
    return str(name or "").strip().lstrip("@")


def _entry_value(entry: Any, field: str, default: str = "") -> Any:
    """Read a declaration-like object or dict through one stable accessor."""

    if isinstance(entry, dict):
        return entry.get(field, default)
    return getattr(entry, field, default)


@dataclass(frozen=True)
class DeclarationShape:
    """Search-index view of a Mathlib/local declaration."""

    name: str
    kind: str
    type_text: str
    result_head: str
    constants: Tuple[str, ...]
    binder_heads: Tuple[str, ...]
    namespaces: Tuple[str, ...]
    shape_tags: Tuple[str, ...]
    tactic_tags: Tuple[str, ...]


def _lean_identifiers(text: str) -> Tuple[str, ...]:
    seen: Set[str] = set()
    out: List[str] = []
    text = _blank_lean_quoted_identifier_contents(str(text or ""))
    for symbol, replacement in _LEAN_TYPE_SYMBOLS.items():
        text = text.replace(symbol, replacement)
    for match in _LEAN_IDENTIFIER_RE.finditer(str(text or "")):
        token = match.group(0)
        if token in seen or token in {"theorem", "lemma", "by", "Prop", "Sort"}:
            continue
        seen.add(token)
        out.append(token)
    return tuple(out)


def _namespace_roots(constants: Sequence[str], *, name: str = "") -> Tuple[str, ...]:
    seen: Set[str] = set()
    out: List[str] = []
    for token in [name, *list(constants or [])]:
        for part in str(token or "").split("."):
            if part and part[:1].isupper() and part not in seen:
                seen.add(part)
                out.append(part)
                break
    return tuple(out)


def _shape_tags_for_text(text: str, constants: Sequence[str]) -> Tuple[str, ...]:
    haystack = str(text or "")
    normalized = haystack
    for symbol, replacement in _LEAN_TYPE_SYMBOLS.items():
        normalized = normalized.replace(symbol, replacement)
    constant_tokens = {
        token
        for constant in [*list(constants or ()), *_lean_identifiers(normalized)]
        for token in (
            str(constant or "").strip(),
            str(constant or "").split(".", 1)[0],
            str(constant or "").rsplit(".", 1)[-1],
        )
        if token
    }
    tags: List[str] = []
    for keyword in sorted(_MATHLIB_SHAPE_KEYWORDS, key=len, reverse=True):
        if keyword in constant_tokens:
            tags.append(keyword if keyword != "choose" else "Nat.choose")
    for symbol, tag in _GOAL_OPERATOR_TAGS:
        if _has_goal_operator(haystack, symbol):
            tags.append(tag)
    if _has_goal_operator(haystack, "∑'") or "tsum" in constants:
        tags.append("tsum infinite sum")
    if _has_goal_operator(haystack, "∑") or "sum" in constants:
        tags.append("finset sum")
    if _has_goal_operator(haystack, "∏") or "prod" in constant_tokens:
        tags.append("finset product")
    deduped: List[str] = []
    seen: Set[str] = set()
    for tag in tags:
        if tag and tag not in seen:
            seen.add(tag)
            deduped.append(tag)
    return tuple(deduped)


def _split_arrow_conclusion(type_text: str) -> str:
    return lean_statement_conclusion(str(type_text or ""))


def _normalized_decl_statement_text(text: str) -> str:
    return canonicalize_lean_statement_for_identity(text)


def _strip_structural_outer_parens(text: str) -> str:
    value = " ".join(str(text or "").split()).strip()
    while value.startswith("(") and value.endswith(")"):
        depth = 0
        closes_at_end = False
        for index, char in enumerate(value):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    closes_at_end = index == len(value) - 1
                    break
        if not closes_at_end:
            break
        value = value[1:-1].strip()
    return value


def _split_top_level_structural(text: str, operator: str) -> Optional[Tuple[str, str]]:
    value = _strip_structural_outer_parens(text)
    depth = 0
    index = 0
    while index < len(value):
        char = value[index]
        if char in "({[":
            depth += 1
        elif char in ")} ]".replace(" ", ""):
            depth = max(0, depth - 1)
        elif depth == 0 and value.startswith(operator, index):
            left = value[:index].strip()
            right = value[index + len(operator) :].strip()
            if left and right:
                return left, right
        index += 1
    return None


def _strip_leading_forall_type(text: str) -> str:
    return lean_statement_forall_body(str(text or ""))


def _top_level_arrow_parts(text: str) -> List[str]:
    remaining = _strip_leading_forall_type(text)
    parts: List[str] = []
    while True:
        split = _split_top_level_structural(remaining, "→")
        if split is None:
            split = _split_top_level_structural(remaining, "->")
        if split is None:
            parts.append(_strip_structural_outer_parens(remaining))
            return [part for part in parts if part]
        left, remaining = split
        parts.append(_strip_structural_outer_parens(left))


def _structural_pattern_unifies(
    pattern: str,
    concrete: str,
    *,
    variables: Set[str],
    substitutions: Dict[str, str],
) -> bool:
    """Small fail-closed unifier for proposition-shaped eliminator premises."""

    pattern = _strip_structural_outer_parens(pattern)
    concrete = _strip_structural_outer_parens(concrete)
    if pattern in variables:
        prior = substitutions.get(pattern)
        if prior is None:
            substitutions[pattern] = concrete
            return True
        return _strip_structural_outer_parens(prior) == concrete
    if pattern == concrete:
        return True
    for operator in ("↔", "→", "->", "∨", "∧"):
        pattern_split = _split_top_level_structural(pattern, operator)
        concrete_split = _split_top_level_structural(concrete, operator)
        if pattern_split is None and concrete_split is None:
            continue
        if pattern_split is None or concrete_split is None:
            return False
        trial = dict(substitutions)
        if _structural_pattern_unifies(
            pattern_split[0],
            concrete_split[0],
            variables=variables,
            substitutions=trial,
        ) and _structural_pattern_unifies(
            pattern_split[1],
            concrete_split[1],
            variables=variables,
            substitutions=trial,
        ):
            substitutions.clear()
            substitutions.update(trial)
            return True
        return False
    return False


def _result_head_for_text(text: str) -> str:
    conclusion = _split_arrow_conclusion(text)
    bound_names = set(lean_statement_bound_names(text))
    for symbol, tag in _GOAL_OPERATOR_TAGS:
        if _has_goal_operator(conclusion, symbol):
            return tag
    ids = _lean_identifiers(conclusion)
    if ids and ids[0] in {"False", "True"}:
        return ids[0]
    for keyword in (
        "Prop",
        "Type",
        "Nat",
        "Int",
        "Rat",
        "Real",
        "Complex",
        "Finset",
        "Set",
    ):
        if keyword in ids:
            return keyword
    for ident in ids:
        if ident in bound_names or ident.rsplit(".", 1)[0] in bound_names:
            continue
        if ident not in {"Nat", "Int", "Rat", "Real", "Complex"}:
            return ident
    return ids[0] if ids else ""


def _binder_heads_for_type(type_text: str) -> Tuple[str, ...]:
    text = str(type_text or "")
    heads: List[str] = []
    for match in re.finditer(r"\(([^:()]+)\s*:\s*([^()]+?)\)", text):
        typ = match.group(2)
        ids = _lean_identifiers(typ)
        head = ids[0] if ids else typ.strip()
        if head:
            heads.append(head)
    for match in re.finditer(r"\{([^:()]+)\s*:\s*([^{}]+?)\}", text):
        typ = match.group(2)
        ids = _lean_identifiers(typ)
        head = ids[0] if ids else typ.strip()
        if head:
            heads.append(head)
    for match in re.finditer(r"(?:∀|forall)\s+([^,]+),", text):
        binder_text = match.group(1)
        colon_match = re.search(r":\s*([^,]+)$", binder_text)
        if not colon_match:
            continue
        typ = colon_match.group(1).strip()
        ids = _lean_identifiers(typ)
        head = ids[0] if ids else typ
        if head:
            heads.append(head)
    deduped: List[str] = []
    seen: Set[str] = set()
    for head in heads:
        if head and head not in seen:
            seen.add(head)
            deduped.append(head)
    return tuple(deduped)


def _tactic_tags_for_shape(type_text: str, shape_tags: Sequence[str]) -> Tuple[str, ...]:
    tags = set(shape_tags or ())
    out: List[str] = []
    if {"finset sum", "finset product", "Nat.choose"} & tags:
        out.extend(["simp", "rewrite", "exact"])
    if {
        "inequality le",
        "inequality ge",
        "inequality lt",
        "inequality gt",
    } & tags:
        out.extend(["nlinarith", "linarith", "omega"])
    if {"equality rewrite", "pow", "Polynomial", "MvPolynomial"} & tags:
        out.extend(["rw", "ring_nf", "simp"])
    if {"divisibility dvd", "Nat.Prime", "Prime"} & tags:
        out.extend(["omega", "norm_num", "exact"])
    if "instance" in str(type_text or "").lower():
        out.append("instance")
    deduped: List[str] = []
    seen: Set[str] = set()
    for tag in out:
        if tag not in seen:
            seen.add(tag)
            deduped.append(tag)
    return tuple(deduped)


def _declaration_shape(entry: Any) -> DeclarationShape:
    name = str(_entry_value(entry, "name", "") or "").strip()
    kind = str(_entry_value(entry, "kind", "") or "").strip().lower()
    type_text = str(_entry_value(entry, "type", "") or "").strip()
    bound_names = set(lean_statement_bound_names(type_text))
    constants = tuple(
        token
        for token in _lean_identifiers(" ".join([name, type_text]))
        if token not in bound_names
        and token.rsplit(".", 1)[0] not in bound_names
    )
    shape_tags = _shape_tags_for_text(type_text, constants)
    return DeclarationShape(
        name=name,
        kind=kind,
        type_text=type_text,
        result_head=_result_head_for_text(type_text),
        constants=constants,
        binder_heads=_binder_heads_for_type(type_text),
        namespaces=_namespace_roots(constants, name=name),
        shape_tags=shape_tags,
        tactic_tags=_tactic_tags_for_shape(type_text, shape_tags),
    )


def _entries_fingerprint(entries: Sequence[Any]) -> str:
    parts = [f"count={len(entries)}"]
    for entry in entries:
        parts.extend(
            [
                str(_entry_value(entry, "name", "") or ""),
                str(_entry_value(entry, "kind", "") or ""),
                text_hash(str(_entry_value(entry, "type", "") or ""))[:12],
            ]
        )
    return text_hash("\n".join(parts))


def _entries_cache_key(entries: Any) -> str:
    try:
        entries_list = [] if entries is None else list(entries)
    except Exception:
        return f"unreadable:{type(entries).__name__}"
    return f"fingerprint={_entries_fingerprint(entries_list)}"


def _declaration_shape_score(
    shape: DeclarationShape,
    *,
    goal_result: str,
    goal_constants: Set[str],
    goal_namespaces: Set[str],
    goal_tags: Set[str],
    goal_binders: Set[str],
    action: str,
) -> float:
    if shape.kind and shape.kind not in {"theorem", "lemma"}:
        return 0.0
    if not shape.name or shape.name.startswith("Mathlib.Command."):
        return 0.0
    score = 0.0
    meaningful_constants = goal_constants - _TYPE_DIRECTED_GENERIC_TERMS
    meaningful_tags = goal_tags - _TYPE_DIRECTED_GENERIC_TERMS
    meaningful_namespaces = goal_namespaces - _TYPE_DIRECTED_GENERIC_TERMS
    meaningful_binders = goal_binders - _TYPE_DIRECTED_GENERIC_TERMS
    constant_hits = meaningful_constants.intersection(shape.constants)
    tag_hits = meaningful_tags.intersection(shape.shape_tags)
    namespace_hits = meaningful_namespaces.intersection(shape.namespaces)
    binder_hits = meaningful_binders.intersection(shape.binder_heads)
    structural_tag_hits = tag_hits - _TYPE_DIRECTED_OPERATOR_TAGS
    strong_signal = (
        constant_hits
        or binder_hits
        or structural_tag_hits
        or (tag_hits and namespace_hits)
    )
    if not strong_signal:
        return 0.0
    if (
        goal_result
        and goal_result not in _TYPE_DIRECTED_GENERIC_TERMS
        and shape.result_head == goal_result
    ):
        score += 5.0
    elif goal_result and goal_result in tag_hits:
        score += 2.0
    score += 4.0 * len(constant_hits)
    score += 3.0 * len(tag_hits)
    score += 1.5 * len(namespace_hits)
    score += 1.0 * len(binder_hits)
    if "rewrite" in action and {"rw", "rewrite", "simp"} & set(shape.tactic_tags):
        score += 2.5
    if "instance" in action and "instance" in shape.tactic_tags:
        score += 3.0
    if "tactic" in action and set(shape.tactic_tags):
        score += 1.0
    return score


def _merge_ranked_entries(
    lexical: Sequence[Any],
    typed: Sequence[Tuple[float, Any]],
    *,
    max_results: int,
) -> List[Any]:
    by_name: Dict[str, Tuple[float, int, Any]] = {}
    for rank, entry in enumerate(lexical):
        name = _canonical_decl_name(str(_entry_value(entry, "name", "") or ""))
        if not name:
            continue
        score = 650.0 - (rank * 2.0)
        current = by_name.get(name)
        if current is None or score > current[0]:
            by_name[name] = (score, rank, entry)
    typed_offset = len(by_name)
    for rank, (score, entry) in enumerate(typed):
        name = _canonical_decl_name(str(_entry_value(entry, "name", "") or ""))
        if not name:
            continue
        typed_score = 560.0 + (float(score) * 12.0)
        current = by_name.get(name)
        if current is None:
            by_name[name] = (typed_score, typed_offset + rank, entry)
        else:
            combined_score = current[0] + max(1.0, float(score)) * 16.0
            by_name[name] = (
                max(current[0], combined_score, typed_score),
                current[1],
                current[2],
            )
    ranked = list(by_name.values())
    ranked.sort(key=lambda item: (-item[0], item[1]))
    return [entry for _, _, entry in ranked[:max_results]]


class TypeDirectedMathlibIndex:
    """Type/namespace aware adapter over the existing Mathlib search backend."""

    def __init__(self, searcher: Any, *, entries_cache_key: str = "") -> None:
        self.searcher = searcher
        entries_source = getattr(searcher, "_entries", None)
        self.entries_cache_key = str(entries_cache_key or _entries_cache_key(entries_source))
        self.entries: List[Any] = list(entries_source or ())
        self.entries_fingerprint = _entries_fingerprint(self.entries)
        self.index_version = (
            f"{_PROOF_STATE_RETRIEVAL_INDEX_VERSION}:"
            f"{self.entries_fingerprint}"
        )
        self.shapes: List[DeclarationShape] = [
            _declaration_shape(entry) for entry in self.entries
        ]
        self._candidate_index = self._build_candidate_index()

    def _build_candidate_index(self) -> Dict[str, Set[int]]:
        index: Dict[str, Set[int]] = {}
        for idx, shape in enumerate(self.shapes):
            tokens = [
                *shape.constants,
                *shape.namespaces,
                *shape.shape_tags,
            ]
            if shape.result_head not in _TYPE_DIRECTED_GENERIC_TERMS:
                tokens.append(shape.result_head)
            for token in tokens:
                if not token or token in _TYPE_DIRECTED_GENERIC_TERMS:
                    continue
                index.setdefault(token, set()).add(idx)
            for head in shape.binder_heads:
                if not head or head in _TYPE_DIRECTED_GENERIC_TERMS:
                    continue
                index.setdefault(f"binder:{head}", set()).add(idx)
        return index

    def search_node(self, node: ProofStateNode, *, max_results: int) -> List[Any]:
        query = _proof_state_node_retrieval_query(node)
        if not query:
            return []
        lexical = _search_proof_state_node_candidates_lexical(
            self.searcher,
            node,
            query,
            max_results=max_results * 3,
        )
        typed = self._search_by_shape(node, max_results=max_results * 4)
        return _merge_ranked_entries(lexical, typed, max_results=max_results)

    def _search_by_shape(
        self,
        node: ProofStateNode,
        *,
        max_results: int,
    ) -> List[Tuple[float, Any]]:
        if node.goal is None or not self.shapes:
            return []
        goal_constants = set(node.goal.constants_used)
        goal_namespaces = set(node.goal.namespaces)
        goal_tags = set(node.goal.shape_tags)
        goal_binders = {
            binder.replace("binder:", "").split(":", 1)[-1].split("->", 1)[-1].strip()
            for binder in node.goal.binder_structure
            if binder
        }
        lookup_terms = (
            goal_constants
            | goal_namespaces
            | goal_tags
            | (
                {node.goal.result_head}
                if node.goal.result_head not in _TYPE_DIRECTED_GENERIC_TERMS
                else set()
            )
        )
        lookup_terms.update(
            f"binder:{binder}"
            for binder in goal_binders
            if binder not in _TYPE_DIRECTED_GENERIC_TERMS
        )
        candidate_indexes: Set[int] = set()
        for term in lookup_terms:
            if not term or term in _TYPE_DIRECTED_GENERIC_TERMS:
                continue
            candidate_indexes.update(self._candidate_index.get(term, set()))
        if not candidate_indexes:
            return []
        scored: List[Tuple[float, int, Any]] = []
        for idx in sorted(candidate_indexes):
            if idx >= len(self.entries) or idx >= len(self.shapes):
                continue
            entry = self.entries[idx]
            shape = self.shapes[idx]
            score = _declaration_shape_score(
                shape,
                goal_result=node.goal.result_head,
                goal_constants=goal_constants,
                goal_namespaces=goal_namespaces,
                goal_tags=goal_tags,
                goal_binders=goal_binders,
                action=node.action,
            )
            if _normalized_decl_statement_text(_entry_value(entry, "type", "")) == (
                _normalized_decl_statement_text(node.target)
            ):
                score += 25.0
            if score <= 0.0:
                continue
            scored.append((score, idx, entry))
        scored.sort(key=lambda item: (-item[0], item[1]))
        return [(score, entry) for score, _, entry in scored[:max_results]]


def _format_search_results(hits: Sequence[Any], max_results: int) -> str:
    hits = list(hits)[:max_results]
    if not hits:
        return "No matches."
    lines: List[str] = [f"{len(hits)} match(es):"]
    for i, entry in enumerate(hits, 1):
        name = _prompt_safe_helper_name(str(_entry_value(entry, "name", "") or "?"))
        kind = _prompt_safe_inline_text(
            str(_entry_value(entry, "kind", "") or ""),
            limit=80,
        )
        type_str = _prompt_safe_inline_text(
            str(_entry_value(entry, "type", "") or "").strip(),
            limit=280,
        )
        if len(type_str) > 280:
            type_str = type_str[:280] + " …"
        file_str = _prompt_safe_inline_text(
            str(_entry_value(entry, "file", "") or ""),
            limit=220,
        )
        tail = "/".join(file_str.split("/")[-2:]) if file_str else ""
        kind_label = f" ({kind})" if kind else ""
        lines.append(f"{i}. {name}{kind_label}")
        if type_str:
            lines.append(f"   : {type_str}")
        if tail:
            lines.append(f"   @ {tail}")
    return "\n".join(lines)


def _proof_state_node_retrieval_query(node: ProofStateNode) -> str:
    parts = [
        node.kind.replace("_", " "),
        node.action.replace("_", " "),
    ]
    if node.goal is not None:
        parts.extend(
            [
                f"result head {node.goal.result_head}",
                "constants " + " ".join(node.goal.constants_used),
                "namespaces " + " ".join(node.goal.namespaces),
                "shape " + " ".join(node.goal.shape_tags),
                "binders " + " ".join(node.goal.binder_structure),
                "typeclasses " + " ".join(node.goal.typeclass_needs),
                node.goal.target_expr,
            ]
        )
        for hyp in node.goal.local_hypotheses[:8]:
            parts.append(str(hyp.get("type") or ""))
    action_terms = {
        "namespace_type_retrieval": "verified declaration lookup or local substitute",
        "manufacture_or_retrieve_missing_identifier": (
            "prove local bridge substitute or retrieve verified declaration"
        ),
        "bridge_rewrite_or_coercion": "rewrite coercion cast congruence simpa",
        "instance_or_domain_retrieval": "instance decidable linear_order field semiring",
        "explicit_instantiation_or_bridge": "apply exact specialize instantiate",
        "split_or_normalize_target": "simp norm_num ring_nf nlinarith omega split",
        "swap_tactic_family": "simp aesop omega nlinarith ring_nf exact",
        "prove_child_helper": "exact apply simp theorem helper",
        "assemble_from_children": "simpa exact using helper theorem",
        "force_graph_decomposition": "lemma theorem auxiliary subgoal decomposition",
        "plan_lemma_dag": "lemma theorem auxiliary subgoal decomposition",
        "repair_syntax_or_binders": "syntax binder forall theorem exact",
        "retry_or_reduce_lean_batch": "shorter proof split helper theorem",
        "answer_safe_bridge_or_rederive": "derive without unfolding answer solution",
    }
    if node.action in action_terms:
        parts.append(action_terms[node.action])
    parts.extend([node.target, *list(node.local_context or [])[:8]])
    return _compact_search_text(" ".join(part for part in parts if part), limit=900)


def _proof_state_retrieval_signature(
    node: ProofStateNode,
    query: str,
    *,
    max_results: int,
    index_version: str = "",
) -> str:
    goal_hash = ""
    source_failure = ""
    if node.goal is not None:
        goal_hash = node.goal.normalized_statement_hash
        source_failure = node.goal.source_failure
    parts = [
        goal_hash,
        f"query={text_hash(str(query or ''))}",
        node.action,
        node.statement_environment_hash,
        source_failure,
        f"top_k={max(0, int(max_results or 0))}",
        f"index={index_version}",
        node.target,
        "|".join(str(item or "") for item in node.local_context),
        "|".join(
            f"{key}={value}"
            for key, value in sorted(node.local_argument_terms.items())
        ),
    ]
    return text_hash("\n".join(str(part or "") for part in parts))


def _proof_state_retrieval_index_version(
    searcher: Optional[MathlibApiSearcher],
    local_helper_blocks: Sequence[str],
) -> str:
    explicit_index_version = str(
        getattr(searcher, "index_version", "")
        or getattr(searcher, "version", "")
        if searcher is not None
        else ""
    )
    index_version = explicit_index_version or (
        type(searcher).__name__ if searcher is not None else "no_mathlib_search"
    )
    federated_snapshot = str(
        getattr(searcher, "index_snapshot_id", "") or ""
    )
    entries_count: Any = "?"
    entries_identity = ""
    if searcher is not None and not federated_snapshot:
        entries_source = getattr(searcher, "_entries", None)
        try:
            entries_count = 0 if entries_source is None else len(entries_source)
        except Exception:
            entries_count = "?"
        if not explicit_index_version:
            # For lightweight/testing backends without a declared generation,
            # replacing the entry container is the only O(1) invalidation
            # signal. Production/forkable backends must expose a stable
            # version so worker views do not depend on process-local identity.
            if not entries_source:
                entries_identity = "empty"
            else:
                entries_identity = str(id(entries_source))
    entries_generation = str(
        getattr(searcher, "entries_generation", "")
        or getattr(searcher, "_entries_generation", "")
        or getattr(searcher, "entries_version", "")
        if searcher is not None
        else ""
    )
    local_helper_version = _local_helper_fingerprint(local_helper_blocks)
    type_index_version = (
        f"federated={federated_snapshot}"
        if federated_snapshot
        else (
            f"entries_count={entries_count}:generation={entries_generation}:"
            f"identity={entries_identity}"
        )
    )
    # The execution filter is part of the persisted retrieval contract too.
    # Include it even for federated snapshots (whose own snapshot id may stay
    # constant across a client-side policy change), so old empty/broad pages
    # are refreshed instead of merely becoming non-executable.
    return (
        f"{_PROOF_STATE_RETRIEVAL_INDEX_VERSION}:"
        f"policy={PROOF_STATE_DECL_EXECUTION_POLICY_VERSION}:"
        f"{index_version}:{type_index_version}:local={local_helper_version}"
    )


def _proof_state_node_retrieval_signature_for_context(
    searcher: Optional[MathlibApiSearcher],
    node: ProofStateNode,
    *,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
) -> Tuple[str, str]:
    query = _proof_state_node_retrieval_query(node)
    retrieval_index_version = _proof_state_retrieval_index_version(
        searcher,
        list(local_helper_blocks or ()),
    )
    signature = _proof_state_retrieval_signature(
        node,
        query,
        max_results=max(0, min(10, int(max_results or 0))),
        index_version=retrieval_index_version,
    )
    return query, signature


def _proof_state_node_needs_retrieval(
    searcher: Optional[MathlibApiSearcher],
    node: ProofStateNode,
    *,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
) -> bool:
    """Whether current retrieval context differs from the node's last scan."""

    if (
        node.kind != "child_goal"
        or node.status != "open"
        or bool(getattr(node, "falsified", False))
    ):
        return False
    if searcher is None and not list(local_helper_blocks or ()):
        # There is no executable retrieval backend.  In particular, a legacy
        # graph declaration quarantined during hydration must not manufacture
        # a permanently live retrieval obligation that no action can service.
        return False
    query, signature = _proof_state_node_retrieval_signature_for_context(
        searcher,
        node,
        max_results=max_results,
        local_helper_blocks=local_helper_blocks,
    )
    if not query:
        return not bool(node.retrieval_attempted)
    policy_is_stale = bool(node.retrieval_attempted) and (
        str(getattr(node, "retrieved_decl_execution_policy_version", "") or "")
        != PROOF_STATE_DECL_EXECUTION_POLICY_VERSION
    )
    mixed_page = bool(
        getattr(node, "retrieved_decl_names", []) or []
    ) and not proof_state_decl_application_page_is_current(node)
    stale_page = policy_is_stale or mixed_page
    if node.retrieval_error and node.retrieval_error_signature == signature:
        # Transient failures reopen after backoff. A matching terminal error
        # still refreshes THIS page when it is mixed/stale. A current page,
        # a first-time invalid query, or a different-context failure must
        # not spin.
        if getattr(node, "retrieval_error_transient", False):
            return time.time() >= float(
                getattr(node, "retrieval_retry_after_epoch_s", 0.0) or 0.0
            )
        same_page = str(getattr(node, "retrieval_signature", "") or "") == signature
        return bool(same_page and stale_page)
    if stale_page:
        return True
    if node.retrieval_attempted and node.retrieval_signature == signature:
        return False
    return True


def _proof_state_retrieval_exception_is_transient(exc: Exception) -> bool:
    """Retry retrieval unless the failure is a deterministic ValueError."""

    return not isinstance(exc, ValueError)


def _proof_state_entry_matches_goal_shape(entry: Any, node: ProofStateNode) -> bool:
    if node.goal is None:
        return True
    haystack = " ".join(
        str(_entry_value(entry, attr, "") or "")
        for attr in ("name", "type", "namespace", "docstring")
    )
    strong_terms = [
        term
        for term in [
            *node.goal.constants_used,
            *node.goal.shape_tags,
            node.goal.result_head,
        ]
        if term
        and term not in {"Nat", "Int", "Rat", "Real", "Complex", "equality rewrite"}
        and not term.startswith("binder:")
    ]
    if not strong_terms:
        return True
    normalized_haystack = haystack.replace(".choose", "Nat.choose")
    operator_aliases = {
        "inequality le": ("≤", "LE.le", "le_"),
        "inequality ge": ("≥", "GE.ge", "ge_"),
        "inequality lt": ("<", "LT.lt", "lt_"),
        "inequality gt": (">", "GT.gt", "gt_"),
        "divisibility dvd": ("∣", "Dvd.dvd", "dvd"),
        "membership set": ("∈", "Membership.mem", "mem"),
        "subset set": ("⊆", "Subset", "subset"),
        "equality rewrite": ("=", "Eq", "eq"),
        "iff": ("↔", "Iff", "iff"),
        "negation": ("¬", "Not", "not"),
    }
    for term in strong_terms:
        if _term_occurs_in_text(term, normalized_haystack):
            return True
        if any(
            _term_occurs_in_text(alias, normalized_haystack)
            for alias in operator_aliases.get(term, ())
        ):
            return True
        if term == "Finset" and "∑" in normalized_haystack:
            return True
        if term == "Icc" and ("Icc" in normalized_haystack or "finsetIcc" in normalized_haystack):
            return True
    return False


def _proof_state_entry_is_execution_relevant(
    entry: Any,
    node: ProofStateNode,
) -> bool:
    """Require direct-application candidates to carry the goal's anchors.

    Shape tags such as ``sum`` and ``membership set`` are intentionally broad
    retrieval features.  They are not, by themselves, enough evidence to pay
    for a kernel application probe when the goal names a problem-specific
    constant.  In that case the declaration must mention at least one such
    constant (or have the exact target type).  Generic goals retain the
    existing shape policy.

    This is an execution-cost gate, not a trust gate: accepted declarations
    are still checked by Lean, while filtered declarations remain available
    to ordinary search/conversation paths.
    """

    if node.goal is None:
        return True
    target = _normalized_decl_statement_text(node.target)
    entry_type = _normalized_decl_statement_text(_entry_value(entry, "type", ""))
    if target and entry_type == target:
        return True

    def execution_anchors(constants: Sequence[str]) -> Set[str]:
        return {
            term
            for term in constants
            if term not in _TYPE_DIRECTED_GENERIC_TERMS
            and term.rsplit(".", 1)[-1] not in _TYPE_DIRECTED_GENERIC_TERMS
            and term not in {"in", "fun", "_"}
            # Dummy binders (n, i, x) stay out. Named objects (G, R, K, D)
            # are problem constants even as a single letter.
            and (len(term) > 1 or term.isupper())
        }

    goal_anchors = execution_anchors(node.goal.constants_used)
    shape = _declaration_shape(entry)
    entry_type_text = str(_entry_value(entry, "type", "") or "").strip()
    entry_conclusion = str(lean_statement_conclusion(entry_type_text) or "").strip()
    conclusion_constants = _lean_identifiers(entry_conclusion)
    conclusion_result_head = _result_head_for_text(entry_conclusion)
    conclusion_shape_tags = set(
        _shape_tags_for_text(entry_conclusion, conclusion_constants)
    )

    def has_compatible_result_shape() -> bool:
        return bool(
            node.goal is not None
            and node.goal.result_head
            and (
                conclusion_result_head == node.goal.result_head
                or node.goal.result_head in conclusion_shape_tags
            )
        )

    def is_context_supported_polymorphic_eliminator() -> bool:
        """Recognize eliminators whose conclusion is a bound result type.

        ``False.elim : ∀ {C : Sort u}, False → C`` deliberately has no
        goal-specific result head.  It is execution-relevant only when its
        non-result premise signal (``False`` here) is also present in the
        contextual goal.  This structural rule covers genuine polymorphic
        eliminators without trusting declaration names or admitting arbitrary
        wrong-result theorems.
        """

        bound_names = set(lean_statement_bound_names(entry_type_text))
        if not entry_conclusion or entry_conclusion not in bound_names:
            return False
        arrow_parts = _top_level_arrow_parts(entry_type_text)
        if len(arrow_parts) < 2:
            return False
        premises = arrow_parts[:-1]
        goal_conclusion = str(lean_statement_conclusion(node.target) or "").strip()
        if not goal_conclusion:
            return False
        initial_substitutions = {entry_conclusion: goal_conclusion}
        contextual_types = [
            str(item.get("type") or "").strip()
            for item in list(node.goal.local_hypotheses or ())
            if isinstance(item, dict) and str(item.get("type") or "").strip()
        ]
        for premise in premises:
            # Require a proposition constructor/eliminator signal.  Merely
            # matching an unconstrained bound premise would re-admit arbitrary
            # wrong-result theorems.
            if not (
                any(symbol in premise for symbol in ("∧", "∨", "↔", "¬", "∃"))
                or re.search(r"(?<![A-Za-z0-9_'.])False(?![A-Za-z0-9_'.])", premise)
            ):
                continue
            for contextual_type in contextual_types:
                substitutions = dict(initial_substitutions)
                if _structural_pattern_unifies(
                    premise,
                    contextual_type,
                    variables=bound_names,
                    substitutions=substitutions,
                ):
                    return True
        return False

    if is_context_supported_polymorphic_eliminator():
        return True
    if goal_anchors:
        if goal_anchors.intersection(shape.constants):
            return has_compatible_result_shape()
        # Generic constructors/eliminators (for example ``Eq.refl``) can be
        # applicable without naming the problem-specific constant. Admit only
        # those whose result shape is exact and whose own type introduces no
        # non-generic anchor; Lean remains the authoritative applicability gate.
        entry_type = str(_entry_value(entry, "type", "") or "")
        bound_names = set(lean_statement_bound_names(entry_type))
        conclusion_bound_names = bound_names.intersection(
            _lean_identifiers(entry_conclusion)
        )
        conclusion_has_unification_variable = bool(
            re.search(r"(?<![A-Za-z0-9_'])\?[A-Za-z_][A-Za-z0-9_']*", entry_conclusion)
        )
        universe_levels = _universe_level_identifiers(entry_type)
        entry_anchors = execution_anchors(
            [
                term
                for term in _lean_identifiers(entry_type)
                if term not in bound_names and term not in universe_levels
            ]
        )
        return bool(
            has_compatible_result_shape()
            and (
                conclusion_bound_names
                or conclusion_has_unification_variable
            )
            and not entry_anchors
        )
    return _proof_state_entry_matches_goal_shape(entry, node)


def _term_occurs_in_text(term: str, text: str) -> bool:
    needle = str(term or "").strip()
    haystack = str(text or "")
    if not needle:
        return False
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_'.]*)*", needle):
        return re.search(
            rf"(?<![A-Za-z0-9_'.]){re.escape(needle)}(?![A-Za-z0-9_'.])",
            haystack,
        ) is not None
    return needle in haystack


def _get_type_directed_index(searcher: Any) -> TypeDirectedMathlibIndex:
    entries_source = getattr(searcher, "_entries", None)
    cache_key = _entries_cache_key(entries_source)
    index = getattr(searcher, "_proof_state_type_index", None)
    if (
        isinstance(index, TypeDirectedMathlibIndex)
        and getattr(index, "entries_cache_key", "") == cache_key
    ):
        return index
    index = TypeDirectedMathlibIndex(searcher, entries_cache_key=cache_key)
    try:
        setattr(searcher, "_proof_state_type_index", index)
    except Exception:
        pass
    return index


def _local_helper_entries(helper_blocks: Sequence[str]) -> List[Any]:
    entries: List[Any] = []
    for block in list(helper_blocks or []):
        source = str(block or "").strip()
        if not source:
            continue
        name = helper_decl_name(source) or ""
        statement = helper_decl_statement(source)
        if not name or not statement:
            continue
        entries.append(
            SimpleNamespace(
                name=name,
                kind="theorem",
                type=statement,
                file="verified_helpers",
                docstring="kernel-verified local helper",
            )
        )
    return entries


def _local_helper_fingerprint(helper_blocks: Sequence[str]) -> str:
    parts: List[str] = []
    for entry in _local_helper_entries(helper_blocks):
        parts.extend(
            [
                str(_entry_value(entry, "name", "") or ""),
                text_hash(str(_entry_value(entry, "type", "") or ""))[:12],
            ]
        )
    return text_hash("\n".join(parts)) if parts else "no_local_helpers"


def _rank_local_helper_entries(
    node: ProofStateNode,
    helper_blocks: Sequence[str],
    *,
    max_results: int,
) -> List[Tuple[float, Any]]:
    if not helper_blocks or node.goal is None:
        return []
    goal_constants = set(node.goal.constants_used)
    goal_namespaces = set(node.goal.namespaces)
    goal_tags = set(node.goal.shape_tags)
    goal_binders = {
        binder.replace("binder:", "").split(":", 1)[-1].split("->", 1)[-1].strip()
        for binder in node.goal.binder_structure
        if binder
    }
    scored: List[Tuple[float, int, Any]] = []
    target_statement = _normalized_decl_statement_text(node.target)
    for index, entry in enumerate(_local_helper_entries(helper_blocks)):
        shape = _declaration_shape(entry)
        score = _declaration_shape_score(
            shape,
            goal_result=node.goal.result_head,
            goal_constants=goal_constants,
            goal_namespaces=goal_namespaces,
            goal_tags=goal_tags,
            goal_binders=goal_binders,
            action=node.action,
        )
        if _normalized_decl_statement_text(_entry_value(entry, "type", "")) == target_statement:
            score += 30.0
        if score <= 0.0:
            continue
        scored.append((score + 8.0, index, entry))
    scored.sort(key=lambda item: (-item[0], item[1]))
    return [(score, entry) for score, _, entry in scored[: max(0, int(max_results or 0))]]


def _is_unexpected_search_keyword_error(exc: BaseException) -> bool:
    return isinstance(exc, TypeError) and "unexpected keyword argument" in str(exc)


def _mathlib_search(searcher: Any, query: str, **kwargs: Any) -> Any:
    """Call ``searcher.search``, peeling unsupported keywords only."""

    try:
        return searcher.search(query, **kwargs)
    except TypeError as exc:
        if not _is_unexpected_search_keyword_error(exc):
            raise
        match = _UNEXPECTED_SEARCH_KEYWORD_RE.search(str(exc))
        named = match.group(1) if match else ""
        if named and named in kwargs:
            next_kwargs = dict(kwargs)
            next_kwargs.pop(named)
            return _mathlib_search(searcher, query, **next_kwargs)
        # Messages that omit the keyword name still peel kind, then max_results.
        if "kind" in kwargs:
            next_kwargs = dict(kwargs)
            next_kwargs.pop("kind")
            return _mathlib_search(searcher, query, **next_kwargs)
        if "max_results" in kwargs:
            next_kwargs = dict(kwargs)
            next_kwargs.pop("max_results")
            return _mathlib_search(searcher, query, **next_kwargs)
        raise


def _search_proof_state_node_candidates_lexical(
    searcher: MathlibApiSearcher,
    node: ProofStateNode,
    query: str,
    *,
    max_results: int,
) -> List[Any]:
    """Retrieve theorem/lemma candidates, filtering out noisy defs/commands."""

    hits: List[Any] = []
    seen: Set[str] = set()
    def _accept_entry(entry: Any) -> bool:
        name = str(_entry_value(entry, "name", "") or "").strip()
        if not name or name in seen:
            return False
        kind = str(_entry_value(entry, "kind", "") or "").strip().lower()
        if kind and kind not in {"theorem", "lemma"}:
            return False
        if name.startswith("Mathlib.Command."):
            return False
        return _proof_state_entry_matches_goal_shape(entry, node)

    for kind in ("theorem", "lemma"):
        batch = _mathlib_search(
            searcher, query, kind=kind, max_results=max_results * 3
        )
        for entry in list(batch or []):
            name = str(_entry_value(entry, "name", "") or "").strip()
            if not _accept_entry(entry):
                continue
            seen.add(name)
            hits.append(entry)
            if len(hits) >= max_results:
                return hits
    if hits:
        return hits[:max_results]
    fallback = _mathlib_search(searcher, query, max_results=max_results * 3)
    for entry in list(fallback or []):
        name = str(_entry_value(entry, "name", "") or "").strip()
        if not _accept_entry(entry):
            continue
        seen.add(name)
        hits.append(entry)
        if len(hits) >= max_results:
            break
    return hits[:max_results]


def _search_federated_proof_state_node_candidates(
    searcher: Any,
    node: ProofStateNode,
    *,
    max_results: int,
    helper_blocks: Sequence[str],
) -> List[Any]:
    """Run the typed federated service without exposing inactive declarations."""

    from .mathematical_retrieval import (
        CandidateOrigin,
        RetrievalQuery,
        RetrievalSourcePolicy,
    )

    if node.goal is None:
        return []
    query = RetrievalQuery.create(
        theorem_name="",
        target_statement=node.goal.target_expr or node.target,
        ordered_local_context=tuple(
            str(item.get("type") or "")
            for item in list(node.goal.local_hypotheses or ())
            if isinstance(item, dict) and str(item.get("type") or "").strip()
        ),
        result_head=node.goal.result_head,
        constants=node.goal.constants_used,
        namespaces=node.goal.namespaces,
        binder_heads=tuple(
            binder.replace("binder:", "")
            .split(":", 1)[-1]
            .split("->", 1)[-1]
            .strip()
            for binder in node.goal.binder_structure
            if binder
        ),
        typeclass_needs=node.goal.typeclass_needs,
        shape_tags=node.goal.shape_tags,
        natural_language=_proof_state_node_retrieval_query(node),
        route_context=f"{node.kind} {node.action} {node.blocker}",
        intended_uses=(node.action, "apply", "rewrite", "bridge"),
        source_policy=RetrievalSourcePolicy(include_inactive=False),
        max_candidates=max_results,
        index_snapshot_id=str(getattr(searcher, "index_snapshot_id", "") or ""),
    )
    extra_entries_list: List[Tuple[Any, CandidateOrigin]] = []
    for block in list(helper_blocks or ()):
        entries = _local_helper_entries((block,))
        if not entries:
            continue
        extra_entries_list.append(
            (
                entries[0],
                CandidateOrigin(
                    source_kind="verified_helper",
                    source_id="current_dossier",
                    module_name="",
                    source_path="verified_helpers",
                    environment_hash=(
                        str(getattr(searcher, "environment_hash", "") or "")
                        or query.local_context_hash
                    ),
                    trust_kind="cached_kernel_verified",
                    availability="already_imported",
                    helper_source=str(block or ""),
                ),
            )
        )
    result = searcher.retrieve(query, extra_entries=tuple(extra_entries_list))
    return [searcher.candidate_entry(candidate) for candidate in result.candidates]


def _retrieve_proof_state_node_candidates(
    searcher: Optional[MathlibApiSearcher],
    proof_state: Optional[ProofSearchState],
    *,
    max_nodes: int,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
    target_node_ids: Optional[Sequence[str]] = None,
) -> List[Dict[str, Any]]:
    """Attach Mathlib candidates to open scheduled child nodes."""

    if proof_state is None:
        return []
    helper_blocks = list(local_helper_blocks or [])
    if searcher is None and not helper_blocks:
        return []
    max_n = max(0, min(10, int(max_results or 0)))
    if max_n <= 0:
        return []
    # Filtering a single upstream page can strand relevant lower-ranked hits.
    # Pull a bounded larger page, apply the execution gate, then retain the
    # caller's requested frontier width.
    candidate_limit = min(40, max_n * 4)
    records: List[Dict[str, Any]] = []
    target_ids = [
        str(item or "").strip()
        for item in list(target_node_ids or ())
        if str(item or "").strip()
    ]
    if target_ids:
        nodes = []
        for node_id in target_ids:
            node = proof_state.nodes.get(node_id)
            if node is None or node.kind != "child_goal" or node.status != "open":
                continue
            nodes.append(node)
            if len(nodes) >= max(1, int(max_nodes or 1)):
                break
    else:
        nodes = proof_state.child_frontier(max_nodes=max_nodes)
    if not nodes:
        return []
    federated = bool(
        searcher is not None
        and getattr(searcher, "index_snapshot_id", "")
        and callable(getattr(searcher, "retrieve", None))
        and callable(getattr(searcher, "candidate_entry", None))
    )
    type_index = None
    type_index_initialization_error: Optional[Exception] = None
    if searcher is not None and not federated:
        try:
            type_index = _get_type_directed_index(searcher)
        except Exception as exc:
            type_index_initialization_error = exc
    for node in nodes:
        query, retrieval_signature = _proof_state_node_retrieval_signature_for_context(
            searcher,
            node,
            max_results=max_n,
            local_helper_blocks=helper_blocks,
        )
        if not _proof_state_node_needs_retrieval(
            searcher,
            node,
            max_results=max_n,
            local_helper_blocks=helper_blocks,
        ):
            continue
        if not query:
            proof_state.record_retrieved_facts(
                node.node_id,
                "",
                decl_names=[],
                hit_count=0,
                retrieval_signature=retrieval_signature,
            )
            continue
        started = time.monotonic()
        try:
            if type_index_initialization_error is not None:
                raise type_index_initialization_error
            hits = (
                _search_federated_proof_state_node_candidates(
                    searcher,
                    node,
                    max_results=candidate_limit,
                    helper_blocks=helper_blocks,
                )
                if federated
                else type_index.search_node(
                    node,
                    max_results=candidate_limit,
                )
                if type_index is not None
                else []
            )
            local_hits = (
                []
                if federated
                else _rank_local_helper_entries(
                    node,
                    helper_blocks,
                    max_results=candidate_limit,
                )
            )
            if local_hits:
                hits = _merge_ranked_entries(
                    hits,
                    local_hits,
                    max_results=candidate_limit,
                )
            raw_result_count = len(hits)
            hits = [
                hit
                for hit in hits
                if _proof_state_entry_is_execution_relevant(hit, node)
            ][:max_n]
            rendered = _format_search_results(hits, max_n)
            decl_names = [
                str(_entry_value(hit, "name", "") or "").strip()
                for hit in hits
                if _CHECK_TERM_RE.fullmatch(
                    str(_entry_value(hit, "name", "") or "").strip().lstrip("@")
                )
            ]
            proof_state.record_retrieved_facts(
                node.node_id,
                rendered,
                decl_names=decl_names,
                hit_count=len(hits),
                retrieval_signature=retrieval_signature,
            )
            record = {
                "node_id": node.node_id,
                "retrieval_signature": retrieval_signature,
                "query": query,
                "result_count": len(hits),
                "raw_result_count": raw_result_count,
                "relevance_filtered_count": max(0, raw_result_count - len(hits)),
                "decl_names": decl_names[:10],
                "rendered": rendered[:1000],
                "elapsed_s": round(time.monotonic() - started, 3),
            }
        except Exception as exc:
            # Retry transport, scoring, and other non-ValueError failures.
            # A deterministic ValueError is invalid for this exact query and
            # must not loop.
            transient = _proof_state_retrieval_exception_is_transient(exc)
            proof_state.record_retrieval_failure(
                node.node_id,
                f"{type(exc).__name__}: {exc}",
                retrieval_signature=retrieval_signature,
                transient=transient,
            )
            record = {
                "node_id": node.node_id,
                "retrieval_signature": retrieval_signature,
                "query": query,
                "error": f"{type(exc).__name__}: {exc}",
                "transient": transient,
                "elapsed_s": round(time.monotonic() - started, 3),
            }
        records.append(record)
    return records


@dataclass(frozen=True)
class _ProofStateRetrievalCommitGuard:
    """Bounded in-memory authority for one asynchronous retrieval commit."""

    node_id: str
    live_node: ProofStateNode
    kind: str
    status: str
    target: str
    action: str
    blocker: str
    context_signature: str
    settlement_fingerprint: Tuple[Any, ...]


def _proof_state_retrieval_settlement_fingerprint(
    node: ProofStateNode,
) -> Tuple[Any, ...]:
    """Return bounded retrieval state used to reject out-of-order workers."""

    return (
        bool(node.retrieval_attempted),
        str(node.retrieval_signature or ""),
        tuple(str(item or "") for item in node.retrieved_decl_names),
        tuple(sorted(node.retrieved_decl_provenance.items())),
        tuple(sorted(node.retrieved_decl_signatures.items())),
        tuple(str(item or "") for item in node.retrieved_facts),
        int(node.retrieval_hit_count or 0),
        str(node.retrieval_error or ""),
        str(node.retrieval_error_signature or ""),
        bool(node.retrieval_error_transient),
        int(node.retrieval_error_attempt_count or 0),
        float(node.retrieval_retry_after_epoch_s or 0.0),
        str(node.retrieved_decl_execution_policy_version or ""),
        tuple(str(item or "") for item in node.graph_retrieved_decl_quarantine_names),
        bool(node.falsified),
        str(node.falsification_reason or ""),
        str(node.falsification_certificate_hash or ""),
        tuple(
            tuple(
                sorted(
                    (str(key or ""), str(value or ""))
                    for key, value in dict(record).items()
                )
            )
            for record in list(node.falsification_retired_assembly_routes or ())
            if isinstance(record, dict)
        ),
    )


def _capture_proof_state_retrieval_commit_guards(
    searcher: Optional[MathlibApiSearcher],
    proof_state: ProofSearchState,
    *,
    max_nodes: int,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
    target_node_ids: Optional[Sequence[str]] = None,
) -> Dict[str, _ProofStateRetrievalCommitGuard]:
    """Capture exact live-node authority before an isolated worker starts."""

    target_ids = [
        str(node_id or "").strip()
        for node_id in list(target_node_ids or ())
        if str(node_id or "").strip()
    ]
    if target_ids:
        nodes = [
            proof_state.nodes[node_id]
            for node_id in target_ids
            if node_id in proof_state.nodes
        ][: max(1, int(max_nodes or 1))]
    else:
        nodes = proof_state.child_frontier(max_nodes=max(1, int(max_nodes or 1)))
    guards: Dict[str, _ProofStateRetrievalCommitGuard] = {}
    for node in nodes:
        if node.kind != "child_goal" or node.status != "open":
            continue
        query, signature = _proof_state_node_retrieval_signature_for_context(
            searcher,
            node,
            max_results=max_results,
            local_helper_blocks=local_helper_blocks,
        )
        if (
            not query
            or not signature
            or not _proof_state_node_needs_retrieval(
                searcher,
                node,
                max_results=max_results,
                local_helper_blocks=local_helper_blocks,
            )
        ):
            continue
        guards[node.node_id] = _ProofStateRetrievalCommitGuard(
            node_id=node.node_id,
            live_node=node,
            kind=node.kind,
            status=node.status,
            target=node.target,
            action=node.action,
            blocker=node.blocker,
            context_signature=signature,
            settlement_fingerprint=(
                _proof_state_retrieval_settlement_fingerprint(node)
            ),
        )
    return guards


def _proof_state_retrieval_commit_guard_is_current(
    searcher: Optional[MathlibApiSearcher],
    proof_state: ProofSearchState,
    guard: _ProofStateRetrievalCommitGuard,
    *,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
) -> bool:
    """Reject worker results when their exact live goal authority changed."""

    node = proof_state.nodes.get(guard.node_id)
    if (
        node is None
        or node is not guard.live_node
        or node.kind != guard.kind
        or node.status != guard.status
        or node.target != guard.target
        or node.action != guard.action
        or node.blocker != guard.blocker
        or _proof_state_retrieval_settlement_fingerprint(node)
        != guard.settlement_fingerprint
    ):
        return False
    _query, signature = _proof_state_node_retrieval_signature_for_context(
        searcher,
        node,
        max_results=max_results,
        local_helper_blocks=local_helper_blocks,
    )
    return bool(signature and signature == guard.context_signature)


def _commit_current_proof_state_retrieval_records(
    searcher: Optional[MathlibApiSearcher],
    proof_state: ProofSearchState,
    guards: Dict[str, _ProofStateRetrievalCommitGuard],
    records: Any,
    *,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
) -> List[Dict[str, Any]]:
    """Commit and return only records whose originating goal is still live."""

    committed: List[Dict[str, Any]] = []
    if not isinstance(records, (list, tuple)):
        return committed
    settled_node_ids: Set[str] = set()
    for record in records:
        if not isinstance(record, dict):
            continue
        node_id = str(record.get("node_id") or "").strip()
        guard = guards.get(node_id)
        signature = str(record.get("retrieval_signature") or "").strip()
        if (
            node_id in settled_node_ids
            or guard is None
            or signature != guard.context_signature
            or not _proof_state_retrieval_commit_guard_is_current(
                searcher,
                proof_state,
                guard,
                max_results=max_results,
                local_helper_blocks=local_helper_blocks,
            )
        ):
            continue
        if record.get("error"):
            proof_state.record_retrieval_failure(
                node_id,
                str(record.get("error") or ""),
                retrieval_signature=signature,
                transient=bool(record.get("transient", True)),
            )
            normalized_record = dict(record)
            normalized_record["decl_names"] = []
            normalized_record["result_count"] = 0
        else:
            raw_decl_names = record.get("decl_names")
            raw_result_count = record.get("result_count")
            if (
                not isinstance(raw_decl_names, (list, tuple))
                or not isinstance(raw_result_count, int)
                or isinstance(raw_result_count, bool)
            ):
                continue
            decl_names = list(
                dict.fromkeys(
                    name
                    for raw_name in raw_decl_names[:10]
                    if (name := str(raw_name or "").strip())
                    and _CHECK_TERM_RE.fullmatch(name.lstrip("@"))
                )
            )
            result_count = max(
                0,
                min(max(0, min(10, int(max_results or 0))), raw_result_count),
            )
            proof_state.record_retrieved_facts(
                node_id,
                str(record.get("rendered") or ""),
                decl_names=decl_names,
                hit_count=result_count,
                retrieval_signature=signature,
            )
            normalized_record = dict(record)
            normalized_record["decl_names"] = decl_names
            normalized_record["result_count"] = result_count
        committed.append(normalized_record)
        settled_node_ids.add(node_id)
    return committed


def _record_current_proof_state_retrieval_failures(
    searcher: Optional[MathlibApiSearcher],
    proof_state: ProofSearchState,
    guards: Dict[str, _ProofStateRetrievalCommitGuard],
    *,
    error: str,
    transient: bool,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
) -> List[str]:
    """Record a worker-boundary failure only on unchanged live goals."""

    committed_node_ids: List[str] = []
    for node_id, guard in guards.items():
        if not _proof_state_retrieval_commit_guard_is_current(
            searcher,
            proof_state,
            guard,
            max_results=max_results,
            local_helper_blocks=local_helper_blocks,
        ):
            continue
        proof_state.record_retrieval_failure(
            node_id,
            error,
            retrieval_signature=guard.context_signature,
            transient=transient,
        )
        committed_node_ids.append(node_id)
    return committed_node_ids


async def _retrieve_proof_state_node_candidates_async(
    searcher: Optional[MathlibApiSearcher],
    proof_state: Optional[ProofSearchState],
    *,
    max_nodes: int,
    max_results: int,
    local_helper_blocks: Sequence[str] = (),
    target_node_ids: Optional[Sequence[str]] = None,
    timeout_s: float = 30.0,
) -> List[Dict[str, Any]]:
    """Compute retrieval on isolated state and commit only accepted records."""

    if proof_state is None:
        return []
    from .mathematical_retrieval.async_runtime import (
        RetrievalWorkerCapacityError,
        run_sync_abandonment_safe,
    )

    started = time.monotonic()
    commit_guards = _capture_proof_state_retrieval_commit_guards(
        searcher,
        proof_state,
        max_nodes=max_nodes,
        max_results=max_results,
        local_helper_blocks=local_helper_blocks,
        target_node_ids=target_node_ids,
    )
    worker_searcher = searcher
    try:
        fork = getattr(searcher, "fork_session_context", None)
        if callable(fork):
            worker_searcher = fork()
        records = await run_sync_abandonment_safe(
            lambda: _retrieve_proof_state_node_candidates(
                worker_searcher,
                copy.deepcopy(proof_state),
                max_nodes=max_nodes,
                max_results=max_results,
                local_helper_blocks=local_helper_blocks,
                target_node_ids=target_node_ids,
            ),
            timeout_s=max(0.05, float(timeout_s)),
        )
    except Exception as exc:
        publish_failure = getattr(searcher, "publish_boundary_failure", None)
        if callable(publish_failure):
            try:
                publish_failure(
                    consumer="proof_state",
                    elapsed_s=time.monotonic() - started,
                    capacity_exhausted=isinstance(
                        exc,
                        RetrievalWorkerCapacityError,
                    ),
                )
            except Exception:
                pass
        _record_current_proof_state_retrieval_failures(
            searcher,
            proof_state,
            commit_guards,
            error=f"{type(exc).__name__}: {exc}",
            transient=_proof_state_retrieval_exception_is_transient(exc),
            max_results=max_results,
            local_helper_blocks=local_helper_blocks,
        )
        return [{"error": f"{type(exc).__name__}: {exc}", "result_count": 0}]
    committed_records = _commit_current_proof_state_retrieval_records(
        searcher,
        proof_state,
        commit_guards,
        records,
        max_results=max_results,
        local_helper_blocks=local_helper_blocks,
    )
    publish = getattr(searcher, "publish_result_metrics", None)
    if callable(publish):
        try:
            publish(
                getattr(worker_searcher, "last_result", None),
                consumer="proof_state",
            )
        except Exception:
            pass
    return committed_records
