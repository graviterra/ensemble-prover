"""Context-closed subgoal compiler.

Builds candidate subgoal variants by closing over root binders and live goal
hypotheses.  This is a syntactic compiler only; Lean validation remains the
source of truth for admissibility.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import List, Optional, Sequence

from .lean_parser import LeanGoalState
from .lean_syntax import normalize_nat_factorial_notation
from .utils import (
    _canonicalize_top_level_let_in,
    _first_top_level_assign,
    _split_leading_forall_statement,
    _split_top_level_let_body,
    _split_top_level_implication_conclusion,
    _split_top_level,
    _telescope_quantifier_bound_names,
    expand_relation_forall_binders,
    merge_contextual_binders,
    normalize_subgoal_statement,
    select_contextual_binders,
)

# Unicode-aware identifier regex (Lean allows identifiers like `γ`, `hγ0`).
# Keep this aligned with the binder tokenizer in utils.py.
_IDENT_RE = re.compile(r"(?:[^\W\d_]|_)[\w']*", re.UNICODE)
_INSTANCE_ASSIGN_NAME_RE = re.compile(
    r"^(?:_+|inst[A-Za-z0-9_']*|_inst[A-Za-z0-9_']*)$"
)
_LEAN_KEYWORDS = frozenset(
    {
        "by",
        "fun",
        "match",
        "let",
        "have",
        "show",
        "theorem",
        "lemma",
        "example",
        "def",
        "abbrev",
        "forall",
        "exists",
        "True",
        "False",
        "Prop",
        "Type",
        "Nat",
        "Int",
        "Real",
        "Set",
        "Finset",
        "And",
        "Or",
        "Not",
        "Iff",
    },
)
_RELATION_SHORTHAND_TOKENS = (
    "∉",
    "∈",
    "≥",
    ">=",
    "≤",
    "<=",
    "≠",
    "!=",
    ">",
    "<",
    "=",
)


@dataclass(frozen=True)
class SubgoalVariant:
    statement: str
    mode: str  # raw | root_context | goal_context | root_and_goal_context
    contract_identity: str = ""
    contract_identity_statement_key: str = ""
    contract_identity_environment_hash: str = ""
    contract_identity_evidence_receipt: str = ""
    contract_display_statement: str = ""
    contract_binder_sorts: tuple[str, ...] = ()
    contract_proof_binder_types: tuple[str, ...] = ()
    contract_proof_binder_structural_hashes: tuple[str, ...] = ()
    contract_conclusion_structural_hash: str = ""
    contract_telescope_evidence_receipt: str = ""


def _identifier_tokens(text: str) -> set[str]:
    if not text:
        return set()
    return {tok for tok in _IDENT_RE.findall(text) if tok and tok not in _LEAN_KEYWORDS}


def _merge_unique_segments(*parts: Sequence[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for seq in parts:
        for seg in seq:
            s = str(seg or "").strip()
            if not s or s in seen:
                continue
            seen.add(s)
            out.append(s)
    return out


def _binder_chunks(segment: str) -> list[str]:
    raw = str(segment or "").strip()
    if not raw:
        return []
    if raw[0] not in "([{⦃":
        return [raw]
    chunks: list[str] = []
    i = 0
    n = len(raw)
    while i < n:
        while i < n and raw[i].isspace():
            i += 1
        if i >= n:
            break
        start = i
        ch = raw[i]
        if ch == "(":
            close = ")"
        elif ch == "{":
            close = "}"
        elif ch == "[":
            close = "]"
        elif ch == "⦃":
            close = "⦄"
        else:
            close = ""
        if close:
            depth = 1
            i += 1
            while i < n and depth > 0:
                if raw[i] == ch:
                    depth += 1
                elif raw[i] == close:
                    depth -= 1
                i += 1
            chunks.append(raw[start:i].strip())
            continue
        i += 1
    return chunks or [raw]


def _declared_names_from_binder_segment(segment: str) -> set[str]:
    raw = str(segment or "").strip()
    if not raw:
        return set()
    if raw.startswith("[") and raw.endswith("]"):
        inner = raw[1:-1].strip()
        if not inner:
            return set()
        if ":=" in inner:
            inner = inner.split(":=", 1)[0].strip()
        if ":" not in inner:
            # Anonymous typeclass binders like `[CommSemigroup S]` declare no
            # user-facing name and should not collide with the local `S`.
            return set()
        head = inner.split(":", 1)[0].strip()
        return _identifier_tokens(head)

    if raw[0] in "({⦃" and raw[-1] in ")}⦄":
        inner = raw[1:-1].strip()
    else:
        inner = raw
    if not inner:
        return set()
    if ":=" in inner:
        inner = inner.split(":=", 1)[0].strip()
    if ":" in inner:
        inner = inner.split(":", 1)[0].strip()
    return _identifier_tokens(inner)


def _declared_names_from_binders(binders: Sequence[str]) -> set[str]:
    declared: set[str] = set()
    for seg in binders:
        raw = str(seg or "").strip()
        if not raw:
            continue
        for chunk in _binder_chunks(raw):
            declared.update(_declared_names_from_binder_segment(chunk))
    return declared


def _goal_hypothesis_binders(
    goal_state: Optional[LeanGoalState],
) -> tuple[list[str], set[str]]:
    if goal_state is None:
        return [], set()
    out: list[str] = []
    blocked_assignment_names: set[str] = set()
    for hyp in getattr(goal_state, "hypotheses", None) or []:
        h = str(hyp or "").strip()
        if not h:
            continue
        if ":=" in h:
            lhs, rhs = h.split(":=", 1)
            lhs = lhs.strip()
            rhs = rhs.strip()
            if ":" not in lhs:
                continue
            head_raw = lhs.split(":", 1)[0].strip()
            head = head_raw.replace("✝", "")
            if not head:
                continue
            if not (
                rhs.startswith("inferInstance")
                or _INSTANCE_ASSIGN_NAME_RE.fullmatch(head)
            ):
                blocked_assignment_names.update(_identifier_tokens(head_raw))
                continue
            h = lhs
        out.append(f"({h})")
    return out, blocked_assignment_names


def _prefixed_statement(
    stmt: str,
    binders: Sequence[str],
    *,
    needed_names: Optional[set[str]] = None,
    max_prefix_chars: int,
) -> Optional[str]:
    if not stmt:
        return None
    context_binders = select_contextual_binders(
        stmt,
        binders,
        needed_names=needed_names,
        include_supporting_assumptions=True,
    )
    if not context_binders:
        return None
    return merge_contextual_binders(
        stmt,
        context_binders,
        max_prefix_chars=int(max_prefix_chars),
    )


def _needed_context_names(
    stmt: str,
    *,
    context_declared: set[str],
) -> set[str]:
    if not stmt or not context_declared:
        return set()
    local_declared = _telescope_quantifier_bound_names(stmt)
    used = _identifier_tokens(stmt)
    return (used & context_declared) - local_declared


def _segment_annotation(segment: str) -> str:
    raw = str(segment or "").strip()
    if not raw:
        return ""
    if raw[0] in "({[⦃" and raw[-1:] in ")}]⦄":
        raw = raw[1:-1].strip()
    if ":=" in raw:
        raw = raw.split(":=", 1)[0].strip()
    if ":" not in raw:
        return ""
    return raw.split(":", 1)[1].strip()


def _segment_looks_supporting_assumption(segment: str) -> bool:
    annotation = _segment_annotation(segment)
    if not annotation:
        return False
    if annotation.startswith(("Prop", "True", "False", "∀", "∃", "¬")):
        return True
    return any(
        token in annotation
        for token in (
            " = ",
            " ≠ ",
            " < ",
            " > ",
            " ≤ ",
            " ≥ ",
            " ∈ ",
            " ∉ ",
            " → ",
            " ↔ ",
            "∧",
            "∨",
            "∣",
        )
    )


def _leading_arrow_premises(body: str) -> list[str]:
    premises: list[str] = []
    current = str(body or "").strip()
    while current:
        split = _split_top_level(current, "→") or _split_top_level(current, "->")
        if split is None:
            break
        premise, current = split
        if not premise:
            break
        premises.append(premise)
    return premises


def _shadowed_root_support_names(stmt: str, root_binders: Sequence[str]) -> set[str]:
    """Select root hypotheses needed by locally re-bound root variables.

    A planner may emit an apparently closed claim such as ``∀ n, ...``
    for a root whose real context is ``∀ (n : ℕ), 2 ≤ n → ...``.  The local
    bare binder shadows the root variable name, so ordinary free-name closure
    sees no need for context and finite sampling cannot identify the Nat binder
    type.  These supporting hypothesis binders repair that narrow shape into
    ``∀ n (h_root_1 : 2 ≤ n), ...`` while leaving explicit generic lemmas like
    ``∀ (n : ℕ), ...`` reusable.
    """

    local_binders, body = _split_leading_forall_statement(stmt)
    if not local_binders:
        return set()
    bare_local_declared: set[str] = set()
    for segment in local_binders:
        raw = str(segment or "").strip()
        if (
            raw
            and raw[0] not in "({[⦃"
            and ":" not in raw
            and not any(op in raw for op in _RELATION_SHORTHAND_TOKENS)
        ):
            bare_local_declared.update(_declared_names_from_binders([segment]))
    if not bare_local_declared:
        return set()

    root_declared = _declared_names_from_binders(root_binders)
    shadowed = bare_local_declared & root_declared
    if not shadowed:
        return set()
    existing_premises = {
        _space_normalized(premise)
        for premise in _leading_arrow_premises(body)
    }

    needed: set[str] = set()
    for segment in root_binders:
        declared = _declared_names_from_binders([segment])
        if not declared or declared <= shadowed:
            continue
        annotation = _segment_annotation(segment)
        if not annotation or not _segment_looks_supporting_assumption(segment):
            continue
        if _space_normalized(annotation) in existing_premises:
            continue
        if _identifier_tokens(annotation) & shadowed:
            needed.update(declared)
    return needed


def _needs_context_closure(
    stmt: str,
    *,
    context_declared: set[str],
) -> bool:
    return bool(
        _needed_context_names(
            stmt,
            context_declared=context_declared,
        )
    )


def _space_normalized(text: str) -> str:
    return re.sub(r"\s+", " ", str(text or "").strip())


def _strip_mutated_root_binder_prefix(stmt: str, root_statement: str) -> str:
    """Drop planner-restated root binders when their types drift.

    Planner models often restate the full root context in a helper claim.
    That is safe only if the restated binders match the actual theorem
    context. If a model mutates a root hypothesis type, the helper becomes a
    different theorem. In that case, remove the polluted root prefix and let
    the context compiler re-close the body over the real root binders.
    """

    raw = str(stmt or "").strip()
    if not raw.startswith("∀"):
        return raw
    claim_binders, body = _split_leading_forall_statement(raw)
    root_binders = expand_relation_forall_binders(root_statement or "")
    if not claim_binders or not root_binders:
        return raw

    root_names = _declared_names_from_binders(root_binders)
    if not root_names:
        return raw

    root_segments: list[str] = []
    kept_segments: list[str] = []
    for seg in claim_binders:
        names = _declared_names_from_binders([seg])
        if names and names <= root_names:
            root_segments.append(seg)
        else:
            kept_segments.append(seg)

    if not root_segments:
        return raw
    if not (_declared_names_from_binders(root_segments) >= root_names):
        return raw
    if _space_normalized(" ".join(root_segments)) == _space_normalized(
        " ".join(root_binders)
    ):
        return raw

    rebuilt = str(body or "").strip()
    if kept_segments:
        rebuilt = "".join(f"∀ {seg}, " for seg in kept_segments) + rebuilt
    return rebuilt


def build_subgoal_variants(
    raw_subgoal: str,
    *,
    root_statement: str,
    goal_state: Optional[LeanGoalState] = None,
    max_prefix_chars: int = 600,
    max_variants: int = 4,
) -> List[SubgoalVariant]:
    """Generate context-closed variants for a candidate subgoal."""
    base = normalize_nat_factorial_notation(
        _canonicalize_top_level_let_in(normalize_subgoal_statement(raw_subgoal))
    )
    base = _canonicalize_top_level_let_in(
        normalize_subgoal_statement(
            _strip_mutated_root_binder_prefix(base, root_statement or "")
        )
    )
    if not base:
        return []
    # If the candidate still contains an assignment marker, it's likely a
    # truncated declaration payload. Do not contextualize malformed shapes.
    assign_idx = _first_top_level_assign(base)
    _binders, base_body = _split_leading_forall_statement(base)
    base_focus = str(base_body or base).strip()
    _implication_prefix, base_conclusion = (
        _split_top_level_implication_conclusion(base_focus)
    )
    has_local_let = (
        _split_top_level_let_body(base) is not None
        or _split_top_level_let_body(base_focus) is not None
        or _split_top_level_let_body(base_conclusion) is not None
    )
    has_suspicious_assign = (
        assign_idx != -1
        and not has_local_let
        and not re.match(r"^\s*let\b", base)
        and not re.match(r":=\s*(?:by|sorry|admit)\b", base[assign_idx:])
    )
    root_binders = expand_relation_forall_binders(root_statement or "")
    goal_binders, blocked_goal_assignment_names = _goal_hypothesis_binders(goal_state)
    combined_binders = _merge_unique_segments(root_binders, goal_binders)
    context_declared = _declared_names_from_binders(combined_binders)
    blocked_goal_names_used = _identifier_tokens(base) & blocked_goal_assignment_names
    needed_context_names = _needed_context_names(
        base,
        context_declared=context_declared,
    )
    needed_context_names.update(
        _shadowed_root_support_names(base, root_binders)
    )
    prefers_context = (
        (not has_suspicious_assign)
        and (not blocked_goal_names_used)
        and bool(needed_context_names)
    )

    candidates: list[SubgoalVariant] = []
    seen: set[str] = set()

    def _add(stmt: Optional[str], mode: str) -> None:
        s = normalize_nat_factorial_notation(
            _canonicalize_top_level_let_in(normalize_subgoal_statement(str(stmt or "")))
        )
        if not s or s in seen:
            return
        seen.add(s)
        candidates.append(SubgoalVariant(statement=s, mode=mode))

    if has_suspicious_assign:
        _add(base, "raw")
    elif prefers_context:
        _add(
            _prefixed_statement(
                base,
                combined_binders,
                needed_names=needed_context_names,
                max_prefix_chars=max_prefix_chars,
            ),
            "root_and_goal_context",
        )
        _add(
            _prefixed_statement(
                base,
                root_binders,
                needed_names=needed_context_names,
                max_prefix_chars=max_prefix_chars,
            ),
            "root_context",
        )
        _add(
            _prefixed_statement(
                base,
                goal_binders,
                needed_names=needed_context_names,
                max_prefix_chars=max_prefix_chars,
            ),
            "goal_context",
        )
        _add(base, "raw")
    else:
        _add(base, "raw")
    return candidates[: max(1, int(max_variants))]
