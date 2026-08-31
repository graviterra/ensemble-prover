"""Finite counterexample probes for recursive helper claims.

The recursive planner is allowed to propose hard intermediate claims, but it
must not spend LLM turns proving statements that small concrete instances
already refute.  This module keeps that gate deterministic and answer-safe:
it only instantiates visible Nat binders, asks Lean to prove the negated
concrete proposition by deterministic kernel/numeric evaluation, and treats
every automation failure as inconclusive rather than as a rejection.
"""

from __future__ import annotations

import inspect
import re
import time
from dataclasses import asdict, dataclass
from itertools import product
from typing import Any, Mapping, Optional, Sequence

from .lean_resource_guard import (
    DANGEROUS_NAT_POW_TOWER_REASON,
    looks_like_dangerous_nat_pow_tower,
)
from .lean_syntax import normalize_nat_factorial_notation
from .proof_dossier import helper_decl_name, is_answer_unsafe_helper_source
from .utils import (
    _first_top_level_assign,
    _first_top_level_comma,
    _split_top_level_let_body,
)


_IDENT_RE_TEMPLATE = r"(?<![A-Za-z0-9_']){}(?![A-Za-z0-9_'])"


@dataclass(frozen=True)
class FiniteClaimSampleAttempt:
    args: tuple[int, ...]
    statement: str
    ok: bool
    elapsed_s: float
    output_preview: str = ""
    exception: str = ""


@dataclass(frozen=True)
class FiniteClaimSampleResult:
    falsified: bool
    attempts: tuple[FiniteClaimSampleAttempt, ...] = ()
    reason: str = ""
    skipped: bool = False
    skip_reason: str = ""
    obstruction_kind: str = ""
    obstruction_detail: str = ""

    def to_record(self) -> dict[str, Any]:
        return {
            "falsified": self.falsified,
            "reason": self.reason,
            "attempts": [asdict(item) for item in self.attempts],
            "skipped": self.skipped,
            "skip_reason": self.skip_reason,
            "obstruction_kind": self.obstruction_kind,
            "obstruction_detail": self.obstruction_detail,
        }


def _normalize_lean_type_text(text: str) -> str:
    compact = re.sub(r"\s+", "", str(text or ""))
    return re.sub(r"(?<![A-Za-z0-9_'.])Nat(?![A-Za-z0-9_'])", "ℕ", compact)


def _leading_quantifier(text: str) -> Optional[tuple[str, str]]:
    raw = str(text or "").lstrip()
    if raw.startswith("∀ᶠ"):
        return None
    if raw.startswith(("∀", "∃")):
        return raw[0], raw[1:].lstrip()
    match = re.match(r"(forall|exists)\b", raw)
    if match is None:
        return None
    quant = "∀" if match.group(1) == "forall" else "∃"
    return quant, raw[match.end() :].lstrip()


def _has_forall(text: str) -> bool:
    raw = str(text or "")
    return "∀" in raw or re.search(r"\bforall\b", raw) is not None


def _unwrap_binder_segment(segment: str) -> str:
    text = str(segment or "").strip()
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    if len(text) >= 2 and text[0] in pairs and text[-1] == pairs[text[0]]:
        return text[1:-1].strip()
    return text


def _binder_chunks(segment: str) -> tuple[str, ...]:
    raw = str(segment or "").strip()
    if not raw:
        return ()
    if raw[0] not in "([{⦃":
        return (raw,)
    chunks: list[str] = []
    i = 0
    n = len(raw)
    while i < n:
        while i < n and raw[i].isspace():
            i += 1
        if i >= n:
            break
        start = i
        opener = raw[i]
        closer = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}.get(opener)
        if closer is None:
            chunks.append(raw[i:].strip())
            break
        depth = 1
        i += 1
        while i < n and depth > 0:
            if raw[i] == opener:
                depth += 1
            elif raw[i] == closer:
                depth -= 1
            i += 1
        chunks.append(raw[start:i].strip())
    return tuple(chunk for chunk in chunks if chunk) or (raw,)


def _binder_names_and_type(segment: str) -> tuple[tuple[str, ...], str]:
    inner = _unwrap_binder_segment(segment)
    if ":" not in inner:
        return (), ""
    names_part, type_part = inner.split(":", 1)
    names = tuple(item for item in names_part.split() if item and item != "_")
    return names, str(type_part or "").strip()


def _nat_binder_names(segment: str) -> tuple[str, ...]:
    names, type_part = _binder_names_and_type(segment)
    if not names:
        return ()
    if _normalize_lean_type_text(type_part) != "ℕ":
        return ()
    return names


def _sampleable_nat_kind(type_part: str) -> str:
    normalized = _normalize_lean_type_text(type_part)
    if normalized == "ℕ":
        return "nat"
    if normalized in {"ℕ+", "PNat"}:
        return "pnat"
    return ""


def _sampleable_nat_binder_names_and_kind(
    segment: str,
) -> tuple[tuple[str, ...], str, str]:
    names, type_part = _binder_names_and_type(segment)
    if not names:
        return (), type_part, ""
    kind = _sampleable_nat_kind(type_part)
    if not kind:
        return (), type_part, ""
    return names, type_part, kind


def _sample_expr_for_nat_kind(raw_arg: int, kind: str) -> str:
    value = int(raw_arg)
    if kind == "pnat":
        value = max(1, value)
        return f"({value} : ℕ+)"
    return f"({value} : ℕ)"


def _first_quantifier_segment(statement: str) -> Optional[tuple[str, str]]:
    text = str(statement or "").strip()
    leading = _leading_quantifier(text)
    if leading is None:
        return None
    _quant, tail = leading
    comma_idx = _first_top_level_comma(tail)
    if comma_idx == -1:
        return None
    segment = tail[:comma_idx].strip()
    body = tail[comma_idx + 1 :].strip()
    if not segment or not body:
        return None
    return segment, body


def _first_forall_segment(statement: str) -> Optional[tuple[str, str]]:
    text = str(statement or "").strip()
    leading = _leading_quantifier(text)
    if leading is None or leading[0] != "∀":
        return None
    return _first_quantifier_segment(text)


def _first_forall_chunk(statement: str) -> Optional[tuple[str, str]]:
    split = _first_forall_segment(statement)
    if split is None:
        return None
    segment, body = split
    chunks = list(_binder_chunks(segment))
    if not chunks:
        return None
    chunk = chunks[0]
    rest = " ".join(chunks[1:]).strip()
    if rest:
        body = f"∀ {rest}, {body}"
    return chunk, body


def _split_sample_let_body(text: str) -> Optional[tuple[str, str]]:
    split = _split_top_level_let_body(text)
    if split is not None:
        return split

    raw = str(text or "").strip()
    if not raw.startswith("let"):
        return None
    assign_idx = _first_top_level_assign(raw)
    if assign_idx == -1 or "\n" not in raw[assign_idx:]:
        return None

    offsets: list[int] = []
    cursor = 0
    for line in raw.splitlines(keepends=True):
        offsets.append(cursor)
        cursor += len(line)
    lines = raw.splitlines()
    assign_line = raw[:assign_idx].count("\n")
    for line_index in range(assign_line + 1, len(lines)):
        stripped = lines[line_index].strip()
        if not stripped:
            continue
        if not (
            stripped.startswith(("∀", "∃", "let", "¬", "("))
            or re.match(r"^(forall|exists)\b", stripped)
        ):
            continue
        body_start = offsets[line_index]
        prefix = raw[:body_start].rstrip()
        body = raw[body_start:].strip()
        if prefix and body:
            return f"{prefix};", body
    return None


def _replace_freeish_identifier(text: str, name: str, replacement: str) -> str:
    """Replace a binder name while avoiding obvious local rebinding.

    This is deliberately conservative, not a Lean parser.  In particular,
    top-level ``let`` bodies are traversed while their RHS prefix is left
    intact; that avoids corrupting local definitions such as ``fun k => ...``
    when a planner accidentally reuses the root binder name.
    """

    raw = str(text or "").strip()
    if not raw or not name:
        return raw

    unwrapped = _unwrap_transparent_parens(raw)
    if unwrapped != raw and _leading_quantifier(unwrapped) is not None:
        return f"({_replace_freeish_identifier(unwrapped, name, replacement)})"

    let_split = _split_sample_let_body(raw)
    if let_split is not None:
        prefix, body = let_split
        return f"{prefix} {_replace_freeish_identifier(body, name, replacement)}"

    and_split = _split_top_level_and(raw)
    if and_split is not None:
        left, right = and_split
        return (
            _replace_freeish_identifier(left, name, replacement)
            + " ∧ "
            + _replace_freeish_identifier(right, name, replacement)
        )

    leading = _leading_quantifier(raw)
    if leading is not None:
        quant = leading[0]
        split = _first_quantifier_segment(raw)
        if split is None:
            return raw
        segment, body = split
        binders = list(_binder_chunks(segment))
        declared_here: set[str] = set()
        for segment in binders:
            names, _type_part = _binder_names_and_type(segment)
            declared_here.update(names)
        if name in declared_here:
            return raw
        if binders and body:
            pattern = re.compile(_IDENT_RE_TEMPLATE.format(re.escape(name)))
            rewritten_binders = [
                pattern.sub(replacement, segment) for segment in binders
            ]
            prefix = "".join(f"{quant} {segment}, " for segment in rewritten_binders)
            return prefix + _replace_freeish_identifier(body, name, replacement)

    pattern = re.compile(_IDENT_RE_TEMPLATE.format(re.escape(name)))
    return pattern.sub(replacement, raw)


def _split_top_level_token(text: str, tokens: tuple[str, ...]) -> Optional[tuple[str, str]]:
    raw = str(text or "").strip()
    depth = 0
    i = 0
    while i < len(raw):
        ch = raw[i]
        if ch in "([{":
            depth += 1
            i += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            for token in tokens:
                if raw.startswith(token, i):
                    left = raw[:i].strip()
                    right = raw[i + len(token) :].strip()
                    if left and right:
                        return left, right
        i += 1
    return None


def _unwrap_transparent_parens(text: str) -> str:
    raw = str(text or "").strip()
    while len(raw) >= 2 and raw[0] == "(" and raw[-1] == ")":
        depth = 0
        whole = True
        for index, ch in enumerate(raw):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and index != len(raw) - 1:
                    whole = False
                    break
        if not whole:
            break
        raw = raw[1:-1].strip()
    return raw


def _split_top_level_equals(text: str) -> Optional[tuple[str, str]]:
    return _split_top_level_token(text, ("=",))


def _split_top_level_arrow(text: str) -> Optional[tuple[str, str]]:
    return _split_top_level_token(text, ("→", "->"))


def _split_top_level_and(text: str) -> Optional[tuple[str, str]]:
    return _split_top_level_token(text, ("∧", "/\\"))


def _split_top_level_commas(text: str) -> tuple[str, ...]:
    raw = str(text or "").strip()
    if not raw:
        return ()
    parts: list[str] = []
    start = 0
    depth = 0
    for index, ch in enumerate(raw):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            part = raw[start:index].strip()
            if part:
                parts.append(part)
            start = index + 1
    tail = raw[start:].strip()
    if tail:
        parts.append(tail)
    return tuple(parts)


def _split_top_level_additive_terms(text: str) -> tuple[str, ...]:
    raw = _unwrap_transparent_parens(str(text or "").strip())
    if not raw:
        return ()
    terms: list[str] = []
    start = 0
    depth = 0
    for index, ch in enumerate(raw):
        if ch in "([{":
            depth += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            continue
        if depth != 0 or ch not in "+-":
            continue
        if index == 0:
            continue
        prev = raw[index - 1]
        if ch == "-" and prev in "-<→":
            continue
        part = raw[start:index].strip()
        if part:
            terms.append(part)
        start = index
    tail = raw[start:].strip()
    if tail:
        terms.append(tail)
    return tuple(terms)


def _unwrap_trailing_power_one(text: str) -> str:
    raw = str(text or "").strip()
    match = re.fullmatch(r"\((.*)\)\s*\^\s*1", raw, flags=re.DOTALL)
    if match is None:
        return raw
    candidate = f"({match.group(1).strip()})"
    if _unwrap_transparent_parens(candidate) != match.group(1).strip():
        return raw
    return match.group(1).strip()


_MVPOLY_X_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])X\s*(?:\(\s*)?(\d+)(?:\s*\))?"
    r"\s*(?:\^\s*(\d+))?"
)


def _mvpoly_term_has_unknown_identifier(term: str) -> bool:
    residual = _MVPOLY_X_RE.sub("", str(term or ""))
    allowed_type_letters = set("ℤℕℚℝ")
    return any(ch.isalpha() and ch not in allowed_type_letters for ch in residual)


def _mvpoly_term_total_degree(term: str) -> Optional[int]:
    raw = str(term or "")
    if _mvpoly_term_has_unknown_identifier(raw):
        return None
    degree = 0
    saw_variable = False
    for match in _MVPOLY_X_RE.finditer(raw):
        saw_variable = True
        cursor = match.end()
        while cursor < len(raw) and raw[cursor].isspace():
            cursor += 1
        if cursor < len(raw) and raw[cursor] == "^" and match.group(2) is None:
            return None
        power = int(match.group(2) or "1")
        degree += power
    if "X" in raw and not saw_variable:
        return None
    return degree


def _mvpoly_expr_has_linear_term(expr: str) -> Optional[bool]:
    terms = _split_top_level_additive_terms(_unwrap_trailing_power_one(expr))
    if not terms:
        return None
    saw_known = False
    for term in terms:
        degree = _mvpoly_term_total_degree(term)
        if degree is None:
            return None
        saw_known = True
        if degree == 1:
            return True
    return False if saw_known else None


_SIMPLE_LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def _mvpoly_definition_map(statement: str) -> dict[str, str]:
    definitions: dict[str, str] = {}
    chunks, _body = _collect_leading_binder_chunks(statement)
    for chunk in chunks:
        _names, type_part = _binder_names_and_type(chunk)
        if not type_part:
            continue
        split = _split_top_level_equals(type_part)
        if split is None:
            continue
        lhs, rhs = split
        lhs = lhs.strip()
        rhs = rhs.strip()
        if _SIMPLE_LEAN_IDENT_RE.fullmatch(lhs) and "X" in rhs:
            definitions[lhs] = rhs
    return definitions


def _take_until_top_level_connector(text: str) -> str:
    raw = str(text or "")
    depth = 0
    index = 0
    while index < len(raw):
        ch = raw[index]
        if ch in "([{":
            depth += 1
            index += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            index += 1
            continue
        if depth == 0:
            if ch in "∧∨,":
                return raw[:index].strip()
            if raw.startswith("/\\", index) or raw.startswith("\\/", index):
                return raw[:index].strip()
            if raw.startswith("->", index) or raw.startswith("→", index):
                return raw[:index].strip()
        index += 1
    return raw.strip()


def _iter_aeval_image_targets(statement: str) -> tuple[tuple[str, tuple[str, ...]], ...]:
    raw = str(statement or "")
    targets: list[tuple[str, tuple[str, ...]]] = []
    marker = "aeval !["
    search_from = 0
    while True:
        start = raw.find(marker, search_from)
        if start == -1:
            break
        vector_start = start + len("aeval !")
        if vector_start >= len(raw) or raw[vector_start] != "[":
            search_from = start + len(marker)
            continue
        depth = 1
        cursor = vector_start + 1
        while cursor < len(raw) and depth > 0:
            if raw[cursor] == "[":
                depth += 1
            elif raw[cursor] == "]":
                depth -= 1
            cursor += 1
        if depth != 0:
            search_from = start + len(marker)
            continue
        vector = raw[vector_start + 1 : cursor - 1]
        vector_items = _split_top_level_commas(vector)
        eq_index = raw.find("=", cursor)
        if eq_index == -1:
            search_from = cursor
            continue
        target = _take_until_top_level_connector(raw[eq_index + 1 :])
        if target:
            targets.append((target, vector_items))
        search_from = cursor
    return tuple(targets)


def falsify_claim_by_structural_obstructions(
    statement: str,
) -> FiniteClaimSampleResult:
    """Reject answer-safe algebraic impossibilities before child proof spend.

    If every polynomial in an ``aeval ![...]`` source vector has zero linear
    part, then every polynomial in those source generators also has zero
    linear part. A target such as ``X 0 + X 1`` cannot lie in that image.
    This catches false inverse-generator bridge claims while staying
    conservative: unknown source definitions or unknown target degrees make the
    check inconclusive.
    """

    raw = str(statement or "").strip()
    if "MvPolynomial" not in raw or "aeval ![" not in raw or "X" not in raw:
        return FiniteClaimSampleResult(falsified=False)
    _leading_chunks, body = _collect_leading_binder_chunks(raw)
    body = _unwrap_transparent_parens(body)
    leading = _leading_quantifier(body)
    if leading is None or leading[0] != "∃":
        return FiniteClaimSampleResult(falsified=False)
    definitions = _mvpoly_definition_map(raw)
    for target, vector_items in _iter_aeval_image_targets(raw):
        if _mvpoly_expr_has_linear_term(target) is not True:
            continue
        source_exprs: list[str] = []
        all_sources_linear_free = True
        for item in vector_items:
            source = definitions.get(item.strip(), item.strip())
            has_linear = _mvpoly_expr_has_linear_term(source)
            if has_linear is not False:
                all_sources_linear_free = False
                break
            source_exprs.append(source)
        if not all_sources_linear_free or not source_exprs:
            continue
        detail = (
            "target has a degree-1 monomial but every aeval source generator "
            "has zero linear part"
        )
        return FiniteClaimSampleResult(
            falsified=True,
            reason=(
                "structural obstruction: an aeval image generated by "
                "linear-free MvPolynomial sources cannot contain the linear "
                f"target `{target}`"
            ),
            obstruction_kind="mvpoly_aeval_image_has_no_linear_terms",
            obstruction_detail=detail,
        )
    return FiniteClaimSampleResult(falsified=False)


def _split_top_level_conjunctive_obligation(text: str) -> Optional[tuple[str, str]]:
    """Split only when conjunction is the proposition's outer connective.

    In Lean precedence, ``A ∧ B → C`` is an implication whose antecedent is a
    conjunction, not a top-level pair of independent obligations. Sampling
    ``B → C`` alone can falsely reject a true implication when ``A`` is false.
    """

    if _split_top_level_arrow(text) is not None:
        return None
    return _split_top_level_and(text)


def _replace_unary_function_app(text: str, fn_name: str, fn_expr: str) -> str:
    raw = str(text or "")
    if not raw or not fn_name:
        return raw
    out: list[str] = []
    i = 0
    pattern = re.compile(_IDENT_RE_TEMPLATE.format(re.escape(fn_name)))
    while i < len(raw):
        match = pattern.search(raw, i)
        if match is None:
            out.append(raw[i:])
            break
        out.append(raw[i : match.start()])
        cursor = match.end()
        if cursor >= len(raw) or not raw[cursor].isspace():
            out.append(raw[match.start() : match.end()])
            i = cursor
            continue
        while cursor < len(raw) and raw[cursor].isspace():
            cursor += 1
        if cursor >= len(raw):
            out.append(raw[match.start() : cursor])
            i = cursor
            continue
        arg_start = cursor
        if raw[cursor] == "(":
            depth = 1
            cursor += 1
            while cursor < len(raw) and depth > 0:
                if raw[cursor] == "(":
                    depth += 1
                elif raw[cursor] == ")":
                    depth -= 1
                cursor += 1
            if depth != 0:
                out.append(raw[match.start() : cursor])
                i = cursor
                continue
        else:
            while cursor < len(raw) and (
                raw[cursor].isalnum() or raw[cursor] in "_'.«»"
            ):
                cursor += 1
        arg = raw[arg_start:cursor].strip()
        if not arg:
            out.append(raw[match.start() : cursor])
        else:
            out.append(f"(({fn_expr}) {arg})")
        i = cursor
    return "".join(out)


def _rewrite_postfix_factorials(text: str) -> str:
    raw = normalize_nat_factorial_notation(str(text or ""))
    i = 0
    while i < len(raw):
        if raw[i] != "!":
            i += 1
            continue
        expr_end = i
        while expr_end > 0 and raw[expr_end - 1].isspace():
            expr_end -= 1
        if expr_end <= 0 or raw[expr_end - 1] != ")":
            i += 1
            continue
        depth = 0
        expr_start: Optional[int] = None
        for cursor in range(expr_end - 1, -1, -1):
            ch = raw[cursor]
            if ch == ")":
                depth += 1
            elif ch == "(":
                depth -= 1
                if depth == 0:
                    expr_start = cursor
                    break
        if expr_start is None:
            i += 1
            continue
        expr = raw[expr_start:expr_end]
        replacement = f"(Nat.factorial {expr})"
        raw = raw[:expr_start] + replacement + raw[i + 1 :]
        i = expr_start + len(replacement)
    return raw


def _collect_leading_binder_chunks(statement: str) -> tuple[list[str], str]:
    chunks: list[str] = []
    current = str(statement or "").strip()
    while True:
        split = _first_forall_segment(current)
        if split is None:
            break
        segment, current = split
        chunks.extend(_binder_chunks(segment))
    return chunks, current


def instantiate_nat_sample_statement(
    statement: str,
    args: Sequence[int],
) -> Optional[str]:
    """Instantiate simple leading/nested Nat binders with concrete samples."""

    current = str(statement or "").strip()
    if not current:
        return None
    for raw_arg in args:
        let_split = _split_sample_let_body(current)
        if let_split is not None:
            prefix, body = let_split
            nested = instantiate_nat_sample_statement(body, [int(raw_arg)])
            if not nested:
                return None
            current = f"{prefix} {nested}".strip()
            continue

        split = _first_forall_chunk(current)
        if split is None:
            return None
        chunk, body = split
        binders, type_part, kind = _sampleable_nat_binder_names_and_kind(chunk)
        if not binders:
            return None
        binder = binders[0]
        sample_expr = _sample_expr_for_nat_kind(int(raw_arg), kind)
        replaced = _replace_freeish_identifier(body, binder, sample_expr).strip()
        if len(binders) > 1:
            remaining = " ".join(binders[1:])
            current = f"∀ ({remaining} : {type_part}), {replaced}"
        else:
            current = replaced
    return current


def _prop_forall_to_implication_prefix(statement: str) -> str:
    current = str(statement or "").strip()
    implications: list[str] = []
    while True:
        split = _first_forall_chunk(current)
        if split is None:
            break
        chunk, body = split
        names, type_part = _binder_names_and_type(chunk)
        if not names or not type_part:
            break
        if _sampleable_nat_kind(type_part):
            break
        if any(
            re.search(_IDENT_RE_TEMPLATE.format(re.escape(name)), body)
            for name in names
        ):
            break
        implications.append(f"({type_part})")
        current = body
    if not implications:
        return str(statement or "").strip()
    return " → ".join([*implications, current])


def _instantiate_nat_sample_statement_variants(
    statement: str,
    args: Sequence[int],
) -> list[str]:
    current = str(statement or "").strip()
    if not current:
        return []
    unwrapped = _unwrap_transparent_parens(current)
    if unwrapped != current:
        current = unwrapped

    let_split = _split_sample_let_body(current)
    if let_split is not None:
        prefix, body = let_split
        return [
            f"{prefix} {item}".strip()
            for item in _instantiate_nat_sample_statement_variants(body, args)
            if item
        ]

    if not args:
        current = _prop_forall_to_implication_prefix(current)
        and_split = _split_top_level_conjunctive_obligation(current)
        if and_split is not None:
            left, right = and_split
            return [
                *_instantiate_nat_sample_statement_variants(left, args),
                *_instantiate_nat_sample_statement_variants(right, args),
            ]
        return [] if _has_forall(current) else [current]

    split = _first_forall_chunk(current)
    if split is not None:
        chunk, body = split
        binders, type_part, kind = _sampleable_nat_binder_names_and_kind(chunk)
        if not binders:
            names, type_part = _binder_names_and_type(chunk)
            if (
                not names
                or not type_part
                or any(
                    re.search(_IDENT_RE_TEMPLATE.format(re.escape(name)), body)
                    for name in names
                )
            ):
                return []
            nested = _instantiate_nat_sample_statement_variants(body, args)
            prefixes = [f"({type_part})" for _name in names]
            return [
                " → ".join([*prefixes, item])
                for item in nested
                if item and not _has_forall(item)
            ]
        binder = binders[0]
        sample_expr = _sample_expr_for_nat_kind(int(args[0]), kind)
        replaced = _replace_freeish_identifier(body, binder, sample_expr).strip()
        if len(binders) > 1:
            remaining = " ".join(binders[1:])
            replaced = f"∀ ({remaining} : {type_part}), {replaced}"
        return _instantiate_nat_sample_statement_variants(replaced, args[1:])

    and_split = _split_top_level_conjunctive_obligation(current)
    if and_split is not None:
        left, right = and_split
        return [
            *_instantiate_nat_sample_statement_variants(left, args),
            *_instantiate_nat_sample_statement_variants(right, args),
        ]
    return []


def _function_definition_sample_statements(
    statement: str,
    sample_args: Sequence[Sequence[int]],
) -> list[tuple[tuple[int, ...], str]]:
    chunks, body = _collect_leading_binder_chunks(statement)
    if not chunks or not body:
        return []

    fn_name = ""
    rewritten_body = body
    for chunk in chunks:
        names, type_part = _binder_names_and_type(chunk)
        norm_type = _normalize_lean_type_text(type_part)
        if len(names) == 1 and norm_type in {"ℕ→ℕ", "ℕ->ℕ"} and not fn_name:
            fn_name = names[0]
            continue
    if not fn_name:
        return []

    arrow = _split_top_level_arrow(rewritten_body)
    if arrow is None:
        return []
    hypothesis, consequent = arrow
    hypothesis = _unwrap_transparent_parens(hypothesis)
    hyp_chunks, hyp_body = _collect_leading_binder_chunks(hypothesis)
    if len(hyp_chunks) != 1:
        return []
    hyp_names = _nat_binder_names(hyp_chunks[0])
    if len(hyp_names) != 1:
        return []
    hyp_var = hyp_names[0]
    equality = _split_top_level_equals(hyp_body)
    if equality is None:
        return []
    lhs, rhs = equality
    if re.sub(r"\s+", " ", lhs).strip() != f"{fn_name} {hyp_var}":
        return []
    fn_expr = f"fun {hyp_var} => {rhs.strip()}"

    concrete: list[tuple[tuple[int, ...], str]] = []
    for args in sample_args:
        sample_tuple = tuple(int(arg) for arg in args)
        if not sample_tuple:
            continue
        instantiated = instantiate_nat_sample_statement(consequent, sample_tuple)
        if not instantiated:
            continue
        replaced = _replace_unary_function_app(instantiated, fn_name, fn_expr).strip()
        if replaced and replaced != instantiated:
            concrete.append((sample_tuple, _rewrite_postfix_factorials(replaced)))
    return concrete


def _looks_sampleable(statement: str) -> bool:
    text = str(statement or "")
    if not text.strip():
        return False
    if "ℕ" not in text and "Nat" not in text:
        return False
    if not _has_forall(text) and not text.lstrip().startswith("let"):
        return False
    return any(
        token in text
        for token in ("=", "≠", "≤", "<", "≥", ">", "∣", "∤", "∈", "∉")
    )


def _safe_helper_blocks(helpers: Sequence[Any]) -> list[str]:
    seen: set[str] = set()
    blocks: list[str] = []
    for helper in helpers or ():
        raw: Any = helper
        if isinstance(helper, Mapping):
            raw = (
                helper.get("source")
                or helper.get("declaration")
                or helper.get("code")
                or raw
            )
        else:
            raw = getattr(helper, "source", None) or raw
        text = str(raw or "").strip()
        if not text or is_answer_unsafe_helper_source(text):
            continue
        name = helper_decl_name(text)
        if not name or name in seen:
            continue
        seen.add(name)
        blocks.append(text)
    return blocks


def default_nat_sample_args() -> tuple[tuple[int, ...], ...]:
    return (
        (0,),
        (1,),
        (2,),
        (3,),
        (4,),
        (5,),
        (7,),
        (11,),
        (1, 1),
        (2, 1),
        (1, 2),
        (2, 2),
        (0, 0),
        (0, 1),
        (1, 0),
        (2, 0),
        (0, 2),
        (3, 1),
        (1, 3),
        (0, 0, 0),
    )


def _leading_nat_binder_count(statement: str) -> int:
    return len(_leading_sampleable_nat_binder_kinds(statement))


def _leading_sampleable_nat_binder_kinds(statement: str) -> tuple[str, ...]:
    chunks, _body = _collect_leading_binder_chunks(statement)
    kinds: list[str] = []
    for chunk in chunks:
        names, _type_part, kind = _sampleable_nat_binder_names_and_kind(chunk)
        kinds.extend(kind for _name in names)
    return tuple(kinds)


def _prioritized_bit_nat_samples(arity: int) -> tuple[tuple[int, ...], ...]:
    if arity <= 0:
        return ()
    samples: list[tuple[int, ...]] = [
        (0,) * arity,
        (1,) * arity,
    ]
    if arity > 1:
        samples.extend(
            (
                (1,) + (0,) * (arity - 1),
                (0,) + (1,) * (arity - 1),
            )
        )
    if arity > 2:
        tail = arity - 1
        left = tail // 2
        right = tail - left
        samples.extend(
            (
                (1,) + (0,) * left + (1,) * right,
                (1,) + (1,) * left + (0,) * right,
                (0,) + (1,) * left + (0,) * right,
                (0,) + (0,) * left + (1,) * right,
            )
        )
    if arity > 1:
        alternating = tuple(index % 2 for index in range(arity))
        samples.extend(
            (
                alternating,
                tuple(1 - bit for bit in alternating),
            )
        )
    return tuple(dict.fromkeys(samples))


def _prioritized_positive_nat_samples(arity: int) -> tuple[tuple[int, ...], ...]:
    if arity <= 0:
        return ()
    samples: list[tuple[int, ...]] = [
        (1,) * arity,
        (2,) + (1,) * (arity - 1),
    ]
    if arity > 1:
        samples.extend(
            (
                (1, 2) + (1,) * (arity - 2),
                (2, 2) + (1,) * (arity - 2),
                (3, 1) + (1,) * (arity - 2),
                (1, 3) + (1,) * (arity - 2),
            )
        )
    else:
        samples.extend(((2,), (3,)))
    return tuple(dict.fromkeys(samples))


def _statement_nat_sample_args(
    statement: str,
    sample_args: Sequence[Sequence[int]],
    *,
    max_generated_arity: int = 6,
    prioritize_generated: bool = True,
    max_checks: Optional[int] = None,
) -> tuple[tuple[int, ...], ...]:
    """Add exhaustive 0/1 samples matching the visible Nat-binder arity.

    The fixed default samples keep cheap unary/binary smoke coverage.  Higher
    arity mistakes are better covered by deriving the arity from the claim
    itself instead of hard-coding any problem-shaped tuple.
    """

    binder_kinds = _leading_sampleable_nat_binder_kinds(statement)
    arity = len(binder_kinds)
    provided_samples = [tuple(int(x) for x in args) for args in (sample_args or ())]
    generated_samples: list[tuple[int, ...]] = []
    if "pnat" in binder_kinds:
        generated_samples.extend(_prioritized_positive_nat_samples(arity))
    if arity > 0:
        generated_samples.extend(_prioritized_bit_nat_samples(arity))
    if 0 < arity <= max_generated_arity:
        generated_samples.extend(
            tuple(int(x) for x in args) for args in product((0, 1), repeat=arity)
        )
    reserve_generated = 0
    if generated_samples and max_checks:
        reserve_generated = min(
            len(generated_samples),
            max(1, int(max_checks) // 2),
        )
    if prioritize_generated or arity >= 3 or (
        reserve_generated
        and len(provided_samples) > max(0, int(max_checks or 0) - reserve_generated)
    ):
        samples = [*generated_samples, *provided_samples]
    else:
        samples = [*provided_samples, *generated_samples]
    seen: set[tuple[int, ...]] = set()
    deduped: list[tuple[int, ...]] = []
    for args in samples:
        if args in seen:
            continue
        seen.add(args)
        deduped.append(args)
    return tuple(deduped)


async def _lean_check_negation(
    lean: Any,
    statement: str,
    preamble: str,
    lemmas: Sequence[str],
    *,
    timeout_s: float,
) -> Any:
    check = getattr(lean, "check", None)
    if check is None:
        raise AttributeError("lean object has no async check(...) method")
    kwargs = {
        "preamble_override": str(preamble or ""),
        "timeout_s": float(timeout_s),
        "fast_fail_timeout_s": min(float(timeout_s), max(1.0, float(timeout_s) / 3.0)),
        "check_kind": "mini_claim_sample_falsifier",
    }
    try:
        sig = inspect.signature(check)
        params = sig.parameters
        if not any(p.kind == inspect.Parameter.VAR_KEYWORD for p in params.values()):
            kwargs = {key: value for key, value in kwargs.items() if key in params}
    except (TypeError, ValueError):
        pass
    result = check(
        f"¬ ({statement})",
        "by\n  first\n  | decide +kernel\n  | native_decide\n  | norm_num",
        list(lemmas),
        **kwargs,
    )
    if inspect.isawaitable(result):
        return await result
    return result


async def falsify_claim_by_nat_samples(
    lean: Any,
    *,
    statement: str,
    preamble: str,
    helpers: Sequence[Any] = (),
    timeout_s: float = 8.0,
    sample_args: Sequence[Sequence[int]] = (),
    max_checks: int = 8,
) -> FiniteClaimSampleResult:
    """Try to refute a helper claim by small Nat instantiations.

    ``falsified=True`` means Lean proved the negation of one concrete instance.
    ``falsified=False`` is only inconclusive; callers must continue normal
    proof search unless they receive a positive refutation.
    """

    if not _looks_sampleable(statement):
        return FiniteClaimSampleResult(falsified=False)
    if looks_like_dangerous_nat_pow_tower(statement):
        return FiniteClaimSampleResult(
            falsified=False,
            skipped=True,
            skip_reason=DANGEROUS_NAT_POW_TOWER_REASON,
        )
    samples = _statement_nat_sample_args(
        statement,
        sample_args or default_nat_sample_args(),
        prioritize_generated=not bool(sample_args),
        max_checks=max_checks,
    )
    lemmas = _safe_helper_blocks(helpers)
    attempts: list[FiniteClaimSampleAttempt] = []
    per_check_timeout = max(1.0, min(float(timeout_s or 8.0), 8.0))
    concrete_samples = _function_definition_sample_statements(statement, samples)
    if not concrete_samples:
        concrete_samples = []
        seen_concrete: set[str] = set()
        for args in samples:
            variants = _instantiate_nat_sample_statement_variants(statement, args)
            if not variants:
                fallback = instantiate_nat_sample_statement(statement, args)
                variants = [fallback] if fallback and not _has_forall(fallback) else []
            for concrete in variants:
                if not concrete or concrete in seen_concrete:
                    continue
                seen_concrete.add(concrete)
                concrete_samples.append((args, _rewrite_postfix_factorials(concrete)))
    for args, concrete in concrete_samples[: max(1, int(max_checks or 1))]:
        if not concrete or concrete == str(statement or "").strip():
            continue
        started = time.monotonic()
        try:
            result = await _lean_check_negation(
                lean,
                concrete,
                preamble,
                lemmas,
                timeout_s=per_check_timeout,
            )
            output = str(getattr(result, "output", "") or "")
            ok = bool(getattr(result, "ok", False))
            attempt = FiniteClaimSampleAttempt(
                args=tuple(args),
                statement=concrete,
                ok=ok,
                elapsed_s=round(time.monotonic() - started, 3),
                output_preview=output[:800],
            )
        except Exception as exc:
            attempt = FiniteClaimSampleAttempt(
                args=tuple(args),
                statement=concrete,
                ok=False,
                elapsed_s=round(time.monotonic() - started, 3),
                output_preview="",
                exception=f"{type(exc).__name__}: {exc}",
            )
        attempts.append(attempt)
        if attempt.ok:
            return FiniteClaimSampleResult(
                falsified=True,
                attempts=tuple(attempts),
                reason=f"sample args {tuple(args)} refuted the claim",
            )
    return FiniteClaimSampleResult(falsified=False, attempts=tuple(attempts))


__all__ = [
    "FiniteClaimSampleAttempt",
    "FiniteClaimSampleResult",
    "default_nat_sample_args",
    "falsify_claim_by_nat_samples",
    "instantiate_nat_sample_statement",
]
