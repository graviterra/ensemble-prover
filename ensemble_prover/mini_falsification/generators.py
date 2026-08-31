"""Lean-surface binder parsing and deterministic witness generation.

This is deliberately a conservative surface parser.  Unsupported syntax is
reported as such; it is never guessed into a proof-search mutation.
"""

from __future__ import annotations

import itertools
import json
import re
from dataclasses import dataclass
from typing import Iterable, Sequence

from ..falsification_cursor_identity import (
    RIGHT_PI_PRESERVED_CANDIDATE_MAX_BYTES,
)
from ..finite_claim_check import (
    _binder_names_and_type,
    _collect_leading_binder_chunks,
    _first_forall_chunk,
    _split_top_level_arrow,
    _split_top_level_equals,
    _split_top_level_token,
    _unwrap_transparent_parens,
)


@dataclass(frozen=True)
class VisibleBinder:
    name: str
    type_text: str


@dataclass(frozen=True)
class GraphCarrier:
    """A conservatively resolved finite carrier for ``SimpleGraph``.

    ``vertex_type`` deliberately preserves the surface type used by the
    statement.  In particular, a local ``abbrev V := Fin 4`` is instantiated
    with vertices of type ``V`` rather than silently rewriting the theorem.
    """

    vertex_type: str
    vertex_terms: tuple[str, ...]
    order: int
    source: str


@dataclass(frozen=True)
class FunctionSpineInstantiation:
    """One closed witness assignment along a proposition's right spine.

    Quantifiers inside implication antecedents remain untouched.  This is
    important for hypotheses such as ``∀ x ∈ s, 0 ≤ f x``: they are
    assumptions that a concrete function must actually satisfy, not values
    the falsifier may silently sample away.
    """

    concrete_statement: str
    witness_terms: tuple[str, ...]
    application_arguments: tuple[str, ...]
    hypothesis_names: tuple[str, ...]


@dataclass(frozen=True)
class RightPiSlot:
    """One Lean-confirmed slot in the outer proposition telescope."""

    kind: str
    name: str
    type_text: str
    lean_type_text: str = ""
    proof_alias: str = ""


@dataclass(frozen=True)
class RightPiPlan:
    slots: tuple[RightPiSlot, ...]
    conclusion: str


@dataclass(frozen=True)
class RightPiInstantiation:
    concrete_statement: str
    witness_terms: tuple[str, ...]
    application_arguments: tuple[str, ...]
    hypothesis_names: tuple[str, ...]
    proof_aliases: tuple[str, ...]
    dependency_closure_complete: bool = True


_LEAN_ASCII_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def _fresh_right_pi_proof_aliases(
    statement: str,
    count: int,
) -> tuple[str, ...]:
    """Allocate deterministic proof names outside the source identifier set."""

    used = set(_LEAN_ASCII_IDENTIFIER_RE.findall(str(statement or "")))
    aliases: list[str] = []
    for index in range(max(0, int(count))):
        stem = f"h_mini_right_pi_{index}"
        candidate = stem
        suffix = 0
        while candidate in used:
            suffix += 1
            candidate = f"{stem}_{suffix}"
        used.add(candidate)
        aliases.append(candidate)
    return tuple(aliases)


def leading_forall_binders(statement: str) -> tuple[tuple[VisibleBinder, ...], str]:
    chunks, body = _collect_leading_binder_chunks(str(statement or ""))
    binders: list[VisibleBinder] = []
    for chunk in chunks:
        names, type_text = _binder_names_and_type(chunk)
        if not names or not type_text:
            return (), str(statement or "").strip()
        binders.extend(VisibleBinder(name, type_text.strip()) for name in names)
    return tuple(binders), body


def instantiate_binders(
    statement: str,
    witness_terms: Sequence[str],
) -> str:
    binders, body = leading_forall_binders(statement)
    if not binders or len(binders) != len(witness_terms):
        return ""
    # Apply a typed lambda instead of rewriting identifiers in Lean source.
    # This delegates lexical scoping to Lean itself: body-local `fun`/`let`
    # binders cannot be captured, and witness terms may safely introduce their
    # own binder names (as generated graph relations do).
    lambda_binders = " ".join(
        f"({binder.name} : {binder.type_text})" for binder in binders
    )
    arguments = " ".join(f"({witness})" for witness in witness_terms)
    return f"((fun {lambda_binders} => {body}) {arguments})"


def normalize_type(type_text: str) -> str:
    return (
        re.sub(r"\s+", "", str(type_text or ""))
        .replace("Nat", "ℕ")
        .replace("Int", "ℤ")
        .replace("Real", "ℝ")
        .replace("Complex", "ℂ")
    )


def binder_domain(type_text: str) -> str:
    compact = normalize_type(type_text)
    if compact == "ℕ":
        return "nat"
    if compact in {"ℕ+", "PNat"}:
        return "pnat"
    if compact == "ℤ":
        return "int"
    if compact in {"ℚ", "Rat"}:
        return "rat"
    if compact == "ℝ":
        return "real"
    if compact == "ℂ":
        return "complex"
    if compact == "Bool":
        return "bool"
    if re.fullmatch(r"Fin\(?[0-9]+\)?", compact):
        return "fin"
    if re.fullmatch(r"SimpleGraph\(Fin\(?[0-9]+\)?\)", compact):
        return "graph_fin"
    if compact in {"SimpleGraphBool", "SimpleGraph(Bool)"}:
        return "graph_bool"
    # These are data/typeclass carriers even when their parameters contain a
    # relation.  The old catch-all relation regex classified all of them as
    # propositions and generated tactic proofs where Lean expected data.
    if re.match(
        r"^(?:Finset|Set|List|Multiset|Decidable)(?:\(|[A-Za-zℕℤℚℝℂ{])",
        compact,
    ) or compact.startswith("{"):
        return ""
    # Dependent proposition binders such as ``(hij : i <= j)`` are proof
    # arguments, not data domains.  Recognition stays deliberately
    # conservative; generated inhabitants still have to elaborate in Lean and
    # a full negation must pass the certificate/axiom boundary.
    proposition_surface = _unwrap_transparent_parens(str(type_text or "").strip())
    if (
        proposition_surface in {"True", "False"}
        or proposition_surface.startswith(("not ", "Not ", "!", "¬"))
        or re.search(r"(?:!=|<=|>=|=|<|>|≠|≤|≥|∈|∉|∧|∨|↔)", proposition_surface)
    ):
        return "prop"
    return ""


def function_binder_domain(type_text: str) -> str:
    """Return the supported closed unary-function domain, or ``""``.

    Only endofunctions over audited scalar carriers are synthesized.  More
    general dependent/function types remain unsupported rather than being
    guessed from surface syntax.
    """

    compact = normalize_type(_unwrap_transparent_parens(str(type_text or ""))).replace(
        "->", "→"
    )
    return {
        "ℕ→ℕ": "nat_function",
        "ℤ→ℤ": "int_function",
        "ℚ→ℚ": "rat_function",
        "ℝ→ℝ": "real_function",
    }.get(compact, "")


def deterministic_function_terms(domain: str) -> tuple[str, ...]:
    """Small closed function family used only to seek Lean replay candidates."""

    scalar = {
        "nat_function": "ℕ",
        "int_function": "ℤ",
        "rat_function": "ℚ",
        "real_function": "ℝ",
    }.get(str(domain or ""), "")
    if not scalar:
        return ()
    terms = [
        f"(fun x : {scalar} => x)",
        f"(fun _ : {scalar} => (0 : {scalar}))",
        f"(fun _ : {scalar} => (1 : {scalar}))",
        f"(fun x : {scalar} => x + 1)",
    ]
    if domain != "nat_function":
        terms.append(f"(fun x : {scalar} => -x)")
    return tuple(terms)


def _function_domain_scalar_type(domain: str) -> str:
    return {
        "nat_function": "ℕ",
        "int_function": "ℤ",
        "rat_function": "ℚ",
        "real_function": "ℝ",
    }.get(str(domain or ""), "")


def _bounded_membership_binder(chunk: str) -> tuple[str, str]:
    """Parse only Lean's conservative ``x ∈ set`` bounded-binder surface."""

    match = re.fullmatch(
        r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*∈\s*(.+?)\s*",
        str(chunk or ""),
        flags=re.DOTALL,
    )
    if match is None:
        return "", ""
    return match.group(1), match.group(2).strip()


def surface_right_pi_slots(statement: str) -> tuple[tuple[RightPiSlot, ...], str]:
    """Parse the outer Pi/implication spine without guessing binder sorts.

    Sorts are filled as ``"unknown"`` here and must normally be replaced by
    Lean's ``isProp`` result.  Bounded membership syntax is expanded before the
    generic binder parser, avoiding the latter's token-level misparse.
    """

    current = str(statement or "").strip()
    slots: list[RightPiSlot] = []
    hypothesis_index = 0
    # The surface pass does not yet know which explicit binders are Props, but
    # every synthetically introduced proof binder must already be fresh
    # against the complete source.  ``right_pi_plan`` re-allocates across all
    # Lean-classified proof slots once their sorts are known.
    while current:
        unwrapped = _unwrap_transparent_parens(current)
        split = _first_forall_chunk(unwrapped)
        if split is not None:
            chunk, current = split
            if str(chunk or "").lstrip().startswith(("{", "[", "⦃")):
                return (), str(statement or "").strip()
            bounded_name, bounded_set = _bounded_membership_binder(chunk)
            if bounded_name and bounded_set:
                proof_alias = _fresh_right_pi_proof_aliases(
                    statement, hypothesis_index + 1
                )[-1]
                # Lean elaborates ``∀ x ∈ s, P`` as a data Pi followed by
                # a proof Pi.  Its data type is inferred by Lean; the surface
                # placeholder is replaced from the contract analysis below.
                slots.append(RightPiSlot("unknown", bounded_name, ""))
                slots.append(
                    RightPiSlot(
                        "proof",
                        proof_alias,
                        f"{bounded_name} ∈ {bounded_set}",
                        proof_alias=proof_alias,
                    )
                )
                hypothesis_index += 1
                continue
            names, type_text = _binder_names_and_type(chunk)
            if not names or not type_text:
                return (), str(statement or "").strip()
            for name in names:
                slots.append(RightPiSlot("unknown", name, type_text.strip()))
            continue
        arrow = _split_top_level_arrow(unwrapped)
        if arrow is None:
            return tuple(slots), unwrapped
        hypothesis, current = arrow
        proof_alias = _fresh_right_pi_proof_aliases(statement, hypothesis_index + 1)[-1]
        slots.append(
            RightPiSlot(
                "proof",
                proof_alias,
                hypothesis.strip(),
                proof_alias=proof_alias,
            )
        )
        hypothesis_index += 1
    return (), str(statement or "").strip()


def right_pi_plan(
    statement: str,
    *,
    binder_sorts: Sequence[str],
    binder_types: Sequence[str] = (),
    binder_normalized_types: Sequence[str] = (),
) -> RightPiPlan | None:
    """Join the surface telescope with Lean-authoritative binder sorts."""

    surface_slots, conclusion = surface_right_pi_slots(statement)
    sorts = tuple(str(item or "").strip().lower() for item in binder_sorts)
    types = tuple(str(item or "").strip() for item in binder_types)
    normalized_types = tuple(
        str(item or "").strip() for item in binder_normalized_types
    )
    if (
        not surface_slots
        or len(surface_slots) > 64
        or sum(item == "proof" for item in sorts) > 32
        or len(surface_slots) != len(sorts)
        or any(item not in {"data", "proof"} for item in sorts)
        or (types and len(types) != len(surface_slots))
        or (normalized_types and len(normalized_types) != len(surface_slots))
    ):
        return None
    slots: list[RightPiSlot] = []
    proof_aliases = iter(
        _fresh_right_pi_proof_aliases(
            statement,
            sum(item == "proof" for item in sorts),
        )
    )
    for index, (surface, sort) in enumerate(zip(surface_slots, sorts)):
        type_text = surface.type_text or (types[index] if types else "")
        if not type_text:
            return None
        proof_alias = next(proof_aliases) if sort == "proof" else ""
        # Arrow and bounded-membership proof slots have no source binder name;
        # use their fresh alias as the binder.  Explicit proof Pi binders keep
        # their source name so dependent types and the conclusion retain the
        # original lexical scope, while ``proof_alias`` controls ``intro``.
        name = (
            proof_alias if sort == "proof" and surface.kind == "proof" else surface.name
        )
        lean_type_text = (
            normalized_types[index]
            if normalized_types
            else types[index]
            if types
            else type_text
        )
        slots.append(
            RightPiSlot(
                sort,
                name,
                type_text,
                lean_type_text,
                proof_alias=proof_alias,
            )
        )
    return RightPiPlan(tuple(slots), conclusion)


def right_pi_witness_terms(type_text: str, *, statement: str = "") -> tuple[str, ...]:
    """Return a small closed catalogue for one audited data-binder type."""

    function_domain = function_binder_domain(type_text)
    if function_domain:
        return deterministic_function_terms(function_domain)
    domain = binder_domain(type_text)
    scalar = deterministic_terms(domain, type_text)
    if scalar:
        return scalar
    compact = normalize_type(_unwrap_transparent_parens(type_text))
    if compact in {"Finsetℕ", "Finset(ℕ)"}:
        # Put statement-derived boundary sets before generic singletons.  The
        # triple is a general small consecutive-boundary probe and catches
        # assumptions whose aggregate threshold needs more than one element.
        numerals = [
            int(item)
            for item in re.findall(r"(?<![A-Za-z0-9_'])[0-9]+", statement)
            if len(item) <= 6
        ]
        lower = min((value for value in numerals if value >= 2), default=3)
        boundary = f"({{{lower}, {lower + 1}, {lower + 2}}} : Finset ℕ)"
        return tuple(
            dict.fromkeys(
                (
                    "(∅ : Finset ℕ)",
                    "({3, 4, 5} : Finset ℕ)",
                    boundary,
                    "({0} : Finset ℕ)",
                    "({1} : Finset ℕ)",
                    "({0, 1} : Finset ℕ)",
                )
            )
        )
    return ()


def _parenthesized_witness_term(term: str) -> str:
    clean = str(term or "").strip()
    if not clean:
        return ""
    if _unwrap_transparent_parens(clean) != clean:
        return clean
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+", clean):
        return clean
    return f"({clean})"


def _exact_unary_function_application(
    expression: str,
    *,
    function_name: str,
    argument_name: str,
) -> bool:
    """Recognize only ``f x``/``f (x)`` for two exact source binders."""

    clean = _unwrap_transparent_parens(str(expression or "").strip())
    function = re.escape(str(function_name or "").strip())
    argument = re.escape(str(argument_name or "").strip())
    if not clean or not function or not argument:
        return False
    return bool(
        re.fullmatch(
            rf"{function}\s+(?:{argument}|\(\s*{argument}\s*\))",
            clean,
            flags=re.DOTALL,
        )
    )


def _identifier_occurs(expression: str, identifier: str) -> bool:
    name = str(identifier or "").strip()
    if not name:
        return False
    source = _lean_lexical_code_view(str(expression or ""))
    return bool(
        re.search(
            rf"(?<![\w'.]){re.escape(name)}(?![\w'])",
            source,
            flags=re.UNICODE,
        )
    )


def _lean_lexical_code_view(expression: str) -> str:
    """Mask Lean comments and strings while preserving source offsets."""

    source = str(expression or "")
    chars = list(source)
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        if block_depth:
            if source.startswith("/-", index):
                chars[index : index + 2] = "  "
                block_depth += 1
                index += 2
                continue
            if source.startswith("-/", index):
                chars[index : index + 2] = "  "
                block_depth -= 1
                index += 2
                continue
            if source[index] != "\n":
                chars[index] = " "
            index += 1
            continue
        if in_string:
            if source[index] != "\n":
                chars[index] = " "
            if escaped:
                escaped = False
            elif source[index] == "\\":
                escaped = True
            elif source[index] == '"':
                in_string = False
            index += 1
            continue
        if source.startswith("/-", index):
            chars[index : index + 2] = "  "
            block_depth = 1
            index += 2
            continue
        if source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                chars[index] = " "
                index += 1
            continue
        if source[index] == '"':
            chars[index] = " "
            in_string = True
            index += 1
            continue
        index += 1
    return "".join(chars)


def _outer_lambda_binds_identifier(expression: str, identifier: str) -> bool:
    """Recognize a source identifier shadowed by the outermost lambda.

    This is a conservative surface fallback. The returned witness is still
    elaborated by Lean, and any shape we cannot identify falls back to the
    complete generic catalogue.
    """

    split = _split_top_level_token(
        _unwrap_transparent_parens(str(expression or "").strip()),
        ("=>",),
    )
    if split is None:
        return False
    head, _body = split
    raw_binders = str(head or "").strip()
    if not raw_binders.startswith("fun "):
        return False
    raw_binders = raw_binders[4:].strip()
    groups = re.findall(r"[({⦃]([^(){}⦃⦄]*)[)}⦄]", raw_binders)
    for group in groups:
        names, _type_text = _binder_names_and_type(group)
        if identifier in names:
            return True
        if ":" not in group and identifier in re.findall(
            r"(?:[^\W\d]|_)[\w']*",
            group,
            re.UNICODE,
        ):
            # Lean pattern lambdas such as ``fun (x, y) =>`` bind every
            # identifier in the pattern.  Their exact pattern is still
            # elaborated by Lean before any candidate can gain authority.
            return True
    # Remove grouped binders, then collect every unparenthesized name before
    # the shared type annotation (``fun x y : ℕ =>``). Lean identifiers are
    # Unicode, so an ASCII-only regex silently loses common names such as g₁.
    ungrouped = re.sub(r"[({⦃][^(){}⦃⦄]*[)}⦄]", " ", raw_binders)
    names_text = ungrouped.split(":", 1)[0]
    if "∈" in names_text:
        names_text = names_text.split("∈", 1)[0]
    identifier_pattern = r"(?:[^\W\d]|_)[\w']*"
    return identifier in re.findall(identifier_pattern, names_text, re.UNICODE)


def _shadowed_identifier_spans(
    expression: str,
    identifier: str,
) -> tuple[tuple[int, int], ...]:
    """Return simple Lean lambda/let regions where ``identifier`` is bound.

    This is deliberately a small lexical scope recognizer, not an elaborator.
    It handles the term shapes admitted by premise mining while Lean remains
    the final type/semantic checker. Unknown syntax is left unshadowed, which
    may cost one optional candidate but cannot invent authority.
    """

    source = _lean_lexical_code_view(str(expression or ""))
    name = str(identifier or "").strip()
    if not source or not name:
        return ()
    depths = [0] * (len(source) + 1)
    stack: list[str] = []
    matching = {")": "(", "]": "[", "}": "{"}
    for index, character in enumerate(source):
        depths[index] = len(stack)
        if character in "([{":
            stack.append(character)
        elif character in matching and stack and stack[-1] == matching[character]:
            stack.pop()
    depths[len(source)] = len(stack)

    def scope_end(start: int, base_depth: int) -> int:
        for position in range(start, len(source)):
            if source[position] in ")] }".replace(" ", "") and depths[position] == base_depth:
                return position
        return len(source)

    spans: list[tuple[int, int]] = []
    lambda_pattern = re.compile(r"(?<![\w'])(?:fun|λ)(?![\w'])", re.UNICODE)
    for match in lambda_pattern.finditer(source):
        base_depth = depths[match.start()]
        end = scope_end(match.end(), base_depth)
        arrow = -1
        for position in range(match.end(), max(match.end(), end - 1)):
            if source.startswith("=>", position) and depths[position] == base_depth:
                arrow = position
                break
        if arrow < 0:
            continue
        header = source[match.end() : arrow]
        if not _outer_lambda_binds_identifier(
            f"fun {header.strip()} => _",
            name,
        ):
            continue
        declaration = re.search(
            rf"(?<![\w']){re.escape(name)}(?![\w'])",
            header,
            flags=re.UNICODE,
        )
        if declaration is not None:
            spans.append(
                (
                    match.end() + declaration.start(),
                    match.end() + declaration.end(),
                )
            )
        spans.append((arrow + 2, end))

    quantifier_pattern = re.compile(
        r"(?<![\w'])(?:∀|∃|forall|exists)(?![\w'])",
        re.UNICODE,
    )
    for match in quantifier_pattern.finditer(source):
        base_depth = depths[match.start()]
        end = scope_end(match.end(), base_depth)
        comma = -1
        for position in range(match.end(), end):
            if source[position] == "," and depths[position] == base_depth:
                comma = position
                break
        if comma < 0:
            continue
        header = source[match.end() : comma]
        if not _outer_lambda_binds_identifier(
            f"fun {header.strip()} => _",
            name,
        ):
            continue
        declaration = re.search(
            rf"(?<![\w'.]){re.escape(name)}(?![\w'])",
            header,
            flags=re.UNICODE,
        )
        if declaration is not None:
            spans.append(
                (
                    match.end() + declaration.start(),
                    match.end() + declaration.end(),
                )
            )
        spans.append((comma + 1, end))

    # Match-alternative patterns introduce locals over the corresponding
    # branch body. Admitting a conservative extra local here can only cause an
    # optional candidate to be Lean-rejected; missing a real pattern binder
    # can suppress the only premise-mined witness.
    if re.search(r"(?<![\w'])match(?![\w'])", source):
        branch_pattern = re.compile(r"\|([^|]*?)=>", re.DOTALL)
        for match in branch_pattern.finditer(source):
            header = match.group(1)
            declaration = re.search(
                rf"(?<![\w'.]){re.escape(name)}(?![\w'])",
                header,
                flags=re.UNICODE,
            )
            if declaration is None:
                continue
            next_branch = source.find("|", match.end())
            branch_end = next_branch if next_branch >= 0 else len(source)
            spans.append(
                (
                    match.start(1) + declaration.start(),
                    match.start(1) + declaration.end(),
                )
            )
            spans.append((match.end(), branch_end))

    let_pattern = re.compile(
        rf"(?<![\w'])let\s+({re.escape(name)})(?![\w'])",
        re.UNICODE,
    )
    for match in let_pattern.finditer(source):
        base_depth = depths[match.start()]
        end = scope_end(match.end(), base_depth)
        let_line_start = source.rfind("\n", 0, match.start()) + 1
        let_indent = len(
            source[let_line_start : match.start()].expandtabs(4)
        )
        assignment = -1
        for position in range(match.end(), max(match.end(), end - 1)):
            if source.startswith(":=", position) and depths[position] == base_depth:
                assignment = position
                break
        if assignment < 0:
            continue
        body_start = -1
        assignment_line_end = source.find("\n", assignment + 2, end)
        inline_assignment = bool(
            source[
                assignment + 2 : (
                    assignment_line_end
                    if assignment_line_end >= 0
                    else end
                )
            ].strip()
        )
        initializer_indent: int | None = None
        for position in range(assignment + 2, end):
            if source[position] == ";" and depths[position] == base_depth:
                body_start = position + 1
                break
            if (
                source.startswith("in", position)
                and depths[position] == base_depth
                and (position == 0 or not re.match(r"[\w']", source[position - 1]))
                and (
                    position + 2 >= len(source)
                    or not re.match(r"[\w']", source[position + 2])
                )
            ):
                body_start = position + 2
                break
            if source[position] == "\n" and depths[position] == base_depth:
                next_line = position + 1
                while next_line < end:
                    line_end = source.find("\n", next_line, end)
                    if line_end < 0:
                        line_end = end
                    line = source[next_line:line_end]
                    if line.strip():
                        indentation = len(line) - len(line.lstrip(" \t"))
                        indentation = len(line[:indentation].expandtabs(4))
                        if not inline_assignment and initializer_indent is None:
                            initializer_indent = indentation
                        elif (
                            inline_assignment and indentation <= let_indent
                        ) or (
                            not inline_assignment
                            and initializer_indent is not None
                            and indentation <= initializer_indent
                        ):
                            body_start = next_line + len(line) - len(
                                line.lstrip(" \t")
                            )
                        break
                    next_line = line_end + 1
                if body_start >= 0:
                    break
        if body_start < 0:
            continue
        spans.append((match.start(1), match.end(1)))
        spans.append((body_start, end))
    return tuple(spans)


def _identifier_occurs_free(expression: str, identifier: str) -> bool:
    source = _lean_lexical_code_view(str(expression or ""))
    name = str(identifier or "").strip()
    if not _identifier_occurs(source, name):
        return False
    shadowed = _shadowed_identifier_spans(source, name)
    for match in re.finditer(
        rf"(?<![\w'.]){re.escape(name)}(?![\w'])",
        source,
        flags=re.UNICODE,
    ):
        if not any(start <= match.start() and match.end() <= end for start, end in shadowed):
            return True
    return False


def _right_pi_dependency_analysis_is_uncertain(term: str) -> bool:
    """Flag binding syntax the bounded surface scope recognizer cannot prove."""

    code = _lean_lexical_code_view(str(term or ""))
    return bool(
        re.search(r"(?<![\w'])(?:by|do)(?![\w'])", code, re.UNICODE)
        or re.search(r"(?<![\w'])(?:fun|λ)\s*\|", code, re.UNICODE)
        or re.search(r"(?<![\w'])match(?![\w'])", code, re.UNICODE)
        or re.search(r"(?<![\w'])let(?![\w'])", code, re.UNICODE)
        or re.search(
            r"(?<![\w'])(?:if|dite)\s+(?:[^\W\d]|_)[\w']*\s*:",
            code,
            re.UNICODE,
        )
        # These are binder-bearing Lean surfaces that the deliberately small
        # scanner above does not elaborate.  Treating their bound names as
        # telescope dependencies can manufacture a false data cycle and skip
        # the only mined witness.  The uncertain path keeps a bounded raw
        # candidate and lets Lean decide instead.
        or "↦" in code
        or any(symbol in code for symbol in ("∑", "∏", "⋃", "⋂", "∫"))
    )


def _right_pi_term_mentions_dependency(term: str, name: str) -> bool:
    """Conservatively retain dependencies for syntax with uncertain scope."""

    return (
        _identifier_occurs(term, name)
        if _right_pi_dependency_analysis_is_uncertain(term)
        else _identifier_occurs_free(term, name)
    )


def _is_bare_top_level_equality(expression: str) -> bool:
    clean = _unwrap_transparent_parens(str(expression or "").strip())
    if not clean or _split_top_level_equals(clean) is None:
        return False
    return _split_top_level_token(
        clean,
        ("→", "->", "↔", "<->", "∧", "/\\", "∨", "\\/"),
    ) is None


def _simplify_unused_tactic_have_witness(term: str) -> str:
    """Erase one definitionally irrelevant ``have`` before an exact term."""

    clean = _unwrap_transparent_parens(str(term or "").strip())
    split = _split_top_level_token(clean, ("=>",))
    if split is None:
        return str(term or "").strip()
    lambda_head, body = split
    if not str(lambda_head or "").strip().startswith(("fun ", "λ ")):
        return str(term or "").strip()
    commands = _split_top_level_token(str(body or "").strip(), (";",))
    if commands is None:
        return str(term or "").strip()
    have_command, exact_command = (str(item or "").strip() for item in commands)
    have_match = re.fullmatch(
        r"by\s+have\s+((?:[^\W\d]|_)[\w']*)\b.*?:=.*",
        have_command,
        flags=re.DOTALL | re.UNICODE,
    )
    exact_match = re.fullmatch(r"exact\s+(.+)", exact_command, flags=re.DOTALL)
    if have_match is None or exact_match is None:
        return str(term or "").strip()
    local_name = have_match.group(1)
    exact_term = exact_match.group(1).strip()
    if _identifier_occurs_free(exact_term, local_name):
        return str(term or "").strip()
    return f"({str(lambda_head).strip()} => {exact_term})"


def _simplify_unused_tactic_cases_witness(term: str) -> str:
    """Erase one exact ``cases h; exact t`` when ``t`` does not use ``h``."""

    clean = _unwrap_transparent_parens(str(term or "").strip())
    split = _split_top_level_token(clean, ("=>",))
    if split is None:
        return str(term or "").strip()
    lambda_head, body = (str(item or "").strip() for item in split)
    if not lambda_head.startswith(("fun ", "λ ")):
        return str(term or "").strip()
    commands = _split_top_level_token(body, (";",))
    if commands is None:
        return str(term or "").strip()
    cases_command, exact_command = (str(item or "").strip() for item in commands)
    cases_match = re.fullmatch(
        r"by\s+cases\s+((?:[^\W\d]|_)[\w']*)",
        cases_command,
        flags=re.DOTALL | re.UNICODE,
    )
    exact_match = re.fullmatch(r"exact\s+(.+)", exact_command, flags=re.DOTALL)
    if cases_match is None or exact_match is None:
        return str(term or "").strip()
    proof_name = cases_match.group(1)
    exact_term = exact_match.group(1).strip()
    if _identifier_occurs_free(exact_term, proof_name):
        return str(term or "").strip()
    return f"({lambda_head} => {exact_term})"


def _simplify_reflexive_if_witness(term: str) -> str:
    """Reduce one exact ``if h = h then t else e`` inside a lambda.

    This is a deliberately narrow, semantics-preserving normalization.  It
    breaks a real proof/data dependency cycle without guessing proof
    irrelevance: equality is reflexive, so Lean's ``if_pos rfl`` selects the
    then branch for every value of ``h``.  The resulting witness is still
    checked by Lean at both the concrete-instance and full-negation boundary.
    """

    clean = _unwrap_transparent_parens(str(term or "").strip())
    split = _split_top_level_token(clean, ("=>",))
    if split is None:
        return str(term or "").strip()
    lambda_head, body = (str(item or "").strip() for item in split)
    if not lambda_head.startswith(("fun ", "λ ")):
        return str(term or "").strip()
    condition_body = _unwrap_transparent_parens(body)
    match = re.fullmatch(
        r"if\s+(?:decide\s*\(\s*)?"
        r"((?:[^\W\d]|_)[\w']*)\s*=\s*\1\s*\)?\s+"
        r"then\s+(.+?)\s+else\s+(.+)",
        condition_body,
        flags=re.DOTALL | re.UNICODE,
    )
    if match is None:
        return str(term or "").strip()
    return f"({lambda_head} => {match.group(2).strip()})"


def _simplify_unused_let_witness(term: str) -> str:
    """Erase one exact semicolon-form let whose value cannot affect the body."""

    clean = _unwrap_transparent_parens(str(term or "").strip())
    split = _split_top_level_token(clean, ("=>",))
    if split is None:
        return str(term or "").strip()
    lambda_head, body = (str(item or "").strip() for item in split)
    if not lambda_head.startswith(("fun ", "λ ")):
        return str(term or "").strip()
    match = re.fullmatch(
        r"let\s+((?:[^\W\d]|_)[\w']*|_)\s*:=\s*(.+?)\s*;\s*(.+)",
        _unwrap_transparent_parens(body),
        flags=re.DOTALL | re.UNICODE,
    )
    if match is None:
        return str(term or "").strip()
    local_name, remainder = match.group(1), match.group(3).strip()
    if local_name != "_" and _identifier_occurs_free(remainder, local_name):
        return str(term or "").strip()
    return f"({lambda_head} => {remainder})"


def _simplify_mined_function_witness(term: str) -> str:
    simplified = _simplify_unused_tactic_have_witness(term)
    simplified = _simplify_unused_tactic_cases_witness(simplified)
    simplified = _simplify_unused_let_witness(simplified)
    return _simplify_reflexive_if_witness(simplified)


def _function_definition_from_proof_type(
    proof_type: str,
    *,
    function_name: str,
    function_domain: str,
) -> str:
    """Mine one conservative function definition from an outer proof slot.

    Supported shapes are exact data equality (``f = term`` or its reverse)
    and, for the small audited scalar endofunction family, exact unary
    pointwise equality (``∀ x, f x = rhs`` or its reverse).  Exact equality
    mining deliberately also covers higher-order data outside the ordinary
    witness catalogue, such as ``S : ℝ → Set ℤ``: the premise itself
    supplies the only witness instead of forcing the lane to report
    ``unsupported`` before Lean sees the claim.

    Returned terms are only search candidates: Lean still checks the concrete
    instance and the independent full-negation/axiom boundary remains final.
    """

    hypothesis = _unwrap_transparent_parens(str(proof_type or "").strip())
    function = str(function_name or "").strip()
    if not hypothesis or not function or len(hypothesis) > 20_000:
        return ""

    equality = (
        _split_top_level_equals(hypothesis)
        if _is_bare_top_level_equality(hypothesis)
        else None
    )
    if equality is not None:
        left, right = (
            _unwrap_transparent_parens(str(item or "").strip())
            for item in equality
        )
        if (
            left == function
            and right
            and right != function
        ):
            term = _parenthesized_witness_term(
                _simplify_mined_function_witness(right)
            )
            return term if len(term) <= 1_024 else ""
        if (
            right == function
            and left
            and left != function
        ):
            term = _parenthesized_witness_term(
                _simplify_mined_function_witness(left)
            )
            return term if len(term) <= 1_024 else ""

    # Pointwise synthesis needs an audited scalar domain so that the lambda's
    # binder type is not guessed.  Bare equality above is already fully typed
    # by the enclosing telescope and therefore remains safe for arbitrary
    # equality-bound data.
    if not function_domain:
        return ""

    binder_chunks, body = _collect_leading_binder_chunks(hypothesis)
    if len(binder_chunks) != 1 or not body:
        return ""
    names, argument_type = _binder_names_and_type(binder_chunks[0])
    if len(names) != 1 or not argument_type:
        return ""
    expected_scalar = _function_domain_scalar_type(function_domain)
    if not expected_scalar or normalize_type(argument_type) != normalize_type(
        expected_scalar
    ):
        return ""
    pointwise_body = _unwrap_transparent_parens(str(body or "").strip())
    pointwise = (
        _split_top_level_equals(pointwise_body)
        if _is_bare_top_level_equality(pointwise_body)
        else None
    )
    if pointwise is None:
        return ""
    argument = names[0]
    left, right = (str(item or "").strip() for item in pointwise)
    if _exact_unary_function_application(
        left,
        function_name=function,
        argument_name=argument,
    ):
        value = right
    elif _exact_unary_function_application(
        right,
        function_name=function,
        argument_name=argument,
    ):
        value = left
    else:
        return ""
    if not value:
        return ""
    term = f"(fun ({argument} : {argument_type.strip()}) => {value})"
    term = _simplify_mined_function_witness(term)
    return term if len(term) <= 1_024 else ""


def _mined_function_definitions(
    plan: RightPiPlan,
    *,
    data_slot_index: int,
) -> tuple[tuple[str, int], ...]:
    """Return mined terms with the proof-slot scope that defined each one."""

    slots = tuple(plan.slots or ())
    if not (0 <= data_slot_index < len(slots)):
        return ()
    slot = slots[data_slot_index]
    function_domain = function_binder_domain(slot.lean_type_text or slot.type_text)
    if slot.kind != "data" or not slot.name:
        return ()
    if (
        not function_domain
        and right_pi_witness_terms(slot.lean_type_text or slot.type_text)
    ):
        # Preserve the established scalar/finite search order.  Generalized
        # exact-equality mining is only needed when the ordinary audited
        # catalogue has no inhabitant for this data type.
        return ()
    derived: list[tuple[str, int]] = []
    for proof_slot_index in range(data_slot_index + 1, len(slots)):
        proof_slot = slots[proof_slot_index]
        if proof_slot.kind != "proof":
            continue
        # The equality's function name resolves to the nearest visible data
        # binder, not every earlier slot with the same surface spelling.
        nearest_function_slot = next(
            (
                prior_index
                for prior_index in range(proof_slot_index - 1, -1, -1)
                if slots[prior_index].name == slot.name
            ),
            -1,
        )
        if nearest_function_slot != data_slot_index:
            continue
        term = _function_definition_from_proof_type(
            proof_slot.type_text,
            function_name=slot.name,
            function_domain=function_domain,
        )
        if not term:
            continue
        if term and not any(existing == term for existing, _ in derived):
            derived.append((term, proof_slot_index))
    return tuple(derived)


def _right_pi_data_dependency_positions(
    plan: RightPiPlan,
    *,
    witness_position: int,
    witness_term: str,
) -> tuple[int, ...]:
    """Resolve free data names in the lexical scope of a mined premise.

    Duplicate telescope names are legal across nested Pi scopes. A definition
    sees the nearest matching data binder *before its defining proof slot*;
    binding the same surface name to every slot silently changes the witness.
    """

    indexed_data_slots = tuple(
        (slot_index, slot)
        for slot_index, slot in enumerate(plan.slots)
        if slot.kind == "data"
    )
    if not (0 <= witness_position < len(indexed_data_slots)):
        return ()
    witness_slot_index, _witness_slot = indexed_data_slots[witness_position]
    defining_proof_index: int | None = None
    for term, proof_slot_index in _mined_function_definitions(
        plan,
        data_slot_index=witness_slot_index,
    ):
        if term == str(witness_term or "").strip():
            defining_proof_index = proof_slot_index
            break
    dependencies: list[int] = []
    names = tuple(
        dict.fromkeys(
            slot.name
            for _slot_index, slot in indexed_data_slots
            if slot.name
        )
    )
    for name in names:
        if not _right_pi_term_mentions_dependency(witness_term, name):
            continue
        scope_end = (
            defining_proof_index
            if defining_proof_index is not None
            else len(plan.slots)
        )
        resolved_slot_index = next(
            (
                slot_index
                for slot_index in range(scope_end - 1, -1, -1)
                if plan.slots[slot_index].name == name
            ),
            -1,
        )
        if resolved_slot_index < 0 or plan.slots[resolved_slot_index].kind != "data":
            continue
        resolved_position = next(
            (
                position
                for position, (slot_index, _slot) in enumerate(indexed_data_slots)
                if slot_index == resolved_slot_index
            ),
            -1,
        )
        if resolved_position >= 0 and resolved_position != witness_position:
            dependencies.append(resolved_position)
    return tuple(dict.fromkeys(dependencies))


def _right_pi_proof_dependency_slot_indices(
    plan: RightPiPlan,
    *,
    witness_position: int,
    witness_term: str,
) -> tuple[int, ...]:
    indexed_data_slots = tuple(
        (slot_index, slot)
        for slot_index, slot in enumerate(plan.slots)
        if slot.kind == "data"
    )
    if not (0 <= witness_position < len(indexed_data_slots)):
        return ()
    witness_slot_index, _witness_slot = indexed_data_slots[witness_position]
    defining_proof_index: int | None = None
    for term, proof_slot_index in _mined_function_definitions(
        plan,
        data_slot_index=witness_slot_index,
    ):
        if term == str(witness_term or "").strip():
            defining_proof_index = proof_slot_index
            break
    scope_end = (
        defining_proof_index
        if defining_proof_index is not None
        else len(plan.slots)
    )
    dependencies: list[int] = []
    for name in dict.fromkeys(slot.name for slot in plan.slots if slot.name):
        if not _right_pi_term_mentions_dependency(witness_term, name):
            continue
        resolved_index = next(
            (
                slot_index
                for slot_index in range(scope_end - 1, -1, -1)
                if plan.slots[slot_index].name == name
            ),
            -1,
        )
        if (
            resolved_index >= 0
            and plan.slots[resolved_index].kind == "proof"
        ):
            dependencies.append(resolved_index)
    return tuple(dict.fromkeys(dependencies))


def _right_pi_dependency_signature(
    plan: RightPiPlan,
    *,
    witness_position: int,
    witness_term: str,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    return (
        _right_pi_data_dependency_positions(
            plan,
            witness_position=witness_position,
            witness_term=witness_term,
        ),
        _right_pi_proof_dependency_slot_indices(
            plan,
            witness_position=witness_position,
            witness_term=witness_term,
        ),
    )


def right_pi_witness_domains(
    plan: RightPiPlan,
    *,
    statement: str = "",
) -> tuple[tuple[str, ...], ...]:
    """Return data-slot domains after mining exact definitional premises.

    Function binders constrained by a later proof slot are not independently
    crossed with the generic function catalogue. This prevents an entire
    finite campaign from consisting only of vacuously true implications.
    Unsupported or non-exact premises retain the ordinary audited catalogue.
    """

    domains: list[tuple[str, ...]] = []
    slots = tuple(plan.slots or ())
    for slot_index, slot in enumerate(slots):
        if slot.kind != "data":
            continue
        type_text = slot.lean_type_text or slot.type_text
        derived: list[str] = []
        if slot.name:
            for term, _proof_slot_index in _mined_function_definitions(
                plan,
                data_slot_index=slot_index,
            ):
                if term and term not in derived:
                    derived.append(term)
        domains.append(
            tuple(derived)
            if derived
            else right_pi_witness_terms(type_text, statement=statement)
        )
    return tuple(domains)


def right_pi_witness_phases(
    plan: RightPiPlan,
    *,
    statement: str = "",
) -> tuple[tuple[tuple[str, ...], ...], ...]:
    """Schedule one mined probe, the baseline, then all mined alternatives.

    Unconstrained slots keep their complete ordinary domains in the first
    phase, so a defining function premise is still crossed with the usual
    scalar boundary values.  Only alternative mined definitions are delayed
    until after the unchanged generic catalogue.
    """

    data_slots = tuple(slot for slot in tuple(plan.slots or ()) if slot.kind == "data")
    baseline = tuple(
        right_pi_witness_terms(
            slot.lean_type_text or slot.type_text,
            statement=statement,
        )
        for slot in data_slots
    )
    priority = right_pi_witness_domains(plan, statement=statement)
    if priority != baseline and all(priority):
        primary = tuple(
            (domain[0],) if domain != baseline_domain else domain
            for domain, baseline_domain in zip(priority, baseline)
        )
        # An equality premise may be the only source of a value for an
        # otherwise unsupported higher-order binder.  In that case there is
        # no generic baseline to schedule; retaining an empty phase would make
        # the engine reject the whole plan before checking the mined witness.
        phases = [primary]
        if all(baseline):
            phases.append(baseline)
        if priority != primary:
            phases.append(priority)
        return tuple(phases)
    return (baseline,)


def _historical_v3_identifier_occurs(
    expression: str,
    identifier: str,
) -> bool:
    """The exact local-name matcher used by persisted V3 schedules."""

    name = str(identifier or "").strip()
    if not name:
        return False
    return bool(
        re.search(
            rf"(?<![\w']){re.escape(name)}(?![\w'])",
            str(expression or ""),
            flags=re.UNICODE,
        )
    )


def _historical_v3_outer_lambda_binds_identifier(
    expression: str,
    identifier: str,
) -> bool:
    split = _split_top_level_token(
        _unwrap_transparent_parens(str(expression or "").strip()),
        ("=>",),
    )
    if split is None:
        return False
    head, _body = split
    raw_binders = str(head or "").strip()
    if not raw_binders.startswith("fun "):
        return False
    raw_binders = raw_binders[4:].strip()
    groups = re.findall(r"\(([^()]*)\)", raw_binders)
    if groups:
        return any(
            identifier in _binder_names_and_type(group)[0]
            for group in groups
        )
    match = re.match(r"([A-Za-z_][A-Za-z0-9_']*)\b", raw_binders)
    return bool(match and match.group(1) == identifier)


def _historical_v3_identifier_occurs_free(
    expression: str,
    identifier: str,
) -> bool:
    return bool(
        _historical_v3_identifier_occurs(expression, identifier)
        and not _historical_v3_outer_lambda_binds_identifier(
            expression,
            identifier,
        )
    )


def _historical_v3_parenthesized_witness_term(term: str) -> str:
    clean = str(term or "").strip()
    if not clean:
        return ""
    if _unwrap_transparent_parens(clean) != clean:
        return clean
    return f"({clean})"


def _historical_v3_function_definition_from_proof_type(
    proof_type: str,
    *,
    function_name: str,
    function_domain: str,
) -> str:
    """Reproduce the V3 premise miner byte-for-byte for cursor migration.

    This must remain frozen. It does not generate live candidates; it only
    authenticates a historical plan hash and locates the already-completed
    generic-baseline prefix before V5 safely replays mined assignments.
    """

    hypothesis = _unwrap_transparent_parens(str(proof_type or "").strip())
    function = str(function_name or "").strip()
    if not hypothesis or not function or len(hypothesis) > 20_000:
        return ""
    equality = (
        _split_top_level_equals(hypothesis)
        if _is_bare_top_level_equality(hypothesis)
        else None
    )
    if equality is not None:
        left, right = (
            _unwrap_transparent_parens(str(item or "").strip())
            for item in equality
        )
        if (
            left == function
            and right
            and right != function
            and not _historical_v3_identifier_occurs_free(right, function)
        ):
            term = _historical_v3_parenthesized_witness_term(right)
            return term if len(term) <= 1_024 else ""
        if (
            right == function
            and left
            and left != function
            and not _historical_v3_identifier_occurs_free(left, function)
        ):
            term = _historical_v3_parenthesized_witness_term(left)
            return term if len(term) <= 1_024 else ""

    binder_chunks, body = _collect_leading_binder_chunks(hypothesis)
    if len(binder_chunks) != 1 or not body:
        return ""
    names, argument_type = _binder_names_and_type(binder_chunks[0])
    if len(names) != 1 or not argument_type:
        return ""
    expected_scalar = _function_domain_scalar_type(function_domain)
    if not expected_scalar or normalize_type(argument_type) != normalize_type(
        expected_scalar
    ):
        return ""
    pointwise_body = _unwrap_transparent_parens(str(body or "").strip())
    pointwise = (
        _split_top_level_equals(pointwise_body)
        if _is_bare_top_level_equality(pointwise_body)
        else None
    )
    if pointwise is None:
        return ""
    argument = names[0]
    left, right = (str(item or "").strip() for item in pointwise)
    if _exact_unary_function_application(
        left,
        function_name=function,
        argument_name=argument,
    ):
        value = right
    elif _exact_unary_function_application(
        right,
        function_name=function,
        argument_name=argument,
    ):
        value = left
    else:
        return ""
    if not value or _historical_v3_identifier_occurs_free(value, function):
        return ""
    term = f"(fun ({argument} : {argument_type.strip()}) => {value})"
    return term if len(term) <= 1_024 else ""


def _historical_v1_function_definition_from_proof_type(
    proof_type: str,
    *,
    function_name: str,
    function_domain: str,
) -> str:
    """Reproduce the permissive V1 premise miner for cursor identity only."""

    hypothesis = _unwrap_transparent_parens(str(proof_type or "").strip())
    function = str(function_name or "").strip()
    if not hypothesis or not function or len(hypothesis) > 20_000:
        return ""
    equality = _split_top_level_equals(hypothesis)
    if equality is not None:
        left, right = (
            _unwrap_transparent_parens(str(item or "").strip())
            for item in equality
        )
        if left == function and right and right != function:
            return _historical_v3_parenthesized_witness_term(right)
        if right == function and left and left != function:
            return _historical_v3_parenthesized_witness_term(left)

    binder_chunks, body = _collect_leading_binder_chunks(hypothesis)
    if len(binder_chunks) != 1 or not body:
        return ""
    names, argument_type = _binder_names_and_type(binder_chunks[0])
    if len(names) != 1 or not argument_type:
        return ""
    expected_scalar = _function_domain_scalar_type(function_domain)
    if not expected_scalar or normalize_type(argument_type) != normalize_type(
        expected_scalar
    ):
        return ""
    pointwise = _split_top_level_equals(
        _unwrap_transparent_parens(str(body or "").strip())
    )
    if pointwise is None:
        return ""
    argument = names[0]
    left, right = (str(item or "").strip() for item in pointwise)
    if _exact_unary_function_application(
        left,
        function_name=function,
        argument_name=argument,
    ):
        value = right
    elif _exact_unary_function_application(
        right,
        function_name=function,
        argument_name=argument,
    ):
        value = left
    else:
        return ""
    if not value:
        return ""
    return f"(fun ({argument} : {argument_type.strip()}) => {value})"


def right_pi_historical_v1_witness_domains(
    plan: RightPiPlan,
    *,
    statement: str = "",
) -> tuple[tuple[str, ...], ...]:
    """Return the exact single Cartesian domain encoded by V1 cursors."""

    domains: list[tuple[str, ...]] = []
    slots = tuple(plan.slots or ())
    for slot_index, slot in enumerate(slots):
        if slot.kind != "data":
            continue
        type_text = slot.lean_type_text or slot.type_text
        function_domain = function_binder_domain(type_text)
        derived: list[str] = []
        if function_domain and slot.name:
            for proof_slot in slots[slot_index + 1 :]:
                if proof_slot.kind != "proof":
                    continue
                term = _historical_v1_function_definition_from_proof_type(
                    proof_slot.type_text,
                    function_name=slot.name,
                    function_domain=function_domain,
                )
                if term and term not in derived:
                    derived.append(term)
        domains.append(
            tuple(derived)
            if derived
            else right_pi_witness_terms(type_text, statement=statement)
        )
    return tuple(domains)


def right_pi_historical_v2_witness_domains(
    plan: RightPiPlan,
    *,
    statement: str = "",
) -> tuple[tuple[str, ...], ...]:
    """Return the exact witness domains encoded by genuine V2 cursors."""

    domains: list[tuple[str, ...]] = []
    slots = tuple(plan.slots or ())
    for slot_index, slot in enumerate(slots):
        if slot.kind != "data":
            continue
        type_text = slot.lean_type_text or slot.type_text
        function_domain = function_binder_domain(type_text)
        derived: list[str] = []
        if function_domain and slot.name:
            for proof_slot in slots[slot_index + 1 :]:
                if proof_slot.kind != "proof":
                    continue
                term = _historical_v3_function_definition_from_proof_type(
                    proof_slot.type_text,
                    function_name=slot.name,
                    function_domain=function_domain,
                )
                if term and term not in derived:
                    derived.append(term)
            later_slot_names = {
                other.name
                for other in slots[slot_index + 1 :]
                if other.name and other.name != slot.name
            }
            derived = [
                term
                for term in derived
                if not any(
                    _historical_v3_identifier_occurs_free(term, name)
                    for name in later_slot_names
                )
            ]
        domains.append(
            tuple(derived)
            if derived
            else right_pi_witness_terms(type_text, statement=statement)
        )
    return tuple(domains)


def right_pi_historical_v2_witness_phases(
    plan: RightPiPlan,
    *,
    statement: str = "",
) -> tuple[tuple[tuple[str, ...], ...], ...]:
    """Return the frozen primary/baseline/alternatives V2 schedule."""

    data_slots = tuple(slot for slot in plan.slots if slot.kind == "data")
    baseline = tuple(
        right_pi_witness_terms(
            slot.lean_type_text or slot.type_text,
            statement=statement,
        )
        for slot in data_slots
    )
    priority = right_pi_historical_v2_witness_domains(
        plan,
        statement=statement,
    )
    if priority != baseline and all(priority):
        primary = tuple(
            (domain[0],) if domain != baseline_domain else domain
            for domain, baseline_domain in zip(priority, baseline)
        )
        phases = [primary, baseline]
        if priority != primary:
            phases.append(priority)
        return tuple(phases)
    return (baseline,)


def right_pi_historical_v3_witness_domains(
    plan: RightPiPlan,
    *,
    statement: str = "",
) -> tuple[tuple[str, ...], ...]:
    """Return the exact witness domains encoded by genuine V3 cursors."""

    domains: list[tuple[str, ...]] = []
    slots = tuple(plan.slots or ())
    for slot_index, slot in enumerate(slots):
        if slot.kind != "data":
            continue
        type_text = slot.lean_type_text or slot.type_text
        function_domain = function_binder_domain(type_text)
        derived: list[str] = []
        if function_domain and slot.name:
            for proof_slot in slots[slot_index + 1 :]:
                if proof_slot.kind != "proof":
                    continue
                term = _historical_v3_function_definition_from_proof_type(
                    proof_slot.type_text,
                    function_name=slot.name,
                    function_domain=function_domain,
                )
                if term and term not in derived:
                    derived.append(term)
            later_proof_slot_names = {
                other.name
                for other in slots[slot_index + 1 :]
                if (
                    other.kind == "proof"
                    and other.name
                    and other.name != slot.name
                )
            }
            derived = [
                term
                for term in derived
                if not any(
                    _historical_v3_identifier_occurs_free(term, name)
                    for name in later_proof_slot_names
                )
            ]
        domains.append(
            tuple(derived)
            if derived
            else right_pi_witness_terms(type_text, statement=statement)
        )
    return tuple(domains)


def right_pi_historical_v3_witness_phases(
    plan: RightPiPlan,
    *,
    statement: str = "",
) -> tuple[tuple[tuple[str, ...], ...], ...]:
    """Return the frozen primary/baseline/alternatives V3 schedule."""

    data_slots = tuple(slot for slot in plan.slots if slot.kind == "data")
    baseline = tuple(
        right_pi_witness_terms(
            slot.lean_type_text or slot.type_text,
            statement=statement,
        )
        for slot in data_slots
    )
    priority = right_pi_historical_v3_witness_domains(
        plan,
        statement=statement,
    )
    if priority != baseline and all(priority):
        primary = tuple(
            (domain[0],) if domain != baseline_domain else domain
            for domain, baseline_domain in zip(priority, baseline)
        )
        phases = [primary, baseline]
        if priority != primary:
            phases.append(priority)
        return tuple(phases)
    return (baseline,)


def right_pi_phase_has_invariant_dependency_cycle(
    plan: RightPiPlan,
    phase: Sequence[Sequence[str]],
) -> bool:
    """Return whether every assignment in a phase has the same data cycle.

    This permits the engine to skip a whole mined Cartesian phase only when
    the dependency graph is assignment-invariant. Phases with even one
    alternative dependency shape continue through ordinary Lean checking.
    """

    data_slots = tuple(slot for slot in plan.slots if slot.kind == "data")
    domains = tuple(tuple(str(term or "") for term in domain) for domain in phase)
    if len(domains) != len(data_slots) or any(not domain for domain in domains):
        return False
    graph: list[tuple[int, ...]] = []
    for witness_position, domain in enumerate(domains):
        if any(_right_pi_dependency_analysis_is_uncertain(term) for term in domain):
            return False
        signatures = {
            _right_pi_data_dependency_positions(
                plan,
                witness_position=witness_position,
                witness_term=term,
            )
            for term in domain
        }
        if len(signatures) != 1:
            return False
        graph.append(next(iter(signatures)))

    visiting: set[int] = set()
    complete: set[int] = set()

    def visit(position: int) -> bool:
        if position in visiting:
            return True
        if position in complete:
            return False
        visiting.add(position)
        if any(visit(dependency) for dependency in graph[position]):
            return True
        visiting.remove(position)
        complete.add(position)
        return False

    return any(visit(position) for position in range(len(graph)))


def right_pi_phase_minimum_concrete_statement_bytes(
    plan: RightPiPlan,
    phase: Sequence[Sequence[str]],
) -> int:
    """Conservatively lower-bound concrete-statement bytes for a phase.

    Dependency specialization only adds syntax, so wrapping each data slot
    with its shortest raw witness gives a safe lower bound. If this bound
    already exceeds the durable candidate envelope, no assignment in the
    phase can cross the later persistence boundary.
    """

    domains = tuple(tuple(str(term or "") for term in domain) for domain in phase)
    data_slots = tuple(slot for slot in plan.slots if slot.kind == "data")
    if len(domains) != len(data_slots) or any(not domain for domain in domains):
        return 0
    shortest = tuple(
        min(
            domain,
            key=lambda term: len(
                json.dumps(term, separators=(",", ":")).encode("utf-8")
            ),
        )
        for domain in domains
    )
    transformed = str(plan.conclusion or "")
    data_position = len(shortest)
    for slot in reversed(plan.slots):
        if slot.kind == "proof":
            transformed = (
                f"(∀ ({slot.name} : {slot.type_text}), ({transformed}))"
            )
            continue
        data_position -= 1
        witness = shortest[data_position]
        transformed = (
            f"((fun ({slot.name} : {slot.type_text}) => ({transformed})) "
            f"({witness}))"
        )
    # Candidate persistence uses the default JSON ASCII escaping. Counting the
    # encoded concrete string (without even the mandatory record envelope) is
    # therefore a conservative lower bound for Unicode-heavy Lean statements.
    return len(
        json.dumps(transformed, separators=(",", ":")).encode("utf-8")
    )


def right_pi_phase_minimum_instantiation(
    plan: RightPiPlan,
    phase: Sequence[Sequence[str]],
    *,
    size_metric: str = "json",
) -> RightPiInstantiation | None:
    """Build a phase-wide lower-envelope assignment when shapes are invariant.

    Every domain must have one lexical dependency signature. Under that
    condition dependency specialization only adds the same wrappers, so the
    shortest default-JSON term per slot yields a conservative durable-record
    envelope. The returned object is still an ordinary Lean candidate; this
    helper grants no authority.
    """

    domains = tuple(tuple(str(term or "") for term in domain) for domain in phase)
    data_slots = tuple(slot for slot in plan.slots if slot.kind == "data")
    if len(domains) != len(data_slots) or any(not domain for domain in domains):
        return None
    for witness_position, domain in enumerate(domains):
        signatures = {
            _right_pi_dependency_signature(
                plan,
                witness_position=witness_position,
                witness_term=term,
            )
            for term in domain
        }
        if len(signatures) != 1:
            return None
    shortest = tuple(
        min(
            domain,
            key=(
                (lambda term: len(str(term or "")))
                if size_metric == "chars"
                else lambda term: len(
                    json.dumps(term, separators=(",", ":")).encode("utf-8")
                )
            ),
        )
        for domain in domains
    )
    return instantiate_right_pi(plan, shortest)


def instantiate_right_pi(
    plan: RightPiPlan,
    witness_terms: Sequence[str],
) -> RightPiInstantiation | None:
    """Instantiate data slots while retaining proof slots as hypotheses."""

    witnesses = tuple(str(item or "").strip() for item in witness_terms)
    if any(not item for item in witnesses):
        return None
    data_count = sum(slot.kind == "data" for slot in plan.slots)
    if not witnesses or data_count != len(witnesses):
        return None
    transformed = str(plan.conclusion or "").strip()
    if not transformed:
        return None
    data_slots = tuple(slot for slot in plan.slots if slot.kind == "data")

    dependency_graph = tuple(
        _right_pi_data_dependency_positions(
            plan,
            witness_position=witness_position,
            witness_term=witnesses[witness_position],
        )
        for witness_position in range(data_count)
    )
    direct_proof_dependency_graph = tuple(
        _right_pi_proof_dependency_slot_indices(
            plan,
            witness_position=witness_position,
            witness_term=witnesses[witness_position],
        )
        for witness_position in range(data_count)
    )

    def dependency_graph_has_cycle() -> bool:
        visiting: set[int] = set()
        complete: set[int] = set()

        def visit(position: int) -> bool:
            if position in visiting:
                return True
            if position in complete:
                return False
            visiting.add(position)
            if any(visit(dependency) for dependency in dependency_graph[position]):
                return True
            visiting.remove(position)
            complete.add(position)
            return False

        return any(visit(position) for position in range(data_count))

    def combined_dependency_graph_has_proof_cycle() -> bool:
        """Detect SCCs spanning selected data and proof-binder types."""

        indexed_data = tuple(
            (slot_index, slot)
            for slot_index, slot in enumerate(plan.slots)
            if slot.kind == "data"
        )
        data_slot_indices = tuple(slot_index for slot_index, _slot in indexed_data)
        edges: dict[int, tuple[int, ...]] = {}
        for data_position, (slot_index, _slot) in enumerate(indexed_data):
            edges[slot_index] = tuple(
                dict.fromkeys(
                    (
                        *(data_slot_indices[position]
                          for position in dependency_graph[data_position]),
                        *direct_proof_dependency_graph[data_position],
                    )
                )
            )
        for proof_slot_index, proof_slot in enumerate(plan.slots):
            if proof_slot.kind != "proof":
                continue
            if _right_pi_dependency_analysis_is_uncertain(proof_slot.type_text):
                # Unknown binder syntax can make a surface occurrence local
                # (for example ``∑ f in ...``). It must not justify a
                # phase-skipping SCC. The bounded rendered candidate remains
                # subject to Lean elaboration below.
                edges[proof_slot_index] = ()
                continue
            dependencies: list[int] = []
            for name in dict.fromkeys(
                slot.name
                for slot in plan.slots[:proof_slot_index]
                if slot.name
            ):
                if not _identifier_occurs_free(proof_slot.type_text, name):
                    continue
                resolved_index = next(
                    (
                        prior_index
                        for prior_index in range(proof_slot_index - 1, -1, -1)
                        if plan.slots[prior_index].name == name
                    ),
                    -1,
                )
                if resolved_index >= 0:
                    dependencies.append(resolved_index)
            edges[proof_slot_index] = tuple(dict.fromkeys(dependencies))

        stack: list[int] = []
        active: dict[int, int] = {}
        complete: set[int] = set()

        def visit(node: int) -> bool:
            if node in active:
                cycle = stack[active[node] :]
                return any(plan.slots[index].kind == "proof" for index in cycle)
            if node in complete:
                return False
            active[node] = len(stack)
            stack.append(node)
            try:
                if any(visit(dependency) for dependency in edges.get(node, ())):
                    return True
            finally:
                stack.pop()
                active.pop(node, None)
            complete.add(node)
            return False

        return any(visit(node) for node in edges)

    closure_cache: dict[int, str] = {}
    proof_dependency_cache: dict[int, tuple[int, ...]] = {}
    closure_visiting: set[int] = set()
    proof_dependency_visiting: set[int] = set()
    closure_work_chars = 0

    class _DependencyClosureEnvelopeExceeded(Exception):
        pass

    def close_data_witness(witness_position: int) -> str:
        """Specialize every referenced data binder with its chosen witness.

        This is needed when a definition for an earlier telescope slot refers
        to a later data binder: the raw term otherwise escapes that binder's
        scope in both the concrete proposition and replay application.  Lean
        still checks the resulting term, so cyclic or ill-typed correlations
        remain ordinary rejected candidates rather than authority.
        """

        nonlocal closure_work_chars
        cached = closure_cache.get(witness_position)
        if cached is not None:
            return cached
        if witness_position in closure_visiting:
            return witnesses[witness_position]
        closure_visiting.add(witness_position)
        term = witnesses[witness_position]
        try:
            for dependency_position in dependency_graph[witness_position]:
                dependency_slot = data_slots[dependency_position]
                dependency_argument = close_data_witness(dependency_position)
                projected_size = (
                    len(term)
                    + len(dependency_argument)
                    + len(dependency_slot.name)
                    + len(dependency_slot.type_text)
                    + 24
                )
                if projected_size > RIGHT_PI_PRESERVED_CANDIDATE_MAX_BYTES:
                    raise _DependencyClosureEnvelopeExceeded
                term = (
                    f"((fun ({dependency_slot.name} : "
                    f"{dependency_slot.type_text}) => ({term})) "
                    f"({dependency_argument}))"
                )
        finally:
            closure_visiting.discard(witness_position)
        # Count only finalized cache entries. Intermediate wrapping work is
        # not duplicated in the durable candidate and can otherwise reject a
        # final record that is still below the preservation envelope.
        if (
            closure_work_chars + len(term)
            > RIGHT_PI_PRESERVED_CANDIDATE_MAX_BYTES
        ):
            raise _DependencyClosureEnvelopeExceeded
        closure_cache[witness_position] = term
        closure_work_chars += len(term)
        return term

    def transitive_proof_dependencies(witness_position: int) -> tuple[int, ...]:
        """Propagate proof locals through substituted data definitions."""

        cached = proof_dependency_cache.get(witness_position)
        if cached is not None:
            return cached
        if witness_position in proof_dependency_visiting:
            return direct_proof_dependency_graph[witness_position]
        proof_dependency_visiting.add(witness_position)
        dependencies: list[int] = list(
            direct_proof_dependency_graph[witness_position]
        )
        try:
            for data_dependency in dependency_graph[witness_position]:
                dependencies.extend(transitive_proof_dependencies(data_dependency))
        finally:
            proof_dependency_visiting.discard(witness_position)
        result = tuple(dict.fromkeys(dependencies))
        proof_dependency_cache[witness_position] = result
        return result

    has_dependency_cycle = dependency_graph_has_cycle()
    has_proof_dependency_cycle = combined_dependency_graph_has_proof_cycle()
    bounded_cycle_break = bool(
        has_dependency_cycle
        and not has_proof_dependency_cycle
        and any(
            _right_pi_dependency_analysis_is_uncertain(witness)
            for witness in witnesses
        )
    )
    dependency_closure_complete = bool(
        not has_proof_dependency_cycle
        and (not has_dependency_cycle or bounded_cycle_break)
    )
    if dependency_closure_complete:
        try:
            specialized_witnesses = tuple(
                close_data_witness(index) for index in range(data_count)
            )
            specialized_proof_dependencies = tuple(
                transitive_proof_dependencies(index)
                for index in range(data_count)
            )
        except _DependencyClosureEnvelopeExceeded:
            dependency_closure_complete = False
            specialized_witnesses = witnesses
            specialized_proof_dependencies = ()
    else:
        specialized_witnesses = witnesses
        specialized_proof_dependencies = ()

    if not dependency_closure_complete:
        # The engine treats this as a bounded priority-assignment skip and
        # advances into the unchanged generic baseline. Do not build the
        # concrete/application strings: doing so would repeat the same cyclic
        # or over-envelope expansion before the event loop can regain control.
        return RightPiInstantiation(
            concrete_statement=transformed,
            witness_terms=witnesses,
            application_arguments=(),
            hypothesis_names=(),
            proof_aliases=(),
            dependency_closure_complete=False,
        )
    application: list[str] = []
    proof_aliases = {
        slot_index: slot.proof_alias
        for slot_index, slot in enumerate(plan.slots)
        if slot.kind == "proof" and slot.proof_alias
    }
    if len(proof_aliases) != sum(slot.kind == "proof" for slot in plan.slots):
        return None

    indexed_data_slots = tuple(
        (slot_index, slot)
        for slot_index, slot in enumerate(plan.slots)
        if slot.kind == "data"
    )

    def specialize_proof_type(slot_index: int, type_text: str) -> str:
        """Close a hoisted proof Pi over its preceding selected data.

        Proof binders are moved outside data instantiations in the derived
        concrete proposition.  This lets a selected earlier data witness
        depend on a later proof value while remaining a valid consequence of
        the original universally quantified claim.  Untyped lambdas let Lean
        infer dependent binder types from the already closed arguments.
        """

        specialized = str(type_text or "").strip()
        if _right_pi_dependency_analysis_is_uncertain(specialized):
            return specialized
        for name in dict.fromkeys(
            candidate.name
            for candidate in plan.slots[:slot_index]
            if candidate.name
        ):
            if not _identifier_occurs_free(specialized, name):
                continue
            resolved_slot_index = next(
                (
                    prior_index
                    for prior_index in range(slot_index - 1, -1, -1)
                    if plan.slots[prior_index].name == name
                ),
                -1,
            )
            if (
                resolved_slot_index < 0
                or plan.slots[resolved_slot_index].kind != "data"
            ):
                continue
            resolved_position = next(
                (
                    position
                    for position, (data_slot_index, _slot) in enumerate(
                        indexed_data_slots
                    )
                    if data_slot_index == resolved_slot_index
                ),
                -1,
            )
            if resolved_position < 0:
                continue
            specialized = (
                f"((fun {name} => ({specialized})) "
                f"({specialized_witnesses[resolved_position]}))"
            )
        return specialized

    # Hoist only proof binders that a preceding selected data witness needs.
    # Ordinary premise binders stay in their original compact position; this
    # avoids duplicating large specialized equality types in the durable
    # candidate record.  Earlier proof dependencies of a hoisted proof are
    # hoisted with it so all moved Pi types remain closed.
    hoisted_proof_indices = {
        proof_slot_index
        for data_position, dependencies in enumerate(
            specialized_proof_dependencies
        )
        for proof_slot_index in dependencies
        if proof_slot_index > indexed_data_slots[data_position][0]
    }
    changed = True
    while changed:
        changed = False
        for proof_slot_index in tuple(hoisted_proof_indices):
            proof_type = plan.slots[proof_slot_index].type_text
            for name in dict.fromkeys(
                slot.name
                for slot in plan.slots[:proof_slot_index]
                if slot.name
            ):
                if not _identifier_occurs_free(proof_type, name):
                    continue
                resolved_index = next(
                    (
                        prior_index
                        for prior_index in range(proof_slot_index - 1, -1, -1)
                        if plan.slots[prior_index].name == name
                    ),
                    -1,
                )
                if (
                    resolved_index >= 0
                    and plan.slots[resolved_index].kind == "proof"
                    and resolved_index not in hoisted_proof_indices
                ):
                    hoisted_proof_indices.add(resolved_index)
                    changed = True

    witness_index = data_count
    for slot_index in range(len(plan.slots) - 1, -1, -1):
        slot = plan.slots[slot_index]
        if slot.kind == "proof":
            if slot_index not in hoisted_proof_indices:
                transformed = (
                    f"(∀ ({slot.name} : {slot.type_text}), ({transformed}))"
                )
            continue
        witness_index -= 1
        witness = specialized_witnesses[witness_index]
        transformed = (
            f"((fun ({slot.name} : {slot.type_text}) => ({transformed})) ({witness}))"
        )
    proof_slot_indices = tuple(
        slot_index
        for slot_index, slot in enumerate(plan.slots)
        if slot.kind == "proof"
    )
    ordered_hoisted_proof_indices = tuple(
        slot_index
        for slot_index in proof_slot_indices
        if slot_index in hoisted_proof_indices
    )
    for slot_index in reversed(ordered_hoisted_proof_indices):
        slot = plan.slots[slot_index]
        specialized_type = specialize_proof_type(slot_index, slot.type_text)
        transformed = f"(∀ ({slot.name} : {specialized_type}), ({transformed}))"
    # The concrete proposition above deliberately retains source binder names
    # under typed lambdas.  The replay proof, however, applies the original
    # claim left-to-right after those source binders have been specialized.
    # Close a dependent later witness over the already-applied arguments so
    # neither earlier data names nor renamed proof binders remain free.
    data_witnesses = iter(specialized_witnesses)
    application_data_position = 0
    for slot_index, slot in enumerate(plan.slots):
        if slot.kind == "proof":
            argument = proof_aliases[slot_index]
        else:
            argument = next(data_witnesses)
            for proof_slot_index in reversed(
                specialized_proof_dependencies[application_data_position]
            ):
                proof_slot = plan.slots[proof_slot_index]
                # The alias already carries the fully specialized dependent
                # type at this sequential application point.  Omitting a
                # source type annotation avoids leaking earlier source data
                # names (for example ``n`` in ``h : n = 0``) into the closed
                # replay argument while the lambda still preserves lexical
                # shadowing inside the mined term.
                argument = (
                    f"((fun {proof_slot.name} => "
                    f"({argument})) ({proof_aliases[proof_slot_index]}))"
                )
            application_data_position += 1
        application.append(argument)
    concrete_proof_order = ordered_hoisted_proof_indices + tuple(
        slot_index
        for slot_index in proof_slot_indices
        if slot_index not in hoisted_proof_indices
    )
    hypotheses = tuple(proof_aliases[index] for index in concrete_proof_order)
    return RightPiInstantiation(
        concrete_statement=transformed,
        witness_terms=specialized_witnesses,
        application_arguments=tuple(application),
        hypothesis_names=hypotheses,
        proof_aliases=hypotheses,
        dependency_closure_complete=dependency_closure_complete,
    )


def right_spine_binders(statement: str) -> tuple[VisibleBinder, ...]:
    """Collect explicit forall binders along the implication consequent spine."""

    current = str(statement or "").strip()
    binders: list[VisibleBinder] = []
    inferred_scalar_types: set[str] = set()
    while current:
        unwrapped = _unwrap_transparent_parens(current)
        split = _first_forall_chunk(unwrapped)
        if split is not None:
            chunk, current = split
            # Function witness application is generated as an ordinary term;
            # reject implicit/instance binders so argument order cannot drift.
            if str(chunk or "").lstrip().startswith(("{", "[", "⦃")):
                return ()
            bounded_name, bounded_set = _bounded_membership_binder(chunk)
            if bounded_name and bounded_set:
                if len(inferred_scalar_types) != 1:
                    return ()
                names = [bounded_name]
                type_text = next(iter(inferred_scalar_types))
                current = f"({bounded_name} ∈ {bounded_set}) → {current}"
            else:
                names, type_text = _binder_names_and_type(chunk)
            if not names or not type_text:
                return ()
            binders.append(VisibleBinder(names[0], type_text.strip()))
            function_domain = function_binder_domain(type_text)
            scalar_type = _function_domain_scalar_type(function_domain)
            if scalar_type:
                inferred_scalar_types.add(scalar_type)
            if len(names) > 1:
                remaining = " ".join(names[1:])
                current = f"∀ ({remaining} : {type_text}), {current}"
            continue
        arrow = _split_top_level_arrow(unwrapped)
        if arrow is None:
            break
        _hypothesis, current = arrow
    return tuple(binders)


def instantiate_function_spine(
    statement: str,
    witness_terms: Sequence[str],
) -> FunctionSpineInstantiation | None:
    """Instantiate explicit right-spine foralls while retaining hypotheses.

    The concrete proposition is built with typed lambda application, so Lean
    owns lexical scoping.  ``application_arguments`` additionally records the
    exact interleaving of witnesses and introduced implication proofs needed
    to derive that concrete proposition from the original universal claim.
    """

    witnesses = tuple(str(item or "").strip() for item in witness_terms)
    if not witnesses or any(not item for item in witnesses):
        return None
    witness_index = 0
    hypothesis_index = 0
    application_arguments: list[str] = []
    hypothesis_names: list[str] = []
    inferred_scalar_types: set[str] = set()

    def visit(source: str) -> str | None:
        nonlocal witness_index, hypothesis_index
        current = str(source or "").strip()
        unwrapped = _unwrap_transparent_parens(current)
        split = _first_forall_chunk(unwrapped)
        if split is not None:
            chunk, body = split
            if str(chunk or "").lstrip().startswith(("{", "[", "⦃")):
                return None
            bounded_name, bounded_set = _bounded_membership_binder(chunk)
            bounded_membership = ""
            if bounded_name and bounded_set:
                if len(inferred_scalar_types) != 1:
                    return None
                names = [bounded_name]
                type_text = next(iter(inferred_scalar_types))
                bounded_membership = f"{bounded_name} ∈ {bounded_set}"
            else:
                names, type_text = _binder_names_and_type(chunk)
            if not names or not type_text or witness_index >= len(witnesses):
                return None
            name = names[0]
            witness = witnesses[witness_index]
            witness_index += 1
            application_arguments.append(witness)
            function_domain = function_binder_domain(type_text)
            scalar_type = _function_domain_scalar_type(function_domain)
            if scalar_type:
                inferred_scalar_types.add(scalar_type)
            remaining_body = body
            if len(names) > 1:
                remaining = " ".join(names[1:])
                remaining_body = f"∀ ({remaining} : {type_text}), {body}"
            if bounded_membership:
                remaining_body = f"({bounded_membership}) → ({remaining_body})"
            transformed = visit(remaining_body)
            if not transformed:
                return None
            return f"((fun ({name} : {type_text}) => ({transformed})) ({witness}))"
        arrow = _split_top_level_arrow(unwrapped)
        if arrow is not None:
            hypothesis, consequent = arrow
            hypothesis_name = f"h_mini_function_probe_{hypothesis_index}"
            hypothesis_index += 1
            hypothesis_names.append(hypothesis_name)
            application_arguments.append(hypothesis_name)
            transformed = visit(consequent)
            if not transformed:
                return None
            return f"({hypothesis}) → ({transformed})"
        return unwrapped

    concrete = visit(str(statement or ""))
    if not concrete or witness_index != len(witnesses):
        return None
    return FunctionSpineInstantiation(
        concrete_statement=concrete,
        witness_terms=witnesses,
        application_arguments=tuple(application_arguments),
        hypothesis_names=tuple(hypothesis_names),
    )


def deterministic_terms(domain: str, type_text: str) -> tuple[str, ...]:
    if domain == "nat":
        return tuple(f"({value} : ℕ)" for value in (0, 1, 2, 3, 4, 5, 7, 11))
    if domain == "pnat":
        return tuple(f"({value} : ℕ+)" for value in (1, 2, 3, 4, 5, 7, 11))
    if domain == "int":
        return tuple(f"({value} : ℤ)" for value in (0, 1, -1, 2, -2, 3, -3, 7))
    if domain == "rat":
        return tuple(
            f"({value} : ℚ)"
            for value in ("0", "1", "-1", "2", "-2", "1 / 2", "-1 / 2", "3 / 2")
        )
    if domain == "real":
        return tuple(
            f"({value} : ℝ)"
            for value in ("0", "1", "-1", "2", "-2", "1 / 2", "-1 / 2", "3 / 2")
        )
    if domain == "complex":
        return (
            "(1 : ℂ)",
            "(0 : ℂ)",
            "(-1 : ℂ)",
            "Complex.I",
            "(-Complex.I)",
            "(1 + Complex.I : ℂ)",
            "(1 - Complex.I : ℂ)",
            "(2 * Complex.I : ℂ)",
        )
    if domain == "bool":
        return ("false", "true")
    if domain == "fin":
        match = re.search(r"([0-9]+)", normalize_type(type_text))
        size = int(match.group(1)) if match else 0
        return tuple(f"({value} : Fin {size})" for value in range(size))
    if domain == "prop":
        return ("by omega", "by norm_num", "by simp")
    return ()


def bounded_product(
    domains: Sequence[Sequence[str]],
    limit: int,
) -> Iterable[tuple[str, ...]]:
    if not domains or any(not domain for domain in domains):
        return ()
    return itertools.islice(itertools.product(*domains), max(1, int(limit)))


def product_window(
    domains: Sequence[Sequence[str]],
    *,
    start: int,
    limit: int,
) -> tuple[tuple[str, ...], ...]:
    """Return a deterministic slice of a Cartesian product without materializing it.

    The absolute ``start`` index is suitable for durable cursors.  In
    particular, callers must not truncate the product before applying that
    cursor or a resumed search will silently stall at the first batch boundary.
    """

    if not domains or any(not domain for domain in domains):
        return ()
    first = max(0, int(start))
    count = max(1, int(limit))
    return tuple(itertools.islice(itertools.product(*domains), first, first + count))


def graph_fin_size(type_text: str) -> int:
    match = re.search(r"SimpleGraph\s*\(\s*Fin\s*\(?\s*([0-9]+)", type_text)
    return int(match.group(1)) if match else 0


def graph_term(size: int, edges: Sequence[tuple[int, int]]) -> str:
    carrier = GraphCarrier(
        vertex_type=f"Fin {size}",
        vertex_terms=tuple(f"({value} : Fin {size})" for value in range(size)),
        order=size,
        source="fin",
    )
    return graph_term_for_carrier(carrier, edges)


def graph_term_for_carrier(
    carrier: GraphCarrier,
    edges: Sequence[tuple[int, int]],
) -> str:
    clauses = [
        f"((i = {carrier.vertex_terms[left]} ∧ j = {carrier.vertex_terms[right]}) ∨ "
        f"(i = {carrier.vertex_terms[right]} ∧ j = {carrier.vertex_terms[left]}))"
        for left, right in edges
    ]
    relation = " ∨ ".join(clauses) if clauses else "False"
    return f"(SimpleGraph.fromRel (fun i j : {carrier.vertex_type} => {relation}))"


def _simple_graph_argument(type_text: str) -> str:
    compact = normalize_type(type_text)
    if compact.startswith("SimpleGraph(") and compact.endswith(")"):
        return compact[len("SimpleGraph(") : -1]
    if compact.startswith("SimpleGraph"):
        return compact[len("SimpleGraph") :]
    return ""


def _preamble_carrier_aliases(preamble: str) -> dict[str, tuple[str, int]]:
    """Return only transparent, closed ``Bool``/``Fin literal`` abbreviations.

    Definitions, variables, type synonyms with parameters, and computed sizes
    are intentionally rejected.  Falsification must not guess a carrier from
    syntax it cannot account for exactly.
    """

    aliases: dict[str, tuple[str, int]] = {}
    alias_pattern = re.compile(
        r"(?m)^\s*(?:private\s+)?abbrev\s+([A-Za-z_][A-Za-z0-9_']*)"
        r"\s*(?::\s*(?:Type(?:\s+[0-9]+)?|Sort(?:\s+[0-9]+)?))?"
        r"\s*:=\s*(Bool|Fin\s*\(?\s*[0-9]+\s*\)?)\s*$"
    )
    for match in alias_pattern.finditer(str(preamble or "")):
        name = match.group(1)
        target = normalize_type(match.group(2))
        if target == "Bool":
            aliases[name] = ("bool", 2)
            continue
        size_match = re.fullmatch(r"Fin\(?([0-9]+)\)?", target)
        if size_match:
            aliases[name] = ("fin", int(size_match.group(1)))
    return aliases


def resolve_graph_carrier(type_text: str, *, preamble: str = "") -> GraphCarrier | None:
    """Resolve an explicitly finite ``SimpleGraph`` carrier without inference."""

    argument = _simple_graph_argument(type_text)
    if not argument:
        return None
    if argument == "Bool":
        return GraphCarrier(
            vertex_type="Bool",
            vertex_terms=("false", "true"),
            order=2,
            source="bool",
        )
    fin_match = re.fullmatch(r"Fin\(?([0-9]+)\)?", argument)
    if fin_match:
        size = int(fin_match.group(1))
        return GraphCarrier(
            vertex_type=f"Fin {size}",
            vertex_terms=tuple(f"({value} : Fin {size})" for value in range(size)),
            order=size,
            source="fin",
        )
    alias = _preamble_carrier_aliases(preamble).get(argument)
    if alias is None:
        return None
    kind, size = alias
    vertex_terms = (
        ("(false : " + argument + ")", "(true : " + argument + ")")
        if kind == "bool"
        else tuple(f"({value} : {argument})" for value in range(size))
    )
    return GraphCarrier(
        vertex_type=argument,
        vertex_terms=vertex_terms,
        order=size,
        source=f"abbrev_{kind}",
    )
