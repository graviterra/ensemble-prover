"""Cast/subtraction normalization support for mini prover tactic lanes.

The mini prover often reaches the right arithmetic route but stalls on Lean's
carrier bureaucracy: natural-number subtraction is truncated, and rewriting a
cast such as ``((a - b : Nat) : Rat)`` requires the side condition ``b <= a``.
This module keeps that policy deterministic and reusable across root and child
tactic closers.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Sequence


_SCALAR_CAST_SYMBOL_MARKERS = (
    "ℚ",
    "ℝ",
    "ℤ",
)
_SCALAR_CAST_NAME_RE = re.compile(
    r"\b(?:Rat|Q|Real|Int|DivisionSemiring|Field|LinearOrderedField)\b"
)
# A bare ``!`` is not evidence of natural-number arithmetic: Lean also uses
# it in the unique-existence binder ``∃!``.  Postfix factorial expressions are
# already recognized structurally below, and well-typed Nat factorial goals
# expose Nat through their binder/type or the ``factorial`` spelling.
_NAT_MARKERS = ("ℕ", "Nat", "choose", "factorial")
_NAT_QUALIFIED_CHOOSE_RE = re.compile(r"\bNat\.choose\b")
_LEAN_IDENT_PATTERN = r"(?:[^\W\d]|_)[\w']*"
_SIMPLE_NAT_ATOM_PATTERN = (
    rf"(?:{_LEAN_IDENT_PATTERN}|\d+|"
    rf"\(\s*(?:{_LEAN_IDENT_PATTERN}|\d+)\s*\))"
)
_NAT_SUB_RE = re.compile(
    r"(?<!-)(?:[\w').»\]]|[)\]])\s*-\s*(?:[\w_(«]|[(])",
    flags=re.UNICODE,
)
_NAT_CAST_SUB_RE = re.compile(
    r"(?:"
    r"\((?=[^()]*-\s*[^()]*:\s*(?:ℕ|Nat)\b)"
    r"[^()]*-\s*[^()]*:\s*(?:ℕ|Nat)\b[^()]*\)"
    rf"|\(\s*{_SIMPLE_NAT_ATOM_PATTERN}\s*-\s*"
    rf"{_SIMPLE_NAT_ATOM_PATTERN}\s*:\s*(?:ℕ|Nat)\b\s*\)"
    r")",
    flags=re.UNICODE,
)
_NAT_FACTORIAL_SUB_RE = re.compile(r"\([^()]*-\s*[^()]*\)\.factorial", flags=re.UNICODE)
_NAT_FACTORIAL_PREFIX_SUB_RE = re.compile(
    r"\bNat\.factorial\s*\([^()]*-\s*[^()]*\)",
    flags=re.UNICODE,
)
_NAT_FACTORIAL_POSTFIX_SUB_RE = re.compile(r"\([^()]*-\s*[^()]*\)!", flags=re.UNICODE)
_FIELD_CAST_EXPR_RE = re.compile(
    r"\([^()]*:\s*(?:ℚ|Rat|Q|ℤ|Int|ℝ|Real)\s*\)"
)
_FIELD_CAST_AFTER_PAREN_RE = re.compile(
    r"\)\s*:\s*(?:ℚ|Rat|Q|ℤ|Int|ℝ|Real)\s*\)"
)
_EXPLICIT_CAST_RE = re.compile(
    r"↑|(?<![\w'.])(?:_root_\.)?(?:Nat\.cast|Int\.ofNat)\b",
    flags=re.UNICODE,
)
_FIELD_BINDER_RE = re.compile(
    rf"(?P<prefix>^|[∀({{])\s*(?P<names>{_LEAN_IDENT_PATTERN}(?:\s+{_LEAN_IDENT_PATTERN})*)\s*:\s*"
    r"(?:ℚ|Rat|Q|ℤ|Int|ℝ|Real)\b",
    flags=re.UNICODE,
)
_GENERIC_FIELD_BINDER_RE = re.compile(
    rf"[\[(]\s*(?:Field|LinearOrderedField)\s+(?P<type>{_LEAN_IDENT_PATTERN})\s*[\])]",
    flags=re.UNICODE,
)
_GENERIC_TYPE_BINDER_RE = re.compile(
    rf"(?P<prefix>[∀({{])\s*(?P<names>{_LEAN_IDENT_PATTERN}(?:\s+{_LEAN_IDENT_PATTERN})*)\s*:\s*"
    rf"(?P<type>{_LEAN_IDENT_PATTERN})\b",
    flags=re.UNICODE,
)
_NAT_BINDER_RE = re.compile(
    rf"(?P<prefix>^|[∀({{])\s*(?P<names>{_LEAN_IDENT_PATTERN}(?:\s+{_LEAN_IDENT_PATTERN})*)\s*:\s*"
    r"(?:ℕ|Nat)\b(?!\s*(?:→|->))",
    flags=re.UNICODE,
)
_SIMPLE_SUBTRACTION_RE = re.compile(
    rf"(?<![\w'.»])(?P<left>{_SIMPLE_NAT_ATOM_PATTERN})\s*-\s*"
    rf"(?P<right>{_SIMPLE_NAT_ATOM_PATTERN})(?![\w'(\u00ab])",
    flags=re.UNICODE,
)
_DOT_CHOOSE_RE = re.compile(
    rf"\b(?P<receiver>{_LEAN_IDENT_PATTERN})\.choose\b",
    flags=re.UNICODE,
)
_LEAN_IDENT_RE = re.compile(_LEAN_IDENT_PATTERN, flags=re.UNICODE)


@dataclass(frozen=True)
class CastNormalizationProfile:
    """Heuristic profile deciding whether guarded cast rewrites are useful."""

    should_attempt: bool
    nat_subtraction_count: int = 0
    nat_choose_count: int = 0
    has_field_cast: bool = False
    has_nat_context: bool = False

    def metadata(self) -> dict[str, Any]:
        return {
            "cast_normalization_should_attempt": self.should_attempt,
            "cast_normalization_nat_subtraction_count": self.nat_subtraction_count,
            "cast_normalization_nat_choose_count": self.nat_choose_count,
            "cast_normalization_has_field_cast": self.has_field_cast,
            "cast_normalization_has_nat_context": self.has_nat_context,
        }


@dataclass(frozen=True)
class CastNormalizationScript:
    """One Lean tactic script emitted by the cast normalization lane."""

    lines: tuple[str, ...]
    tactic: str
    source: str


def detect_cast_normalization_profile(text: str) -> CastNormalizationProfile:
    """Return the guarded-cast profile for a Lean goal or statement."""

    raw = str(text or "")
    compact = " ".join(raw.split())
    nat_subtractions = _count_nat_subtractions(compact)
    nat_chooses = _count_nat_chooses(compact)
    has_field_cast = _has_scalar_cast(compact)
    has_linked_nat_cast = _has_scalar_casted_nat_operation(compact)
    has_nat_context = any(marker in compact for marker in _NAT_MARKERS)
    should_attempt = bool(
        has_nat_context
        and has_field_cast
        and has_linked_nat_cast
        and (nat_subtractions > 0 or nat_chooses > 0)
    )
    return CastNormalizationProfile(
        should_attempt=should_attempt,
        nat_subtraction_count=nat_subtractions,
        nat_choose_count=nat_chooses,
        has_field_cast=has_field_cast,
        has_nat_context=has_nat_context,
    )


def _has_scalar_cast(text: str) -> bool:
    """Detect actual scalar coercion syntax, excluding unrelated binders."""

    raw = str(text or "")
    if _EXPLICIT_CAST_RE.search(raw):
        return True

    concrete_binders = [
        match
        for match in _FIELD_BINDER_RE.finditer(raw)
        if match.group("prefix") not in {"(", "{"}
        or _parenthesized_match_is_binder(raw, match)
    ]
    without_binders = _replace_spans_with_spaces(raw, concrete_binders)
    if _FIELD_CAST_EXPR_RE.search(
        without_binders
    ) or _FIELD_CAST_AFTER_PAREN_RE.search(without_binders):
        return True

    generic_field_types = {
        str(match.group("type") or "").strip()
        for match in _GENERIC_FIELD_BINDER_RE.finditer(raw)
        if str(match.group("type") or "").strip()
    }
    if not generic_field_types:
        return False
    generic_binders = [
        match
        for match in _GENERIC_TYPE_BINDER_RE.finditer(without_binders)
        if str(match.group("type") or "").strip() in generic_field_types
        and (
            match.group("prefix") not in {"(", "{"}
            or _parenthesized_match_is_binder(without_binders, match)
        )
    ]
    without_binders = _replace_spans_with_spaces(
        without_binders, generic_binders
    )
    return any(
        re.search(
            rf"(?:\([^()]*|\))\s*:\s*{re.escape(field_type)}\s*\)",
            without_binders,
        )
        for field_type in generic_field_types
    )


def _has_scalar_casted_nat_operation(text: str) -> bool:
    """Require the scalar cast to structurally contain the Nat operation."""

    raw = str(text or "")
    nat_vars = _nat_binder_names(raw)
    generic_field_types = {
        str(match.group("type") or "").strip()
        for match in _GENERIC_FIELD_BINDER_RE.finditer(raw)
        if str(match.group("type") or "").strip()
    }
    cast_targets = {
        "ℚ",
        "Rat",
        "Q",
        "ℤ",
        "Int",
        "ℝ",
        "Real",
        *generic_field_types,
    }
    target_pattern = "|".join(
        re.escape(target)
        for target in sorted(cast_targets, key=len, reverse=True)
    )
    for match in re.finditer(rf":\s*(?:{target_pattern})\s*\)", raw):
        close_index = match.end() - 1
        open_index = _matching_open_paren(raw, close_index)
        if open_index is None:
            continue
        operand = raw[open_index + 1 : match.start()]
        if _count_nat_chooses(operand, nat_vars=nat_vars) > 0:
            return True
        if _is_direct_nat_subtraction(
            operand,
            nat_vars=nat_vars,
            require_type_ascription=True,
        ):
            return True

    for match in _EXPLICIT_CAST_RE.finditer(raw):
        cast_prefix = raw[: match.start()].rstrip()
        explicit_nat_cast = (
            match.group(0).endswith("Nat.cast")
            and cast_prefix.endswith("@")
        )
        operand = _explicit_cast_operand(
            raw,
            match.end(),
            explicit_nat_cast=explicit_nat_cast,
        )
        if operand is None:
            continue
        if _count_nat_chooses(operand, nat_vars=nat_vars) > 0:
            return True
        if _is_direct_nat_subtraction(operand, nat_vars=nat_vars):
            return True
    return False


def _is_direct_nat_subtraction(
    text: str,
    *,
    nat_vars: set[str],
    require_type_ascription: bool = False,
) -> bool:
    operand = str(text or "").strip()
    while operand:
        if _NAT_CAST_SUB_RE.fullmatch(operand):
            return True
        if not require_type_ascription:
            match = _SIMPLE_SUBTRACTION_RE.fullmatch(operand)
            if match is not None:
                values = tuple(
                    str(match.group(name) or "")
                    .strip()
                    .strip("()")
                    .strip()
                    for name in ("left", "right")
                )
                identifiers = tuple(
                    value for value in values if not value.isdigit()
                )
                return bool(identifiers) and all(
                    value in nat_vars for value in identifiers
                )
        if not (
            operand.startswith("(")
            and operand.endswith(")")
            and _matching_open_paren(operand, len(operand) - 1) == 0
        ):
            return False
        operand = operand[1:-1].strip()
    return False


def _matching_open_paren(text: str, close_index: int) -> int | None:
    raw = str(text or "")
    if not (0 <= close_index < len(raw)) or raw[close_index] != ")":
        return None
    depth = 0
    for index in range(close_index, -1, -1):
        if raw[index] == ")":
            depth += 1
        elif raw[index] == "(":
            depth -= 1
            if depth == 0:
                return index
    return None


def _explicit_cast_operand(
    text: str,
    start: int,
    *,
    explicit_nat_cast: bool,
) -> str | None:
    raw = str(text or "")
    index = max(0, start)
    positional_target = 3 if explicit_nat_cast else 1
    positional_seen = 0
    if raw.startswith(".{", index):
        universe_end = raw.find("}", index + 2)
        if universe_end < 0:
            return None
        index = universe_end + 1
    while True:
        while index < len(raw) and raw[index].isspace():
            index += 1
        if index >= len(raw):
            return None
        if raw[index] == "(":
            depth = 0
            group_end = None
            for end in range(index, len(raw)):
                if raw[end] == "(":
                    depth += 1
                elif raw[end] == ")":
                    depth -= 1
                    if depth == 0:
                        group_end = end
                        break
            if group_end is None:
                operand = raw[index + 1 :]
                if ":=" in operand:
                    return None
                positional_seen += 1
                return operand if positional_seen == positional_target else None
            operand = raw[index + 1 : group_end]
            index = group_end + 1
            if ":=" in operand:
                argument_name, _separator, _value = operand.partition(":=")
                if explicit_nat_cast and argument_name.strip() == "R":
                    positional_target = max(1, positional_target - 1)
                continue
            positional_seen += 1
            if positional_seen == positional_target:
                return operand
            continue
        match = re.match(
            rf"{_LEAN_IDENT_PATTERN}(?:\.{_LEAN_IDENT_PATTERN})*",
            raw[index:],
        )
        if match is None:
            return None
        operand = match.group(0)
        index += match.end()
        positional_seen += 1
        if positional_seen == positional_target:
            return operand


def cast_normalization_scripts(
    profile: CastNormalizationProfile,
    *,
    needs_intro: bool,
    max_scripts: int = 8,
) -> tuple[CastNormalizationScript, ...]:
    """Generate guarded cast-normalization tactic scripts for a profile."""

    if not profile.should_attempt:
        return ()
    rewrite_steps = _rewrite_steps_for_profile(profile)
    if not rewrite_steps:
        return ()
    prefix = ("intros",) if needs_intro else ()
    scripts: list[CastNormalizationScript] = []

    def add(lines: Sequence[str], *, tactic: str, source: str) -> None:
        full_lines = tuple([*prefix, *[str(line) for line in lines if str(line).strip()]])
        scripts.append(
            CastNormalizationScript(
                lines=full_lines,
                tactic=("intros; " if prefix else "") + tactic,
                source=source,
            )
        )

    add(
        (*rewrite_steps, "all_goals try ring_nf", "all_goals omega"),
        tactic="; ".join([*rewrite_steps, "all_goals try ring_nf", "all_goals omega"]),
        source="cast_normalization_guarded_ring",
    )
    add(
        (*rewrite_steps, "all_goals omega"),
        tactic="; ".join([*rewrite_steps, "all_goals omega"]),
        source="cast_normalization_guarded_rw",
    )
    add(
        ("norm_num at *", *rewrite_steps, "all_goals omega"),
        tactic="; ".join(["norm_num at *", *rewrite_steps, "all_goals omega"]),
        source="cast_normalization_norm_num_guarded_rw",
    )
    add(
        (*rewrite_steps, "all_goals try norm_num", "all_goals omega"),
        tactic="; ".join([*rewrite_steps, "all_goals try norm_num", "all_goals omega"]),
        source="cast_normalization_guarded_norm_num",
    )
    add(
        rewrite_steps,
        tactic="; ".join(rewrite_steps),
        source="cast_normalization_guard_probe",
    )
    add(
        ("push_cast at *", "all_goals try ring_nf", "all_goals try omega"),
        tactic="push_cast at *; all_goals try ring_nf; all_goals try omega",
        source="cast_normalization_push_cast",
    )
    add(
        ("zify at *", "all_goals omega"),
        tactic="zify at *; all_goals omega",
        source="cast_normalization_zify",
    )

    cap = max(0, int(max_scripts or 0))
    return tuple(scripts[:cap] if cap else ())


def cast_normalization_context_key(text: str, helper_names: Sequence[str] = ()) -> str:
    """Build a stable exact-context key for one cast-normalization pass."""

    compact_goal = " ".join(str(text or "").split())
    helpers = ",".join(sorted(str(name or "").strip() for name in helper_names if str(name or "").strip()))
    return f"{compact_goal}|helpers={helpers}"


def cast_side_condition_goal_count(attempts: Sequence[Any]) -> int:
    """Count exposed residual obligations in failed cast-normalization attempts."""

    count = 0
    for attempt in list(attempts or ()):
        if not isinstance(attempt, dict):
            continue
        source = str(attempt.get("source") or "")
        if not source.startswith("cast_normalization"):
            continue
        for goal in list(attempt.get("remaining_goals") or ()):
            if not isinstance(goal, dict):
                continue
            target = str(goal.get("target") or "")
            if target.strip():
                count += 1
    return count


def _count_nat_subtractions(
    text: str, *, nat_vars: set[str] | None = None
) -> int:
    raw = str(text or "")
    structural_matches = list(_NAT_CAST_SUB_RE.finditer(raw))
    count = len(structural_matches)
    compact = _replace_spans_with_spaces(raw, structural_matches)
    compact = _NAT_FACTORIAL_SUB_RE.sub(" ", compact)
    compact = _NAT_FACTORIAL_PREFIX_SUB_RE.sub(" ", compact)
    compact = _NAT_FACTORIAL_POSTFIX_SUB_RE.sub(" ", compact)
    compact = _FIELD_CAST_EXPR_RE.sub(" ", compact)
    if nat_vars is None:
        nat_vars = _nat_binder_names(raw)
    if " - " not in compact and "-" not in compact:
        return count
    for match in _SIMPLE_SUBTRACTION_RE.finditer(compact):
        operands = tuple(
            str(match.group(name) or "").strip().strip("()").strip()
            for name in ("left", "right")
        )
        identifiers = tuple(item for item in operands if not item.isdigit())
        if not identifiers or any(item not in nat_vars for item in identifiers):
            continue
        count += 1
    return count


def _count_nat_chooses(
    text: str, *, nat_vars: set[str] | None = None
) -> int:
    raw = str(text or "")
    if nat_vars is None:
        nat_vars = _nat_binder_names(raw)
    return len(_NAT_QUALIFIED_CHOOSE_RE.findall(raw)) + sum(
        1
        for match in _DOT_CHOOSE_RE.finditer(raw)
        if str(match.group("receiver") or "") in nat_vars
    )


def _nat_binder_names(text: str) -> set[str]:
    raw = str(text or "")
    names: set[str] = set()
    for match in _NAT_BINDER_RE.finditer(raw):
        if match.group("prefix") in {"(", "{"} and not _parenthesized_match_is_binder(
            raw, match
        ):
            continue
        names.update(_LEAN_IDENT_RE.findall(match.group("names") or ""))
    return names


def _replace_spans_with_spaces(text: str, matches: Sequence[re.Match[str]]) -> str:
    raw = str(text or "")
    if not matches:
        return raw
    chars = list(raw)
    for match in matches:
        start, end = match.span()
        for index in range(max(0, start), min(len(chars), end)):
            chars[index] = " "
    return "".join(chars)


def _field_binder_names(text: str) -> set[str]:
    raw = str(text or "")
    names: set[str] = set()
    generic_field_types = {
        str(match.group("type") or "").strip()
        for match in _GENERIC_FIELD_BINDER_RE.finditer(raw)
        if str(match.group("type") or "").strip()
    }
    for match in _FIELD_BINDER_RE.finditer(raw):
        idents = _LEAN_IDENT_RE.findall(match.group("names") or "")
        if match.group("prefix") in {"(", "{"} and not _parenthesized_match_is_binder(
            raw, match
        ):
            continue
        for ident in idents:
            names.add(ident)
    if generic_field_types:
        for match in _GENERIC_TYPE_BINDER_RE.finditer(raw):
            if str(match.group("type") or "").strip() not in generic_field_types:
                continue
            if match.group("prefix") in {"(", "{"} and not _parenthesized_match_is_binder(
                raw, match
            ):
                continue
            for ident in _LEAN_IDENT_RE.findall(match.group("names") or ""):
                names.add(ident)
    return names


def _parenthesized_match_is_binder(text: str, match: re.Match[str]) -> bool:
    raw = str(text or "")
    closer = "}" if match.group("prefix") == "{" else ")"
    index = match.end()
    while index < len(raw) and raw[index].isspace():
        index += 1
    if index >= len(raw) or raw[index] != closer:
        return False
    index += 1
    while index < len(raw) and raw[index].isspace():
        index += 1
    if index >= len(raw):
        return False
    return raw[index] in {"(", ",", ":", "→"} or raw.startswith("->", index)


def _identifier_before(text: str, index: int) -> str:
    prefix = str(text or "")[: max(0, index + 1)]
    match = re.search(rf"({_LEAN_IDENT_PATTERN})\s*$", prefix)
    return match.group(1) if match else ""


def _identifier_after(text: str, index: int) -> str:
    suffix = str(text or "")[max(0, index) :]
    match = re.match(rf"\s*\(?\s*({_LEAN_IDENT_PATTERN})", suffix)
    return match.group(1) if match else ""


def _rewrite_steps_for_profile(profile: CastNormalizationProfile) -> tuple[str, ...]:
    steps: list[str] = []
    if profile.nat_choose_count > 0:
        steps.append("repeat rw [Nat.cast_choose]")
    if profile.nat_subtraction_count > 0:
        steps.append("repeat rw [Nat.cast_sub]")
    return tuple(steps)


__all__ = [
    "CastNormalizationProfile",
    "CastNormalizationScript",
    "cast_normalization_context_key",
    "cast_normalization_scripts",
    "cast_side_condition_goal_count",
    "detect_cast_normalization_profile",
]
