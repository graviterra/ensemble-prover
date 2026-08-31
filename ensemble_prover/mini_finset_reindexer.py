"""Finite indexed sum/product reindexing support for mini prover lanes.

Finite reindexing is a mechanical Lean fluency problem: mathematicians see
``same finite support, pointwise equal summand`` or ``swap two finite sums`` as
finished, while Lean needs the exact congruence/rewrite lemma plus side goals.
This module keeps those attempts deterministic, bounded, and separate from
infinite ``tsum`` goals.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Sequence

from .proof_state import lean_statement_conclusion


_FINITE_SUM_RE = re.compile(
    r"(?:∑(?!')|Finset\.sum\b|(?:\([^)]*Finset\.[^)]*\)|\bFinset\.[A-Za-z0-9_'.]+)\.sum\b)",
    flags=re.UNICODE,
)
_FINITE_PRODUCT_RE = re.compile(
    r"(?:∏(?!')|Finset\.prod\b|(?:\([^)]*Finset\.[^)]*\)|\bFinset\.[A-Za-z0-9_'.]+)\.prod\b)",
    flags=re.UNICODE,
)
_INFINITE_BIGOP_RE = re.compile(
    r"(?:∑'|∏'|(?:\b(?:tsum|tprod)\b|«(?:tsum|tprod)»)"
    r"(?=\s*(?:\.\{|<\||\(|@|«|[^\W\d])))",
    flags=re.UNICODE,
)
_EQUALITY_RE = re.compile(r"(?<![:<>=])=(?!=|>)")


@dataclass(frozen=True)
class FinsetReindexingProfile:
    """Heuristic profile deciding whether finite reindexing is worth trying."""

    should_attempt: bool
    finite_sum_count: int = 0
    finite_product_count: int = 0
    has_equality: bool = False
    has_filter: bool = False
    has_nested_sum: bool = False
    has_nested_product: bool = False
    has_antidiagonal: bool = False
    has_range: bool = False
    has_interval: bool = False
    has_attach: bool = False
    has_image_or_map: bool = False
    has_sigma: bool = False
    has_infinite_sum: bool = False

    def metadata(self) -> dict[str, Any]:
        return {
            "finset_reindexing_should_attempt": self.should_attempt,
            "finset_reindexing_finite_sum_count": self.finite_sum_count,
            "finset_reindexing_finite_product_count": self.finite_product_count,
            "finset_reindexing_has_equality": self.has_equality,
            "finset_reindexing_has_filter": self.has_filter,
            "finset_reindexing_has_nested_sum": self.has_nested_sum,
            "finset_reindexing_has_nested_product": self.has_nested_product,
            "finset_reindexing_has_antidiagonal": self.has_antidiagonal,
            "finset_reindexing_has_range": self.has_range,
            "finset_reindexing_has_interval": self.has_interval,
            "finset_reindexing_has_attach": self.has_attach,
            "finset_reindexing_has_image_or_map": self.has_image_or_map,
            "finset_reindexing_has_sigma": self.has_sigma,
            "finset_reindexing_has_infinite_sum": self.has_infinite_sum,
        }


@dataclass(frozen=True)
class FinsetReindexingScript:
    """One Lean tactic script emitted by the finite reindexing lane."""

    lines: tuple[str, ...]
    tactic: str
    source: str


def _blank_lean_comments_and_strings(text: str) -> str:
    """Blank non-code lexical regions while preserving offsets and newlines."""

    source = str(text or "")
    output = list(source)
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        if block_depth:
            if source.startswith("/-", index):
                output[index : index + 2] = "  "
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                output[index : index + 2] = "  "
                block_depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    output[index] = " "
                index += 1
            continue
        if in_string:
            if source[index] == "\\" and index + 1 < len(source):
                output[index : index + 2] = "  "
                index += 2
            else:
                if source[index] != "\n":
                    output[index] = " "
                if source[index] == '"':
                    in_string = False
                index += 1
            continue
        if source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                output[index] = " "
                index += 1
            continue
        if source.startswith("/-", index):
            output[index : index + 2] = "  "
            block_depth = 1
            index += 2
            continue
        if source[index] == '"':
            output[index] = " "
            in_string = True
        index += 1
    return "".join(output)


_LOCAL_BINDER_RE = re.compile(
    r"(?P<intro>∀|λ|\bfun\b)\s*(?:[({[]\s*)?"
    r"(?P<names>[^\W\d]\w*(?:\s+[^\W\d]\w*)*)\s*(?P<end>:|=>|,)",
    flags=re.UNICODE,
)
_LOCAL_LET_RE = re.compile(r"\blet\s+(?P<name>tsum|tprod)\b", flags=re.UNICODE)


def _blank_shadowed_infinite_bigop_names(text: str) -> str:
    """Blank unqualified local binders named ``tsum``/``tprod`` in scope."""

    source = str(text or "")
    output = list(source)

    def blank_name(name: str, start: int, end: int) -> None:
        for occurrence in re.finditer(
            rf"(?<![\w.]){re.escape(name)}\b",
            source[start:end],
            flags=re.UNICODE,
        ):
            occurrence_start = start + occurrence.start()
            occurrence_end = start + occurrence.end()
            output[occurrence_start:occurrence_end] = " " * (
                occurrence_end - occurrence_start
            )

    def enclosing_scope_end(
        start: int,
        *,
        stop_at_term_separator: bool = True,
    ) -> int:
        closing = {"(": ")", "{": "}", "[": "]"}
        delimiter_stack: list[str] = []
        quoted_identifier = False
        for character in source[:start]:
            if quoted_identifier:
                quoted_identifier = character != "»"
            elif character == "«":
                quoted_identifier = True
            elif character in closing:
                delimiter_stack.append(closing[character])
            elif delimiter_stack and character == delimiter_stack[-1]:
                delimiter_stack.pop()
        if not delimiter_stack:
            if not stop_at_term_separator:
                return len(source)
            quoted_identifier = False
            for cursor in range(start, len(source)):
                character = source[cursor]
                if quoted_identifier:
                    quoted_identifier = character != "»"
                elif character == "«":
                    quoted_identifier = True
                elif character in closing:
                    delimiter_stack.append(closing[character])
                elif delimiter_stack and character == delimiter_stack[-1]:
                    delimiter_stack.pop()
                elif not delimiter_stack:
                    if character == ";":
                        return cursor
                    if source.startswith("in", cursor):
                        previous = source[cursor - 1] if cursor > start else " "
                        following = (
                            source[cursor + 2]
                            if cursor + 2 < len(source)
                            else " "
                        )
                        if not (previous.isalnum() or previous in "_'") and not (
                            following.isalnum() or following in "_'"
                        ):
                            return cursor
            return len(source)
        scope_depth = len(delimiter_stack)
        quoted_identifier = False
        for cursor in range(start, len(source)):
            character = source[cursor]
            if quoted_identifier:
                quoted_identifier = character != "»"
            elif character == "«":
                quoted_identifier = True
            elif character in closing:
                delimiter_stack.append(closing[character])
            elif delimiter_stack and character == delimiter_stack[-1]:
                delimiter_stack.pop()
                if len(delimiter_stack) < scope_depth:
                    return cursor + 1
        return len(source)

    def let_body_start(start: int, end: int) -> int:
        delimiter_stack: list[str] = []
        closing = {"(": ")", "{": "}", "[": "]"}
        assignment_end = -1
        cursor = start
        quoted_identifier = False
        while cursor < end:
            character = source[cursor]
            if quoted_identifier:
                quoted_identifier = character != "»"
            elif character == "«":
                quoted_identifier = True
            elif character in closing:
                delimiter_stack.append(closing[character])
            elif delimiter_stack and character == delimiter_stack[-1]:
                delimiter_stack.pop()
            elif not delimiter_stack and source.startswith(":=", cursor):
                assignment_end = cursor + 2
                break
            cursor += 1
        if assignment_end < 0:
            return -1
        cursor = assignment_end
        quoted_identifier = False
        while cursor < end:
            character = source[cursor]
            if quoted_identifier:
                quoted_identifier = character != "»"
            elif character == "«":
                quoted_identifier = True
            elif character in closing:
                delimiter_stack.append(closing[character])
            elif delimiter_stack and character == delimiter_stack[-1]:
                delimiter_stack.pop()
            elif not delimiter_stack:
                if character == ";":
                    return cursor + 1
                if source.startswith("in", cursor):
                    previous = source[cursor - 1] if cursor > assignment_end else " "
                    following = source[cursor + 2] if cursor + 2 < end else " "
                    if not (previous.isalnum() or previous in "_'") and not (
                        following.isalnum() or following in "_'"
                    ):
                        return cursor + 2
            cursor += 1
        return -1

    for binder in _LOCAL_BINDER_RE.finditer(source):
        shadowed = {binder_name for binder_name in binder.group("names").split()}
        shadowed.intersection_update({"tsum", "tprod"})
        if not shadowed:
            continue
        scope_end = enclosing_scope_end(binder.start())
        for name in shadowed:
            blank_name(name, binder.start(), scope_end)
    for binder in _LOCAL_LET_RE.finditer(source):
        name = binder.group("name")
        blank_name(name, binder.start("name"), binder.end("name"))
        scope_end = enclosing_scope_end(
            binder.start(),
            stop_at_term_separator=False,
        )
        body_start = let_body_start(binder.end(), scope_end)
        if body_start >= 0:
            blank_name(name, body_start, scope_end)
    return "".join(output)


def detect_finset_reindexing_profile(text: str) -> FinsetReindexingProfile:
    """Return the finite-sum/product reindexing profile for a Lean statement."""

    raw = _blank_lean_comments_and_strings(str(text or ""))
    compact = " ".join(lean_statement_conclusion(raw).split())
    full_statement = " ".join(_blank_shadowed_infinite_bigop_names(raw).split())
    finite_sum_count = len(_FINITE_SUM_RE.findall(compact))
    finite_product_count = len(_FINITE_PRODUCT_RE.findall(compact))
    # Scope finite-pattern detection to the conclusion so sums mentioned only
    # in hypotheses do not activate this lane. Keep the infinite-bigop veto
    # conservative across the complete statement: generated scripts begin
    # with ``intros`` and must not enter a mixed finite/infinite context.
    has_infinite_sum = bool(_INFINITE_BIGOP_RE.search(full_statement))
    has_equality = bool(_EQUALITY_RE.search(compact))
    has_filter = " with " in compact or ".filter" in compact or "Finset.filter" in compact
    has_nested_sum = _has_syntactically_nested_bigop(compact, "∑")
    has_nested_product = _has_syntactically_nested_bigop(compact, "∏")
    has_antidiagonal = "antidiagonal" in compact
    has_range = "Finset.range" in compact or ".range" in compact
    has_interval = any(token in compact for token in ("Finset.Icc", "Finset.Ico", "Finset.Ioc", "Finset.Ioo"))
    has_attach = ".attach" in compact or "Finset.attach" in compact
    has_image_or_map = bool(
        re.search(
            r"(?:Finset\.(?:image|map)\b|\([^)]*Finset\.[^)]*\)\.(?:image|map)\b|\bFinset\.[A-Za-z0-9_'.]+\.(?:image|map)\b)",
            compact,
        )
    )
    has_sigma = ".sigma" in compact or "Finset.sigma" in compact or "Sigma" in compact
    should_attempt = bool(
        has_equality
        and not has_infinite_sum
        and (finite_sum_count > 0 or finite_product_count > 0)
    )
    return FinsetReindexingProfile(
        should_attempt=should_attempt,
        finite_sum_count=finite_sum_count,
        finite_product_count=finite_product_count,
        has_equality=has_equality,
        has_filter=has_filter,
        has_nested_sum=has_nested_sum,
        has_nested_product=has_nested_product,
        has_antidiagonal=has_antidiagonal,
        has_range=has_range,
        has_interval=has_interval,
        has_attach=has_attach,
        has_image_or_map=has_image_or_map,
        has_sigma=has_sigma,
        has_infinite_sum=has_infinite_sum,
    )


def finset_reindexing_scripts(
    profile: FinsetReindexingProfile,
    *,
    needs_intro: bool,
    max_scripts: int = 18,
) -> tuple[FinsetReindexingScript, ...]:
    """Generate bounded finite reindexing tactic scripts for a profile."""

    if not profile.should_attempt:
        return ()
    prefix = ("intros",) if needs_intro else ()
    scripts: list[FinsetReindexingScript] = []

    def add(lines: Sequence[str], *, tactic: str, source: str) -> None:
        full_lines = tuple([*prefix, *[str(line) for line in lines if str(line).strip()]])
        scripts.append(
            FinsetReindexingScript(
                lines=full_lines,
                tactic=("intros; " if prefix else "") + tactic,
                source=source,
            )
        )

    if profile.has_filter:
        add(
            ("classical", "simp [Finset.sum_filter, Finset.prod_filter]"),
            tactic="classical; simp [Finset.sum_filter, Finset.prod_filter]",
            source="finset_reindexing_filter_simp",
        )
    if profile.has_filter or profile.has_attach:
        add(
            (
                "classical",
                "simp [Finset.sum_filter, Finset.prod_filter, Finset.sum_attach, Finset.prod_attach]",
            ),
            tactic=(
                "classical; simp [Finset.sum_filter, Finset.prod_filter, "
                "Finset.sum_attach, Finset.prod_attach]"
            ),
            source="finset_reindexing_support_simp",
        )

    if profile.finite_sum_count > 0:
        _add_sum_scripts(add, profile)
    if profile.finite_product_count > 0:
        _add_product_scripts(add, profile)

    cap = max(0, int(max_scripts or 0))
    return tuple(scripts[:cap] if cap else ())


def finset_reindexing_context_key(text: str, helper_names: Sequence[str] = ()) -> str:
    """Build a stable exact-context key for one finite reindexing pass."""

    compact_goal = " ".join(str(text or "").split())
    helpers = ",".join(sorted(str(name or "").strip() for name in helper_names if str(name or "").strip()))
    return f"{compact_goal}|helpers={helpers}"


def reindexing_materializable_goals(attempts: Sequence[Any]) -> tuple[dict[str, Any], ...]:
    """Extract verified residual goals worth scheduling from failed attempts."""

    out: list[dict[str, Any]] = []
    seen_targets: set[str] = set()
    for attempt in list(attempts or ()):
        if not isinstance(attempt, dict):
            continue
        source = str(attempt.get("source") or "")
        if not source.startswith("finset_reindexing"):
            continue
        if not bool(attempt.get("partial_stub_validated", False)):
            continue
        proof = str(
            attempt.get("partial_proof_stub")
            or attempt.get("proof_stub")
            or ""
        ).strip()
        if not proof:
            continue
        for goal in list(attempt.get("remaining_goals") or ()):
            if not isinstance(goal, dict):
                continue
            target = str(goal.get("target") or "").strip()
            if not _is_materializable_reindexing_target(target):
                continue
            hypotheses = list(goal.get("hypotheses") or ())
            goal_key = target + "\n" + "\n".join(str(item or "") for item in hypotheses)
            if goal_key in seen_targets:
                continue
            out.append(
                {
                    "target": target,
                    "hypotheses": hypotheses,
                    "source": source,
                    "proof": proof,
                }
            )
            seen_targets.add(goal_key)
    return tuple(out)


def _add_sum_scripts(add: Any, profile: FinsetReindexingProfile) -> None:
    add(
        ("classical", "refine Finset.sum_congr rfl ?_", "intro x hx", "ring_nf"),
        tactic="classical; refine Finset.sum_congr rfl ?_; intro x hx; ring_nf",
        source="finset_reindexing_sum_congr_ring",
    )
    add(
        ("classical", "refine Finset.sum_congr rfl ?_", "intro x hx", "simp_all"),
        tactic="classical; refine Finset.sum_congr rfl ?_; intro x hx; simp_all",
        source="finset_reindexing_sum_congr_simp",
    )
    add(
        ("apply Finset.sum_congr",),
        tactic="apply Finset.sum_congr",
        source="finset_reindexing_sum_congr_residual",
    )
    add(
        (
            "classical",
            "refine Finset.sum_congr ?_ ?_",
            "· ext x",
            "  simp",
            "  omega",
            "· intro x hx",
            "  ring_nf",
        ),
        tactic=(
            "classical; refine Finset.sum_congr ?_ ?_; "
            "ext x; simp; omega; intro x hx; ring_nf"
        ),
        source="finset_reindexing_sum_ext_omega_ring",
    )
    add(
        (
            "classical",
            "refine Finset.sum_congr ?_ ?_",
            "· ext x",
            "  simp",
            "· intro x hx",
            "  simp_all",
        ),
        tactic=(
            "classical; refine Finset.sum_congr ?_ ?_; "
            "ext x; simp; intro x hx; simp_all"
        ),
        source="finset_reindexing_sum_ext_simp",
    )
    if profile.has_nested_sum:
        add(
            ("classical", "rw [Finset.sum_comm]"),
            tactic="classical; rw [Finset.sum_comm]",
            source="finset_reindexing_sum_comm",
        )
    if profile.has_sigma:
        add(
            ("classical", "rw [Finset.sum_sigma]"),
            tactic="classical; rw [Finset.sum_sigma]",
            source="finset_reindexing_sum_sigma",
        )
        add(
            ("classical", "rw [← Finset.sum_sigma]"),
            tactic="classical; rw [← Finset.sum_sigma]",
            source="finset_reindexing_sum_sigma_reverse",
        )
    if profile.has_range:
        add(
            ("classical", "rw [Finset.sum_range_succ]", "all_goals try omega"),
            tactic="classical; rw [Finset.sum_range_succ]; all_goals try omega",
            source="finset_reindexing_sum_range_succ",
        )
        add(
            ("classical", "rw [Finset.sum_range_succ']", "all_goals try omega"),
            tactic="classical; rw [Finset.sum_range_succ']; all_goals try omega",
            source="finset_reindexing_sum_range_succ_prime",
        )
    if profile.has_interval:
        add(
            ("classical", "rw [Finset.sum_Icc_succ_top]", "all_goals omega"),
            tactic="classical; rw [Finset.sum_Icc_succ_top]; all_goals omega",
            source="finset_reindexing_sum_Icc_succ_top",
        )
    if profile.has_attach:
        add(
            ("classical", "rw [Finset.sum_attach]"),
            tactic="classical; rw [Finset.sum_attach]",
            source="finset_reindexing_sum_attach",
        )
        add(
            ("classical", "rw [← Finset.sum_attach]"),
            tactic="classical; rw [← Finset.sum_attach]",
            source="finset_reindexing_sum_attach_reverse",
        )
    if profile.has_image_or_map:
        add(
            ("classical", "rw [Finset.sum_map]"),
            tactic="classical; rw [Finset.sum_map]",
            source="finset_reindexing_sum_map",
        )
        add(
            ("classical", "rw [Finset.sum_image]", "all_goals aesop"),
            tactic="classical; rw [Finset.sum_image]; all_goals aesop",
            source="finset_reindexing_sum_image",
        )
    if profile.has_antidiagonal:
        add(
            ("classical", "rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]", "all_goals try omega"),
            tactic=(
                "classical; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]; "
                "all_goals try omega"
            ),
            source="finset_reindexing_sum_antidiagonal_range",
        )
        add(
            ("classical", "rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ]", "all_goals try omega"),
            tactic=(
                "classical; rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ]; "
                "all_goals try omega"
            ),
            source="finset_reindexing_sum_antidiagonal_range_reverse",
        )


def _add_product_scripts(add: Any, profile: FinsetReindexingProfile) -> None:
    add(
        ("classical", "refine Finset.prod_congr rfl ?_", "intro x hx", "ring_nf"),
        tactic="classical; refine Finset.prod_congr rfl ?_; intro x hx; ring_nf",
        source="finset_reindexing_prod_congr_ring",
    )
    add(
        ("classical", "refine Finset.prod_congr rfl ?_", "intro x hx", "simp_all"),
        tactic="classical; refine Finset.prod_congr rfl ?_; intro x hx; simp_all",
        source="finset_reindexing_prod_congr_simp",
    )
    add(
        ("apply Finset.prod_congr",),
        tactic="apply Finset.prod_congr",
        source="finset_reindexing_prod_congr_residual",
    )
    if profile.has_nested_product:
        add(
            ("classical", "rw [Finset.prod_comm]"),
            tactic="classical; rw [Finset.prod_comm]",
            source="finset_reindexing_prod_comm",
        )
    if profile.has_range:
        add(
            ("classical", "rw [Finset.prod_range_succ]", "all_goals try omega"),
            tactic="classical; rw [Finset.prod_range_succ]; all_goals try omega",
            source="finset_reindexing_prod_range_succ",
        )
        add(
            ("classical", "rw [Finset.prod_range_succ']", "all_goals try omega"),
            tactic="classical; rw [Finset.prod_range_succ']; all_goals try omega",
            source="finset_reindexing_prod_range_succ_prime",
        )
    if profile.has_interval:
        add(
            ("classical", "rw [Finset.prod_Icc_succ_top]", "all_goals omega"),
            tactic="classical; rw [Finset.prod_Icc_succ_top]; all_goals omega",
            source="finset_reindexing_prod_Icc_succ_top",
        )
    if profile.has_attach:
        add(
            ("classical", "rw [Finset.prod_attach]"),
            tactic="classical; rw [Finset.prod_attach]",
            source="finset_reindexing_prod_attach",
        )
        add(
            ("classical", "rw [← Finset.prod_attach]"),
            tactic="classical; rw [← Finset.prod_attach]",
            source="finset_reindexing_prod_attach_reverse",
        )
    if profile.has_image_or_map:
        add(
            ("classical", "rw [Finset.prod_map]"),
            tactic="classical; rw [Finset.prod_map]",
            source="finset_reindexing_prod_map",
        )


def _is_materializable_reindexing_target(target: str) -> bool:
    compact = " ".join(str(target or "").split()).strip()
    if not compact or len(compact) > 500:
        return False
    if "?" in compact:
        return False
    if compact in {"True", "False"}:
        return False
    return any(
        marker in compact
        for marker in ("=", "↔", "∈", "≤", "<=", "<", ">", "≥", ">=", "∣")
    )


def _has_syntactically_nested_bigop(text: str, symbol: str) -> bool:
    raw = str(text or "")
    if symbol == "∑":
        return any(
            re.search(pattern, raw) is not None
            for pattern in (
                r"∑(?!')[^=]{0,180},\s*∑(?!')",
                r"∑(?!')[^=]{0,180}(?:=>|↦)\s*∑(?!')",
                r"Finset\.sum\b[^=]{0,220}(?:fun\s+\w+\s*=>\s*)Finset\.sum\b",
            )
        )
    if symbol == "∏":
        return any(
            re.search(pattern, raw) is not None
            for pattern in (
                r"∏[^=]{0,180},\s*∏",
                r"∏[^=]{0,180}(?:=>|↦)\s*∏",
                r"Finset\.prod\b[^=]{0,220}(?:fun\s+\w+\s*=>\s*)Finset\.prod\b",
            )
        )
    return False


__all__ = [
    "FinsetReindexingProfile",
    "FinsetReindexingScript",
    "detect_finset_reindexing_profile",
    "finset_reindexing_context_key",
    "finset_reindexing_scripts",
    "reindexing_materializable_goals",
]
