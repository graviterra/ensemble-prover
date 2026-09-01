"""Structured feedback formatter for Lean verification output.

Transforms ``LeanParseResult`` into LLM-friendly text that separates
error diagnosis, goal state, and actionable suggestions.  Wired into
the refinement pipeline so the refiner sees structured context instead
of raw Lean stderr.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, List, Optional

from .lean_parser import (
    LeanGoalState,
    LeanParseResult,
    canonical_error_type,
    diagnostic_headline,
)
from .utils import estimate_tokens

_LEAN_SUGGESTIONS_PROMPT_CAP = 5


@dataclass
class StructuredFeedback:
    """Formatted feedback ready for prompt insertion."""

    error_summary: str
    goal_states: str = ""
    suggestion: str = ""
    failed_strategies: str = ""
    raw_excerpt: str = ""
    error_details: str = ""
    diagnostics: str = ""
    lean_suggestions: List[str] = field(default_factory=list)
    domain_suggestion_branch: str = ""

    def to_prompt_block(self) -> str:
        parts = [f"Error type: {self.error_summary}"]
        if self.error_details:
            parts.append(f"Details:\n{self.error_details}")
        if self.diagnostics:
            parts.append(f"Diagnostics:\n{self.diagnostics}")
        if self.goal_states:
            parts.append(f"Current proof state:\n{self.goal_states}")
        if self.lean_suggestions:
            # Lean already vetted these (info-severity, in-block) via
            # extract_tactic_suggestions. Promote ahead of the templated Hint
            # and the truncated raw excerpt so the LLM treats Lean's emitted
            # closing tactic as the primary signal.
            bullets = "\n".join(f"  - {tac}" for tac in self.lean_suggestions)
            parts.append(f"Lean suggested closing tactic(s):\n{bullets}")
        if self.suggestion:
            parts.append(f"Hint: {self.suggestion}")
        if self.failed_strategies:
            parts.append(
                f"Strategies already failed on similar problems: {self.failed_strategies}"
            )
        if self.raw_excerpt:
            parts.append(f"Raw Lean output (excerpt):\n{self.raw_excerpt}")
        return "\n\n".join(parts)


# Error type -> actionable hint mapping
_ERROR_SUGGESTIONS = {
    "parse_error": (
        "Lean rejected the proof syntax before elaboration. Check tactic block "
        "structure, missing separators/indentation, and malformed `simp`/`calc` arguments."
    ),
    "timeout": (
        "Lean timed out (max heartbeats). Try a simpler tactic sequence, "
        "break the proof into smaller steps, or reduce heavy tactics like `simp`/`aesop`."
    ),
    "termination_failed": (
        "Lean rejected a recursive definition because it could not prove termination. "
        "Use structural recursion, add a decreasing argument, or supply a termination proof."
    ),
    "missing_instance": (
        "A typeclass instance is missing. Try `infer_instance`, "
        "add the necessary instance lemma, or open the right namespace."
    ),
    "type_mismatch": (
        "The proof term has the wrong type. Check that apply/exact targets "
        "match the goal type. Consider using `show`/`change` to clarify the expected type."
    ),
    "unknown_identifier": (
        "An identifier was not found. If it is a hypothesis, use the EXACT name from the "
        "goal state (including suffixes like ✝). Do NOT invent names like h1, h2. "
        "If it is a lemma, check Mathlib naming (e.g. Nat.add_comm not addComm). "
        "Try `exact?` or `apply?` to discover the correct name."
    ),
    "unification_failed": (
        "Unification failed. Make terms explicit, use `refine` or `apply` with arguments, "
        "or rewrite the goal to match the lemma's expected form."
    ),
    "binder_arity_mismatch": (
        "A binder-introducing tactic expected more binders than the goal exposes. "
        "Use fewer `intro`/`rintro` binders, or inspect whether the goal still starts with `∀`/`→`."
    ),
    "simp_no_progress": (
        "`simp` made no progress. Try `simp?`, add specific lemmas "
        "(`simp [lemma]`), or switch to `linarith`/`nlinarith` for arithmetic goals."
    ),
    "tactic_failed": (
        "The tactic made no progress or does not apply. Try a different tactic "
        "or provide explicit arguments. If simp failed, try `simp [lemma_name]` "
        "or switch to omega/linarith for arithmetic goals."
    ),
    "proposition_falsified": (
        "REFUTATION: Lean's decision procedure (`decide`/`Decidable.decide`) PROVED "
        "the goal is FALSE. The current concrete witness/value/equation does not hold. "
        "No tactic refinement can recover — the claim itself is mathematically wrong. "
        "Re-derive a different witness or revise the claim. If this is an existential "
        "(`∃ x, P x`), the chosen `x` does not satisfy `P`; pick another. If this is "
        "an equation with concrete numerals, the arithmetic does not balance; "
        "recompute and propose corrected values."
    ),
    "unsolved_goals": (
        "Goals remain after the tactic block. Address each remaining goal "
        "listed below. Consider `<;>` for branching or `all_goals` to handle "
        "multiple goals uniformly."
    ),
    "unknown_error": (
        "The error does not match a known category. Examine the raw Lean output "
        "below for the actual error message and adjust the proof accordingly."
    ),
}


# ---------------------------------------------------------------------------
# Domain-specific error pattern detection
# ---------------------------------------------------------------------------
# These patterns scan Lean diagnostics for specific failure reasons and
# provide precise, actionable guidance that the generic _ERROR_SUGGESTIONS
# cannot.  Order matters: first match wins.
#
# 2026-04-28 fix: patterns are SINGLE-LINE within a diagnostic message
# (no ``re.DOTALL``; ``.*`` replaced with ``[^\n]*``) and the scanner iterates
# ``parsed.diagnostics`` per-message rather than the unbounded raw blob. The
# previous DOTALL+unanchored design bridged source-code echo (e.g.,
# ``field_simp [h]`` shown by Lean's CLI) to unrelated "failed" tokens in
# later diagnostics, mis-firing the denominator-nonzero hint on type
# mismatches, parse errors, and unsolved-goal failures. cache.jsonl evidence:
# 25/137 field_simp records mis-fired the original pattern (e.g., "field_simp
# made no progress" — a simp_no_progress failure — got the
# establish-nonzeroness hint).

# Each entry: (branch_name, compiled_regex, suggestion_text). The branch name
# is exposed via ``StructuredFeedback.domain_suggestion_branch`` so live
# traces can measure which branch fires.
_DOMAIN_PATTERNS: List[tuple] = [
    # field_simp nonzero denominator failures
    (
        "field_simp",
        re.compile(
            r"field_simp[^\n]*failed|"
            r"failed to prove[^\n]*(?:nonzero|≠\s*0|!=\s*0)|"
            r"denominator[^\n]*(?:nonzero|not[^\n]*zero|≠\s*0)",
            re.IGNORECASE,
        ),
        (
            "`field_simp` failed because a denominator was not proven nonzero. "
            "Before calling `field_simp`, establish nonzeroness explicitly:\n"
            "  have hne : <denom> ≠ 0 := by positivity\n"
            "  field_simp [hne]\n"
            "If `positivity` fails, build the chain: prove the argument is > 0 "
            "via `nlinarith` or `linarith` from interval bounds, then use `ne_of_gt`."
        ),
    ),
    # positivity tactic failures
    (
        "positivity",
        re.compile(
            r"not a positivity\s+goal|"
            r"failed to prove (?:strict\s+)?positivity|"
            r"positivity[^\n]*failed|"
            r"failed to prove[^\n]*(?:nonneg|nonzero)",
            re.IGNORECASE,
        ),
        (
            "`positivity` could not close the goal. Build the positivity chain manually:\n"
            "  1. From interval bounds (e.g., x ∈ [2,4]), derive `0 < arg` via `linarith`\n"
            "  2. Use `Real.log_pos` (for `0 < log x` when `1 < x`) or `Real.sqrt_pos`\n"
            "  3. Chain: `have : 0 < a := by linarith; have : 0 < √a := Real.sqrt_pos.mpr this`\n"
            "  4. For `a ≠ 0`, use `ne_of_gt` on the positivity result."
        ),
    ),
    # integrability failures
    (
        "integrability",
        re.compile(
            r"IntervalIntegrable[^\n]*failed|"
            r"failed to prove[^\n]*(?:integrab|Integrable|measurab)|"
            r"Continuous(?:On)?[^\n]*failed",
            re.IGNORECASE,
        ),
        (
            "An integrability or continuity side condition failed. Try:\n"
            "  1. `apply ContinuousOn.intervalIntegrable` then prove continuity with `fun_prop`\n"
            "  2. For composed functions (f/g), use `ContinuousOn.div` and prove each part continuous\n"
            "  3. For `ContinuousOn.sqrt ∘ ContinuousOn.log`, prove the argument is positive on the interval\n"
            "  4. The custom tactic `prove_integrable` handles common patterns automatically."
        ),
    ),
    # calc step type mismatch (common with interval integrals)
    (
        "calc_step",
        re.compile(
            r"invalid\s+'calc'\s+step|invalid\s+`calc`\s+step",
            re.IGNORECASE,
        ),
        (
            "A `calc` step has the wrong left-hand side. Each calc step must chain: "
            "the LHS of step N+1 must exactly match the RHS of step N. Use `show` or `conv` "
            "to normalize before the calc chain, or replace calc with explicit `have` steps."
        ),
    ),
]


def helper_inventory_hint_for_unknown_identifier(
    identifier_name: str,
    dossier: Optional[Any],
) -> Optional[str]:
    """Build a helper-inventory hint for a hallucinated mini_* identifier.

    Returns the hint string (suitable for appending to LLM-facing feedback),
    or ``None`` if no hint should be injected (non-mini_* namespace, no
    dossier, missing block-getter, parse failures).

    This is the single source of truth used by BOTH feedback paths:
    ``build_structured_feedback`` (legacy orchestrator path) and
    ``FailureAnalyzer.format_feedback`` (mini_prover path). Targets the
    putnam_1978_b2 hallucination cascade where the LLM cited a non-existent
    ``outer_tsum_eval_p3_c1_v1`` helper 6 times in a row.

    The mini_* prefix gate uses startswith("mini_") — matches the
    ``_suggest_helper_name`` convention in mini_recursive.py. Mathlib-style
    identifiers fall through to the existing ``unknown_identifier`` advice
    (which points at ``exact?``/``apply?``).
    """
    name = str(identifier_name or "").strip()
    if not name or not name.startswith("mini_") or dossier is None:
        return None

    # Prefer the deduped LLM-facing view; fall back if the dossier predates
    # Fix 1 (e.g., a SimpleNamespace stub).
    blocks_getter = getattr(
        dossier, "verified_helper_blocks_unique_by_statement", None
    ) or getattr(dossier, "verified_helper_blocks", None)
    if blocks_getter is None:
        return None
    try:
        blocks = list(blocks_getter() or [])
    except Exception:
        return None

    # Call the canonical parser instead of duplicating regex logic. This
    # avoids the capability regression observed during adversarial review
    # (multiple `@[...]` attribute clauses were silently dropped by the
    # previous inline regex).
    from .proof_dossier import helper_decl_name

    helper_names: List[str] = []
    seen: set[str] = set()
    for block in blocks:
        text = str(block or "").strip()
        if not text:
            continue
        helper_name = helper_decl_name(text)
        if not helper_name:
            continue
        # Defense-in-depth: strip control chars from the parsed name before
        # it lands in an LLM prompt. Lean's «...» quoted identifiers can
        # contain whitespace; sanitize newlines/CR before bullet rendering.
        helper_name = (
            helper_name.replace("\r", " ").replace("\n", " ").strip()
        )
        if not helper_name or helper_name in seen:
            continue
        seen.add(helper_name)
        helper_names.append(helper_name)

    if helper_names:
        bullet = "\n  - ".join(helper_names)
        return (
            "AVAILABLE verified helpers for this problem "
            "(use ONLY these names, do not invent new ones):\n  - "
            + bullet
        )
    return (
        "No verified helpers exist for this problem yet. "
        "Do not cite a mini_* helper that has not been verified."
    )


def _inject_helper_inventory_for_unknown_identifier(
    details: List[str],
    identifier_name: str,
    dossier: Optional[Any],
) -> None:
    """Legacy in-place injector kept for ``build_structured_feedback`` callers."""
    hint = helper_inventory_hint_for_unknown_identifier(identifier_name, dossier)
    if hint is not None:
        details.append(hint)


def _detect_domain_suggestion(
    parsed: "Optional[LeanParseResult]" = None,
    raw_output: str = "",
) -> tuple[str, str]:
    """Scan Lean diagnostics for domain-specific error patterns.

    Returns a ``(suggestion_text, branch_name)`` tuple. ``branch_name`` is
    one of ``"field_simp"``, ``"positivity"``, ``"integrability"``,
    ``"calc_step"``, or ``""`` when no pattern matched.

    The scanner prefers per-diagnostic matching when ``parsed`` carries
    structured diagnostics — this prevents the historical bug where
    ``re.DOTALL``-style cross-boundary matching bridged source-code echo
    (e.g., ``field_simp [h]``) to unrelated ``failed`` tokens in later
    diagnostics, mis-firing the denominator-nonzero hint on type mismatches.
    Falls back to scanning ``raw_output`` only when ``parsed`` carries no
    diagnostics (e.g., raw-only verifier failures).

    Backward compatibility: legacy callers passing a single string are still
    accepted via the ``raw_output``-only path; ``parsed=None`` skips the
    structured pre-pass entirely.
    """
    diagnostics = []
    if parsed is not None:
        diagnostics = list(getattr(parsed, "diagnostics", None) or [])

    failed_tactic = ""
    if parsed is not None:
        failed_tactic = str(getattr(parsed, "failed_tactic", "") or "").strip()

    if diagnostics:
        for diag in diagnostics:
            severity = str(getattr(diag, "severity", "") or "").strip().lower()
            if severity and severity != "error":
                continue
            message = str(getattr(diag, "message", "") or "")
            if not message:
                continue
            for branch, pattern, suggestion in _DOMAIN_PATTERNS:
                if not pattern.search(message):
                    continue
                if branch == "field_simp" and failed_tactic and failed_tactic != "field_simp":
                    continue
                return suggestion, branch
        return "", ""

    if not raw_output:
        return "", ""
    for branch, pattern, suggestion in _DOMAIN_PATTERNS:
        if not pattern.search(raw_output):
            continue
        if branch == "field_simp" and failed_tactic and failed_tactic != "field_simp":
            continue
        return suggestion, branch
    return "", ""


def format_goal_state(goal: LeanGoalState) -> str:
    """Format a single goal with its hypotheses."""
    lines = []
    for hyp in goal.hypotheses:
        lines.append(f"  {hyp}")
    lines.append(f"  |- {goal.target}")
    return "\n".join(lines)


def classify_error(parsed: LeanParseResult) -> str:
    """Return a one-line error classification."""
    error_type = canonical_error_type(parsed)
    if error_type:
        return error_type
    if parsed.diagnostics:
        first = parsed.diagnostics[0]
        headline = (
            getattr(first, "summary", "") or diagnostic_headline(first.message)
        )[:80]
        if headline:
            return headline
    return "unknown_error"


def build_structured_feedback(
    parsed: Optional[LeanParseResult],
    raw_output: str,
    failed_strategies: Optional[List[str]] = None,
    *,
    max_goals: int = 3,
    max_hypotheses: int = 8,
    full_goal_state_budget_tokens: Optional[int] = None,
    full_goal_state_max_goals: Optional[int] = None,
    dossier: Optional[Any] = None,
) -> StructuredFeedback:
    """Build structured feedback from a Lean parse result."""
    if parsed is None:
        strat_text = ", ".join(failed_strategies) if failed_strategies else ""
        suggestion, domain_branch = _detect_domain_suggestion(None, raw_output)
        return StructuredFeedback(
            error_summary="parse_unavailable",
            error_details="",
            diagnostics="",
            goal_states="",
            suggestion=suggestion,
            failed_strategies=strat_text,
            raw_excerpt=raw_output[:1500],
            lean_suggestions=[],
            domain_suggestion_branch=domain_branch,
        )

    error_type = classify_error(parsed)
    # Domain-specific patterns override generic suggestions when a structured
    # diagnostic message reveals a specific failure reason. The scanner
    # prefers parsed.diagnostics over raw_output to prevent cross-diagnostic
    # false positives (e.g., source-echoed `field_simp [h]` bridging to an
    # unrelated `failed` token in a later diagnostic).
    suggestion, domain_branch = _detect_domain_suggestion(parsed, raw_output)
    if not suggestion:
        suggestion = _ERROR_SUGGESTIONS.get(error_type, "")
        # T2#7 root fix (2026-04-28): the priority classifier returns ONE
        # error_type. When `tactic_failed` and `unsolved_goals` co-occur
        # (cache.jsonl evidence: ~735/15,811 records), the LLM gets only the
        # tactic_failed advice, missing the "address each remaining goal"
        # framing. Compose hints when both Lean signals are present so the
        # LLM sees BOTH. Per "Lean = source of truth": both signals are
        # real Lean facts; the hint should not gate one on the other.
        if (
            error_type == "tactic_failed"
            and int(getattr(parsed, "unsolved_goal_count", 0) or 0) > 0
        ):
            unsolved_advice = _ERROR_SUGGESTIONS.get("unsolved_goals", "")
            if unsolved_advice and unsolved_advice not in suggestion:
                suggestion = f"{suggestion} {unsolved_advice}".strip()

    goal_blocks = []
    remaining = parsed.remaining_goals
    extra_goals = max(0, len(remaining) - max_goals)
    for goal in remaining[:max_goals]:
        if goal.hypotheses and len(goal.hypotheses) > max_hypotheses:
            trimmed = goal.hypotheses[:max_hypotheses]
            trimmed.append(
                f"... ({len(goal.hypotheses) - max_hypotheses} more hypotheses)"
            )
            goal_blocks.append(
                format_goal_state(LeanGoalState(goal.index, trimmed, goal.target))
            )
        else:
            goal_blocks.append(format_goal_state(goal))
    goal_states = "\n---\n".join(goal_blocks) if goal_blocks else ""
    if extra_goals > 0:
        goal_states += f"\n... ({extra_goals} more goals not shown)"

    # Optional: include full goal state (no hypothesis truncation) if it
    # fits within a token budget.  When full_goal_state_max_goals is not set,
    # fall back to max_goals so we never silently expand more goals than the
    # caller requested.
    budget = int(full_goal_state_budget_tokens or 0)
    if budget > 0 and remaining:
        max_full = (
            int(full_goal_state_max_goals)
            if full_goal_state_max_goals is not None
            else 0
        )
        goal_cap = max_full if max_full > 0 else max_goals
        if len(remaining) <= goal_cap:
            full_blocks = [format_goal_state(g) for g in remaining]
            full_text = "\n---\n".join(full_blocks)
            if estimate_tokens(full_text) <= budget:
                goal_states = full_text

    strat_text = ""
    if failed_strategies:
        strat_text = ", ".join(failed_strategies)

    details: List[str] = []
    if parsed.timeout:
        details.append("Timeout: maximum heartbeats exceeded")
    if parsed.failed_tactic:
        details.append(f"Failed tactic: {parsed.failed_tactic}")
    if parsed.unknown_identifier_name:
        details.append(f"Unknown identifier: {parsed.unknown_identifier_name}")
        # Fix 2 (2026-05-22): when the LLM cites a hallucinated mini_*
        # helper, append the actual verified-helper inventory so the next
        # turn can self-correct. This prevents repeated hallucinated-helper
        # cascades observed in long repair sessions.
        _inject_helper_inventory_for_unknown_identifier(
            details, parsed.unknown_identifier_name, dossier
        )
    # List available hypothesis names from all remaining goals so the LLM
    # can pick correct identifiers.  Useful for unknown_identifier AND for
    # tactic_failed/type_mismatch where the refiner needs to reference the
    # right hypothesis names.
    if remaining:
        seen: set[str] = set()
        avail: List[str] = []
        for g in remaining:
            for h in g.hypotheses or []:
                if ":" not in h:
                    continue
                name = h.split(":")[0].strip()
                if name and name not in seen:
                    seen.add(name)
                    avail.append(name)
        if avail:
            details.append(f"Available hypotheses: {', '.join(avail[:20])}")
    if parsed.missing_instance:
        details.append(f"Missing instance: {parsed.missing_instance}")
    if parsed.unification_failure:
        details.append(f"Unification failure: {parsed.unification_failure}")
    if parsed.simp_no_progress:
        details.append("Simp made no progress")
    if parsed.expected_type or parsed.actual_type:
        if parsed.expected_type:
            details.append(f"Expected type: {parsed.expected_type}")
        if parsed.actual_type:
            details.append(f"Actual type: {parsed.actual_type}")
    error_details = "\n".join(details)

    diagnostics = ""
    if parsed.diagnostics:
        diag_lines = []
        for d in parsed.diagnostics[:2]:
            file_short = d.file.split("/")[-1]
            summary = getattr(d, "summary", "") or diagnostic_headline(d.message)
            diag_lines.append(
                f"{d.severity}: {summary} ({file_short}:{d.line}:{d.col})"
            )
        diagnostics = "\n".join(diag_lines)

    # Surface Lean's `Try this:` output. The parser already vets these to
    # info-severity and in-block source lines (lean_parser.py:455-566); we
    # only need to dedup, drop blanks, and cap the count for prompt budget.
    lean_suggestions: List[str] = []
    seen_suggestions: set[str] = set()
    raw_suggestions = getattr(parsed, "suggestions", None) or []
    for tac in raw_suggestions:
        if not isinstance(tac, str):
            continue
        cleaned = tac.strip()
        if not cleaned or cleaned in seen_suggestions:
            continue
        seen_suggestions.add(cleaned)
        lean_suggestions.append(cleaned)
        if len(lean_suggestions) >= _LEAN_SUGGESTIONS_PROMPT_CAP:
            break

    return StructuredFeedback(
        error_summary=error_type,
        error_details=error_details,
        diagnostics=diagnostics,
        goal_states=goal_states,
        suggestion=suggestion,
        failed_strategies=strat_text,
        raw_excerpt=raw_output[:1500],
        lean_suggestions=lean_suggestions,
        domain_suggestion_branch=domain_branch,
    )
