"""Structured Lean 4 output parser.

Extracts diagnostics, remaining goals, sorry counts, and common error
patterns from ``lake env lean`` stderr/stdout.
"""

from __future__ import annotations

import logging
import math
import re
from dataclasses import dataclass, field
from typing import List, Optional

_log = logging.getLogger(__name__)


@dataclass
class LeanGoalState:
    """A single remaining proof goal extracted from Lean output."""

    index: int
    hypotheses: List[str]
    target: str


@dataclass
class LeanDiagnostic:
    """A single diagnostic message emitted by Lean."""

    file: str
    line: int
    col: int
    severity: str  # "error", "warning", "info"
    message: str
    summary: str = ""

    def __post_init__(self) -> None:
        if not self.summary and self.message:
            self.summary = diagnostic_preview(self.message)


@dataclass
class LeanParseResult:
    """Structured parse of Lean verification output."""

    ok: bool
    diagnostics: List[LeanDiagnostic] = field(default_factory=list)
    remaining_goals: List[LeanGoalState] = field(default_factory=list)
    sorry_count: int = 0
    unsolved_goal_count: int = 0
    termination_failed: bool = False
    parse_error: bool = False
    type_mismatch: bool = False
    unknown_identifier: bool = False
    tactic_failed: bool = False
    binder_arity_mismatch: bool = False
    simp_no_progress: bool = False
    unknown_universe: bool = False
    # Lean's decision-procedure refutation: `decide`, `Decidable.decide`,
    # etc. proved that the goal is FALSE (vs. true or undecidable). This
    # is a strong semantic verdict — no tactic refinement can recover
    # because the proposition itself is provably wrong. Distinct from
    # generic ``tactic_failed`` which only means "this attempt did not
    # close the goal." Surfaced to the planner as feedback so the LLM
    # can re-derive a different witness rather than retrying the same
    # mathematically-false claim.
    proposition_falsified: bool = False
    timeout: bool = False
    # Infrastructure failure: the verifier itself (persistent LSP worker,
    # subprocess, disk, transport) failed before Lean could run/finish.
    # Distinct from ``timeout`` which is a SEMANTIC Lean timeout
    # (heartbeats exceeded, deterministic-timeout tactic). Infra failures
    # are RETRYABLE without changing the proof — whereas a lean timeout
    # means the proof itself is too hard. Downstream routing must treat
    # these differently (e.g. scaffold activation should not burn 15
    # subset retries when every compile is hitting the SAME infra
    # failure).
    infra_failure: bool = False
    # Populated by LeanRunner's same-compilation ``#print axioms`` gate.
    # These fields are not inferred from ordinary diagnostics because the
    # audit has a stricter completeness contract than free-form Lean output.
    axiom_audit_ok: Optional[bool] = None
    axioms: List[str] = field(default_factory=list)
    unexpected_axioms: List[str] = field(default_factory=list)
    axiom_audit_error: str = ""
    expected_type: Optional[str] = None
    actual_type: Optional[str] = None
    unknown_identifier_name: Optional[str] = None
    unknown_universe_name: Optional[str] = None
    missing_instance: Optional[str] = None
    failed_tactic: Optional[str] = None
    unification_failure: Optional[str] = None
    raw: str = ""
    suggestions: List[str] = field(default_factory=list)


# ---- goal-state feature extraction ------------------------------------

# Bitmask flags for structural patterns detected in goal targets.
PATTERN_EQUALITY: int = 1
PATTERN_IFF: int = 2
PATTERN_FORALL: int = 4
PATTERN_EXISTS: int = 8
PATTERN_AND: int = 16
PATTERN_OR: int = 32
PATTERN_NOT: int = 64
PATTERN_LE_GE: int = 128
PATTERN_MEMBERSHIP: int = 256

_PATTERN_CHECKS = [
    (PATTERN_EQUALITY, re.compile(r"(?<![<>!=])=(?!=)")),
    (PATTERN_IFF, re.compile(r"\u2194|↔|\bIff\b")),
    (PATTERN_FORALL, re.compile(r"\u2200|∀|\bforall\b")),
    (PATTERN_EXISTS, re.compile(r"\u2203|∃|\bexists\b")),
    (PATTERN_AND, re.compile(r"\u2227|∧|\bAnd\b")),
    (PATTERN_OR, re.compile(r"\u2228|∨|\bOr\b")),
    (PATTERN_NOT, re.compile(r"\u00AC|¬|\bNot\b")),
    (PATTERN_LE_GE, re.compile(r"[<>]|\u2264|≤|\u2265|≥")),
    (PATTERN_MEMBERSHIP, re.compile(r"\u2208|∈")),
]

_ALL_PATTERNS_MASK: int = sum(flag for flag, _ in _PATTERN_CHECKS)


@dataclass
class GoalStateFeatures:
    """Rich structural features extracted from a Lean goal state."""

    goal_count: int
    total_hypothesis_count: int
    complexity_estimate: float
    has_type_mismatch: bool
    has_unknown_identifier: bool
    tactic_failed: bool
    progress_ratio: float
    pattern_flags: int  # bitmask of PATTERN_* constants
    avg_target_length: float
    max_nesting_depth: int

    def to_feature_vector(self) -> List[float]:
        """Flat float vector for ensemble scoring."""
        return [
            float(self.goal_count),
            float(self.total_hypothesis_count),
            self.complexity_estimate,
            float(self.has_type_mismatch),
            float(self.has_unknown_identifier),
            float(self.tactic_failed),
            self.progress_ratio,
            float(self.pattern_flags) / float(_ALL_PATTERNS_MASK or 1),
            self.avg_target_length / 100.0,
            float(self.max_nesting_depth) / 10.0,
        ]


def _nesting_depth(s: str) -> int:
    """Max parenthesis/bracket nesting depth."""
    depth = 0
    max_d = 0
    for ch in s:
        if ch in "([{":
            depth += 1
            if depth > max_d:
                max_d = depth
        elif ch in ")]}":
            depth = max(0, depth - 1)
    return max_d


def _complexity_estimate(targets: List[str]) -> float:
    """Estimate complexity from target strings (structure-aware heuristic)."""
    if not targets:
        return 0.0
    total = 0.0
    for t in targets:
        length_factor = len(t) / 120.0
        nesting_factor = _nesting_depth(t) / 6.0
        ops = len(re.findall(r"[+\-*/∧∨→↔∀∃¬≤≥=<>∈]", t))
        op_factor = ops / 12.0
        quant = t.count("∀") + t.count("∃")
        quant_factor = quant / 6.0
        rel = len(re.findall(r"[=<>≤≥≠∈]", t))
        rel_factor = rel / 8.0
        total += (
            0.45 * length_factor
            + 0.30 * nesting_factor
            + 0.15 * op_factor
            + 0.05 * quant_factor
            + 0.05 * rel_factor
        )
    return total / len(targets)


def _detect_patterns(targets: List[str]) -> int:
    """Detect structural patterns across all targets, return bitmask."""
    flags = 0
    combined = " ".join(targets)
    for flag, regex in _PATTERN_CHECKS:
        if regex.search(combined):
            flags |= flag
    return flags


def extract_goal_state_features(
    current_goals: List[LeanGoalState],
    initial_goals: List[LeanGoalState],
    parse_result: Optional[LeanParseResult] = None,
) -> GoalStateFeatures:
    """Extract rich structural features from a goal state."""
    targets = [g.target for g in current_goals]
    initial_count = max(1, len(initial_goals))
    current_count = len(current_goals)

    total_hyps = sum(len(g.hypotheses) for g in current_goals)
    avg_target_len = (sum(len(t) for t in targets) / len(targets)) if targets else 0.0
    max_nest = max((_nesting_depth(t) for t in targets), default=0)
    complexity = _complexity_estimate(targets)
    # Hypothesis density adds structural burden but should scale gently.
    complexity += 0.1 * math.log1p(total_hyps)
    progress = max(0.0, (initial_count - current_count) / initial_count)
    patterns = _detect_patterns(targets)

    return GoalStateFeatures(
        goal_count=current_count,
        total_hypothesis_count=total_hyps,
        complexity_estimate=complexity,
        has_type_mismatch=parse_result.type_mismatch if parse_result else False,
        has_unknown_identifier=(
            parse_result.unknown_identifier if parse_result else False
        ),
        tactic_failed=parse_result.tactic_failed if parse_result else False,
        progress_ratio=progress,
        pattern_flags=patterns,
        avg_target_length=avg_target_len,
        max_nesting_depth=max_nest,
    )


# ---- regexes ----------------------------------------------------------

_DIAG_RE = re.compile(
    r"^([^\n]+?):(\d+):(\d+):\s*(error|warning|info)(?:\([^)]+\))?:\s*"
    r"([\s\S]*?)(?=^(?:[^\n]+?):\d+:\d+:\s*(?:error|warning|info)(?:\([^)]+\))?:|\Z)",
    re.MULTILINE,
)

# Lean 4 unsolved goals block:
#   unsolved goals
#   case ...
#   hyp : T
#   ...
#   ⊢ target
_UNSOLVED_HEADER_RE = re.compile(r"unsolved goals?", re.IGNORECASE)
_TURNSTILE_RE = re.compile(r"^\s*⊢\s*(.+)$", re.MULTILINE)

_SORRY_RE = re.compile(r"\bsorry\b", re.IGNORECASE)
_REAL_SORRY_WARNING_RE = re.compile(
    r"(?:declaration\s+)?uses\s+[`']sorry[`']",
    re.IGNORECASE,
)
_SORRY_TACTIC_DOES_NOTHING_RE = re.compile(
    r"[`']sorry[`']\s+tactic does nothing",
    re.IGNORECASE,
)
_TYPE_MISMATCH_RE = re.compile(
    r"type mismatch|application type mismatch|invalid projection|non-propositional type|"
    r"invalid field|(?:'calc'|calc) expression has type|"
    r"failed to elaborate eliminator, expected type is not available|"
    r"function expected at|invalid constructor|mod_cast has type|invalid 'calc' step|"
    r"numerals are data in lean, but the expected type is a proposition|"
    r"expected type must not contain (?:free|meta) variables|"
    r"type of theorem\s+(?:'[^']+'|`[^`]+`)\s+is not a proposition",
    re.IGNORECASE,
)
_UNKNOWN_ID_RE = re.compile(
    r"unknown\s+(?:identifier|constant|declaration|namespace)",
    re.IGNORECASE,
)
_UNKNOWN_ID_PREFIX_RE = re.compile(
    r"unknown\s+(?:identifier|constant|declaration|namespace)\s+",
    re.IGNORECASE,
)
_TACTIC_FAILED_RE = re.compile(
    r"tactic\s+(?:'[^']+'|`[^`]+`)\s+failed|tactic .*? has not been implemented",
    re.IGNORECASE,
)
_QUOTED_TACTIC_FAILED_RE = re.compile(
    r"(?:'([^']+)'|`([^`]+)`)\s+tactic\s+failed",
    re.IGNORECASE,
)
_FAILED_SYNTH_RE = re.compile(r"failed to synthesize(?: instance)?", re.IGNORECASE)
_TYPECLASS_STUCK_RE = re.compile(
    r"typeclass instance problem is stuck",
    re.IGNORECASE,
)
_MISSING_INSTANCE_RE = re.compile(
    r"failed to synthesize(?: instance)?|typeclass instance problem is stuck",
    re.IGNORECASE,
)
_FAILED_TACTIC_NAME_RE = re.compile(
    r"tactic\s+(?:'([^']+)'|`([^`]+)`)\s+failed",
    re.IGNORECASE,
)
_BINDER_ARITY_MISMATCH_RE = re.compile(
    r"insufficient number of binders|"
    r"there are no additional binders(?: or [`']?let[`']? bindings)? in the goal to introduce",
    re.IGNORECASE,
)
# Unknown universe level (typically `Type u_N` referenced without a
# matching `universe u_N` declaration). When this fires, every
# downstream binder/intro tactic emits cascading errors because the
# elaborated goal is `S : sorry / inst : Mul sorry / ⊢ sorry`.
# Recognizing it as a distinct error type prevents the parser from
# flattening the symptom (introN failed) over the actual root cause
# (live trace 2001_a1_16apr_8.jsonl: 49 valid proofs misclassified).
_UNKNOWN_UNIVERSE_RE = re.compile(
    r"unknown universe level\s+[`']?([A-Za-z_][A-Za-z0-9_']*)[`']?",
    re.IGNORECASE,
)
_SIMP_NO_PROGRESS_RE = re.compile(
    r"\bsimp(?:_all)?\b[\s\S]{0,240}?made no progress",
    re.IGNORECASE,
)
_PARSE_ERROR_RE = re.compile(
    r"unexpected end of input|unexpected token|expected token|"
    r"unexpected [^;\n]+(?:;|,)\s*expected [^\n]+|"
    r"expected interpolated string|invalid pattern variable|"
    r"unexpected term .+ expected single reference to variable",
    re.IGNORECASE,
)
_TERMINATION_FAILED_RE = re.compile(
    r"fail to show termination for|termination check failed",
    re.IGNORECASE,
)
_NO_PROGRESS_TACTIC_RE = re.compile(
    r"\b([A-Za-z_][A-Za-z0-9_']*)\b made no progress",
    re.IGNORECASE,
)
_COULD_NOT_PROVE_GOAL_RE = re.compile(
    r"\b([A-Za-z_][A-Za-z0-9_']*)\b could not prove the goal",
    re.IGNORECASE,
)
_RCASES_TACTIC_FAILED_RE = re.compile(r"\brcases tactic failed\b", re.IGNORECASE)
_OBTAIN_TACTIC_FAILED_RE = re.compile(
    r"`?obtain`? requires either an expected type or a value",
    re.IGNORECASE,
)
_POSITIVITY_TACTIC_FAILED_RE = re.compile(
    r"not a positivity\s+goal|failed to prove (?:strict\s+)?positivity(?:/nonnegativity/nonzeroness)?",
    re.IGNORECASE,
)
_EXT_TACTIC_FAILED_RE = re.compile(
    r"no applicable extensionality theorem found for|"
    r"applyExtTheorem only applies to equations, not|"
    r"this extensionality tactic only applies to equalities, not",
    re.IGNORECASE,
)
_INVALID_ALT_NAME_RE = re.compile(
    r"invalid alternative name\s+(?:'[^']+'|`[^`]+`)\s*:\s*expected\s+(?:'[^']+'|`[^`]+`)",
    re.IGNORECASE,
)
_INVALID_ALT_NO_UNHANDLED_RE = re.compile(
    r"invalid alternative name\s+(?:'[^']+'|`[^`]+`)\s*:\s*there are no unhandled alternatives",
    re.IGNORECASE,
)
_DUPLICATE_ALT_NAME_RE = re.compile(
    r"duplicate alternative name\s+(?:'[^']+'|`[^`]+`)",
    re.IGNORECASE,
)
_INVALID_REWRITE_ARGUMENT_RE = re.compile(
    r"invalid rewrite argument:\s*expected an equality or iff proof or definition name",
    re.IGNORECASE,
)
_INVALID_TRIANGLE_NOTATION_RE = re.compile(
    r"invalid\s+(?:'▸'|`▸`|▸)\s+notation,\s*argument",
    re.IGNORECASE,
)
_DECISION_TACTIC_FAILED_RE = re.compile(
    r"tactic\s+(?:'([^']+)'|`([^`]+)`)\s+(?:proved that the proposition|evaluated that the proposition)",
    re.IGNORECASE,
)
_INTERVAL_CASES_FAILED_RE = re.compile(
    r"\binterval_cases failed:",
    re.IGNORECASE,
)
_INSUFFICIENT_TARGETS_RE = re.compile(
    r"\binsufficient number of targets for\b",
    re.IGNORECASE,
)
_NO_GOALS_TO_BE_SOLVED_RE = re.compile(
    r"\bno goals to be solved\b",
    re.IGNORECASE,
)
_UNIFICATION_FAILED_RE = re.compile(r"failed to unify|cannot unify", re.IGNORECASE)
_TIMEOUT_RE = re.compile(
    r"maximum heartbeats exceeded|maximum number of heartbeats .* has been reached|"
    r"time limit exceeded|lean timeout|fast[- ]fail timeout|timeout at `|"
    # The persistent LSP verifier emits this when Lean diagnostics don't
    # arrive within the per-request budget. Historically this string was
    # not matched, leading infra timeouts to be silently classified as
    # "no error, 0 unsolved goals" and routed as legitimate failures
    # through every downstream gate. See WORK_VALIDATION_LOG_2026-04-19.
    r"persistent verifier timed out",
    re.IGNORECASE,
)

# Infrastructure failure messages emitted by the persistent verifier
# transport / worker layer or by the subprocess runner itself. These
# indicate the verifier never ran to completion — the proof was neither
# accepted nor rejected by Lean. They are semantically "retryable"
# (unlike a Lean type error). Keep this list anchored to the strings
# actually emitted by the infra code:
#
#   ensemble_prover/persistent_verifier_worker.py:
#     - "persistent verifier timed out waiting for Lean diagnostics" (609)
#     - "persistent verifier worker crash: ..." (632)
#   ensemble_prover/persistent_verifier.py:
#     - "Lean timeout" (460, 479 — host-side LSP transport timeout,
#        emitted via _status_with_output as a trailing status label;
#        distinct from Lean's own "maximum heartbeats exceeded" which
#        uses different phrasing)
#     - "persistent verifier worker crashed" (496)
#     - "persistent verifier protocol desynchronization detected" (521)
#     - "unexpected persistent verifier message: ..." (609)
#     - "unexpected persistent verifier protocol: ..."
#     - "unexpected persistent verifier version: ..."
#     - "unexpected persistent verifier worker id: ..."
#     - "stale persistent verifier hello"
#     - "persistent verifier worker exited before reply"
#     - "invalid persistent verifier JSON"
#     - "persistent verifier pool unavailable"
#     - "no persistent verifier workers became available"
#   ensemble_prover/lean_runner.py / lean_server.py:
#     - "Lean timeout" (lake subprocess host-side timeout — runner
#        killed the process before Lean finished)
#     - "Lean subprocess error: ..." (subprocess raised an exception)
#     - "disk write failed" (temp-file write itself errored)
#   ensemble_prover/orchestrator.py:
#     - "candidate_check_exception: ..." (live verifier call raised before
#        Lean produced a verdict)
#
# Rather than enumerating every exact string, match on the sentinel
# substrings so future variants don't silently slip past. The
# ``\bLean timeout\b`` / ``Lean subprocess error`` patterns are
# distinctive enough that real Lean diagnostics don't emit them — Lean
# itself says ``maximum heartbeats exceeded`` or ``time limit exceeded``.
_INFRA_FAILURE_RE = re.compile(
    r"persistent verifier"
    r"|persistent verifier worker"
    r"|protocol desync"
    r"|\bLean timeout\b"
    r"|Lean subprocess error"
    r"|candidate_check_exception"
    r"|\bdisk write failed\b"
    r"|worker exited before reply"
    r"|no persistent verifier workers became available",
    re.IGNORECASE,
)

# Lean tactic suggestion output (`exact?`, `apply?`, `simp?`, `rw?`, `congr!`, ...)
_TRY_THIS_RE = re.compile(r"Try this:\s*(.+)")
_TRY_THESE_ITEM_RE = re.compile(r"\[(?:[A-Za-z_][A-Za-z0-9_']*(?:[?!])?)\]\s*(.+)")


def extract_tactic_suggestions(
    diagnostics: List[LeanDiagnostic],
    raw: str = "",
    *,
    goal_start_line: Optional[int] = None,
) -> List[str]:
    """Extract tactic suggestions from Lean info diagnostics AND raw output.

    Lean's ``exact?``, ``apply?``, ``simp?``, and ``rw?`` tactics emit
    suggestions as ``info``-level diagnostics.  However, the CLI output
    format is multi-line::

        file.lean:6:2: info: Try this:
          [apply] exact Nat.add_comm x y

    Diagnostics can arrive either as full multi-line blocks or as truncated
    CLI text, so we scan both structured diagnostic lines and the raw output
    text for ``[apply]``/``[exact]``-style items and ``Try this: <tactic>``
    patterns.

    When ``goal_start_line`` is provided, suggestions whose source line is
    BEFORE that line are rejected. This prevents harvesting ``Try this:``
    output from linters like ``Mathlib.Tactic.TacticAnalysis.introMerge``
    that fire against context-lemma bodies preceding the actual goal — see
    `WORK_VALIDATION_LOG_2026-04-24_oracle_try_this_harvest_root_fix.md`.
    """
    suggestions: List[str] = []
    seen: set[str] = set()
    rejected_off_block = 0

    def _line_in_goal(line_no: int) -> bool:
        if goal_start_line is None:
            return True
        return int(line_no) >= int(goal_start_line)

    # --- Pass 1: structured diagnostics ---
    # Pass 1 only accepts ``info`` severity; this correctly drops linter
    # ``warning`` suggestions like ``introMerge`` and ``unused variable``
    # tactic-stylization warnings even before the source-line filter.
    for d in diagnostics:
        if d.severity != "info":
            continue
        if not _line_in_goal(d.line):
            rejected_off_block += 1
            continue
        for line in str(d.message or "").splitlines():
            stripped = line.strip()
            m = _TRY_THIS_RE.search(stripped)
            if m:
                tactic = m.group(1).strip()
                if tactic and tactic not in seen and not tactic.startswith("["):
                    suggestions.append(tactic)
                    seen.add(tactic)
                continue
            m = _TRY_THESE_ITEM_RE.search(stripped)
            if m:
                tactic = m.group(1).strip()
                if tactic and tactic not in seen:
                    suggestions.append(tactic)
                    seen.add(tactic)

    # --- Pass 2: raw text scan (handles multi-line CLI output) ---
    # Re-walk diagnostic blocks via _DIAG_RE so each ``Try this:`` carries
    # its source line and severity. The previous unanchored ``raw.splitlines()``
    # scan was the load-bearing bug: any ``Try this:`` from any source position
    # got harvested, including from inside ``lemma`` bodies preceding the
    # goal — which produced cross-goal proof reuse and binder_arity_mismatch
    # cascades when context lemmas had consecutive ``intro`` calls.
    if raw:
        for m_diag in _DIAG_RE.finditer(raw):
            try:
                diag_line = int(m_diag.group(2))
            except (TypeError, ValueError):
                continue
            severity = (m_diag.group(4) or "").strip().lower()
            # Pass 2 must filter by severity too — suggestions from the
            # legitimate tactic oracle (``exact?`` / ``apply?`` / ...) come
            # through as ``info``. Linter ``warning`` "Try this:" output
            # is never a goal-closing tactic candidate.
            if severity != "info":
                continue
            if not _line_in_goal(diag_line):
                rejected_off_block += 1
                continue
            body = m_diag.group(5) or ""
            for body_line in body.splitlines():
                stripped = body_line.strip()
                if not stripped:
                    continue
                m = _TRY_THIS_RE.search(stripped)
                if m:
                    tactic = m.group(1).strip()
                    if tactic and tactic not in seen and not tactic.startswith("["):
                        suggestions.append(tactic)
                        seen.add(tactic)
                    continue
                m = _TRY_THESE_ITEM_RE.search(stripped)
                if m:
                    tactic = m.group(1).strip()
                    if tactic and tactic not in seen:
                        suggestions.append(tactic)
                        seen.add(tactic)

    if rejected_off_block:
        # Stash the count on the suggestions list via a side-channel attribute
        # so callers (parse_lean_output / oracle bookkeeping) can surface it
        # in run metrics. ``list`` doesn't natively support attributes, so
        # we wrap in a subclass instance only when needed.
        suggestions = _SuggestionList(suggestions)
        suggestions.rejected_off_block = rejected_off_block  # type: ignore[attr-defined]

    return suggestions


class _SuggestionList(list):
    """List subclass that allows attaching a ``rejected_off_block`` count.

    Lets ``parse_lean_output`` propagate the source-line filter telemetry
    without changing every caller's signature. A regular ``list`` instance
    is returned when no rejections occurred.
    """

    rejected_off_block: int = 0


def _next_nonempty_line(
    lines: List[str], start: int, *, max_lookahead: int = 6
) -> Optional[str]:
    for i in range(start, min(len(lines), start + max_lookahead)):
        line = lines[i].strip()
        if line:
            return line
    return None


def _extract_type_mismatch_details_from_text(
    text: str,
) -> tuple[Optional[str], Optional[str]]:
    """Extract expected/actual types from one type-mismatch diagnostic block."""
    lines = str(text or "").splitlines()
    actual = None
    expected = None
    for i, line in enumerate(lines):
        stripped = line.strip()
        low = stripped.lower()
        if actual is None and (
            low.startswith("has type")
            or low.startswith("'calc' expression has type")
            or low.startswith("calc expression has type")
            or low.startswith("mod_cast has type")
        ):
            actual = _next_nonempty_line(lines, i + 1, max_lookahead=len(lines))
        if "expected to have type" in low and expected is None:
            expected = _next_nonempty_line(lines, i + 1, max_lookahead=len(lines))
        if actual and expected:
            return (expected, actual)
    return (None, None)


def _extract_type_mismatch_details(
    raw: str,
    *,
    diagnostics: Optional[List[LeanDiagnostic]] = None,
) -> tuple[Optional[str], Optional[str]]:
    """Extract expected/actual types without crossing diagnostic boundaries."""
    candidate_texts: list[str] = []
    if diagnostics:
        candidate_texts.extend(
            d.message
            for d in diagnostics
            if d.severity == "error" and has_type_mismatch(d.message)
        )
    if not candidate_texts:
        candidate_texts.extend(
            m.group(5)
            for m in _DIAG_RE.finditer(raw)
            if m.group(4) == "error" and has_type_mismatch(m.group(5))
        )
    if not candidate_texts and has_type_mismatch(raw):
        candidate_texts.append(raw)
    for text in candidate_texts:
        expected, actual = _extract_type_mismatch_details_from_text(text)
        if expected or actual:
            return (expected, actual)
    return (None, None)


def _extract_unknown_identifier(raw: str) -> Optional[str]:
    m = _UNKNOWN_ID_PREFIX_RE.search(raw)
    if not m:
        return None
    tail = raw[m.end() :].lstrip()
    if not tail:
        return None
    ident = ""
    if tail[0] in {"'", "`"}:
        quote = tail[0]
        remainder = tail[1:]
        quote_idx = remainder.find(quote)
        if quote_idx >= 0:
            ident = remainder[:quote_idx]
        else:
            parts = remainder.split(None, 1)
            ident = parts[0] if parts else ""
    else:
        chars: list[str] = []
        for ch in tail:
            if ch.isspace() or ch in ",:;()[]{}":
                break
            chars.append(ch)
        ident = "".join(chars)
    ident = ident.strip().strip("`'\" ")
    if ident:
        return ident
    return None


_DIAG_HEADER_PREFIX_RE = re.compile(r"^[^\s:]+:\d+:\d+:\s*(?:error|warning|info):")
_GOAL_NOISE_PREFIX_RE = re.compile(r"^(?:error|warning|info|note):", re.IGNORECASE)
_GOAL_NOISE_LINE_RE = re.compile(
    r"^(?:error|warning|info|note):|^Try this:", re.IGNORECASE
)
_GOAL_EXPLANATORY_LABELS = {
    "explanation",
    "hint",
    "reason",
    "suggestion",
}
_GOAL_PROSE_START_RE = re.compile(
    r"^(?:the|a|an|this|that|these|those|try|use|because|failed|unable|expected|"
    r"actual|did|does|cannot|can't|could|should|would)\b",
    re.IGNORECASE,
)
_GOAL_PROSE_WORD_RE = re.compile(
    r"\b(?:tactic|constructor-based|reasoning|occurrence|failed|unable|"
    r"cannot|because|invalid|malformed)\b",
    re.IGNORECASE,
)
_GOAL_LEAN_TAIL_SIGNAL_RE = re.compile(
    r"(?:[=<>≤≥≠∈∉⊆⊂∣∧∨¬↔→∀∃λ]|->|=>|\bfun\b|\bby\b)"
)


def _lean_quoted_identifier_end(text: str, start: int) -> int:
    """Return the exclusive end of a Lean ``«... »`` identifier span."""

    raw = str(text or "")
    if not raw.startswith("«", start):
        return start
    end = raw.find("»", start + 1)
    return len(raw) if end < 0 else end + 1


def _split_goal_hypothesis_head(text: str) -> tuple[str, str, str]:
    raw = str(text or "")
    if not raw:
        return raw, "", ""

    closer_for = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    opener_for = {value: key for key, value in closer_for.items()}
    stack: list[str] = []
    idx = 0
    while idx < len(raw):
        if raw.startswith("«", idx):
            idx = _lean_quoted_identifier_end(raw, idx)
            continue
        ch = raw[idx]
        if ch in closer_for:
            stack.append(closer_for[ch])
            idx += 1
            continue
        if stack and ch == stack[-1]:
            stack.pop()
            idx += 1
            continue
        if not stack:
            if raw.startswith(":=", idx):
                return raw[:idx], ":=", raw[idx + 2 :]
            if ch == ":":
                return raw[:idx], ":", raw[idx + 1 :]
        elif ch in opener_for and ch != stack[-1]:
            # Ignore mismatched closers inside malformed fragments; the caller
            # will reject the line if the resulting head/tail look incomplete.
            pass
        idx += 1
    return raw, "", ""


def split_goal_definition_binding(text: str) -> tuple[str, str]:
    """Split a rendered local definition at its top-level ``:=``."""
    raw = str(text or "")
    if not raw:
        return "", ""

    closer_for = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    opener_for = {value: key for key, value in closer_for.items()}
    stack: list[str] = []
    idx = 0
    while idx < len(raw):
        if raw.startswith("«", idx):
            idx = _lean_quoted_identifier_end(raw, idx)
            continue
        ch = raw[idx]
        if ch in closer_for:
            stack.append(closer_for[ch])
            idx += 1
            continue
        if stack and ch == stack[-1]:
            stack.pop()
            idx += 1
            continue
        if not stack and raw.startswith(":=", idx):
            return raw[:idx], raw[idx + 2 :]
        if stack and ch in opener_for and ch != stack[-1]:
            # Ignore mismatched closers inside malformed fragments; callers
            # validate the resulting head and body before preserving the line.
            pass
        idx += 1
    return "", ""


def _goal_hypothesis_balance(text: str) -> int:
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    opens = set(pairs)
    closes = {v: k for k, v in pairs.items()}
    balance = 0
    raw = str(text or "")
    idx = 0
    while idx < len(raw):
        if raw.startswith("«", idx):
            idx = _lean_quoted_identifier_end(raw, idx)
            continue
        ch = raw[idx]
        if ch in opens:
            balance += 1
        elif ch in closes:
            balance = max(0, balance - 1)
        idx += 1
    return balance


def _goal_hypothesis_needs_continuation(text: str) -> bool:
    _head, sep, tail = _split_goal_hypothesis_head(text)
    if not sep:
        return False
    rhs = str(tail or "").strip()
    if not rhs:
        return True
    if _goal_hypothesis_balance(rhs) > 0:
        return True
    # Lean's pretty-printer wraps long hypothesis types across lines, typically
    # after a binary operator that requires a right operand. Without these
    # tokens in the continuation set, a wrapped hypothesis like
    #   h : ∀ x, √(log (9-x)) / (√(log (9-x)) + √(log (x+3))) +
    #     √(log (x+3)) / (√(log (x+3)) + √(log (9-x))) = 1
    # flushes the first line as a "complete" hypothesis and silently drops the
    # continuation — the resulting goal statement becomes unparseable when
    # re-elaborated (live trace 1987_b1_21ap_12.jsonl: 132 parse-error rejects
    # all ending in ``+)`` because the truncated hypothesis was wrapped as a
    # ``(h : ... +)`` Pi binder by ``_goal_state_with_target_body``).
    return rhs.endswith(
        (
            "→", "↔", "∧", "∨", ",", "(", "[", "{", "⦃",
            "+", "-", "*", "/", "=", "≠", "≤", "<", "≥", ">",
            "·", "∘", "∣", "^", "%",
            "⊕", "⊗", "⊔", "⊓", "∪", "∩",
            "∈", "∉",
        )
    )


def _goal_target_needs_continuation(text: str) -> bool:
    rhs = str(text or "").strip()
    if not rhs:
        return False
    if _goal_hypothesis_balance(rhs) > 0:
        return True
    return rhs.endswith(
        (
            "→", "->", "=>", "↔", "<->", "∧", "∨", ",", "(", "[", "{", "⦃",
            "+", "-", "*", "/", "=", "≠", "≤", "<", "≥", ">",
            "·", "∘", "∣", "^", "%",
            "⊕", "⊗", "⊔", "⊓", "∪", "∩",
            "∈", "∉",
        )
    )


def _is_goal_diagnostic_like_line(text: str) -> bool:
    stripped = str(text or "").strip()
    if not stripped:
        return False
    head, sep, tail = _split_goal_hypothesis_head(stripped)
    if sep == ":" and _looks_like_goal_explanatory_noise(head, tail):
        return True
    return bool(
        _DIAG_HEADER_PREFIX_RE.match(stripped)
        or _GOAL_NOISE_PREFIX_RE.match(stripped)
        or _GOAL_NOISE_LINE_RE.match(stripped)
        or has_tactic_failure(stripped)
        or has_parse_error(stripped)
        or has_type_mismatch(stripped)
        or has_unknown_identifier(stripped)
        or has_missing_instance(stripped)
        or has_unification_failure(stripped)
        or has_binder_arity_mismatch(stripped)
    )


def _looks_like_goal_explanatory_noise(head: str, tail: str) -> bool:
    label = str(head or "").strip().lower()
    body = str(tail or "").strip()
    if not label or not body:
        return False
    lean_signal = bool(_GOAL_LEAN_TAIL_SIGNAL_RE.search(body))
    if lean_signal:
        return False
    # Do not reject solely because the local hypothesis name is a familiar
    # English label. Lean can legitimately print `Reason : Nat` or
    # `Hint : Set Nat`; only the tail can prove the line is prose noise.
    labelled_explanation = label in _GOAL_EXPLANATORY_LABELS
    if "`" in body and _GOAL_PROSE_WORD_RE.search(body):
        return True
    if _GOAL_PROSE_START_RE.search(body) and (
        len(body.split()) >= 3 or labelled_explanation
    ):
        return True
    if _GOAL_PROSE_WORD_RE.search(body) and len(body.split()) >= 3:
        return True
    return False


def _looks_like_goal_hypothesis_head(head: str) -> bool:
    raw = str(head or "").strip()
    if not raw:
        return False
    if any(ch in raw for ch in "\n⊢,;"):
        return False
    # Lean's goal printer commonly emits grouped local hypotheses such as
    # `x y : Nat`. Parenthesized/binder syntax is not expected in a rendered
    # local-context line and is unsafe to wrap again as a Pi binder.
    tokens = re.findall(r"«[^»]+»|[^\s]+", raw)
    if not tokens:
        return False
    for token in tokens:
        if re.fullmatch(r"«[^»]+»", token):
            continue
        if not re.fullmatch(r"(?:[^\W\d]|_)[\w'✝]*", token, flags=re.UNICODE):
            return False
    return True


def _looks_like_single_goal_name(name: str) -> bool:
    raw = str(name or "").strip()
    if not raw or any(ch in raw for ch in "\n⊢,;"):
        return False
    if re.fullmatch(r"«[^»]+»", raw):
        return True
    return bool(re.fullmatch(r"(?:[^\W\d]|_)[\w'✝]*", raw, flags=re.UNICODE))


def _looks_like_goal_let_pattern_head(head: str) -> bool:
    raw = str(head or "").strip()
    if not raw or any(ch in raw for ch in "\n⊢;"):
        return False
    if not (
        (raw.startswith("(") and raw.endswith(")"))
        or (raw.startswith("⟨") and raw.endswith("⟩"))
    ):
        return False
    if _goal_hypothesis_balance(raw) != 0:
        return False
    return bool(re.search(r"(?:[^\W\d]|_)[\w'✝]*|«[^»]+»", raw, flags=re.UNICODE))


def _looks_like_goal_definition_head(head: str) -> bool:
    raw = str(head or "").strip()
    if not raw:
        return False
    has_let = raw.startswith("let ")
    if has_let:
        raw = raw[4:].strip()
    if not raw:
        return False
    name_part, sep, type_part = _split_goal_hypothesis_head(raw)
    if sep == ":":
        candidate_name = str(name_part or "").strip()
        type_text = str(type_part or "").strip()
        if type_text.startswith("let ") or " let " in type_text:
            return False
        if not (
            _looks_like_single_goal_name(candidate_name)
            or (has_let and _looks_like_goal_let_pattern_head(candidate_name))
        ):
            return False
        return _looks_like_goal_hypothesis_tail(type_part)
    if sep:
        return False
    return _looks_like_single_goal_name(raw) or (
        has_let and _looks_like_goal_let_pattern_head(raw)
    )


def _looks_like_goal_hypothesis_tail(tail: str) -> bool:
    body = str(tail or "").strip()
    if not body:
        return False
    if "\n" in body or "⊢" in body:
        return False
    if _looks_like_goal_explanatory_noise("", body):
        return False
    return True


def _looks_like_complete_goal_hypothesis(text: str) -> bool:
    stripped = str(text or "").strip()
    if not stripped or _is_goal_diagnostic_like_line(stripped):
        return False
    return bool(sanitize_goal_hypothesis(stripped))


def sanitize_goal_hypothesis(text: str) -> str:
    """Return a safe hypothesis line extracted from Lean goal output."""
    stripped = str(text or "").strip()
    if not stripped:
        return ""
    if _is_goal_diagnostic_like_line(stripped):
        return ""
    definition_head, definition_body = split_goal_definition_binding(stripped)
    if definition_head and definition_body:
        if (
            _looks_like_goal_definition_head(definition_head)
            and _looks_like_goal_hypothesis_tail(definition_body)
        ):
            return stripped
    head, sep, tail = _split_goal_hypothesis_head(stripped)
    if definition_head and definition_body and not (
        sep == ":" and "let " in str(tail or "").strip()
    ):
        return ""
    if not sep:
        return ""
    if not str(head or "").strip() or not str(tail or "").strip():
        return ""
    if not _looks_like_goal_hypothesis_head(head):
        return ""
    if not _looks_like_goal_hypothesis_tail(tail):
        return ""
    return stripped


def _extract_missing_instance(raw: str) -> Optional[str]:
    lines = raw.splitlines()
    for i, line in enumerate(lines):
        low = line.lower()
        if (
            "failed to synthesize" in low
            or "typeclass instance problem is stuck" in low
        ):
            detail = _next_nonempty_line(lines, i + 1)
            # Don't cross into a different diagnostic's header line.
            if detail and _DIAG_HEADER_PREFIX_RE.match(detail):
                return line.strip()
            return detail or line.strip()
    return None


def _extract_failed_tactic(raw: str) -> Optional[str]:
    m = _FAILED_TACTIC_NAME_RE.search(raw)
    if m:
        name = m.group(1) or m.group(2)
        if name:
            return name.strip()
    m = _QUOTED_TACTIC_FAILED_RE.search(raw)
    if m:
        name = m.group(1) or m.group(2)
        if name:
            return name.strip()
    m = _DECISION_TACTIC_FAILED_RE.search(raw)
    if m:
        name = m.group(1) or m.group(2)
        if name:
            return name.strip()
    m = _NO_PROGRESS_TACTIC_RE.search(raw)
    if m:
        return m.group(1).strip()
    m = _COULD_NOT_PROVE_GOAL_RE.search(raw)
    if m:
        return m.group(1).strip()
    if _RCASES_TACTIC_FAILED_RE.search(raw):
        return "rcases"
    if _INTERVAL_CASES_FAILED_RE.search(raw):
        return "interval_cases"
    if _OBTAIN_TACTIC_FAILED_RE.search(raw):
        return "obtain"
    if _POSITIVITY_TACTIC_FAILED_RE.search(raw):
        return "positivity"
    if _EXT_TACTIC_FAILED_RE.search(raw):
        return "ext"
    if _INVALID_REWRITE_ARGUMENT_RE.search(raw):
        return "rw"
    if _INVALID_TRIANGLE_NOTATION_RE.search(raw):
        return "▸"
    if (
        _INVALID_ALT_NAME_RE.search(raw)
        or _INVALID_ALT_NO_UNHANDLED_RE.search(raw)
        or _DUPLICATE_ALT_NAME_RE.search(raw)
    ):
        return "cases"
    return None


def _extract_unification_failure(raw: str) -> Optional[str]:
    for line in raw.splitlines():
        if _UNIFICATION_FAILED_RE.search(line):
            return line.strip()
    return None


def has_binder_arity_mismatch(text: str) -> bool:
    return bool(_BINDER_ARITY_MISMATCH_RE.search(str(text or "")))


def has_unknown_universe(text: str) -> bool:
    return bool(_UNKNOWN_UNIVERSE_RE.search(str(text or "")))


def _extract_unknown_universe_name(text: str) -> Optional[str]:
    match = _UNKNOWN_UNIVERSE_RE.search(str(text or ""))
    if match is None:
        return None
    name = (match.group(1) or "").strip()
    return name or None


def has_timeout(text: str) -> bool:
    return bool(_TIMEOUT_RE.search(str(text or "")))


def has_infra_failure(text: str) -> bool:
    """Detect infrastructure-layer verifier failures.

    Unlike ``has_timeout``, this matches errors from the LSP transport,
    persistent verifier worker, or subprocess harness — i.e. cases
    where Lean itself never reported a verdict on the proof. Callers
    should treat these as retryable rather than as authoritative
    "proof failed" signals.
    """
    return bool(_INFRA_FAILURE_RE.search(str(text or "")))


def has_simp_no_progress(text: str) -> bool:
    return bool(_SIMP_NO_PROGRESS_RE.search(str(text or "")))


def has_parse_error(text: str) -> bool:
    return bool(_PARSE_ERROR_RE.search(str(text or "")))


def has_termination_failure(text: str) -> bool:
    return bool(_TERMINATION_FAILED_RE.search(str(text or "")))


def has_type_mismatch(text: str) -> bool:
    return bool(_TYPE_MISMATCH_RE.search(str(text or "")))


def has_unknown_identifier(text: str) -> bool:
    return bool(_UNKNOWN_ID_RE.search(str(text or "")))


def has_missing_instance(text: str) -> bool:
    return bool(_MISSING_INSTANCE_RE.search(str(text or "")))


def has_unification_failure(text: str) -> bool:
    return bool(_UNIFICATION_FAILED_RE.search(str(text or "")))


def has_proposition_falsified(text: str) -> bool:
    """Detect Lean's decision-procedure refutation message.

    Lean emits the phrase ``tactic 'X' (proved|evaluated) that the proposition``
    UNIQUELY when a decision tactic (`decide`, `Decidable.decide`,
    `Bool.decide`, `Nat.decide`, etc.) refuted the goal — i.e. proved
    the goal is FALSE. Other failure modes (missing `Decidable`
    instance, non-reducing terms, heartbeat exhaustion) emit different
    phrasings and never use this exact wording.

    The full Lean output is multi-line:

        tactic 'decide' proved that the proposition
          ⊢ <goal-text>
        is false

    The first line alone is uniquely diagnostic. We do NOT require
    matching the ``is false`` token because line-by-line preview
    generation routinely drops trailing lines, but the verdict is
    already certain from the first-line phrasing.
    """
    return bool(_DECISION_TACTIC_FAILED_RE.search(str(text or "")))


def has_tactic_failure(text: str) -> bool:
    raw = str(text or "")
    return any(
        regex.search(raw)
        for regex in (
            _TACTIC_FAILED_RE,
            _QUOTED_TACTIC_FAILED_RE,
            _DECISION_TACTIC_FAILED_RE,
            _NO_PROGRESS_TACTIC_RE,
            _COULD_NOT_PROVE_GOAL_RE,
            _RCASES_TACTIC_FAILED_RE,
            _INTERVAL_CASES_FAILED_RE,
            _INSUFFICIENT_TARGETS_RE,
            _NO_GOALS_TO_BE_SOLVED_RE,
            _OBTAIN_TACTIC_FAILED_RE,
            _POSITIVITY_TACTIC_FAILED_RE,
            _EXT_TACTIC_FAILED_RE,
            _INVALID_ALT_NAME_RE,
            _INVALID_ALT_NO_UNHANDLED_RE,
            _DUPLICATE_ALT_NAME_RE,
            _INVALID_REWRITE_ARGUMENT_RE,
            _INVALID_TRIANGLE_NOTATION_RE,
        )
    )


def has_focus_structure_mismatch(text: str) -> bool:
    raw = str(text or "")
    return any(
        regex.search(raw)
        for regex in (
            _NO_GOALS_TO_BE_SOLVED_RE,
            _INVALID_ALT_NAME_RE,
            _INVALID_ALT_NO_UNHANDLED_RE,
            _DUPLICATE_ALT_NAME_RE,
            _INSUFFICIENT_TARGETS_RE,
        )
    )


# Keep parsed-flag and text-fallback classification in lockstep so mixed-signal
# diagnostics resolve to the same canonical family everywhere.
# Prefer explicit missing names over downstream instance fallout. Note:
# `unknown_universe` sits at the top because an undeclared universe
# variable turns the whole goal into `sorry / sorry / sorry / ⊢ sorry`,
# and every downstream tactic (intro, exact, rfl) emits cascading
# introN/type_mismatch errors. Without this priority, the parser flattens
# the whole diagnostic to binder_arity_mismatch and the LLM chases the
# wrong symptom (live trace 2001_a1_16apr_8.jsonl: 49 valid proofs
# misclassified this way). `type_mismatch` is placed above
# `binder_arity_mismatch` because the `introN failed: no additional
# binders` regex spuriously matches inside `simpa`/`simp` internal
# expansions when the real error is a type mismatch (live trace
# 2001_a1_16apr_7.jsonl: 73× identical regeneration cascade).
# `binder_arity_mismatch` stays ahead of generic
# `simp_no_progress`/`tactic_failed` for cases where the binder error
# truly is the top-level failure (e.g. `intro a b c` against a 2-binder
# goal — the only error Lean emits is introN).
_CANONICAL_ERROR_PRIORITY: tuple[str, ...] = (
    "infra_failure",
    "forbidden_axioms",
    "timeout",
    "unknown_universe",
    "termination_failed",
    "parse_error",
    "unknown_identifier",
    "missing_instance",
    # D1 fix (2026-05-08): ``proposition_falsified`` ranks above
    # ``type_mismatch``/``unification_failed`` because Lean's ``decide``
    # has DEFINITIVELY refuted the proposition. No witness polishing or
    # type alignment can recover a goal whose proposition is provably
    # false — the planner must revise the CLAIM, not the WITNESS. When
    # decide-refutation co-occurs with a unification/type-mismatch
    # cascade (common: metavar contexts where Lean reports both),
    # routing the LLM to "instantiate the lemma explicitly" wastes
    # budget on a witness that cannot exist (the putnam_2001_a5
    # wrong-witness loop pattern).
    "proposition_falsified",
    "type_mismatch",
    "unification_failed",
    "binder_arity_mismatch",
    "simp_no_progress",
    "tactic_failed",
)


def _first_matching_error_type(
    matches: dict[str, bool],
    *,
    unsolved_goal_count: int = 0,
    raw_text: str = "",
) -> str:
    for error_type in _CANONICAL_ERROR_PRIORITY:
        if matches.get(error_type, False):
            return error_type
    if unsolved_goal_count > 0 or "unsolved goals" in str(raw_text or "").lower():
        return "unsolved_goals"
    return ""


def prefer_canonical_error_type(*error_types: str) -> str:
    """Return the highest-priority non-empty error type from the canonical order."""
    matches = {error_type: False for error_type in _CANONICAL_ERROR_PRIORITY}
    for error_type in error_types:
        normalized = str(error_type or "").strip()
        if normalized in matches:
            matches[normalized] = True
    return _first_matching_error_type(matches)


def primary_error_type(parsed: LeanParseResult) -> str:
    return _first_matching_error_type(
        {
            "forbidden_axioms": bool(
                getattr(parsed, "unexpected_axioms", [])
            ),
            "timeout": bool(parsed.timeout),
            "infra_failure": bool(getattr(parsed, "infra_failure", False)),
            "unknown_universe": bool(getattr(parsed, "unknown_universe", False)),
            "termination_failed": bool(parsed.termination_failed),
            "parse_error": bool(parsed.parse_error),
            "unknown_identifier": bool(parsed.unknown_identifier),
            "missing_instance": bool(parsed.missing_instance),
            "type_mismatch": bool(parsed.type_mismatch),
            "unification_failed": bool(parsed.unification_failure),
            "proposition_falsified": bool(
                getattr(parsed, "proposition_falsified", False)
            ),
            "binder_arity_mismatch": bool(
                getattr(parsed, "binder_arity_mismatch", False)
            ),
            "simp_no_progress": bool(parsed.simp_no_progress),
            "tactic_failed": bool(parsed.tactic_failed),
        },
        unsolved_goal_count=int(parsed.unsolved_goal_count or 0),
    )


def fallback_error_type_from_text(text: str, *, unsolved_goal_count: int = 0) -> str:
    raw = str(text or "")
    return _first_matching_error_type(
        {
            "timeout": has_timeout(raw),
            "infra_failure": has_infra_failure(raw),
            "unknown_universe": has_unknown_universe(raw),
            "termination_failed": has_termination_failure(raw),
            "parse_error": has_parse_error(raw),
            "unknown_identifier": has_unknown_identifier(raw),
            "missing_instance": has_missing_instance(raw),
            "type_mismatch": has_type_mismatch(raw),
            "unification_failed": has_unification_failure(raw),
            "proposition_falsified": has_proposition_falsified(raw),
            "binder_arity_mismatch": has_binder_arity_mismatch(raw),
            "simp_no_progress": has_simp_no_progress(raw),
            "tactic_failed": has_tactic_failure(raw),
        },
        unsolved_goal_count=unsolved_goal_count,
        raw_text=raw,
    )


def _diagnostic_compact_lines(message: str) -> List[str]:
    # Lean diagnostics can contain terminal styling when they originate from
    # an interactive worker.  Preview text is persisted and later supplied to
    # models, so strip terminal escapes and non-printing controls here rather
    # than relying on every consumer to sanitize them independently.
    sanitized = re.sub(r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))", "", str(message or ""))
    sanitized = "".join(
        character
        for character in sanitized
        if character in {"\n", "\r", "\t"} or character.isprintable()
    )
    return [
        compact
        for compact in (
            " ".join(line.split()) for line in sanitized.splitlines()
        )
        if compact
    ]


def diagnostic_headline(message: str) -> str:
    """Return a stable one-line headline for a diagnostic message."""
    lines = _diagnostic_compact_lines(message)
    if not lines:
        return " ".join(str(message or "").split())
    headline = lines[0]
    if fallback_error_type_from_text(headline):
        return headline
    candidate = headline
    for line in lines[1:3]:
        candidate = f"{candidate} {line}"
        if fallback_error_type_from_text(candidate):
            return candidate
    return headline


def diagnostic_preview(message: str, *, canonical_error: str = "") -> str:
    """Return a bounded one-line diagnostic with a stable canonical headline.

    Lean normally places the actionable part of type/application diagnostics
    on continuation lines.  Keeping only the recognized headline loses the
    distinction between, for example, a bad argument and a wrong result type.
    The headline remains byte-for-byte compatible with the old formatter and
    decisive continuation lines are appended under a fixed budget.  Detail
    that would introduce a *different* canonical error class is excluded so a
    preview cannot silently change downstream error classification.
    """
    lines = _diagnostic_compact_lines(message)
    if not lines:
        return diagnostic_headline(message)
    target = canonical_error or fallback_error_type_from_text(str(message or ""))
    headline = ""
    if target:
        for line in lines[:3]:
            if fallback_error_type_from_text(line) == target:
                headline = line
                break
        candidate = ""
        if not headline:
            for line in lines[:3]:
                candidate = line if not candidate else f"{candidate} {line}"
                if fallback_error_type_from_text(candidate) == target:
                    headline = candidate
                    break
    if not headline:
        headline = diagnostic_headline(message)

    # A malformed/cascading diagnostic may mention a second, higher-priority
    # error much later in the block.  Detail selection follows the stable
    # headline's identity, not that unrelated tail, so enriching a preview
    # cannot reclassify its leading error.
    detail_target = fallback_error_type_from_text(headline) or target
    details = _diagnostic_decisive_details(
        lines,
        headline=headline,
        target=detail_target,
    )
    if not details:
        return _bounded_diagnostic_preview(headline)
    preview = f"{headline} | {' | '.join(details)}"
    return _bounded_diagnostic_preview(preview)


_DIAGNOSTIC_PREVIEW_LIMIT = 360
_DIAGNOSTIC_DETAIL_LIMIT = 150
_DIAGNOSTIC_DETAIL_MARKERS = (
    "has type",
    "but is expected to have type",
    "is expected to have type",
    "expected type",
    "actual type",
    "argument",
    "application",
    "function expected at",
    "failed to synthesize",
    "typeclass instance problem is stuck",
    "cannot unify",
    "failed to unify",
)


def _bounded_diagnostic_preview(text: str, *, limit: int = _DIAGNOSTIC_PREVIEW_LIMIT) -> str:
    compact = " ".join(str(text or "").split())
    if len(compact) <= limit:
        return compact
    return compact[: max(0, limit - 1)].rstrip() + "…"


def _diagnostic_decisive_details(
    lines: List[str],
    *,
    headline: str,
    target: str,
) -> List[str]:
    """Select bounded continuation detail without changing error identity."""
    if not target:
        return []
    normalized_headline = " ".join(headline.split())
    selected: List[str] = []
    seen = {normalized_headline}

    def admit(detail: str) -> None:
        compact = " ".join(str(detail or "").split())
        if not compact or compact in seen or compact == normalized_headline:
            return
        detail_error = fallback_error_type_from_text(compact)
        if detail_error and detail_error != target:
            return
        bounded = _bounded_diagnostic_preview(compact, limit=_DIAGNOSTIC_DETAIL_LIMIT)
        if bounded and bounded not in seen:
            seen.add(bounded)
            selected.append(bounded)

    relevant_targets = {"type_mismatch", "unification_failed", "missing_instance"}
    if target not in relevant_targets:
        return []

    for index, line in enumerate(lines):
        normalized = " ".join(line.split())
        low = normalized.lower()
        if normalized == normalized_headline:
            continue
        # A single Lean diagnostic block can contain a cascading diagnostic
        # after the useful continuation lines.  Stop at that new headline
        # instead of admitting its individually unclassified ``has type`` /
        # ``expected`` fragments as detail for the primary error.  Checking
        # the complete boundary line here is essential: classifying each
        # later fragment independently cannot recognize a multiline error.
        boundary_error = fallback_error_type_from_text(normalized)
        if boundary_error and boundary_error != target:
            break
        marker = next(
            (item for item in _DIAGNOSTIC_DETAIL_MARKERS if item in low),
            "",
        )
        if marker:
            if (
                target == "type_mismatch"
                and marker == "has type"
                and index > 0
                and any(
                    item in normalized_headline.lower()
                    for item in ("argument", "application")
                )
            ):
                previous = " ".join(lines[index - 1].split())
                if previous and previous != normalized_headline:
                    admit(f"failed argument/application: {previous}")
            admit(normalized)
            if index + 1 < len(lines):
                continuation = lines[index + 1]
                continuation_low = continuation.lower()
                # A marker's following line is normally the concrete term or
                # type.  Do not consume the next structural marker as if it
                # were that payload.
                if not any(
                    item in continuation_low for item in _DIAGNOSTIC_DETAIL_MARKERS
                ):
                    admit(continuation)
        elif target == "missing_instance" and not selected:
            # ``failed to synthesize`` is commonly the headline, followed by
            # the missing typeclass itself without a label.
            admit(normalized)
        if len(selected) >= 5:
            break
    return selected


def canonical_error_type(parsed: Optional[LeanParseResult]) -> str:
    """Return the canonical Lean error type for a parse result, if any."""
    if parsed is None:
        return ""
    error_type = primary_error_type(parsed)
    if error_type:
        return error_type
    err_msgs = "\n".join(
        str(d.message)
        for d in getattr(parsed, "diagnostics", [])
        if getattr(d, "severity", "") == "error"
    )
    raw = str(getattr(parsed, "raw", "") or "")
    text = err_msgs if err_msgs.strip() else raw
    return fallback_error_type_from_text(
        text,
        unsolved_goal_count=int(getattr(parsed, "unsolved_goal_count", 0) or 0),
    )


def _is_real_sorry_warning(text: str) -> bool:
    message = str(text or "")
    if not _REAL_SORRY_WARNING_RE.search(message):
        return False
    return not _SORRY_TACTIC_DOES_NOTHING_RE.search(message)


def parse_lean_output(
    raw: str,
    returncode: int,
    *,
    goal_start_line: Optional[int] = None,
) -> LeanParseResult:
    """Parse raw Lean output into a structured result.

    When ``goal_start_line`` is provided, ``Try this:`` suggestion harvesting
    is restricted to diagnostics whose source line is at or after that line.
    Callers building a Lean file with a context ``lemma`` block followed by
    a goal block should pass the goal block's starting line so suggestions
    from inside lemma bodies (notably the ``introMerge`` linter) are not
    promoted as candidate proofs for the goal.
    """
    ok = returncode == 0
    result = LeanParseResult(ok=ok, raw=raw)

    # Extract diagnostics
    for m in _DIAG_RE.finditer(raw):
        try:
            line = int(m.group(2))
            col = int(m.group(3))
        except ValueError:
            # Skip malformed diagnostic lines rather than crashing.
            continue
        result.diagnostics.append(
            LeanDiagnostic(
                file=m.group(1),
                line=line,
                col=col,
                severity=m.group(4),
                message=m.group(5).strip(),
                summary=diagnostic_preview(m.group(5).strip()),
            )
        )

    # sorry count: count diagnostic warnings about sorry, not raw text matches.
    # Lean 4 emits "declaration uses 'sorry'" as a warning.
    result.sorry_count = sum(
        1
        for d in result.diagnostics
        if d.severity == "warning" and _is_real_sorry_warning(d.message)
    )
    # Fallback: if no diagnostics were parsed, look for sorry mentions in
    # lines that resemble warnings/diagnostics.  Counting all "sorry" in the
    # entire raw output would false-positive on echoed source and error
    # context snippets (the proof being checked often *contains* "sorry").
    if result.sorry_count == 0:
        for raw_line in raw.splitlines():
            if _is_real_sorry_warning(raw_line) and (
                "warning" in raw_line.lower() or "declaration uses" in raw_line.lower()
            ):
                result.sorry_count += 1

    # Prefer structured error diagnostics to avoid false positives from echoed
    # source code, but recover any *missing* families from the raw output so
    # wrapped diagnostics do not disappear behind a different first-line match.
    _err_msgs = [d.message for d in result.diagnostics if d.severity == "error"]

    def _classify_texts(
        texts: List[str],
    ) -> tuple[bool, bool, bool, bool, bool, bool, bool, bool, bool]:
        termination_failed = False
        parse_error = False
        type_mismatch = False
        unknown_identifier = False
        tactic_failed = False
        binder_arity_mismatch = False
        missing_instance_like = False
        unification_failure_like = False
        simp_no_progress = False
        for text in texts:
            termination_failed = termination_failed or has_termination_failure(text)
            parse_error = parse_error or has_parse_error(text)
            type_mismatch = type_mismatch or has_type_mismatch(text)
            unknown_identifier = unknown_identifier or has_unknown_identifier(text)
            tactic_failed = tactic_failed or has_tactic_failure(text)
            binder_arity_mismatch = binder_arity_mismatch or has_binder_arity_mismatch(
                text
            )
            missing_instance_like = missing_instance_like or has_missing_instance(text)
            unification_failure_like = (
                unification_failure_like or has_unification_failure(text)
            )
            simp_no_progress = simp_no_progress or has_simp_no_progress(text)
        return (
            termination_failed,
            parse_error,
            type_mismatch,
            unknown_identifier,
            tactic_failed,
            binder_arity_mismatch,
            missing_instance_like,
            unification_failure_like,
            simp_no_progress,
        )

    _classification_texts = _err_msgs if _err_msgs else [raw]
    (
        termination_failed,
        parse_error,
        type_mismatch,
        unknown_identifier,
        tactic_failed,
        binder_arity_mismatch,
        missing_instance_like,
        unification_failure_like,
        simp_no_progress,
    ) = _classify_texts(_classification_texts)
    if _err_msgs:
        (
            raw_termination_failed,
            raw_parse_error,
            raw_type_mismatch,
            raw_unknown_identifier,
            raw_tactic_failed,
            raw_binder_arity_mismatch,
            raw_missing_instance_like,
            raw_unification_failure_like,
            raw_simp_no_progress,
        ) = _classify_texts([raw])
        termination_failed = termination_failed or raw_termination_failed
        parse_error = parse_error or raw_parse_error
        type_mismatch = type_mismatch or raw_type_mismatch
        unknown_identifier = unknown_identifier or raw_unknown_identifier
        # Do not OR tactic-failure phrases from the entire raw stream when
        # structured errors exist. Warning text may legitimately quote names
        # such as ``«tactic 'foo' failed»`` and otherwise contaminate a valid
        # residual state. Real tactic failures are classified from their error
        # diagnostics above; raw fallback remains available when no structured
        # error was parsed.
        binder_arity_mismatch = binder_arity_mismatch or raw_binder_arity_mismatch
        missing_instance_like = missing_instance_like or raw_missing_instance_like
        unification_failure_like = (
            unification_failure_like or raw_unification_failure_like
        )
        # Skip raw_simp_no_progress in the OR-merge: the simp_no_progress regex
        # uses a 240-char gap that can false-positive across diagnostic boundaries
        # when run on the full concatenated raw text (e.g. matching "simp" from one
        # diagnostic and "made no progress" from another).  The per-message
        # classification above is sufficient and boundary-safe.

    result.termination_failed = termination_failed
    result.parse_error = parse_error
    result.type_mismatch = type_mismatch
    result.unknown_identifier = unknown_identifier
    result.tactic_failed = tactic_failed
    result.binder_arity_mismatch = binder_arity_mismatch
    result.simp_no_progress = simp_no_progress
    # Decision-procedure refutation: search per-error-message AND raw to
    # catch wrapped diagnostics. The first-line phrasing is uniquely
    # diagnostic — see ``has_proposition_falsified`` for rationale.
    # ``tactic_failed`` remains True alongside (the tactic also failed
    # in the structural sense) but the canonical priority routes to
    # ``proposition_falsified`` first so downstream feedback can give
    # the planner the strong "your claim is mathematically false" verdict
    # rather than the generic "try a different tactic" advice.
    result.proposition_falsified = any(
        has_proposition_falsified(text) for text in (_err_msgs or [raw])
    ) or has_proposition_falsified(raw)
    # Unknown universe (e.g. `Type u_2` referenced without a matching
    # `universe u_2` declaration). Detected over both per-error-message
    # and raw text so we don't miss it whether Lean reports it as a
    # standalone error or wrapped in a multi-error diagnostic. Treated
    # as a structural top-priority error because every downstream
    # tactic emits cascading errors when this is unresolved.
    result.unknown_universe = any(
        has_unknown_universe(text) for text in (_err_msgs or [raw])
    ) or has_unknown_universe(raw)
    if result.unknown_universe:
        result.unknown_universe_name = _extract_unknown_universe_name(raw)
    # Timeout can originate from the runner (not a Lean diagnostic), keep raw search.
    result.timeout = has_timeout(raw)
    # Infrastructure failures (persistent verifier / subprocess / transport)
    # always originate from the runner layer and never appear as Lean
    # diagnostics. Detect from raw text so downstream routing can treat
    # them as retryable instead of authoritative compile failures.
    result.infra_failure = has_infra_failure(raw)
    # Detail extraction uses raw text but is gated on flags (confirmed real).
    if result.type_mismatch:
        result.expected_type, result.actual_type = _extract_type_mismatch_details(
            raw,
            diagnostics=result.diagnostics,
        )
    if result.unknown_identifier:
        result.unknown_identifier_name = _extract_unknown_identifier(raw)
    result.missing_instance = (
        _extract_missing_instance(raw) if missing_instance_like else None
    )
    result.failed_tactic = _extract_failed_tactic(raw) if result.tactic_failed else None
    result.unification_failure = (
        _extract_unification_failure(raw) if unification_failure_like else None
    )

    # Parse unsolved goals
    result.remaining_goals = _parse_unsolved_goals(raw)
    result.unsolved_goal_count = len(result.remaining_goals)

    # Extract tactic suggestions from info diagnostics AND raw output.
    # The raw text scan is critical because Lean's CLI emits multi-line
    # "Try this:" output where the actual tactic is on a continuation line
    # that _DIAG_RE never captures.
    result.suggestions = extract_tactic_suggestions(
        result.diagnostics, raw=raw, goal_start_line=goal_start_line
    )

    return result


def _parse_unsolved_goals(raw: str) -> List[LeanGoalState]:
    """Extract goal states from 'unsolved goals' blocks."""
    goals: List[LeanGoalState] = []
    sections = _UNSOLVED_HEADER_RE.split(raw)
    if len(sections) < 2:
        # No "unsolved goals" header.  Inline goals can still appear inside
        # error diagnostics, so feed only those bodies to the section parser
        # instead of the full raw output (which includes echoed source code).
        err_bodies = "\n".join(
            m.group(5) for m in _DIAG_RE.finditer(raw) if m.group(4) == "error"
        )
        if err_bodies:
            _extract_goals_from_section(err_bodies, goals)
        if goals:
            return goals
        for i, m in enumerate(_TURNSTILE_RE.finditer(raw)):
            goals.append(
                LeanGoalState(index=i, hypotheses=[], target=m.group(1).strip())
            )
        return goals

    # Process each section after the header
    for section in sections[1:]:
        _extract_goals_from_section(section, goals)
    return goals


def _extract_goals_from_section(section: str, goals: List[LeanGoalState]) -> None:
    """Extract individual goals from a single unsolved-goals section."""
    current_hyps: List[str] = []
    current_hyp_lines: List[str] = []
    current_target_lines: List[str] = []

    def _flush_hypothesis() -> None:
        nonlocal current_hyp_lines, current_hyps
        if not current_hyp_lines:
            return
        hypothesis = sanitize_goal_hypothesis(" ".join(current_hyp_lines))
        if hypothesis:
            current_hyps.append(hypothesis)
        current_hyp_lines = []

    def _flush_target() -> None:
        nonlocal current_hyps, current_target_lines
        _flush_hypothesis()
        if not current_target_lines:
            return
        target = " ".join(part for part in current_target_lines if part).strip()
        if target:
            idx = len(goals)
            goals.append(
                LeanGoalState(index=idx, hypotheses=list(current_hyps), target=target)
            )
        current_hyps = []
        current_target_lines = []

    for line in section.splitlines():
        raw_line = str(line or "")
        stripped = raw_line.strip()
        if not stripped:
            continue
        if _is_goal_diagnostic_like_line(stripped):
            _flush_hypothesis()
            if current_target_lines:
                _flush_target()
            continue
        if re.match(r"^case\s+", stripped):
            _flush_target()
            current_hyps = []
            continue
        m = re.match(r"^\s*⊢\s*(.*)$", raw_line)
        if m:
            _flush_hypothesis()
            _flush_target()
            current_target_lines = [m.group(1).strip()]
            continue
        if current_target_lines and raw_line[:1].isspace():
            current_target_lines.append(stripped)
            continue
        if current_target_lines:
            # Some goal renderings (and some non-"unsolved goals" diagnostics)
            # continue the target on the next line without leading indentation.
            # This commonly shows up with wrapped binary operators, where the
            # right operand is emitted on a fresh line starting at column 1.
            prev = (current_target_lines[-1] or "").rstrip()
            if _goal_target_needs_continuation(prev):
                current_target_lines.append(stripped)
                continue
        if current_target_lines:
            _flush_target()
        if current_hyp_lines and _goal_hypothesis_needs_continuation(" ".join(current_hyp_lines)):
            if _looks_like_complete_goal_hypothesis(stripped):
                _flush_hypothesis()
            else:
                current_hyp_lines.append(stripped)
                continue
        _flush_hypothesis()
        if ":" in stripped and not stripped.startswith("⊢"):
            head, sep, tail = _split_goal_hypothesis_head(stripped)
            if sanitize_goal_hypothesis(stripped) or (
                sep == ":"
                and _looks_like_goal_hypothesis_head(head)
                and not _looks_like_goal_explanatory_noise(head, tail)
            ):
                current_hyp_lines = [stripped]
    _flush_hypothesis()
    _flush_target()


def has_sorry(output: str) -> bool:
    """Check if Lean output indicates sorry usage."""
    return _is_real_sorry_warning(output)


def goal_count_from_output(raw: str) -> int:
    """Quick count of remaining goals via turnstile regex."""
    return len(_TURNSTILE_RE.findall(raw))


def progress_score(before_goals: int, after_goals: int, ok: bool) -> float:
    """Compute a [0.0, 1.0] progress metric.

    - 1.0 if the proof is complete (ok=True)
    - Partial credit for reducing goal count (only when after_goals > 0,
      meaning Lean actually reported remaining goals)
    - 0.0 if no progress, regression, or after_goals is 0 on a failure
      (0 unsolved goals on a failure means Lean didn't print goal state,
      not that all goals were closed)
    """
    if ok:
        return 1.0
    if before_goals <= 0:
        return 0.0
    # Clamp after_goals to non-negative to prevent score > 1.0
    after_goals = max(0, after_goals)
    # When after_goals is 0 on a failure, Lean didn't report any goal state
    # (e.g. type_mismatch, unknown_identifier).  Don't reward that as progress.
    if after_goals <= 0:
        return 0.0
    if after_goals >= before_goals:
        return 0.0
    return (before_goals - after_goals) / before_goals


def is_oracle_silent_success(parsed: LeanParseResult) -> bool:
    """Return True if a decision-procedure tactic closed the goal silently.

    Decision procedures (omega, ring, linarith, etc.) succeed with
    returncode=0 and no ``Try this:`` suggestions.  Under
    ``set_option warningAsError false``, remaining sorrys produce
    warnings (sorry_count > 0), not errors, so returncode can be 0
    even with unfilled holes.  Therefore both conditions are required:
    the file compiled AND no sorry declarations remain.
    """
    return parsed.ok and parsed.sorry_count == 0
