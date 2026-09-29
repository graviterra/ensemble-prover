"""Target-integrity signals for Lean-rejected proof attempts.

These checks do not prove that a graph target is false. They identify proof
attempts whose surrounding text or Lean diagnostics are unsafe to treat as
ordinary local proof-search failures.
"""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Tuple

from .mini_lean_extract import _lean_comment_text


_REFUTATION_PATTERNS: Tuple[Tuple[re.Pattern[str], str], ...] = (
    (
        re.compile(
            r"\bclaim\s+(?:is|was)\s+(?:mathematically\s+)?false\b",
            re.IGNORECASE,
        ),
        "claim is false",
    ),
    (
        re.compile(
            r"\bstatement\s+(?:is|was)\s+(?:mathematically\s+)?false\b",
            re.IGNORECASE,
        ),
        "statement is false",
    ),
    (
        re.compile(
            r"\btarget\s+(?:is|was)\s+(?:mathematically\s+)?false\b",
            re.IGNORECASE,
        ),
        "target is false",
    ),
    (
        re.compile(
            r"\broute\s+(?:is|was)\s+(?:mathematically\s+)?false\b",
            re.IGNORECASE,
        ),
        "route is false",
    ),
    (
        re.compile(r"\bnot\s+provable\s+as\s+stated\b", re.IGNORECASE),
        "not provable as stated",
    ),
    (
        re.compile(
            r"\b(?:claim|statement|target|assertion)\b[^\n]{0,120}"
            r"\bnot\s+derivable\b",
            re.IGNORECASE,
        ),
        "not derivable",
    ),
    (
        re.compile(
            r"\bcannot\s+be\s+derived\s+from\s+(?:the\s+)?(?:given\s+)?"
            r"(?:hypotheses|hypothesis|assumptions)\b",
            re.IGNORECASE,
        ),
        "cannot be derived",
    ),
    (
        re.compile(
            r"\bdoes\s+not\s+follow\s+from\s+(?:the\s+)?(?:given\s+)?"
            r"(?:hypotheses|hypothesis|assumptions)\b",
            re.IGNORECASE,
        ),
        "does not follow",
    ),
    (
        re.compile(r"\bcounterexample\s*:", re.IGNORECASE),
        "counterexample",
    ),
    (
        re.compile(
            r"\bcounterexample\s+(?:is|would\s+be|take|takes)\b",
            re.IGNORECASE,
        ),
        "counterexample",
    ),
)

_REFUTATION_EXCLUSION_RE = re.compile(
    r"\b(?:no|not|without)\s+counterexamples?\b|"
    r"\b(?:exclude|excluded|excludes|rule out|rules out)\s+counterexamples?\b",
    re.IGNORECASE,
)

_CONTRADICTION_ASSUMPTION_RE = re.compile(
    r"\b(?:assume|suppose)\s+(?:the\s+)?(?:claim|statement|target|route)\s+"
    r"(?:is|was)\s+false\b|"
    r"\bby\s+contradiction\b[^\n]{0,160}\b(?:claim|statement|target|route)\s+"
    r"(?:is|was)\s+false\b|"
    r"\b(?:claim|statement|target|route)\s+(?:is|was)\s+false\b[^\n]{0,160}"
    r"\b(?:derive|obtain|reach)\s+(?:a\s+)?contradiction\b",
    re.IGNORECASE,
)

_LEAN_BY_CONTRA_RE = re.compile(r"\bby_contra\b|\bbyContradiction\b")

_FAKE_CONTRADICTION_PATTERNS: Tuple[Tuple[re.Pattern[str], str], ...] = (
    (
        re.compile(
            r"\b(?:claim|statement|target|assertion)\b[^\n]{0,120}"
            r"\bnot\s+mathematically\s+correct\b|"
            r"\bnot\s+mathematically\s+correct\b[^\n]{0,120}"
            r"\b(?:claim|statement|target|assertion)\b",
            re.IGNORECASE,
        ),
        "target not mathematically correct",
    ),
    (
        re.compile(
            r"\b(?:cannot|can't|can\s+not|impossible\s+to)\s+"
            r"(?:derive|obtain|reach)\s+(?:a\s+)?contradiction\b",
            re.IGNORECASE,
        ),
        "cannot derive contradiction",
    ),
    (
        re.compile(
            r"\b(?:no|not)\s+(?:way|possible)\s+to\s+"
            r"(?:derive|obtain|reach)\s+(?:a\s+)?contradiction\b",
            re.IGNORECASE,
        ),
        "impossible to derive contradiction",
    ),
    (
        re.compile(r"\bFalse\b\s+is\s+not\s+derivable\b", re.IGNORECASE),
        "False is not derivable",
    ),
    (
        re.compile(r"\bNo\s+contradiction\s+can\s+be\s+derived\b", re.IGNORECASE),
        "no contradiction can be derived",
    ),
    (
        re.compile(
            r"\bonly\s+way\s+to\s+close\b[^\n]{0,160}\bnot\b",
            re.IGNORECASE,
        ),
        "only way to close is invalid",
    ),
)

_TARGET_INTEGRITY_WORK_TYPES = frozenset(
    {
        "",
        "assemble_route",
        "child_llm_prove",
        "formalize_claim",
        "formalize_missing_obligation",
        "mine_missing_obligation",
        "prove_claim_variant",
        "root_repair",
        "route_replan",
    }
)

_TARGET_INTEGRITY_EXCLUDED_WORK_TYPE_FRAGMENTS = (
    "adjudicat",
    "api_search",
    "counterexample",
    "decl_probe",
    "materialize_replay_source",
    "retrieval",
    "tactic_swarm",
)


def _one_line(text: str, *, limit: int = 180) -> str:
    value = " ".join(str(text or "").split())
    if len(value) <= limit:
        return value
    return value[: max(0, limit - 3)].rstrip() + "..."


def _first_match(
    text: str,
    patterns: Tuple[Tuple[re.Pattern[str], str], ...],
) -> Optional[Tuple[str, str]]:
    for regex, label in patterns:
        match = regex.search(text)
        if match:
            return label, _one_line(match.group(0))
    return None


def _counterexample_refutation_excluded(text: str, match: re.Match[str]) -> bool:
    start = max(0, match.start() - 80)
    end = min(len(text), match.end() + 80)
    for exclusion in _REFUTATION_EXCLUSION_RE.finditer(text[start:end]):
        exclusion_start = start + exclusion.start()
        exclusion_end = start + exclusion.end()
        if exclusion_start <= match.start() <= exclusion_end:
            return True
    return False


def _first_refutation_match(text: str) -> Optional[Tuple[str, str]]:
    for regex, label in _REFUTATION_PATTERNS:
        match = regex.search(text)
        if not match:
            continue
        if label == "counterexample" and _counterexample_refutation_excluded(
            text, match
        ):
            continue
        return label, _one_line(match.group(0))
    return None


def _looks_like_contradiction_assumption(text: str, proof: str) -> bool:
    """Recognize false-assumption setup, not target-retirement prose."""

    combined = str(text or "")
    if not _CONTRADICTION_ASSUMPTION_RE.search(combined):
        return False
    if re.search(r"\bcounterexample\s*:", combined, re.IGNORECASE):
        return False
    if re.search(
        r"\b(?:not\s+provable\s+as\s+stated|does\s+not\s+follow|"
        r"not\s+derivable|cannot\s+be\s+derived)\b",
        combined,
        re.IGNORECASE,
    ):
        return False
    return bool(
        _LEAN_BY_CONTRA_RE.search(str(proof or ""))
        or re.search(
            r"\b(?:derive|obtain|reach)\s+(?:a\s+)?contradiction\b",
            combined,
            re.IGNORECASE,
        )
    )


def _is_parse_error_analysis(analysis: Dict[str, Any]) -> bool:
    error_type = str((analysis or {}).get("error_type") or "").strip().lower()
    if error_type in {"parse_error", "syntax_error"}:
        return True
    family = str((analysis or {}).get("failure_family") or "").strip().lower()
    return family in {"parse_error", "syntax_error", "code_generation"}


def _proof_comment_text(proof: str) -> str:
    try:
        return _lean_comment_text(str(proof or ""))
    except Exception:
        return ""


def _bridge_type_text(text: str) -> str:
    value = " ".join(str(text or "").split()).strip()
    value = re.sub(r"\s*(<=|≤)\s*", r"\1", value)
    value = re.sub(r"\s*([()+*/=,:])\s*", r"\1", value)
    value = re.sub(r"\s+-\s*", "-", value)
    return value


def _outer_parens_wrap(text: str) -> bool:
    value = str(text or "").strip()
    if len(value) < 2 or not (value.startswith("(") and value.endswith(")")):
        return False
    depth = 0
    for index, char in enumerate(value):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0 and index != len(value) - 1:
                return False
        if depth < 0:
            return False
    return depth == 0


def _strip_outer_parens(text: str) -> str:
    value = str(text or "").strip()
    while _outer_parens_wrap(value):
        value = value[1:-1].strip()
    return value


def _split_top_level_plus(text: str) -> List[str]:
    value = str(text or "").strip()
    parts: List[str] = []
    start = 0
    depth = 0
    for index, char in enumerate(value):
        if char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        elif char == "+" and depth == 0:
            part = _strip_outer_parens(value[start:index])
            if part:
                parts.append(part)
            start = index + 1
    tail = _strip_outer_parens(value[start:])
    if tail:
        parts.append(tail)
    return parts


def _split_le_type(text: str) -> Optional[Tuple[str, str]]:
    compact = _bridge_type_text(text)
    marker = "≤" if "≤" in compact else "<=" if "<=" in compact else ""
    if not marker:
        return None
    left, right = compact.split(marker, 1)
    if not left or not right:
        return None
    return left, right


def _looks_like_dropped_summand(expected: str, actual: str) -> bool:
    expected_parts = _split_le_type(expected)
    actual_parts = _split_le_type(actual)
    if expected_parts is None or actual_parts is None:
        return False
    expected_left, expected_right = expected_parts
    actual_left, actual_right = actual_parts
    if expected_left != actual_left:
        return False
    expected_right = _strip_outer_parens(expected_right)
    actual_terms = _split_top_level_plus(actual_right)
    return len(actual_terms) > 1 and expected_right in actual_terms


def _looks_like_reversed_nonnegative(expected: str, actual: str) -> bool:
    expected_parts = _split_le_type(expected)
    actual_parts = _split_le_type(actual)
    if expected_parts is None or actual_parts is None:
        return False
    expected_left, expected_right = expected_parts
    actual_left, actual_right = actual_parts
    return actual_left == "0" and expected_right == "0" and actual_right == expected_left


def _diagnostic_expected_actual_pairs(analysis: Dict[str, Any]) -> List[Tuple[str, str]]:
    pairs: List[Tuple[str, str]] = []
    details = analysis.get("details")
    if isinstance(details, dict):
        expected = str(details.get("expected_type") or "").strip()
        actual = str(details.get("actual_type") or "").strip()
        if expected and actual:
            pairs.append((expected, actual))
    for diag in list(analysis.get("diagnostics") or []):
        if not isinstance(diag, dict):
            continue
        message = str(diag.get("message") or "").strip()
        if not message:
            continue
        actual_match = re.search(
            r"has type\s+(.+?)\s+but is expected to have type\s+(.+?)(?:$|\n)",
            message,
            re.IGNORECASE | re.DOTALL,
        )
        if actual_match:
            pairs.append((actual_match.group(2).strip(), actual_match.group(1).strip()))
            continue
        expected_match = re.search(
            r"expected.*?type\s+(.+?)(?:$|\n).*?actual.*?type\s+(.+?)(?:$|\n)",
            message,
            re.IGNORECASE | re.DOTALL,
        )
        if expected_match:
            pairs.append((expected_match.group(1).strip(), expected_match.group(2).strip()))
    return pairs


def _semantic_bridge_direction_signal(
    analysis: Dict[str, Any],
) -> Optional[Dict[str, Any]]:
    for expected, actual in _diagnostic_expected_actual_pairs(analysis):
        if _looks_like_dropped_summand(expected, actual):
            return {
                "kind": "semantic_bridge_direction",
                "match": "dropped summand from inequality",
                "expected_type": expected,
                "actual_type": actual,
            }
        if _looks_like_reversed_nonnegative(expected, actual):
            return {
                "kind": "semantic_bridge_direction",
                "match": "reversed nonnegative inequality",
                "expected_type": expected,
                "actual_type": actual,
            }
    return None


def _target_integrity_enabled_for_work_type(selected_work_type: str) -> bool:
    work_type = str(selected_work_type or "").strip()
    lowered = work_type.lower()
    if any(fragment in lowered for fragment in _TARGET_INTEGRITY_EXCLUDED_WORK_TYPE_FRAGMENTS):
        return False
    return work_type in _TARGET_INTEGRITY_WORK_TYPES


def _base_signal(kind: str, match: str, target_statement: str) -> Dict[str, Any]:
    metric = {
        "fake_contradiction_commentary": (
            "mini_session_target_integrity_fake_contradiction_detected"
        ),
        "unverified_target_refutation": (
            "mini_session_target_integrity_unverified_refutation_detected"
        ),
        "semantic_bridge_direction": (
            "mini_session_target_integrity_semantic_bridge_direction_detected"
        ),
    }.get(kind, "mini_session_target_integrity_signals")
    return {
        "kind": kind,
        "match": match,
        "metric": metric,
        "target_statement": str(target_statement or "").strip(),
        "bypass_local_repair": True,
        "disable_proof_state_repair": True,
        "formalization_failure_class": "target_integrity",
    }


def classify_target_integrity_signals(
    *,
    llm_output: str,
    proof: str,
    failure_analysis: Dict[str, Any],
    target_statement: str = "",
    selected_work_type: str = "",
) -> List[Dict[str, Any]]:
    """Return untrusted target-integrity signals for a rejected attempt."""

    if not _target_integrity_enabled_for_work_type(selected_work_type):
        return []
    if _is_parse_error_analysis(dict(failure_analysis or {})):
        return []
    signals: List[Dict[str, Any]] = []
    text = "\n".join([str(llm_output or ""), _proof_comment_text(proof)])
    fake = _first_match(text, _FAKE_CONTRADICTION_PATTERNS)
    if fake is not None:
        label, match = fake
        signal = _base_signal(
            "fake_contradiction_commentary",
            match or label,
            target_statement,
        )
        signal["label"] = label
        signals.append(signal)
    else:
        refutation = _first_refutation_match(text)
        if refutation is not None:
            label, match = refutation
            false_statement_labels = {
                "claim is false",
                "statement is false",
                "target is false",
                "route is false",
            }
            if label not in false_statement_labels or not (
                _looks_like_contradiction_assumption(text, proof)
            ):
                signal = _base_signal(
                    "unverified_target_refutation",
                    match or label,
                    target_statement,
                )
                signal["label"] = label
                signals.append(signal)

    semantic = _semantic_bridge_direction_signal(dict(failure_analysis or {}))
    if semantic is not None:
        signal = _base_signal(
            "semantic_bridge_direction",
            str(semantic.get("match") or ""),
            target_statement,
        )
        signal.update(semantic)
        signals.append(signal)

    return signals


def target_integrity_feedback(signals: List[Dict[str, Any]]) -> str:
    """Human/LLM feedback block for the next proof turn."""

    if not signals:
        return ""
    kinds = {str(item.get("kind") or "") for item in signals}
    lines = [
        "Target-integrity notice:",
        (
            "Treat the rejected proof's refutation or contradiction commentary "
            "as unverified. Do not repeat it as a reason to abandon the active "
            "target unless you first provide a Lean-checked counterexample, a "
            "Lean-checked negation, or a concrete failed local calculation that "
            "pinpoints a smaller replacement lemma."
        ),
    ]
    if "semantic_bridge_direction" in kinds:
        lines.append(
            "Lean indicates a bridge-direction problem. Do not retry a pointwise "
            "inequality that drops or reverses a nonnegative summand; replace it "
            "with an aggregate/sum or partition lemma that preserves the full "
            "verified inequality."
        )
    for signal in signals[:3]:
        match = _one_line(str(signal.get("match") or signal.get("kind") or ""))
        if match:
            lines.append(f"- signal: {signal.get('kind')}: {match}")
    return "\n".join(lines)
