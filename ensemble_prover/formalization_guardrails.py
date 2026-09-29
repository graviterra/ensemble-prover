"""Shared formalization guardrails for mini-prover proof search.

These helpers are deliberately small and syntactic.  They do not decide
mathematical truth; they decide when generated proof work is too poorly
grounded to schedule as ordinary proof search.
"""

from __future__ import annotations

import re
from typing import Any, Mapping, Sequence

from .proof_dossier import helper_decl_statement


_GLOBAL_ANALYTIC_SHAPE_PREDICATES = (
    "StrictConvexOn",
    "StrictConcaveOn",
    "ConvexOn",
    "ConcaveOn",
    "StrictMono",
    "StrictAnti",
    "Monotone",
    "Antitone",
)

_ANALYTIC_FUNCTION_TOKENS = (
    "Real.log",
    "Real.exp",
    "Real.sin",
    "Real.cos",
    "Real.tan",
    "Real.sqrt",
    "deriv",
    "iteratedDeriv",
    "HasDeriv",
    "Differentiable",
    "∑'",
    "tsum",
)

_ANALYTIC_OPERATOR_TOKENS = (
    "deriv",
    "iteratedDeriv",
    "HasDeriv",
    "Differentiable",
    "∑'",
    "tsum",
)

_WORKSHEET_TOKENS = (
    "deriv",
    "iteratedDeriv",
    "HasDeriv",
    "fderiv",
    "ContDiff",
    "Monotone",
    "StrictMono",
    "Antitone",
    "StrictAnti",
    "ConvexOn",
    "ConcaveOn",
    "StrictConvexOn",
    "StrictConcaveOn",
)


def _compact(text: str) -> str:
    return " ".join(str(text or "").split()).strip()


def _analysis_family(analysis: Mapping[str, Any]) -> str:
    return str((analysis or {}).get("error_type") or "").strip()


def unknown_identifier_name(analysis: Mapping[str, Any]) -> str:
    """Return the structured unknown identifier name, if available."""

    details = dict((analysis or {}).get("details") or {})
    return _compact(str(details.get("unknown_identifier") or ""))


def is_parse_error_failure(analysis: Mapping[str, Any]) -> bool:
    return _analysis_family(analysis) == "parse_error"


def parse_error_repair_reason(analysis: Mapping[str, Any]) -> str:
    if is_parse_error_failure(analysis):
        return "parse_error_code_generation_failure"
    return ""


def needs_unknown_identifier_api_search(
    analysis: Mapping[str, Any],
    *,
    parent_ticket: Any = None,
) -> bool:
    """Whether this failure must be grounded by Mathlib/API lookup.

    A first unknown identifier already needs lookup as feedback.  The hard
    invariant is for repeated same-name failures: if the selected parent
    repair ticket required API grounding for this identifier, another proof
    repair must show search/check evidence before it can continue.
    """

    if _analysis_family(analysis) != "unknown_identifier":
        return False
    name = unknown_identifier_name(analysis)
    if not name:
        return False
    metadata = dict(getattr(parent_ticket, "metadata", {}) or {})
    return bool(
        metadata.get("requires_api_search_for_unknown_identifier")
        and str(metadata.get("unknown_identifier") or "").strip() == name
    )


def tool_log_has_api_grounding(tool_call_log: Sequence[Any]) -> bool:
    """Return True if the turn used Mathlib/API grounding tools."""

    for entry in list(tool_call_log or ()):
        if isinstance(entry, Mapping):
            name = str(
                entry.get("name")
                or entry.get("tool_name")
                or entry.get("function")
                or ""
            ).strip()
        else:
            name = str(getattr(entry, "name", "") or "").strip()
        if name in {"search_mathlib", "check_lean", "apply_decl_to_goal"}:
            return True
    return False


def repeated_unknown_identifier_without_api_search(
    analysis: Mapping[str, Any],
    *,
    parent_ticket: Any = None,
    tool_call_log: Sequence[Any] = (),
) -> bool:
    return needs_unknown_identifier_api_search(
        analysis,
        parent_ticket=parent_ticket,
    ) and not tool_log_has_api_grounding(tool_call_log)


def is_global_analytic_shape_statement(statement: str) -> bool:
    """Detect broad analytic shape claims that need a worksheet first."""

    text = _compact(statement)
    if not text:
        return False
    if not any(pred in text for pred in _GLOBAL_ANALYTIC_SHAPE_PREDICATES):
        return False
    if not any(token in text for token in _ANALYTIC_FUNCTION_TOKENS):
        return False
    lowered = text.lower()
    if "set.univ" in lowered or re.search(r"\bℝ\b", text):
        return True
    return bool(re.search(r"\b(?:univ|iic|ici|icc|ioo|ico|ioc)\b", lowered))


def is_global_analytic_closed_form_identity(statement: str) -> bool:
    """Detect monolithic analytic closed-form identities that need scaffolding."""

    text = _compact(statement)
    if not text or "=" not in text:
        return False
    if "iteratedDeriv" not in text and "taylorCoeff" not in text:
        return False
    if not re.search(r"∀\s+[A-Za-z_][A-Za-z0-9_']*\s*:\s*ℕ", text):
        return False
    return bool(
        re.search(r"\bif\s+[A-Za-z_][A-Za-z0-9_']*\s*=", text)
        or re.search(r"[A-Za-z_][A-Za-z0-9_']*\s*[-+]\s*\d", text)
        or "Nat.choose" in text
        or "choose" in text
    )


def _function_tokens(statement: str) -> set[str]:
    text = str(statement or "")
    tokens = {
        token
        for token in _ANALYTIC_FUNCTION_TOKENS
        if token in text
    }
    tokens.update(re.findall(r"Real\.[A-Za-z_][A-Za-z0-9_']*", text))
    return tokens


def _specific_function_tokens(statement: str) -> set[str]:
    return _function_tokens(statement).difference(_ANALYTIC_OPERATOR_TOKENS)


def verified_analytic_worksheet_available(
    *,
    statement: str,
    helper_blocks: Sequence[str],
) -> bool:
    """Whether verified helper context contains a worksheet for this claim.

    The caller supplies only already-verified helper blocks.  We require a
    worksheet-looking statement and at least one shared analytic function token
    when the claim names a concrete analytic function, avoiding broad bypasses
    from unrelated lemmas.
    """

    target_tokens = _function_tokens(statement)
    target_specific_tokens = _specific_function_tokens(statement)
    for block in list(helper_blocks or ()):
        helper_statement = helper_decl_statement(str(block or "")) or str(block or "")
        helper_text = _compact(helper_statement)
        if not helper_text:
            continue
        if not any(token in helper_text for token in _WORKSHEET_TOKENS):
            continue
        helper_tokens = _function_tokens(helper_text)
        helper_specific_tokens = _specific_function_tokens(helper_text)
        if (
            target_specific_tokens
            and helper_specific_tokens
            and target_specific_tokens.isdisjoint(helper_specific_tokens)
        ):
            continue
        if target_specific_tokens and not helper_specific_tokens:
            continue
        if (
            not target_specific_tokens
            and target_tokens
            and helper_tokens
            and target_tokens.isdisjoint(helper_tokens)
        ):
            continue
        return True
    return False


def analytic_worksheet_rejection_reason(
    *,
    statement: str,
    helper_blocks: Sequence[str],
) -> str:
    closed_form_identity = is_global_analytic_closed_form_identity(statement)
    if not is_global_analytic_shape_statement(statement) and not closed_form_identity:
        return ""
    if verified_analytic_worksheet_available(
        statement=statement,
        helper_blocks=helper_blocks,
    ):
        return ""
    if closed_form_identity:
        return (
            "global analytic closed-form identity lacks a verified "
            "derivative recurrence/base-case worksheet in helper context"
        )
    return (
        "global analytic shape claim lacks a verified derivative/monotonicity "
        "worksheet in helper context"
    )
