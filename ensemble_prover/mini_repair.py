"""Repair-time retrieval and search formatting helpers for mini-prover runs."""

from __future__ import annotations

import re
import time
from typing import TYPE_CHECKING, Any, Dict, List, Optional, Set, Tuple

from .mini_failure_analysis import (
    FailureAnalyzer as FailureAnalyzer,
    _FAILURE_ANALYZER as _FAILURE_ANALYZER,
    _RAW_FEEDBACK_MAX_CHARS as _RAW_FEEDBACK_MAX_CHARS,
    _analyze_lean_failure as _analyze_lean_failure,
    _failure_signature_from_analysis as _failure_signature_from_analysis,
    _failure_signature_from_feedback as _failure_signature_from_feedback,
    _format_lean_failure_feedback as _format_lean_failure_feedback,
    _format_raw_lean_feedback as _format_raw_lean_feedback,
    _lean_failure_all_goals_are_direct_local_closes as _lean_failure_all_goals_are_direct_local_closes,
    _manual_lean_failure_analysis as _manual_lean_failure_analysis,
    _needs_answer_safe_feedback_check as _needs_answer_safe_feedback_check,
    _prepend_repeated_failure_notice as _prepend_repeated_failure_notice,
)
from .proof_dossier import (
    _prompt_safe_helper_name,
    _prompt_safe_inline_text,
    is_answer_unsafe_statement_text,
)

if TYPE_CHECKING:
    from .mathlib_api_search import MathlibApiSearcher


def _repair_hit_field_is_answer_unsafe(
    entry: Any,
    *,
    field: str,
    redact_solution_refs: bool,
) -> bool:
    if not redact_solution_refs:
        return False
    raw_value = (
        str(entry.get(field, "") or "")
        if isinstance(entry, dict)
        else str(getattr(entry, field, "") or "")
    )
    return bool(
        raw_value.strip()
        and is_answer_unsafe_statement_text(
            raw_value,
            suppress_solution_placeholders=True,
            opaque_mode=True,
            allow_official_answer_visibility=False,
            official_answer_payload_present=None,
        )
    )


def _format_search_results(
    hits: List[Any],
    max_results: int,
    *,
    redact_solution_refs: bool = True,
) -> str:
    """Render a list of LemmaEntry hits for the LLM."""
    hits = hits[:max_results]
    if not hits:
        return "No matches."
    lines: List[str] = [f"{len(hits)} match(es):"]
    def entry_value(entry: Any, field: str, default: str = "") -> Any:
        if isinstance(entry, dict):
            return entry.get(field, default)
        return getattr(entry, field, default)

    for i, entry in enumerate(hits, 1):
        name = _prompt_safe_helper_name(
            str(entry_value(entry, "name", "") or "?"),
            redact_solution_refs=redact_solution_refs,
        )
        kind = (
            "[answer-dependent declaration kind hidden]"
            if _repair_hit_field_is_answer_unsafe(
                entry,
                field="kind",
                redact_solution_refs=redact_solution_refs,
            )
            else _prompt_safe_inline_text(
                str(entry_value(entry, "kind", "") or ""),
                limit=80,
                redact_solution_refs=redact_solution_refs,
            )
        )
        type_str = (
            "[answer-dependent declaration signature hidden]"
            if _repair_hit_field_is_answer_unsafe(
                entry,
                field="type",
                redact_solution_refs=redact_solution_refs,
            )
            else _prompt_safe_inline_text(
                str(entry_value(entry, "type", "") or "").strip(),
                limit=280,
                redact_solution_refs=redact_solution_refs,
            )
        )
        # Truncate long types so a single result doesn't blow the budget.
        if len(type_str) > 280:
            type_str = type_str[:280] + " …"
        file_str = (
            "[answer-dependent source path hidden]"
            if _repair_hit_field_is_answer_unsafe(
                entry,
                field="file",
                redact_solution_refs=redact_solution_refs,
            )
            else _prompt_safe_inline_text(
                str(entry_value(entry, "file", "") or ""),
                limit=180,
                redact_solution_refs=redact_solution_refs,
            )
        )
        # Show just the file's tail (last 2 path segments) for readability.
        tail = "/".join(file_str.split("/")[-2:]) if file_str else ""
        kind_label = f" ({kind})" if kind else ""
        lines.append(f"{i}. {name}{kind_label}")
        if type_str:
            lines.append(f"   : {type_str}")
        if tail:
            # Keep declaration identity and source location visually distinct.
            # The old ``@ Fintype/BigOperators`` rendering directly beneath a
            # declaration such as ``Finset.prod_fin_eq_prod_range`` encouraged
            # models to splice the module token into the declaration namespace.
            lines.append(f"   file: {tail}")
    return "\n".join(lines)


_LEAN_IDENTIFIER_RE = re.compile(
    r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*"
)
_LEAN_RESERVED_LOCAL_NAMES = {
    "by",
    "calc",
    "do",
    "else",
    "fun",
    "have",
    "if",
    "let",
    "match",
    "namespace",
    "then",
    "where",
}
_LEAN_BUILTIN_WORDS = _LEAN_RESERVED_LOCAL_NAMES | {
    "axiom",
    "classical",
    "def",
    "example",
    "exact",
    "forall",
    "intro",
    "lemma",
    "namespace",
    "noncomputable",
    "open",
    "simp",
    "theorem",
}
_LEAN_TYPE_SYMBOLS = {
    "ℕ": "Nat",
    "ℤ": "Int",
    "ℚ": "Rat",
    "ℝ": "Real",
    "ℂ": "Complex",
}
_MATHLIB_SHAPE_KEYWORDS = {
    "Nat",
    "Int",
    "Rat",
    "Real",
    "Complex",
    "Finset",
    "Fintype",
    "Set",
    "List",
    "Multiset",
    "Polynomial",
    "MvPolynomial",
    "Nat.choose",
    "choose",
    "Nat.Prime",
    "Prime",
    "Even",
    "Odd",
    "Function",
    "Equiv",
    "Matrix",
    "Interval",
    "Icc",
    "Ico",
    "range",
    "sum",
    "prod",
    "card",
    "dvd",
    "gcd",
    "lcm",
    "pow",
    "cast",
}
_GOAL_OPERATOR_TAGS = (
    ("≤", "inequality le"),
    ("≥", "inequality ge"),
    ("<", "inequality lt"),
    (">", "inequality gt"),
    ("∣", "divisibility dvd"),
    ("∑", "finset sum"),
    ("∏", "finset product"),
    ("∈", "membership set"),
    ("⊆", "subset set"),
    ("¬", "negation"),
    ("↔", "iff"),
    ("=", "equality rewrite"),
)


_REPAIR_RETRIEVAL_QUERY_MAX_CHARS = 900
_LEAN_SOURCE_LOCATION_RE = re.compile(
    r"(?:^|\s)(?:/[^\s:]+|[A-Za-z]:\\[^\s:]+):\d+:\d+:?"
)
_LEAN_METAVAR_RE = re.compile(
    r"\?(?:m|u|x)?\.\d+|\?[A-Za-z_][A-Za-z0-9_'.]*|_[A-Za-z_][A-Za-z0-9_']*\.\d+"
)
_REPAIR_QUERY_NOISE_WORDS = _LEAN_BUILTIN_WORDS | {
    "error",
    "warning",
    "type",
    "mismatch",
    "has",
    "is",
    "expected",
    "expect",
    "actual",
    "have",
    "function",
    "failed",
    "failure",
    "synthesize",
    "synthetic",
    "source",
    "line",
    "column",
    "unknown",
    "identifier",
    "application",
    "argument",
    "inst",
    "mvar",
    "goal",
    "goals",
    "term",
    "sort",
    "proof",
}




def _compact_search_text(value: Any, *, limit: int) -> str:
    text = " ".join(str(value or "").split())
    if limit > 0 and len(text) > limit:
        return text[: max(0, limit - 4)].rstrip() + " ..."
    return text


def _sanitize_repair_query_fragment(value: Any, *, limit: int) -> str:
    text = str(value or "")
    text = _LEAN_SOURCE_LOCATION_RE.sub(" ", text)
    text = _LEAN_METAVAR_RE.sub(" ", text)
    text = re.sub(r"\b\d+:\d+\b", " ", text)
    return _compact_search_text(text, limit=limit)


def _repair_query_keywords(value: Any, *, max_terms: int = 8) -> List[str]:
    text = _sanitize_repair_query_fragment(value, limit=500)
    if not text:
        return []
    terms: List[str] = []
    seen: Set[str] = set()

    def add(term: str) -> None:
        clean = str(term or "").strip()
        if not clean or clean in seen:
            return
        seen.add(clean)
        terms.append(clean)

    for symbol, label in _GOAL_OPERATOR_TAGS:
        if symbol in text:
            add(label)
    for symbol, name in _LEAN_TYPE_SYMBOLS.items():
        if symbol in text:
            add(name)

    for match in _LEAN_IDENTIFIER_RE.finditer(text):
        token = match.group(0).strip()
        if not token:
            continue
        if token in _REPAIR_QUERY_NOISE_WORDS:
            continue
        if token.lower() in _REPAIR_QUERY_NOISE_WORDS:
            continue
        if token.startswith("_"):
            continue
        if token.isdigit():
            continue
        if "." in token or token in _MATHLIB_SHAPE_KEYWORDS or token[:1].isupper():
            add(token)
        elif len(token) >= 4 and token not in _LEAN_RESERVED_LOCAL_NAMES:
            add(token)
        if len(terms) >= max_terms:
            break
    return terms


def _repair_retrieval_query(
    conv: Any,
    analysis: Dict[str, Any],
    *,
    goal_statement_override: Optional[str] = None,
) -> str:
    """Build a type/diagnostic-shaped Mathlib query after a Lean failure."""

    goal_statement = str(
        goal_statement_override
        if goal_statement_override is not None
        else getattr(conv, "goal_statement", "")
    )

    parts: List[str] = []
    seen_parts: Set[str] = set()

    def add_part(value: Any, *, limit: int = 220) -> None:
        text = _sanitize_repair_query_fragment(value, limit=limit)
        if not text or text in seen_parts:
            return
        seen_parts.add(text)
        parts.append(text)

    def add_keywords(value: Any, *, max_terms: int = 8) -> None:
        keywords = _repair_query_keywords(value, max_terms=max_terms)
        if keywords:
            add_part(" ".join(keywords), limit=220)

    family = str(analysis.get("error_type") or "").strip()
    if family:
        add_part(family.replace("_", " "), limit=80)

    # Always ground repair retrieval in the theorem/current goal shape. Manual
    # analysis and answer-safe feedback suppression can otherwise produce
    # syntactically valid but content-free queries like "answer safe feedback
    # unavailable".
    add_part(goal_statement, limit=360)
    add_keywords(goal_statement, max_terms=10)

    details = dict(analysis.get("details") or {})
    for key in ("unknown_identifier", "missing_instance", "failed_tactic"):
        add_keywords(details.get(key), max_terms=5)
    for key in ("expected_type", "actual_type", "unification_failure"):
        add_keywords(details.get(key), max_terms=10)

    add_keywords(analysis.get("diagnostic_search_text"), max_terms=10)
    for diag in list(analysis.get("diagnostics") or [])[:2]:
        if not isinstance(diag, dict):
            continue
        add_keywords(diag.get("message") or diag.get("summary"), max_terms=8)

    for goal in list(analysis.get("remaining_goals") or [])[:2]:
        if not isinstance(goal, dict):
            continue
        add_part(goal.get("target"), limit=260)
        for hyp in list(goal.get("hypotheses") or [])[:4]:
            add_part(hyp, limit=120)

    if not parts:
        add_part(goal_statement, limit=500)

    query = " ".join(part for part in parts if part)
    return _compact_search_text(
        query,
        limit=_REPAIR_RETRIEVAL_QUERY_MAX_CHARS,
    )


def _retrieve_repair_candidates(
    searcher: Optional[MathlibApiSearcher],
    conv: Any,
    analysis: Dict[str, Any],
    *,
    max_results: int,
    goal_statement_override: Optional[str] = None,
    redact_solution_refs: bool = True,
) -> Tuple[str, Dict[str, Any]]:
    """Retrieve likely repair facts from the current failed goal shape."""

    if searcher is None:
        return "", {}
    max_n = max(0, min(12, int(max_results or 0)))
    if max_n <= 0:
        return "", {}
    query = _repair_retrieval_query(
        conv,
        analysis,
        goal_statement_override=goal_statement_override,
    )
    if not query:
        return "", {}
    started = time.monotonic()
    goal_statement = str(goal_statement_override or "").strip()
    if not goal_statement:
        remaining_goals = list(analysis.get("remaining_goals") or ())
        if remaining_goals and isinstance(remaining_goals[0], dict):
            goal_statement = str(remaining_goals[0].get("target") or "").strip()
    if not goal_statement:
        goal_statement = str(getattr(conv, "statement_type", "") or "").strip()
    try:
        # Over-fetch before safety/availability filtering so an unusable
        # answer-hidden hit does not permanently consume a ranked slot.
        search_max_n = min(36, max(max_n, max_n * 3))
        hits = list(
            searcher.search(
                query,
                goal_state=goal_statement,
                max_results=search_max_n,
            )
            or []
        )
    except Exception as exc:
        return "", {
            "query": query,
            "error": f"{type(exc).__name__}: {exc}",
            "elapsed_s": round(time.monotonic() - started, 3),
        }

    inactive_hits = []
    prompt_unusable_hits = []
    usable_hits = []
    for hit in hits:
        candidate = getattr(hit, "retrieval_candidate", None)
        availability = str(
            getattr(candidate, "availability", "already_imported")
            or "already_imported"
        )
        if availability != "already_imported":
            inactive_hits.append(hit)
            continue
        raw_name = str(getattr(hit, "name", "") or "").strip()
        safe_name = (
            _prompt_safe_helper_name(
                raw_name,
                redact_solution_refs=redact_solution_refs,
            )
            if raw_name
            else ""
        )
        if (
            not raw_name
            or safe_name != raw_name
            or "_hidden_" in safe_name
            or _repair_hit_field_is_answer_unsafe(
                hit,
                field="type",
                redact_solution_refs=redact_solution_refs,
            )
        ):
            # A sanitized declaration name cannot be cited in Lean. Retaining
            # it in the slate wastes capacity and can teach the model a
            # deliberately non-executable identifier.
            prompt_unusable_hits.append(hit)
            continue
        usable_hits.append(hit)
    hits = usable_hits[:max_n]
    rendered = _format_search_results(
        hits,
        max_n,
        redact_solution_refs=redact_solution_refs,
    )
    record = {
        "query": query,
        "result_count": len(hits),
        "inactive_result_count": len(inactive_hits),
        "prompt_unusable_result_count": len(prompt_unusable_hits),
        "inactive_decl_names": [
            str(getattr(hit, "name", "") or "")
            for hit in inactive_hits[:10]
        ],
        "rendered": rendered[:1200],
        "elapsed_s": round(time.monotonic() - started, 3),
    }
    if not hits:
        return "", record
    block = (
        "Repair-time Mathlib candidates from the failed goal and diagnostics "
        "(ranked guesses; verify exact signatures before citing):\n"
        + rendered
    )
    return block, record


async def _retrieve_repair_candidates_async(
    searcher: Optional[MathlibApiSearcher],
    conv: Any,
    analysis: Dict[str, Any],
    *,
    max_results: int,
    goal_statement_override: Optional[str] = None,
    timeout_s: float = 30.0,
    redact_solution_refs: bool = True,
) -> Tuple[str, Dict[str, Any]]:
    """Bound repair retrieval and discard results from abandoned workers."""

    from .mathematical_retrieval.async_runtime import (
        RetrievalWorkerCapacityError,
        run_sync_abandonment_safe,
    )

    started = time.monotonic()
    worker_searcher = searcher
    fork = getattr(searcher, "fork_session_context", None)
    if callable(fork):
        worker_searcher = fork()
    try:
        rendered, record = await run_sync_abandonment_safe(
            lambda: _retrieve_repair_candidates(
                worker_searcher,
                conv,
                analysis,
                max_results=max_results,
                goal_statement_override=goal_statement_override,
                redact_solution_refs=redact_solution_refs,
            ),
            timeout_s=max(0.05, float(timeout_s)),
        )
    except (TimeoutError, RetrievalWorkerCapacityError) as exc:
        publish_failure = getattr(searcher, "publish_boundary_failure", None)
        if callable(publish_failure):
            publish_failure(
                consumer="repair",
                elapsed_s=time.monotonic() - started,
                capacity_exhausted=isinstance(
                    exc,
                    RetrievalWorkerCapacityError,
                ),
            )
        return "", {
            "query": "",
            "result_count": 0,
            "error": f"{type(exc).__name__}: {exc}",
            "elapsed_s": round(time.monotonic() - started, 3),
        }
    if searcher is not None and worker_searcher is not searcher:
        try:
            searcher.last_result = worker_searcher.last_result
        except Exception:
            pass
        publish = getattr(searcher, "publish_result_metrics", None)
        if callable(publish):
            publish(worker_searcher.last_result, consumer="repair")
    return rendered, record
