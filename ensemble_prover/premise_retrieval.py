"""Retrieve likely Mathlib premises before proof conversation begins.

The service queries the in-memory ``MathlibApiSearcher`` with the goal and
optional planner notes, filters the result to useful declaration kinds, and
surfaces a bounded top-K list so model search does not depend on remembering
library names unaided.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

from .mathlib_api_search import MathlibApiSearcher
from .proof_dossier import _prompt_safe_helper_name, _prompt_safe_inline_text

logger = logging.getLogger(__name__)

DEFAULT_TOP_K: int = 8
_MAX_TYPE_CHARS: int = 240
_MAX_OBSERVATION_TERMS: int = 5
# Mathlib entry kinds that are useful to surface as "premise candidates"
# the model might cite in a proof. Instances are typeclass plumbing —
# almost never what the model wants — and defs are usually too low-level
# (e.g., ``Mathlib.Tactic.ITauto.whenOk``). Live evidence from
# putnam_1988_b2 retrieval at 2026-05-01: the unfiltered top-8 included
# two ``(instance)`` declarations from manifold and measure-regularity
# files, and an ITauto def — none of which a polynomial-inequality
# proof can use. Filtering to just theorems and lemmas removes the
# noise floor.
_ALLOWED_KINDS: frozenset = frozenset({"theorem", "lemma"})
# Over-fetch from the searcher so post-hoc filtering still leaves
# enough useful results to fill ``top_k``. With the unfiltered top-8
# regularly including 2-3 instances/defs, fetching ~3x gives headroom
# without measurable cost (searcher is in-memory).
_OVERFETCH_MULTIPLIER: int = 3
# Per-part and total query length caps. The Mathlib API searcher does
# token-based candidate ID lookup against a 207k-entry inverted index;
# unbounded queries (multi-KB strategies + observations) drive the
# tokenizer into a multi-minute scan. These caps keep the query in the
# regime where retrieval finishes in tens of milliseconds.
_MAX_QUERY_PART_CHARS: int = 500
_MAX_QUERY_TOTAL_CHARS: int = 2000


@dataclass(frozen=True)
class PremiseHit:
    """Compact provenance-aware premise candidate for prompt injection."""

    name: str
    kind: str
    type_signature: str
    file_tail: str
    source_kind: str = "mathlib"
    source_id: str = ""
    availability: str = "already_imported"
    module_name: str = ""
    required_bundle_ids: Tuple[str, ...] = ()
    source_hash: str = ""
    helper_source: str = ""
    full_type_signature: str = ""
    fusion_score: float = 0.0
    origin_source_ids: Tuple[str, ...] = ()
    project_origin_source_ids: Tuple[str, ...] = ()
    ambiguous_module_origin: bool = False

    @classmethod
    def from_entry(cls, entry: Any) -> "PremiseHit":
        type_str = str(getattr(entry, "type", "") or "").strip()
        if len(type_str) > _MAX_TYPE_CHARS:
            type_str = type_str[:_MAX_TYPE_CHARS] + " …"
        file_str = str(getattr(entry, "file", "") or "")
        # Last two path segments give "Module/File.lean" — readable, short.
        tail = "/".join(file_str.split("/")[-2:]) if file_str else ""
        candidate = getattr(entry, "retrieval_candidate", None)
        origins = tuple(getattr(candidate, "origins", ()) or ())
        origin = origins[0] if origins else None
        project_module_origins = {
            (str(getattr(item, "source_id", "") or ""),
             str(getattr(item, "module_name", "") or ""))
            for item in origins
            if str(getattr(item, "source_kind", "") or "") == "project"
        }
        return cls(
            name=str(getattr(entry, "name", "") or "?"),
            kind=str(getattr(entry, "kind", "") or ""),
            type_signature=type_str,
            file_tail=tail,
            source_kind=(
                str(getattr(origin, "source_kind", "") or "mathlib")
                if origin is not None
                else "mathlib"
            ),
            source_id=(
                str(getattr(origin, "source_id", "") or "")
                if origin is not None
                else ""
            ),
            availability=(
                str(
                    getattr(origin, "availability", "")
                    or "already_imported"
                )
                if origin is not None
                else "already_imported"
            ),
            module_name=(
                str(getattr(origin, "module_name", "") or "")
                if origin is not None
                else ""
            ),
            required_bundle_ids=tuple(
                str(item).strip()
                for item in (
                    getattr(origin, "required_bundle_ids", ())
                    if origin is not None
                    else ()
                )
                if str(item).strip()
            ),
            source_hash=(
                str(getattr(origin, "source_hash", "") or "")
                if origin is not None
                else ""
            ),
            helper_source=(
                str(getattr(origin, "helper_source", "") or "")
                if origin is not None
                else ""
            ),
            full_type_signature=str(getattr(entry, "type", "") or "").strip(),
            fusion_score=float(getattr(candidate, "fusion_score", 0.0) or 0.0),
            origin_source_ids=tuple(
                dict.fromkeys(
                    str(getattr(item, "source_id", "") or "")
                    for item in origins
                    if str(getattr(item, "source_id", "") or "")
                )
            ),
            project_origin_source_ids=tuple(
                dict.fromkeys(
                    str(getattr(item, "source_id", "") or "")
                    for item in origins
                    if str(getattr(item, "source_kind", "") or "")
                    == "project"
                    and str(getattr(item, "source_id", "") or "")
                )
            ),
            ambiguous_module_origin=len(project_module_origins) > 1,
        )


@dataclass(frozen=True)
class PremiseRetrievalRecord:
    """Typed outcome for one eager premise retrieval attempt."""

    enabled: bool
    searcher_available: bool
    query: str
    top_k: int
    raw_hit_count: int
    filtered_hit_count: int
    hits: Tuple[PremiseHit, ...] = ()
    hit_names: Tuple[str, ...] = ()
    top_scores: Tuple[float, ...] = ()
    filtered_out_kind_counts: Dict[str, int] = field(default_factory=dict)
    source_health: Dict[str, str] = field(default_factory=dict)
    index_snapshot_id: str = ""
    failure_kind: str = "none"
    error: str = ""
    elapsed_s: float = 0.0

    @property
    def local_micro_theory_candidate(self) -> bool:
        """True when retrieval really ran and found no usable premise hits."""

        source_health_clean = not self.source_health or all(
            health in {"success_with_hits", "success_zero_hits"}
            for health in self.source_health.values()
        )
        raw_zero_clean = (
            self.failure_kind != "zero_raw_hits"
            or not self.source_health
            or all(
                health == "success_zero_hits"
                for health in self.source_health.values()
            )
        )
        return bool(
            self.enabled
            and self.searcher_available
            and self.query
            and self.top_k > 0
            and self.failure_kind in {"zero_raw_hits", "zero_filtered_hits"}
            and source_health_clean
            and raw_zero_clean
        )

    def metadata(self) -> Dict[str, Any]:
        """Return a compact JSON-safe metadata payload."""

        source_counts: Dict[str, int] = {}
        availability_counts: Dict[str, int] = {}
        for hit in self.hits:
            source_counts[hit.source_kind] = source_counts.get(hit.source_kind, 0) + 1
            availability_counts[hit.availability] = (
                availability_counts.get(hit.availability, 0) + 1
            )
        return {
            "premise_retrieval_enabled": bool(self.enabled),
            "premise_retrieval_searcher_available": bool(self.searcher_available),
            "premise_retrieval_query": self.query[:500],
            "premise_retrieval_top_k": int(self.top_k),
            "premise_retrieval_raw_hit_count": int(self.raw_hit_count),
            "premise_retrieval_filtered_hit_count": int(self.filtered_hit_count),
            "premise_retrieval_hit_names": list(self.hit_names),
            "premise_retrieval_top_scores": list(self.top_scores),
            "premise_retrieval_source_counts": source_counts,
            "premise_retrieval_availability_counts": availability_counts,
            "premise_retrieval_filtered_out_kind_counts": dict(
                self.filtered_out_kind_counts or {}
            ),
            "premise_retrieval_source_health": dict(self.source_health or {}),
            "premise_retrieval_index_snapshot_id": self.index_snapshot_id,
            "premise_retrieval_failure_kind": self.failure_kind,
            "premise_retrieval_error": self.error[:500],
            "premise_retrieval_elapsed_s": round(float(self.elapsed_s or 0.0), 4),
            "premise_local_micro_theory_candidate": bool(
                self.local_micro_theory_candidate
            ),
        }


def premise_retrieval_metric_increments(
    metadata: Dict[str, Any],
    policy_metadata: Optional[Dict[str, Any]] = None,
) -> Dict[str, int]:
    """Return canonical metric increments for one eager retrieval record."""

    payload = dict(metadata or {})
    policy_payload = dict(policy_metadata or {})
    increments: Dict[str, int] = {
        "mini_premise_retrieval_runs": 1,
    }
    failure_kind = str(payload.get("premise_retrieval_failure_kind") or "")
    if failure_kind == "zero_raw_hits":
        increments["mini_premise_retrieval_zero_raw_hits"] = 1
    if failure_kind == "zero_filtered_hits":
        increments["mini_premise_retrieval_zero_filtered_hits"] = 1
    filtered_out_total = sum(
        int(value or 0)
        for value in dict(
            payload.get("premise_retrieval_filtered_out_kind_counts") or {}
        ).values()
    )
    if filtered_out_total > 0:
        increments[
            "mini_premise_retrieval_filtered_out_nonpremise_hits"
        ] = filtered_out_total
    snapshot_id = str(payload.get("premise_retrieval_index_snapshot_id") or "")
    if snapshot_id:
        increments["mini_mathematical_retrieval_runs"] = 1
        source_metric = {
            "mathlib": "mini_mathematical_retrieval_mathlib_hits",
            "project": "mini_mathematical_retrieval_project_hits",
            "published_theory": "mini_mathematical_retrieval_theory_hits",
            "verified_helper": "mini_mathematical_retrieval_helper_hits",
        }
        for source_kind, count in dict(
            payload.get("premise_retrieval_source_counts") or {}
        ).items():
            metric = source_metric.get(str(source_kind or ""))
            if metric and int(count or 0) > 0:
                increments[metric] = int(count or 0)
        inactive_count = sum(
            int(count or 0)
            for availability, count in dict(
                payload.get("premise_retrieval_availability_counts") or {}
            ).items()
            if str(availability or "") != "already_imported"
        )
        if inactive_count:
            increments["mini_mathematical_retrieval_inactive_hits"] = inactive_count
        degraded = sum(
            1
            for health in dict(
                payload.get("premise_retrieval_source_health") or {}
            ).values()
            if str(health or "") not in {
                "success_with_hits",
                "success_zero_hits",
            }
        )
        if degraded:
            increments["mini_mathematical_retrieval_source_failures"] = degraded
    if policy_payload.get("premise_zero_hit_shadow_recommendation"):
        increments["mini_premise_zero_hit_shadow_local_micro_theory"] = 1
    if policy_payload.get("local_micro_theory_activated"):
        increments["mini_premise_zero_hit_local_micro_theory_activated"] = 1
    return increments


def record_premise_retrieval_metrics(
    metric_sink: Any,
    metadata: Dict[str, Any],
    policy_metadata: Optional[Dict[str, Any]] = None,
) -> None:
    """Increment canonical premise-retrieval metrics on a dossier/session sink."""

    if not callable(metric_sink):
        return
    for key, amount in premise_retrieval_metric_increments(
        metadata,
        policy_metadata,
    ).items():
        metric_sink(key, amount)


def _record(
    *,
    enabled: bool,
    searcher_available: bool,
    query: str,
    top_k: int,
    raw_hit_count: int = 0,
    filtered_hit_count: int = 0,
    hits: Sequence[PremiseHit] = (),
    top_scores: Sequence[float] = (),
    filtered_out_kind_counts: Optional[Dict[str, int]] = None,
    source_health: Optional[Dict[str, str]] = None,
    index_snapshot_id: str = "",
    failure_kind: str = "none",
    error: str = "",
    elapsed_s: float = 0.0,
) -> PremiseRetrievalRecord:
    hit_tuple = tuple(hits or ())
    return PremiseRetrievalRecord(
        enabled=bool(enabled),
        searcher_available=bool(searcher_available),
        query=str(query or ""),
        top_k=int(top_k or 0),
        raw_hit_count=int(raw_hit_count or 0),
        filtered_hit_count=int(filtered_hit_count or 0),
        hits=hit_tuple,
        hit_names=tuple(
            str(getattr(hit, "name", "") or "").strip()
            for hit in hit_tuple
            if str(getattr(hit, "name", "") or "").strip()
        ),
        top_scores=tuple(float(score) for score in list(top_scores or ())[:5]),
        filtered_out_kind_counts=dict(filtered_out_kind_counts or {}),
        source_health=dict(source_health or {}),
        index_snapshot_id=str(index_snapshot_id or ""),
        failure_kind=str(failure_kind or "none"),
        error=str(error or ""),
        elapsed_s=float(elapsed_s or 0.0),
    )


def _build_query(
    goal_statement: str,
    exploration: Optional[Any],
) -> str:
    """Construct the search query from goal + optional planner signals.

    Goal text alone is often too symbolic to surface useful matches;
    ``strategy`` and ``key_observations`` attributes can add
    natural-language and named-lemma cues that drive the searcher's
    token-based scoring more sharply.
    """
    def _cap(s: str) -> str:
        return s if len(s) <= _MAX_QUERY_PART_CHARS else s[:_MAX_QUERY_PART_CHARS]

    def _cap_goal(s: str) -> str:
        """Preserve both binders/context and the theorem conclusion."""

        if len(s) <= _MAX_QUERY_PART_CHARS:
            return s
        separator = " ... "
        remaining = _MAX_QUERY_PART_CHARS - len(separator)
        head_chars = remaining // 2
        tail_chars = remaining - head_chars
        return f"{s[:head_chars]}{separator}{s[-tail_chars:]}"

    parts: List[str] = []
    g = str(goal_statement or "").strip()
    if g:
        parts.append(_cap_goal(g))
    if exploration is not None and exploration.ok:
        strategy = str(exploration.strategy or "").strip()
        if strategy:
            parts.append(_cap(strategy))
        for obs in list(exploration.key_observations or ())[:_MAX_OBSERVATION_TERMS]:
            obs_str = str(obs or "").strip()
            if obs_str:
                parts.append(_cap(obs_str))
    joined = " ".join(parts).strip()
    if len(joined) > _MAX_QUERY_TOTAL_CHARS:
        joined = joined[:_MAX_QUERY_TOTAL_CHARS]
    return joined


def retrieve_premise_record(
    searcher: Optional[MathlibApiSearcher],
    *,
    goal_statement: str,
    exploration: Optional[Any] = None,
    top_k: int = DEFAULT_TOP_K,
    deadline_exhausted: Optional[Any] = None,
) -> PremiseRetrievalRecord:
    """Return typed eager retrieval telemetry plus promptable premise hits."""

    import time

    started = time.monotonic()
    searcher_available = searcher is not None
    if searcher is None:
        return _record(
            enabled=False,
            searcher_available=False,
            query="",
            top_k=int(top_k or 0),
            failure_kind="disabled",
            elapsed_s=time.monotonic() - started,
        )
    query = _build_query(goal_statement, exploration)
    try:
        k_int = int(top_k)
    except Exception:
        k_int = DEFAULT_TOP_K
    if not query:
        return _record(
            enabled=True,
            searcher_available=searcher_available,
            query=query,
            top_k=k_int,
            failure_kind="empty_query",
            elapsed_s=time.monotonic() - started,
        )
    if k_int <= 0:
        return _record(
            enabled=False,
            searcher_available=searcher_available,
            query=query,
            top_k=k_int,
            failure_kind="top_k_disabled",
            elapsed_s=time.monotonic() - started,
        )
    k = k_int
    fetch_k = max(k * _OVERFETCH_MULTIPLIER, k + 4)
    search_kwargs: Dict[str, Any] = {
        # Preserve the typed-goal retrieval channel without reintroducing the
        # previous uncapped duplicate lexical scan.  The federated service
        # explicitly separates a full typed target from its bounded natural
        # query; legacy/raw searchers receive the bounded representation.
        "goal_state": (
            str(goal_statement or "").strip()
            if bool(
                getattr(searcher, "preserves_typed_goal_separately", False)
            )
            else _build_query(goal_statement, None)
        ),
        "max_results": fetch_k,
    }
    if deadline_exhausted is not None:
        search_kwargs["deadline_exhausted"] = deadline_exhausted
    try:
        if hasattr(searcher, "search_with_scores"):
            search_with_scores = searcher.search_with_scores
            try:
                scored_result = search_with_scores(query, **search_kwargs)
            except TypeError as exc:
                if (
                    "deadline_exhausted" not in search_kwargs
                    or "deadline_exhausted" not in str(exc)
                ):
                    raise
                compatibility_kwargs = dict(search_kwargs)
                compatibility_kwargs.pop("deadline_exhausted", None)
                scored_result = search_with_scores(query, **compatibility_kwargs)
            raw_scored_hits = list(
                scored_result or []
            )
            raw_entries = [
                getattr(hit, "entry", None)
                for hit in raw_scored_hits
                if getattr(hit, "entry", None) is not None
            ]
            raw_scores = [
                float(getattr(hit, "score", 0.0) or 0.0)
                for hit in raw_scored_hits
            ]
        else:
            search = searcher.search
            try:
                search_result = search(query, **search_kwargs)
            except TypeError as exc:
                if (
                    "deadline_exhausted" not in search_kwargs
                    or "deadline_exhausted" not in str(exc)
                ):
                    raise
                compatibility_kwargs = dict(search_kwargs)
                compatibility_kwargs.pop("deadline_exhausted", None)
                search_result = search(query, **compatibility_kwargs)
            raw_entries = list(
                search_result or []
            )
            raw_scores = []
    except Exception as exc:
        logger.warning(
            "premise retrieval: searcher raised %s: %s",
            type(exc).__name__,
            exc,
        )
        return _record(
            enabled=True,
            searcher_available=searcher_available,
            query=query,
            top_k=k,
            failure_kind="search_exception",
            error=f"{type(exc).__name__}: {exc}",
            elapsed_s=time.monotonic() - started,
        )
    if not raw_entries:
        federated_result = getattr(searcher, "last_result", None)
        return _record(
            enabled=True,
            searcher_available=searcher_available,
            query=query,
            top_k=k,
            raw_hit_count=0,
            filtered_hit_count=0,
            source_health={
                str(getattr(report, "source_id", "") or ""): str(
                    getattr(report, "health", "") or ""
                )
                for report in tuple(
                    getattr(federated_result, "source_reports", ()) or ()
                )
            },
            index_snapshot_id=str(
                getattr(federated_result, "index_snapshot_id", "") or ""
            ),
            failure_kind="zero_raw_hits",
            elapsed_s=time.monotonic() - started,
        )
    out: List[PremiseHit] = []
    filtered_out_kind_counts: Dict[str, int] = {}
    for entry in raw_entries:
        kind = str(getattr(entry, "kind", "") or "").strip().lower()
        if kind not in _ALLOWED_KINDS:
            filtered_out_kind_counts[kind or "<missing>"] = (
                filtered_out_kind_counts.get(kind or "<missing>", 0) + 1
            )
            continue
        if len(out) >= k:
            continue
        out.append(PremiseHit.from_entry(entry))
    failure_kind = "none" if out else "zero_filtered_hits"
    federated_result = getattr(searcher, "last_result", None)
    return _record(
        enabled=True,
        searcher_available=searcher_available,
        query=query,
        top_k=k,
        raw_hit_count=len(raw_entries),
        filtered_hit_count=len(out),
        hits=out,
        top_scores=raw_scores,
        filtered_out_kind_counts=filtered_out_kind_counts,
        source_health={
            str(getattr(report, "source_id", "") or ""): str(
                getattr(report, "health", "") or ""
            )
            for report in tuple(
                getattr(federated_result, "source_reports", ()) or ()
            )
        },
        index_snapshot_id=str(
            getattr(federated_result, "index_snapshot_id", "") or ""
        ),
        failure_kind=failure_kind,
        elapsed_s=time.monotonic() - started,
    )


async def retrieve_premise_record_async(
    searcher: Optional[MathlibApiSearcher],
    *,
    goal_statement: str,
    exploration: Optional[Any] = None,
    top_k: int = DEFAULT_TOP_K,
    timeout_s: float = 30.0,
    deadline_monotonic: Optional[float] = None,
    deadline_exhausted: Optional[Any] = None,
) -> PremiseRetrievalRecord:
    """Run eager retrieval behind a strict, abandonment-safe boundary.

    Federated services are forked so a timed-out worker cannot publish a late
    ``last_result`` or availability mutation into the live session.  Shared
    backend indexes remain protected by source-level locks.
    """

    from .mathematical_retrieval.async_runtime import (
        RetrievalWorkerCapacityError,
        run_sync_abandonment_safe,
    )

    import time

    started = time.monotonic()
    def expired() -> bool:
        if deadline_monotonic is not None and time.monotonic() >= float(
            deadline_monotonic
        ):
            return True
        if callable(deadline_exhausted):
            try:
                return bool(deadline_exhausted())
            except Exception:
                return True
        return False

    if expired():
        return _record(
            enabled=True,
            searcher_available=searcher is not None,
            query=_build_query(goal_statement, exploration),
            top_k=int(top_k or 0),
            failure_kind="retrieval_timeout",
            error="retrieval deadline exhausted before dispatch",
            elapsed_s=0.0,
        )
    effective_timeout_s = max(0.001, float(timeout_s))
    if deadline_monotonic is not None:
        effective_timeout_s = min(
            effective_timeout_s,
            max(0.001, float(deadline_monotonic) - started),
        )
    worker_searcher = searcher
    fork = getattr(searcher, "fork_session_context", None)
    if callable(fork):
        worker_searcher = fork()

    def invoke_sync_retrieval() -> PremiseRetrievalRecord:
        try:
            return retrieve_premise_record(
                worker_searcher,
                goal_statement=goal_statement,
                exploration=exploration,
                top_k=top_k,
                deadline_exhausted=expired,
            )
        except TypeError as exc:
            if "deadline_exhausted" not in str(exc):
                raise
            return retrieve_premise_record(
                worker_searcher,
                goal_statement=goal_statement,
                exploration=exploration,
                top_k=top_k,
            )

    try:
        record = await run_sync_abandonment_safe(
            invoke_sync_retrieval,
            timeout_s=effective_timeout_s,
            deadline_exhausted=expired,
        )
    except (TimeoutError, RetrievalWorkerCapacityError) as exc:
        publish_failure = getattr(searcher, "publish_boundary_failure", None)
        if callable(publish_failure):
            publish_failure(
                consumer="eager",
                elapsed_s=time.monotonic() - started,
                capacity_exhausted=isinstance(
                    exc,
                    RetrievalWorkerCapacityError,
                ),
            )
        return _record(
            enabled=True,
            searcher_available=searcher is not None,
            query=_build_query(goal_statement, exploration),
            top_k=int(top_k or 0),
            failure_kind=(
                "retrieval_timeout"
                if isinstance(exc, TimeoutError)
                else "retrieval_capacity_exhausted"
            ),
            error=f"{type(exc).__name__}: {exc}",
            elapsed_s=time.monotonic() - started,
        )
    if expired():
        publish_failure = getattr(searcher, "publish_boundary_failure", None)
        if callable(publish_failure):
            publish_failure(
                consumer="eager",
                elapsed_s=time.monotonic() - started,
            )
        return _record(
            enabled=True,
            searcher_available=searcher is not None,
            query=_build_query(goal_statement, exploration),
            top_k=int(top_k or 0),
            failure_kind="retrieval_timeout",
            error="retrieval result finished after deadline",
            elapsed_s=time.monotonic() - started,
        )
    if searcher is not None and worker_searcher is not searcher:
        try:
            searcher.last_result = worker_searcher.last_result
        except Exception:
            pass
        publish = getattr(searcher, "publish_result_metrics", None)
        if callable(publish):
            publish(worker_searcher.last_result, consumer="eager")
    return record


def retrieve_premises(
    searcher: Optional[MathlibApiSearcher],
    *,
    goal_statement: str,
    exploration: Optional[Any] = None,
    top_k: int = DEFAULT_TOP_K,
) -> List[PremiseHit]:
    """Return up to ``top_k`` Mathlib lemmas relevant to the goal.

    Returns ``[]`` when the searcher is unavailable, when the query is
    empty, or when the searcher raises.  Eager retrieval must never
    block the prove loop; failures fall through silently to "no
    pre-retrieval, model can still call search_mathlib reactively".
    """
    return list(
        retrieve_premise_record(
            searcher,
            goal_statement=goal_statement,
            exploration=exploration,
            top_k=top_k,
        ).hits
    )


def format_premise_block(premises: Sequence[PremiseHit]) -> str:
    """Render premises as a prompt-injectable block.  Empty when none."""
    items = list(premises or [])
    if not items:
        return ""
    corpus_label = (
        "Mathlib lemmas"
        if all(item.source_kind == "mathlib" for item in items)
        else "declarations from configured mathematical libraries"
    )
    lines: List[str] = [
        f"Pre-retrieved {corpus_label} ranked by goal/strategy similarity "
        f"(top {len(items)}; may or may not be relevant — verify the "
        "type fits before citing):",
    ]
    for i, p in enumerate(items, 1):
        kind_label = f" ({p.kind})" if p.kind else ""
        lines.append(
            f"{i}. {_prompt_safe_helper_name(p.name)}"
            f"{_prompt_safe_inline_text(kind_label, limit=90)}"
        )
        if p.type_signature:
            lines.append(
                f"   : {_prompt_safe_inline_text(p.type_signature, limit=_MAX_TYPE_CHARS + 20)}"
            )
        if p.file_tail:
            lines.append(
                f"   @ {_prompt_safe_inline_text(p.file_tail, limit=220)}"
            )
        if p.source_kind != "mathlib" or p.availability != "already_imported":
            lines.append(
                "   source="
                f"{_prompt_safe_inline_text(p.source_kind, limit=80)} "
                "availability="
                f"{_prompt_safe_inline_text(p.availability, limit=80)}"
            )
        if p.module_name:
            lines.append(
                f"   module={_prompt_safe_inline_text(p.module_name, limit=180)}"
            )
        if p.availability != "already_imported":
            lines.append(
                "   Discovery only: do not cite until the session explicitly "
                "activates/imports/rechecks this declaration."
            )
    return "\n".join(lines)
