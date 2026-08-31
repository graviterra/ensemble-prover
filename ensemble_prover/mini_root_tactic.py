"""Root-level tactic close orchestration for mini-prover runs."""

from __future__ import annotations

import asyncio
import inspect
import re
import time
from typing import Any, Awaitable, Callable, Dict, List, Mapping, Optional, Sequence, Tuple

from .mini_tactic_closer import (
    OUTPUT_PREVIEW_CHARS,
    TacticCandidate,
    TacticPatternCache,
    TacticCloseResult,
    _helper_lemma_blocks,
    is_transient_tactic_close_failure,
    try_close_with_tactics,
)
from .proof_dossier import (
    active_root_targets_for_frame,
    active_root_target_statement,
    canonical_dossier_statement_key,
    helper_decl_name,
    text_hash,
)
from .proof_graph import helper_decl_statement
from .tactic_attempt_telemetry import (
    LeanAttemptObserver,
    dossier_lean_attempt_observer,
    notify_lean_attempt_observer,
    tactic_attempt_telemetry_fields,
    tactic_lane_for_phase,
)


TacticCloser = Callable[..., Awaitable[Any]]
TransientChecker = Callable[[Any], bool]
TraceFn = Callable[[str, str], None]


def _accepted_tactic_kwargs(fn: Callable[..., Any], kwargs: Dict[str, Any]) -> Dict[str, Any]:
    try:
        signature = inspect.signature(fn)
    except (TypeError, ValueError):
        return dict(kwargs)
    if any(
        param.kind == inspect.Parameter.VAR_KEYWORD
        for param in signature.parameters.values()
    ):
        return dict(kwargs)
    return {key: value for key, value in kwargs.items() if key in signature.parameters}


def _supports_keyword_tactic_call(fn: Callable[..., Any], kwargs: Dict[str, Any]) -> bool:
    try:
        signature = inspect.signature(fn)
    except (TypeError, ValueError):
        return True
    try:
        signature.bind_partial(**kwargs)
    except TypeError:
        return False
    return True


def _excluded_source_prefixes_for_statement(
    *,
    excluded_source_prefixes: Sequence[str],
    tactic_source_suppression_records: Sequence[Mapping[str, Any]],
    tactic_source_suppression_helper_blocks: Sequence[str],
    goal_statement: str,
) -> Tuple[str, ...]:
    """Return source exclusions for the exact tactic target being checked."""

    records = tuple(
        item
        for item in list(tactic_source_suppression_records or ())
        if isinstance(item, Mapping)
    )
    if records:
        try:
            from .mini_session.tactic_source_suppression import (
                excluded_tactic_source_prefixes_from_records,
            )

            return excluded_tactic_source_prefixes_from_records(
                records,
                goal_statement=goal_statement,
                helper_blocks=tactic_source_suppression_helper_blocks,
            )
        except Exception:
            return ()
    return tuple(
        str(prefix or "").strip()
        for prefix in list(excluded_source_prefixes or ())
        if str(prefix or "").strip()
    )


async def _call_tactic_closer(
    close_with_tactics: TacticCloser,
    lean: Any,
    goal_statement: str,
    preamble: str,
    helpers: Sequence[Any],
    **kwargs: Any,
) -> TacticCloseResult:
    extra_kwargs = _accepted_tactic_kwargs(close_with_tactics, kwargs)
    call_kwargs = {
        "lean": lean,
        "goal_statement": goal_statement,
        "preamble": preamble,
        "helpers": helpers,
        **extra_kwargs,
    }
    if _supports_keyword_tactic_call(close_with_tactics, call_kwargs):
        result = close_with_tactics(**call_kwargs)
    else:
        result = close_with_tactics(
            lean,
            goal_statement,
            preamble,
            helpers,
            **extra_kwargs,
        )
    if hasattr(result, "__await__"):
        result = await result
    return result


def _active_root_target_items(
    active_root_targets: Sequence[Mapping[str, Any]],
) -> List[Dict[str, Any]]:
    return [
        dict(item)
        for item in list(active_root_targets or ())
        if isinstance(item, Mapping)
        and str(item.get("working_target") or item.get("target") or "").strip()
    ]


def _with_active_root_attempt_metadata(
    attempts: Sequence[Mapping[str, Any]],
    *,
    target_statement: str,
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for attempt in list(attempts or ()):
        if not isinstance(attempt, Mapping):
            continue
        out.append(
            {
                **dict(attempt),
                "active_root_attempt": True,
                "target_statement": target_statement,
                # Carry the active-target statement on the attempt itself so that
                # every ensure_root_tactic_route_contract caller (not just the one
                # that manually re-patches success_attempt) can classify an
                # active_root_exact_helper.
                "active_root_target_statement": target_statement,
            }
        )
    return out


def _demote_active_root_attempts(
    attempts: Sequence[Mapping[str, Any]],
    *,
    reason: str,
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for attempt in list(attempts or ()):
        if not isinstance(attempt, Mapping):
            continue
        item = dict(attempt)
        if bool(item.get("ok")):
            item["active_target_ok"] = True
            item["root_authoritative_ok"] = False
            item["ok"] = False
            item["error_type"] = str(reason or "active_root_lift_failed")
            item["diagnostic"] = str(
                item.get("diagnostic")
                or item.get("output_preview")
                or "active target proof did not lift to the root theorem"
            )
        out.append(item)
    return out


def _shift_attempt_indices(
    attempts: Sequence[Mapping[str, Any]],
    *,
    offset: int,
) -> List[Dict[str, Any]]:
    shifted: List[Dict[str, Any]] = []
    for attempt in list(attempts or ()):
        if not isinstance(attempt, Mapping):
            continue
        item = dict(attempt)
        item["index"] = int(item.get("index", 0) or 0) + int(offset or 0)
        shifted.append(item)
    return shifted


def _suppressed_proofs_for_statement(
    *,
    suppressed_proofs: Sequence[str] = (),
    suppressed_proof_records: Sequence[Mapping[str, Any]] = (),
    statement: str,
) -> Tuple[str, ...]:
    target = str(statement or "").strip()
    out: List[str] = []
    seen: set[str] = set()

    def add(proof: str) -> None:
        text = str(proof or "").strip()
        if not text or text in seen:
            return
        seen.add(text)
        out.append(text)

    for proof in list(suppressed_proofs or ()):
        add(str(proof or ""))
    for record in list(suppressed_proof_records or ()):
        if not isinstance(record, Mapping):
            continue
        record_target = str(record.get("target_statement") or "").strip()
        if record_target and record_target != target:
            continue
        add(str(record.get("proof") or ""))
    return tuple(out)


def _merge_tactic_metadata(
    *items: Mapping[str, Any],
) -> Dict[str, Any]:
    merged: Dict[str, Any] = {}
    for item in items:
        for key, value in dict(item or {}).items():
            if isinstance(value, bool):
                merged[key] = bool(value)
            elif isinstance(value, int):
                merged[key] = int(merged.get(key, 0) or 0) + int(value)
            elif value not in (None, ""):
                merged[key] = value
    return merged


async def _check_active_root_lift(
    *,
    lean: Any,
    goal_statement: str,
    lifted_proof: str,
    preamble: str,
    helpers: Sequence[Any],
    timeout_s: float,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
    attempt_observer: Optional[LeanAttemptObserver] = None,
) -> Dict[str, Any]:
    started = time.monotonic()
    check = getattr(lean, "check", None)
    if check is None:
        attempt = {
            "index": 0,
            "ok": False,
            "proof": lifted_proof,
            "tactic": "active_root_lift",
            "source": "active_root_lift",
            "helper": None,
            "elapsed_s": 0.0,
            "error_type": "exception",
            "diagnostic": "lean object has no async check(...) method",
            "output_preview": "",
            "remaining_goals": [],
            "partial_proof_stub": "",
            "partial_stub_validated": False,
            "exception": "AttributeError",
            "active_root_lift": True,
        }
        notify_lean_attempt_observer(
            attempt_observer,
            "portfolio",
            {"candidate_count": 1},
        )
        notify_lean_attempt_observer(attempt_observer, "started", attempt)
        notify_lean_attempt_observer(attempt_observer, "finished", attempt)
        return attempt
    try:
        notify_lean_attempt_observer(
            attempt_observer,
            "portfolio",
            {"candidate_count": 1, "source": "active_root_lift"},
        )
        notify_lean_attempt_observer(
            attempt_observer,
            "started",
            {
                "proof": lifted_proof,
                "tactic": "active_root_lift",
                "source": "active_root_lift",
            },
        )
        result = check(
            goal_statement,
            lifted_proof,
            _helper_lemma_blocks(
                helpers,
                suppress_solution_placeholders=suppress_solution_placeholders,
                opaque_mode=opaque_mode,
                allow_official_answer_visibility=allow_official_answer_visibility,
                official_answer_payload_present=official_answer_payload_present,
            ),
            preamble_override=str(preamble or ""),
            timeout_s=max(0.1, float(timeout_s or 0.1)),
            fast_fail_timeout_s=min(
                max(0.1, float(timeout_s or 0.1)),
                max(1.0, max(0.1, float(timeout_s or 0.1)) / 3.0),
            ),
            check_kind="mini_root_tactic_active_root_lift",
        )
        if hasattr(result, "__await__"):
            result = await result
        output = str(getattr(result, "output", "") or "")
        ok = bool(getattr(result, "ok", False))
        attempt = {
            "index": 0,
            "ok": ok,
            "proof": lifted_proof,
            "tactic": "active_root_lift",
            "source": "active_root_lift",
            "helper": None,
            "elapsed_s": round(time.monotonic() - started, 3),
            "returncode": getattr(result, "returncode", None),
            "error_type": "" if ok else "active_root_lift_failed",
            "diagnostic": output[:OUTPUT_PREVIEW_CHARS],
            "output_preview": output[:OUTPUT_PREVIEW_CHARS],
            "remaining_goals": [],
            "partial_proof_stub": "",
            "partial_stub_validated": False,
            "exception": "",
            "active_root_lift": True,
        }
        notify_lean_attempt_observer(attempt_observer, "finished", attempt)
        return attempt
    except asyncio.CancelledError:
        notify_lean_attempt_observer(
            attempt_observer,
            "finished",
            {
                "index": 0,
                "ok": False,
                "proof": lifted_proof,
                "tactic": "active_root_lift",
                "source": "active_root_lift",
                "elapsed_s": round(time.monotonic() - started, 3),
                "error_type": "cancelled",
                "exception": "CancelledError",
                "cancelled": True,
            },
        )
        raise
    except Exception as exc:
        attempt = {
            "index": 0,
            "ok": False,
            "proof": lifted_proof,
            "tactic": "active_root_lift",
            "source": "active_root_lift",
            "helper": None,
            "elapsed_s": round(time.monotonic() - started, 3),
            "error_type": "exception",
            "diagnostic": str(exc)[:OUTPUT_PREVIEW_CHARS],
            "output_preview": "",
            "remaining_goals": [],
            "partial_proof_stub": "",
            "partial_stub_validated": False,
            "exception": type(exc).__name__,
            "active_root_lift": True,
        }
        notify_lean_attempt_observer(attempt_observer, "finished", attempt)
        return attempt


async def try_close_root_with_active_lift(
    *,
    lean: Any,
    goal_statement: str,
    preamble: str,
    helpers: Sequence[Any],
    active_root_targets: Sequence[Mapping[str, Any]] = (),
    timeout_s: float,
    max_candidates: int,
    candidate_portfolio: Optional[Sequence[TacticCandidate]] = None,
    candidate_portfolio_offset: int = 0,
    candidate_portfolio_phase: str = "direct",
    candidate_attempt_limit: int = 0,
    pattern_cache: Optional[TacticPatternCache] = None,
    pattern_context: Optional[Dict[str, Any]] = None,
    defer_success_cache: bool = False,
    excluded_source_prefixes: Sequence[str] = (),
    suppressed_proofs: Sequence[str] = (),
    suppressed_proof_records: Sequence[Mapping[str, Any]] = (),
    tactic_source_suppression_records: Sequence[Mapping[str, Any]] = (),
    tactic_source_suppression_helper_blocks: Sequence[str] = (),
    active_root_frame_helper_blocks: Optional[Sequence[str]] = None,
    tactic_closer: Optional[TacticCloser] = None,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
    attempt_observer: Optional[LeanAttemptObserver] = None,
) -> TacticCloseResult:
    """Close an active root target, then stitch the proof into the root shell.

    Visible-answer runs prompt the model with the mechanically reduced active
    target, not the original ``*_solution`` shell. Deterministic root assembly
    must use the same contract: prove the active target first, then verify the
    standard lift back into the original theorem.
    """

    close_with_tactics = tactic_closer or try_close_with_tactics
    helper_context_blocks = tuple(
        str(item or "")
        for item in list(tactic_source_suppression_helper_blocks or helpers or ())
        if str(item or "").strip()
    )
    frame_helper_source = (
        helpers if active_root_frame_helper_blocks is None else active_root_frame_helper_blocks
    )
    frame_helper_blocks = tuple(
        str(item or "").strip()
        for item in list(frame_helper_source or ())
        if str(item or "").strip()
    )
    active_items = _active_root_target_items(
        active_root_targets_for_frame(
            active_root_targets,
            root_statement=goal_statement,
            preamble=preamble,
            helper_blocks=frame_helper_blocks,
            require_helper_context_hash_match=True,
        )
    )
    active_statement = active_root_target_statement(
        active_items,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    requested_phase = str(candidate_portfolio_phase or "").strip()
    attempt_limit = max(0, int(candidate_attempt_limit or 0))
    if active_statement and active_statement != str(goal_statement or "").strip():
        active_started = time.monotonic()
        continuation_phase = (
            requested_phase
            if requested_phase in {"active", "fallback"}
            else "active"
        )
        active_pattern_context = {
            **dict(pattern_context or {}),
            "active_root_target": "1",
            "active_root_target_statement": active_statement,
        }
        active_attempts: List[Dict[str, Any]] = []
        active_candidate_count = 0
        lift_attempts: List[Dict[str, Any]] = []
        lifted_proof_count = 0
        metadata = {
            "active_root_target_statement": active_statement,
            "active_root_lift_attempted": False,
            "active_root_lift_succeeded": False,
        }
        active_failure_reason = "active_root_phase_complete"
        active_result: Optional[TacticCloseResult] = None
        if continuation_phase == "active":
            active_start_offset = max(
                0,
                int(candidate_portfolio_offset or 0),
            )
            active_result = await _call_tactic_closer(
                close_with_tactics,
                lean,
                active_statement,
                preamble,
                helpers,
                timeout_s=timeout_s,
                max_candidates=max_candidates,
                pattern_cache=pattern_cache,
                pattern_context=active_pattern_context,
                defer_success_cache=True,
                candidate_portfolio=(
                    tuple(candidate_portfolio)
                    if candidate_portfolio is not None
                    else None
                ),
                candidate_portfolio_offset=max(
                    0, active_start_offset
                ),
                candidate_attempt_limit=attempt_limit,
                suppressed_proofs=_suppressed_proofs_for_statement(
                    suppressed_proofs=suppressed_proofs,
                    suppressed_proof_records=suppressed_proof_records,
                    statement=active_statement,
                ),
                excluded_source_prefixes=_excluded_source_prefixes_for_statement(
                    excluded_source_prefixes=excluded_source_prefixes,
                    tactic_source_suppression_records=(
                        tactic_source_suppression_records
                    ),
                    tactic_source_suppression_helper_blocks=(
                        helper_context_blocks
                    ),
                    goal_statement=active_statement,
                ),
                suppress_solution_placeholders=suppress_solution_placeholders,
                opaque_mode=opaque_mode,
                allow_official_answer_visibility=(
                    allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    official_answer_payload_present
                ),
                attempt_observer=attempt_observer,
            )
            active_attempts = _with_active_root_attempt_metadata(
                active_result.attempts,
                target_statement=active_statement,
            )
            active_candidate_count = int(active_result.candidate_count or 0)
            metadata.update(
                dict(getattr(active_result, "cache_metadata", {}) or {})
            )
            active_failure_reason = (
                f"active_root_{getattr(active_result, 'exit_reason', '') or 'rejected'}"
            )
            active_next_offset = int(
                getattr(active_result, "next_candidate_index", 0) or 0
            )
            if (
                attempt_limit > 0
                and str(getattr(active_result, "exit_reason", "") or "")
                == "timeout"
                and active_next_offset <= active_start_offset
            ):
                # The candidate began but never settled. Preserve its exact
                # active-phase cursor; an attempt record alone cannot consume
                # the allowance or advance ownership to the fallback phase.
                return TacticCloseResult(
                    ok=False,
                    proof=None,
                    attempts=active_attempts,
                    candidate_count=active_candidate_count,
                    timeout_s=float(timeout_s),
                    elapsed_s=round(time.monotonic() - active_started, 3),
                    backend=str(
                        getattr(active_result, "backend", "")
                        or "deterministic_loop"
                    ),
                    exit_reason="timeout",
                    cache_metadata=_merge_tactic_metadata(
                        metadata,
                        {"root_tactic_candidate_portfolio_phase": "active"},
                    ),
                    candidate_portfolio=tuple(
                        getattr(active_result, "candidate_portfolio", ()) or ()
                    ),
                    next_candidate_index=active_start_offset,
                )
            if (
                str(getattr(active_result, "exit_reason", "") or "")
                == "candidate_quantum_exhausted"
            ):
                return TacticCloseResult(
                    ok=False,
                    proof=None,
                    attempts=active_attempts,
                    candidate_count=active_candidate_count,
                    timeout_s=float(timeout_s),
                    elapsed_s=round(time.monotonic() - active_started, 3),
                    backend=str(
                        getattr(active_result, "backend", "")
                        or "deterministic_loop"
                    ),
                    exit_reason="candidate_quantum_exhausted",
                    cache_metadata=_merge_tactic_metadata(
                        metadata,
                        {"root_tactic_candidate_portfolio_phase": "active"},
                    ),
                    candidate_portfolio=tuple(
                        getattr(active_result, "candidate_portfolio", ()) or ()
                    ),
                    next_candidate_index=int(
                        getattr(active_result, "next_candidate_index", 0) or 0
                    ),
                )
        if active_result is not None and active_result.ok and active_result.proof:
            from .mini_session.turn.lean_check import _active_root_lifted_proofs

            lifted_proofs = _active_root_lifted_proofs(
                root_statement=goal_statement,
                proof=active_result.proof,
                active_root_targets=active_items,
            )
            lifted_proof_count = len(lifted_proofs)
            metadata["active_root_lift_attempted"] = bool(lifted_proofs)
            for lifted_proof in lifted_proofs:
                lift_attempt = await _check_active_root_lift(
                    lean=lean,
                    goal_statement=goal_statement,
                    lifted_proof=lifted_proof,
                    preamble=preamble,
                    helpers=helpers,
                    timeout_s=min(max(0.1, float(timeout_s or 0.1)), 8.0),
                    suppress_solution_placeholders=suppress_solution_placeholders,
                    opaque_mode=opaque_mode,
                    allow_official_answer_visibility=allow_official_answer_visibility,
                    official_answer_payload_present=official_answer_payload_present,
                    attempt_observer=attempt_observer,
                )
                # Stamp the active-target statement so the winning lift attempt
                # (the first ok attempt in the returned result) carries the key
                # ensure_root_tactic_route_contract classifies off.
                lift_attempt["active_root_target_statement"] = active_statement
                lift_attempt["index"] = len(lift_attempts)
                lift_attempts.append(lift_attempt)
                if bool(lift_attempt.get("ok")):
                    # Preserve every prior (failed) lift attempt and keep indices
                    # unique by shifting the active attempts past ALL lift
                    # attempts rather than a hard-coded single slot.
                    attempts = [
                        *lift_attempts,
                        *_shift_attempt_indices(
                            active_attempts,
                            offset=len(lift_attempts),
                        ),
                    ]
                    return TacticCloseResult(
                        ok=True,
                        proof=lifted_proof,
                        attempts=attempts,
                        candidate_count=active_candidate_count + lifted_proof_count,
                        timeout_s=float(timeout_s),
                        elapsed_s=round(time.monotonic() - active_started, 3),
                        backend=str(
                            getattr(active_result, "backend", "")
                            or "deterministic_loop"
                        ),
                        exit_reason="active_root_lift_solved",
                        cache_metadata=_merge_tactic_metadata(
                            metadata,
                            {"active_root_lift_succeeded": True},
                        ),
                    )
            if lift_attempts:
                active_failure_reason = "active_root_lift_failed"
        demoted_active_attempts = _demote_active_root_attempts(
            active_attempts,
            reason=active_failure_reason,
        )
        active_allowance_consumed = bool(
            continuation_phase == "active"
            and attempt_limit > 0
            and active_result is not None
            and (
                int(getattr(active_result, "next_candidate_index", 0) or 0)
                > active_start_offset
                or (
                    bool(getattr(active_result, "ok", False))
                    and bool(list(getattr(active_result, "attempts", []) or ()))
                )
            )
        )
        if active_allowance_consumed:
            # The final active candidate used this action's entire allowance.
            # A failed lift cannot authorize an immediate fallback burst; hand
            # the untouched fallback phase to the next scheduler action.
            return TacticCloseResult(
                ok=False,
                proof=None,
                attempts=[
                    *lift_attempts,
                    *_shift_attempt_indices(
                        demoted_active_attempts,
                        offset=len(lift_attempts),
                    ),
                ],
                candidate_count=active_candidate_count + lifted_proof_count,
                timeout_s=float(timeout_s),
                elapsed_s=round(time.monotonic() - active_started, 3),
                backend=str(
                    getattr(active_result, "backend", "")
                    or "deterministic_loop"
                ),
                exit_reason="candidate_quantum_exhausted",
                cache_metadata=_merge_tactic_metadata(
                    metadata,
                    {"root_tactic_candidate_portfolio_phase": "fallback"},
                ),
                candidate_portfolio=(),
                next_candidate_index=0,
            )
        fallback_result = await _call_tactic_closer(
            close_with_tactics,
            lean,
            goal_statement,
            preamble,
            helpers,
            timeout_s=timeout_s,
            max_candidates=max_candidates,
            pattern_cache=pattern_cache,
            pattern_context={
                **dict(pattern_context or {}),
                "active_root_fallback": "1",
                "active_root_target_statement": active_statement,
            },
            defer_success_cache=defer_success_cache,
            candidate_portfolio=(
                tuple(candidate_portfolio)
                if continuation_phase == "fallback"
                and candidate_portfolio is not None
                else None
            ),
            candidate_portfolio_offset=(
                max(0, int(candidate_portfolio_offset or 0))
                if continuation_phase == "fallback"
                else 0
            ),
            candidate_attempt_limit=attempt_limit,
            suppressed_proofs=_suppressed_proofs_for_statement(
                suppressed_proofs=suppressed_proofs,
                suppressed_proof_records=suppressed_proof_records,
                statement=goal_statement,
            ),
            excluded_source_prefixes=_excluded_source_prefixes_for_statement(
                excluded_source_prefixes=excluded_source_prefixes,
                tactic_source_suppression_records=tactic_source_suppression_records,
                tactic_source_suppression_helper_blocks=helper_context_blocks,
                goal_statement=goal_statement,
            ),
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
            attempt_observer=attempt_observer,
        )
        active_failure_attempts = [
            *lift_attempts,
            *_shift_attempt_indices(
                demoted_active_attempts,
                offset=len(lift_attempts),
            ),
        ]
        fallback_attempts = _shift_attempt_indices(
            getattr(fallback_result, "attempts", []) or (),
            offset=len(active_failure_attempts),
        )
        combined_attempts = [*active_failure_attempts, *fallback_attempts]
        combined_metadata = _merge_tactic_metadata(
            metadata,
            getattr(fallback_result, "cache_metadata", {}) or {},
            {
                "active_root_fallback_attempted": True,
                "active_root_fallback_succeeded": bool(fallback_result.ok),
                "root_tactic_candidate_portfolio_phase": "fallback",
            },
        )
        if fallback_result.ok and fallback_result.proof:
            return TacticCloseResult(
                ok=True,
                proof=fallback_result.proof,
                attempts=combined_attempts,
                candidate_count=active_candidate_count
                + lifted_proof_count
                + int(getattr(fallback_result, "candidate_count", 0) or 0),
                timeout_s=float(timeout_s),
                elapsed_s=round(time.monotonic() - active_started, 3),
                backend=str(
                    getattr(fallback_result, "backend", "")
                    or "deterministic_loop"
                ),
                exit_reason="active_root_fallback_solved",
                cache_metadata=combined_metadata,
            )
        return TacticCloseResult(
            ok=False,
            proof=None,
            attempts=combined_attempts,
            candidate_count=active_candidate_count
            + lifted_proof_count
            + int(getattr(fallback_result, "candidate_count", 0) or 0),
            timeout_s=float(timeout_s),
            elapsed_s=round(time.monotonic() - active_started, 3),
            backend=str(
                getattr(fallback_result, "backend", "") or "deterministic_loop"
            ),
            exit_reason=(
                str(getattr(fallback_result, "exit_reason", "") or "")
                if attempt_limit > 0
                and str(getattr(fallback_result, "exit_reason", "") or "")
                in {"candidate_quantum_exhausted", "timeout"}
                else (
                    f"{active_failure_reason};"
                    "fallback_"
                    f"{getattr(fallback_result, 'exit_reason', '') or 'rejected'}"
                )
            ),
            cache_metadata=combined_metadata,
            candidate_portfolio=tuple(
                getattr(fallback_result, "candidate_portfolio", ()) or ()
            ),
            next_candidate_index=int(
                getattr(fallback_result, "next_candidate_index", 0) or 0
            ),
        )

    return await _call_tactic_closer(
        close_with_tactics,
        lean,
        goal_statement,
        preamble,
        helpers,
        timeout_s=timeout_s,
        max_candidates=max_candidates,
        candidate_portfolio=(
            tuple(candidate_portfolio)
            if candidate_portfolio is not None
            else None
        ),
        candidate_portfolio_offset=max(
            0,
            int(candidate_portfolio_offset or 0),
        ),
        candidate_attempt_limit=attempt_limit,
        pattern_cache=pattern_cache,
        pattern_context=pattern_context,
        defer_success_cache=defer_success_cache,
        suppressed_proofs=_suppressed_proofs_for_statement(
            suppressed_proofs=suppressed_proofs,
            suppressed_proof_records=suppressed_proof_records,
            statement=goal_statement,
        ),
        excluded_source_prefixes=_excluded_source_prefixes_for_statement(
            excluded_source_prefixes=excluded_source_prefixes,
            tactic_source_suppression_records=tactic_source_suppression_records,
            tactic_source_suppression_helper_blocks=helper_context_blocks,
            goal_statement=goal_statement,
        ),
        suppress_solution_placeholders=suppress_solution_placeholders,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
        attempt_observer=attempt_observer,
    )


def _helper_names_from_blocks(blocks: List[str]) -> List[str]:
    names: List[str] = []
    seen: set[str] = set()
    for block in blocks:
        name = helper_decl_name(block)
        if name and name not in seen:
            seen.add(name)
            names.append(name)
    return names


def _helper_blocks_for_names(
    blocks: Sequence[str],
    names: Sequence[str],
) -> List[str]:
    wanted = {
        str(name or "").strip()
        for name in list(names or ())
        if str(name or "").strip()
    }
    if not wanted:
        return [str(block or "") for block in list(blocks or ())]
    return [
        str(block or "")
        for block in list(blocks or ())
        if (helper_decl_name(str(block or "")) or "") in wanted
    ]


def _root_replay_blocks_for_helper_names(
    *,
    dossier: Any,
    helper_context: Sequence[str],
    helper_names: Sequence[str],
) -> List[str]:
    clean_names = [
        str(name or "").strip()
        for name in list(helper_names or ())
        if str(name or "").strip()
    ]
    selected_blocks = _helper_blocks_for_names(helper_context, clean_names)
    replay_closure = getattr(dossier, "root_replay_helper_closure", None)
    if callable(replay_closure):
        closed = replay_closure(
            replay_helpers=selected_blocks,
            support_helper_names=clean_names,
        )
        if closed:
            return list(closed)
    return selected_blocks


def _lean_name_occurs(text: str, name: str) -> bool:
    clean_name = str(name or "").strip()
    if not clean_name:
        return False
    return bool(
        re.search(
            rf"(?<![\w'.]){re.escape(clean_name)}(?![\w'])",
            str(text or ""),
            flags=re.UNICODE,
        )
    )


def _success_attempt_helper_names(success_attempt: Any) -> List[str]:
    if not isinstance(success_attempt, dict):
        return []
    raw = str(success_attempt.get("helper") or "").strip()
    if not raw:
        return []
    names: List[str] = []
    for piece in raw.split(","):
        name = piece.strip()
        if name and name not in names:
            names.append(name)
    return names


_BROAD_CONTEXT_TACTIC_RE = re.compile(
    r"(?<![\w'.])(simp(?:a)?|aesop|exact\?|omega|linarith|nlinarith|"
    r"ring_nf|norm_num|positivity|field_simp|tauto|decide)(?![\w'])",
    flags=re.UNICODE,
)


def _proof_may_use_helper_context_implicitly(proof: str) -> bool:
    return bool(_BROAD_CONTEXT_TACTIC_RE.search(str(proof or "")))


def root_tactic_helper_dependencies(
    proof: str,
    helpers: Sequence[str],
    *,
    success_attempt: Any = None,
) -> List[str]:
    """Return verified helper names visibly used by a root tactic proof."""

    helper_names = _helper_names_from_blocks(list(helpers or []))
    if not helper_names:
        return []
    proof_text = str(proof or "")
    if _proof_may_use_helper_context_implicitly(proof_text):
        return list(helper_names)
    selected: List[str] = []
    for name in _success_attempt_helper_names(success_attempt):
        if name in helper_names and name not in selected:
            selected.append(name)
    for name in helper_names:
        if name in selected:
            continue
        if _lean_name_occurs(proof_text, name):
            selected.append(name)
    return selected


def ensure_root_tactic_route_contract(
    dossier: Any,
    *,
    proof: str,
    helper_blocks: Sequence[str],
    success_attempt: Any = None,
    phase: str,
    turn_index: int = 0,
    target_statement: str = "",
) -> Dict[str, Any]:
    """Materialize a root-assembly contract from a Lean-accepted helper proof."""

    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {"created": False, "verdict": "missing_proof_graph"}
    target = str(target_statement or getattr(dossier, "root_statement", "") or "")
    used_helper_names = root_tactic_helper_dependencies(
        proof,
        list(helper_blocks or []),
        success_attempt=success_attempt,
    )
    if not used_helper_names:
        return {"created": False, "verdict": "root_tactic_no_helper_dependencies"}
    helper_node_ids: List[str] = []
    missing_helper_names: List[str] = []
    helper_name_to_node_id = getattr(graph, "helper_name_to_node_id", {}) or {}
    graph_nodes = getattr(graph, "nodes", {}) or {}
    for helper_name in used_helper_names:
        node_id = str(helper_name_to_node_id.get(helper_name) or "").strip()
        if not node_id:
            try:
                node_id = str(graph.helper_node_id(helper_name) or "").strip()
            except Exception:
                node_id = ""
        if node_id and node_id in graph_nodes:
            if node_id not in helper_node_ids:
                helper_node_ids.append(node_id)
        elif helper_name not in missing_helper_names:
            missing_helper_names.append(helper_name)
    if missing_helper_names or not helper_node_ids:
        return {
            "created": False,
            "verdict": "root_tactic_missing_helper_nodes",
            "helper_names": used_helper_names,
            "missing_helper_names": missing_helper_names,
            "required_node_ids": helper_node_ids,
        }
    try:
        root_key = canonical_dossier_statement_key(target)
        active_target_statement = (
            str(success_attempt.get("active_root_target_statement") or "").strip()
            if isinstance(success_attempt, dict)
            else ""
        )
        active_target_key = canonical_dossier_statement_key(active_target_statement)
        proof_key = text_hash(str(proof or ""))
        helper_statements = {
            helper_name: helper_decl_statement(block)
            for block in list(helper_blocks or ())
            for helper_name in [helper_decl_name(str(block or ""))]
            if helper_name
        }
        root_exact_helper_node_id = ""
        if len(used_helper_names) == 1:
            only_helper_name = used_helper_names[0]
            if (
                root_key
                and canonical_dossier_statement_key(
                    helper_statements.get(only_helper_name, "")
                )
                == root_key
            ):
                root_exact_helper_node_id = helper_node_ids[0]
        active_root_exact_helper_node_id = ""
        if (
            not root_exact_helper_node_id
            and active_target_key
            and len(used_helper_names) == 1
        ):
            only_helper_name = used_helper_names[0]
            if (
                canonical_dossier_statement_key(
                    helper_statements.get(only_helper_name, "")
                )
                == active_target_key
            ):
                active_root_exact_helper_node_id = helper_node_ids[0]
        root_exact_metadata = (
            {
                "source": "root_exact_helper",
                "root_exact_helper_name": used_helper_names[0],
                "root_exact_helper_node_id": root_exact_helper_node_id,
            }
            if root_exact_helper_node_id
            else {}
        )
        active_root_exact_metadata = (
            {
                "source": "active_root_exact_helper",
                "active_root_target_statement": active_target_statement,
                "active_root_exact_helper_name": used_helper_names[0],
                "active_root_exact_helper_node_id": active_root_exact_helper_node_id,
            }
            if active_root_exact_helper_node_id
            else {}
        )
        route = graph.record_strategy_route(
            name=f"root_tactic_route_{proof_key}",
            description=(
                "Root assembly contract inferred from a Lean-accepted "
                "deterministic helper tactic proof."
            ),
            route_key=":".join(
                [
                    "root_tactic",
                    root_key or text_hash(target),
                    proof_key,
                    text_hash("|".join(helper_node_ids)),
                ]
            ),
            score=0.7,
            phase=phase,
            turn_index=turn_index,
            metadata={
                "route_scope": "root_assembly",
                "source_phase": phase,
                "root_tactic_helper_names": list(used_helper_names),
                "root_tactic_proof_hash": proof_key,
                **root_exact_metadata,
                **active_root_exact_metadata,
            },
        )
        for node_id in helper_node_ids:
            graph.attach_claim_to_route(route.node_id, node_id)
        graph.set_route_assembly_contract(
            route.node_id,
            required_node_ids=helper_node_ids,
            target_statement=target,
            phase=phase,
            turn_index=turn_index,
            metadata={
                "root_tactic_helper_names": list(used_helper_names),
                "root_tactic_proof_hash": proof_key,
                **root_exact_metadata,
                **active_root_exact_metadata,
            },
        )
        status_getter = getattr(graph, "route_assembly_contract_status", None)
        if callable(status_getter):
            status = dict(status_getter(route.node_id, target_statement=target) or {})
        else:
            status = {"ready": False, "verdict": "route_contract_status_api_missing"}
        status["created"] = True
        status["created_route_id"] = route.node_id
        status["helper_names"] = list(used_helper_names)
        return status
    except Exception as exc:
        return {
            "created": False,
            "verdict": "root_tactic_contract_creation_exception",
            "exception_type": type(exc).__name__,
            "helper_names": list(used_helper_names),
            "required_node_ids": helper_node_ids,
        }


def root_tactic_success_contract_status(
    dossier: Any,
    *,
    proof: str,
    helper_blocks: Sequence[str],
    success_attempt: Any = None,
    phase: str,
    turn_index: int = 0,
    target_statement: str = "",
) -> Dict[str, Any]:
    """Return the contract status required for a successful root tactic proof."""

    dependencies = root_tactic_helper_dependencies(
        proof,
        list(helper_blocks or []),
        success_attempt=success_attempt,
    )
    if not dependencies:
        return {
            "ready": True,
            "verdict": "root_tactic_no_helper_dependencies",
            "helper_names": [],
        }
    created = ensure_root_tactic_route_contract(
        dossier,
        proof=proof,
        helper_blocks=helper_blocks,
        success_attempt=success_attempt,
        phase=phase,
        turn_index=turn_index,
        target_statement=target_statement,
    )
    if not bool(created.get("created")):
        status = dict(created)
        status.setdefault("ready", False)
        status["helper_names"] = list(dependencies)
        status["contract_creation_verdict"] = str(created.get("verdict") or "")
        return status
    status = dict(created)
    status["helper_names"] = list(dependencies)
    status["contract_creation_verdict"] = str(created.get("verdict") or "")
    return status


def _trace(prefix: str, msg: str) -> None:
    print(f"{prefix}{msg}", flush=True)


def root_assembly_contract_status(
    dossier: Any,
    *,
    target_statement: str = "",
) -> Dict[str, Any]:
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {
            "ready": False,
            "verdict": "missing_proof_graph",
        }
    status_getter = getattr(graph, "ready_root_assembly_contract_status", None)
    if not callable(status_getter):
        return {
            "ready": False,
            "verdict": "root_assembly_contract_status_api_missing",
        }
    try:
        status = dict(
            status_getter(
                target_statement=str(
                    target_statement
                    or getattr(dossier, "root_statement", "")
                    or ""
                ),
            )
            or {}
        )
    except Exception as exc:
        status = {
            "ready": False,
            "verdict": "root_assembly_contract_status_exception",
            "exception_type": type(exc).__name__,
        }
    if not bool(status.get("ready")):
        increment = getattr(dossier, "increment_tool_metric", None)
        if callable(increment):
            try:
                increment("mini_root_assembly_contract_blocked", 1)
            except Exception:
                pass
    return status


async def try_root_tactic_close(
    *,
    phase: str,
    theorem_name: str,
    goal_statement: str,
    preamble: str,
    lean: Any,
    dossier: Any,
    recorder: Optional[Any],
    trace_prefix: str,
    timeout_s: float,
    max_candidates: int,
    pattern_cache: Optional[TacticPatternCache] = None,
    pattern_context: Optional[Dict[str, Any]] = None,
    helper_blocks: Optional[List[str]] = None,
    active_root_targets: Sequence[Mapping[str, Any]] = (),
    excluded_source_prefixes: Sequence[str] = (),
    suppressed_proofs: Sequence[str] = (),
    suppressed_proof_records: Sequence[Mapping[str, Any]] = (),
    tactic_source_suppression_records: Sequence[Mapping[str, Any]] = (),
    tactic_source_suppression_helper_blocks: Sequence[str] = (),
    active_root_frame_helper_blocks: Optional[Sequence[str]] = None,
    tactic_closer: Optional[TacticCloser] = None,
    transient_checker: Optional[TransientChecker] = None,
    trace: Optional[TraceFn] = None,
    finalize_root: bool = True,
    opaque_mode: Optional[bool] = None,
    allow_official_answer_visibility: Optional[bool] = None,
    official_answer_payload_present: Optional[bool] = None,
    suppress_solution_placeholders: Optional[bool] = None,
) -> Tuple[bool, Optional[str]]:
    """Run the deterministic root closer and persist the result."""

    timeout = max(0.0, float(timeout_s or 0.0))
    max_cands = max(0, int(max_candidates or 0))
    if timeout <= 0.0 or max_cands <= 0:
        return False, None

    close_with_tactics = tactic_closer or try_close_with_tactics
    is_transient = transient_checker or is_transient_tactic_close_failure
    trace_fn = trace or _trace
    effective_opaque_mode = bool(
        getattr(dossier, "opaque_mode", True) if opaque_mode is None else opaque_mode
    )
    effective_allow_official_answer_visibility = bool(
        getattr(dossier, "allow_official_answer_visibility", False)
        if allow_official_answer_visibility is None
        else allow_official_answer_visibility
    )
    effective_official_answer_payload_present = (
        getattr(dossier, "official_answer_payload_present", None)
        if official_answer_payload_present is None
        else official_answer_payload_present
    )
    effective_suppress_solution_placeholders = bool(
        getattr(dossier, "suppress_solution_placeholders", True)
        if suppress_solution_placeholders is None
        else suppress_solution_placeholders
    )

    helpers = (
        list(helper_blocks)
        if helper_blocks is not None
        else dossier.verified_helper_blocks()
    )
    if active_root_frame_helper_blocks is None:
        try:
            active_root_frame_helper_blocks = dossier.verified_helper_blocks()
        except Exception:
            active_root_frame_helper_blocks = helpers
    trace_fn(
        trace_prefix,
        f"=== {phase} {theorem_name} "
        f"({len(helpers)} helper(s), {max_cands} candidate cap) ===",
    )
    attempt_lane = tactic_lane_for_phase(phase) or "other_root_tactic"
    attempt_observer = dossier_lean_attempt_observer(dossier, attempt_lane)
    result = await try_close_root_with_active_lift(
        lean=lean,
        goal_statement=goal_statement,
        preamble=preamble,
        helpers=helpers,
        active_root_targets=active_root_targets_for_frame(
            active_root_targets or dossier,
            root_statement=goal_statement,
            preamble=preamble,
            helper_blocks=active_root_frame_helper_blocks,
            require_helper_context_hash_match=True,
        ),
        timeout_s=timeout,
        max_candidates=max_cands,
        pattern_cache=pattern_cache,
        pattern_context=pattern_context,
        excluded_source_prefixes=excluded_source_prefixes,
        suppressed_proofs=suppressed_proofs,
        suppressed_proof_records=suppressed_proof_records,
        tactic_source_suppression_records=tactic_source_suppression_records,
        tactic_source_suppression_helper_blocks=(
            tactic_source_suppression_helper_blocks or helpers
        ),
        active_root_frame_helper_blocks=active_root_frame_helper_blocks,
        tactic_closer=close_with_tactics,
        suppress_solution_placeholders=effective_suppress_solution_placeholders,
        opaque_mode=effective_opaque_mode,
        allow_official_answer_visibility=effective_allow_official_answer_visibility,
        official_answer_payload_present=effective_official_answer_payload_present,
        attempt_observer=attempt_observer,
    )
    success_attempt = next(
        (
            attempt
            for attempt in result.attempts
            if isinstance(attempt, dict) and attempt.get("ok")
        ),
        None,
    )
    helper_names = _helper_names_from_blocks(helpers)
    first_attempt = (
        result.attempts[0]
        if result.attempts and isinstance(result.attempts[0], dict)
        else {}
    )
    attempted_proofs = [
        str(attempt.get("proof") or "").strip()
        for attempt in result.attempts
        if isinstance(attempt, dict) and str(attempt.get("proof") or "").strip()
    ]
    attempted_proof_records = [
        {
            "proof": str(attempt.get("proof") or "").strip(),
            "target_statement": str(
                attempt.get("target_statement") or goal_statement or ""
            ).strip(),
        }
        for attempt in result.attempts
        if isinstance(attempt, dict) and str(attempt.get("proof") or "").strip()
    ]
    record = {
        "phase": phase,
        "helper_count": len(helpers),
        "helper_names": helper_names,
        "tactic_candidate_count": result.candidate_count,
        **tactic_attempt_telemetry_fields(result.attempts),
        "tactic_attempts": result.attempts[:10],
        "tactic_attempted_proofs": attempted_proofs,
        "tactic_attempted_proof_records": attempted_proof_records,
        "tactic_success_attempt": success_attempt,
        "tactic_success_index": (
            success_attempt.get("index") if success_attempt else None
        ),
        "tactic_elapsed_s": result.elapsed_s,
        "tactic_exit_reason": result.exit_reason,
        "tactic_pattern_cache": dict(getattr(result, "cache_metadata", {}) or {}),
        "verdict": "tactic_solved" if result.ok else "tactic_rejected",
    }
    active_root_target_statement_text = str(
        dict(getattr(result, "cache_metadata", {}) or {}).get(
            "active_root_target_statement"
        )
        or ""
    ).strip()
    if active_root_target_statement_text:
        record["active_root_target_statement"] = active_root_target_statement_text
        record["active_root_lift_attempted"] = bool(
            dict(getattr(result, "cache_metadata", {}) or {}).get(
                "active_root_lift_attempted"
            )
        )
        record["active_root_lift_succeeded"] = bool(
            dict(getattr(result, "cache_metadata", {}) or {}).get(
                "active_root_lift_succeeded"
            )
        )
    contract_status: Dict[str, Any] = {}
    root_assembly_uses_helpers = False
    if result.ok and result.proof:
        contract_status = root_tactic_success_contract_status(
            dossier,
            proof=result.proof,
            helper_blocks=helpers,
            success_attempt=success_attempt,
            phase=phase,
            turn_index=0,
            target_statement=goal_statement,
        )
        root_assembly_uses_helpers = (
            str(contract_status.get("verdict") or "")
            != "root_tactic_no_helper_dependencies"
        )
    if result.ok and result.proof and root_assembly_uses_helpers:
        record["route_assembly_contract_status"] = contract_status
        if not bool(contract_status.get("ready")):
            record["verdict"] = "root_route_contract_not_ready"
            record["route_contract_verdict"] = str(
                contract_status.get("verdict") or ""
            )
    transient_failure = is_transient(result)
    if transient_failure:
        record["verdict"] = "tactic_transient_failure"
        record["root_tactic_context_preserved"] = True
    if recorder is not None:
        recorder.record_turn(record)

    if (
        result.ok
        and result.proof
        and (not root_assembly_uses_helpers or bool(contract_status.get("ready")))
    ):
        if not finalize_root:
            trace_fn(
                trace_prefix,
                f"=== {phase} found root proof in {result.elapsed_s}s; "
                "finalization deferred to caller ===",
            )
            return True, result.proof
        from .root_finalization import (
            finalize_root_solution,
            root_verification_certificate,
        )

        route_helper_names = [
            str(name or "").strip()
            for name in list(contract_status.get("helper_names") or [])
            if str(name or "").strip()
        ]
        replay_helper_names = route_helper_names or helper_names
        replay_helpers = _root_replay_blocks_for_helper_names(
            dossier=dossier,
            helper_context=helpers,
            helper_names=replay_helper_names,
        )
        if not replay_helpers:
            replay_helpers = list(helpers)
        replay_helper_names = _helper_names_from_blocks(replay_helpers) or replay_helper_names
        finalization = finalize_root_solution(
            dossier=dossier,
            proof_state=None,
            proof=result.proof,
            replay_helpers=replay_helpers,
            helper_names=replay_helper_names,
            phase=phase,
            turn_index=0,
            route_id=str(
                contract_status.get("route_id")
                or contract_status.get("created_route_id")
                or ""
            ),
            dependency_node_ids=tuple(
                str(node_id or "").strip()
                for node_id in list(
                    contract_status.get("dependency_node_ids")
                    or contract_status.get("required_node_ids")
                    or []
                )
                if str(node_id or "").strip()
            ),
            dependency_helper_names=route_helper_names or replay_helper_names,
            target_statement=goal_statement,
            require_route_contract=root_assembly_uses_helpers,
            verification_certificate=root_verification_certificate(
                accepted=True,
                proof=result.proof,
                phase=phase,
                turn_index=0,
                target_statement=goal_statement,
                replay_helpers=replay_helpers,
                helper_names=replay_helper_names,
                output=str(
                    (success_attempt or {}).get("output")
                    or (success_attempt or {}).get("output_preview")
                    or ""
                ),
                source="mini_root_tactic",
            ),
            require_verification_certificate=True,
        )
        record["root_finalization"] = {
            "accepted": finalization.accepted,
            "verdict": finalization.verdict,
        }
        if not finalization.accepted:
            trace_fn(
                trace_prefix,
                f"=== {phase} found root proof but finalization blocked: "
                f"{finalization.verdict} ===",
            )
            return False, None
        notify_lean_attempt_observer(
            attempt_observer,
            "certificate_accepted",
            {"proof": result.proof, "phase": phase},
        )
        trace_fn(
            trace_prefix,
            f"=== {phase} solved root in {result.elapsed_s}s ===",
        )
        return True, result.proof
    if result.ok and result.proof and root_assembly_uses_helpers:
        dossier.record_attempt(
            phase=phase,
            turn_index=0,
            proof=result.proof,
            helper_names=helper_names,
            verdict="root_route_contract_not_ready",
            metadata={"route_assembly_contract_status": contract_status},
        )
        trace_fn(
            trace_prefix,
            f"=== {phase} found root proof but no ready root route contract ===",
        )
        return False, None

    rejected_verdict = (
        "tactic_transient_failure" if transient_failure else "tactic_rejected"
    )
    dossier.record_attempt(
        phase=phase,
        turn_index=0,
        proof="",
        helper_names=helper_names,
        verdict=rejected_verdict,
        error_type=str(first_attempt.get("error_type", "") or ""),
        metadata={
            "tactic_candidate_count": result.candidate_count,
            **tactic_attempt_telemetry_fields(result.attempts),
            "tactic_attempts": result.attempts[:10],
            "tactic_attempted_proofs": attempted_proofs,
            "tactic_attempted_proof_records": attempted_proof_records,
            "tactic_exit_reason": result.exit_reason,
            "root_tactic_context_preserved": bool(transient_failure),
        },
    )
    trace_fn(
        trace_prefix,
        f"=== {phase} did not close root ({result.exit_reason}, "
        f"{result.elapsed_s}s) ===",
    )
    return False, None


__all__ = [
    "ensure_root_tactic_route_contract",
    "root_assembly_contract_status",
    "root_tactic_helper_dependencies",
    "root_tactic_success_contract_status",
    "try_close_root_with_active_lift",
    "try_root_tactic_close",
]
