"""Deterministic tactic/root closer for the mini prover.

This module is intentionally disjoint from ``mini_prover.py``.  It provides a
small, answer-safe closing loop that only checks candidates against the
caller-supplied prompt-visible preamble.  Hidden/materialized answer values and
oracle suggestion harvesting are deliberately out of scope here.

The public ``try_close_with_tactics`` API runs candidates through the configured
``TacticBackend`` contract and returns a stable result shape with attempt
telemetry.
"""

from __future__ import annotations

import asyncio
import inspect
import re
import time
from dataclasses import asdict, dataclass, field
from typing import Any, Mapping, Optional, Protocol, Sequence

from .deadline_guard import outer_guard_timeout_s
from .lean_parser import canonical_error_type, diagnostic_preview
from .lean_resource_guard import (
    looks_like_dangerous_nat_pow_tower,
    uses_expensive_normalizer,
)
from .mini_cast_normalizer import (
    cast_normalization_scripts,
    detect_cast_normalization_profile,
)
from .mini_finset_reindexer import (
    detect_finset_reindexing_profile,
    finset_reindexing_scripts,
)
from .mini_session.process_watchdog import begin_process_deadline
from .tactic_attempt_telemetry import (
    LeanAttemptObserver,
    notify_lean_attempt_observer,
)
from .proof_dossier import (
    effective_solution_placeholder_suppression,
    helper_decl_name,
    helper_decl_statement,
    is_answer_unsafe_helper_source,
)
from .proof_dossier import text_hash
from .utils import normalize_statement


DEFAULT_TIMEOUT_S = 30.0
DEFAULT_MAX_CANDIDATES = 64
OUTPUT_PREVIEW_CHARS = 1200
HELPER_STITCH_LIMIT = 12
HELPER_SET_EXT_LIMIT = 8
HELPER_DIRECT_SIMPA_LIMIT = 16
HELPER_DIRECT_EXACT_LIMIT = 4
HELPER_STRUCTURAL_LIMIT = 8
MAX_STRUCTURAL_PAIR_CANDIDATES = 24
MAX_STRUCTURAL_TRIPLE_CANDIDATES = 12
MAX_CONJUNCTION_PROJECTION_HELPERS = 2
MAX_CONJUNCTION_PROJECTIONS = 5
_TRANSIENT_TACTIC_ERROR_TYPES = {"exception", "infra_failure"}
_NON_CACHEABLE_TACTIC_ERROR_TYPES = {"exception", "infra_failure"}

_LEAN_NAME_SEGMENT_RE = r"(?:«[^»]+»|(?:[^\W\d]|_)[\w']*)"
_LEAN_NAME_RE = re.compile(
    rf"^{_LEAN_NAME_SEGMENT_RE}(?:\.{_LEAN_NAME_SEGMENT_RE})*$",
    flags=re.UNICODE,
)
_DECL_NAME_RE = re.compile(
    rf"\b(?:lemma|theorem|axiom|def)\s+"
    rf"({_LEAN_NAME_SEGMENT_RE}(?:\.{_LEAN_NAME_SEGMENT_RE})*)",
    flags=re.UNICODE,
)


def _strip_balanced_outer_parens(text: str) -> str:
    stripped = str(text or "").strip()
    while stripped.startswith("(") and stripped.endswith(")"):
        depth = 0
        balanced_outer = True
        for index, char in enumerate(stripped):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(stripped) - 1:
                    balanced_outer = False
                    break
            if depth < 0:
                balanced_outer = False
                break
        if not balanced_outer or depth != 0:
            break
        stripped = stripped[1:-1].strip()
    return stripped


def _split_top_level_once(text: str, symbol: str) -> tuple[str, str] | None:
    raw = str(text or "")
    depth = 0
    for index, char in enumerate(raw):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and char == symbol:
            left = raw[:index].strip()
            right = raw[index + 1 :].strip()
            if left and right:
                return left, right
            return None
    return None


def _conjunction_projection_paths(statement: str) -> list[str]:
    """Return valid Lean projection suffixes for top-level conjunction leaves."""

    def walk(expr: str, prefix: str) -> list[str]:
        current = _strip_balanced_outer_parens(expr)
        split = _split_top_level_once(current, "∧")
        if split is None:
            return [prefix] if prefix else []
        left, right = split
        return [
            *walk(left, f"{prefix}.1" if prefix else ".1"),
            *walk(right, f"{prefix}.2" if prefix else ".2"),
        ]

    paths = walk(statement, "")
    if len(paths) < 2:
        return []
    return paths[:MAX_CONJUNCTION_PROJECTIONS]


def _normalize_statement_for_tactic_cache(statement: str) -> str:
    return normalize_statement(statement)


@dataclass(frozen=True)
class TacticCandidate:
    """A Lean proof candidate produced by the closer."""

    proof: str
    tactic: str
    source: str
    helper: Optional[str] = None


@dataclass(frozen=True)
class TacticAttempt:
    """One Lean check record for a tactic candidate."""

    index: int
    ok: bool
    proof: str
    tactic: str
    source: str
    helper: Optional[str]
    elapsed_s: float
    returncode: Optional[int] = None
    error_type: str = ""
    diagnostic: str = ""
    output_preview: str = ""
    remaining_goals: list[dict[str, Any]] = field(default_factory=list)
    partial_proof_stub: str = ""
    partial_stub_validated: bool = False
    exception: str = ""


@dataclass(frozen=True)
class TacticCloseResult:
    """Result returned by ``try_close_with_tactics``."""

    ok: bool
    proof: Optional[str]
    attempts: list[dict[str, Any]]
    candidate_count: int
    timeout_s: float
    elapsed_s: float
    backend: str = "deterministic_loop"
    exit_reason: str = "exhausted"
    cache_metadata: dict[str, Any] = field(default_factory=dict)
    # Reusable generated/ranked portfolio plus the first unattempted index.
    # Callers may resume after an external acceptance veto without copying,
    # regenerating, or rechecking earlier candidates.
    candidate_portfolio: tuple[TacticCandidate, ...] = field(
        default_factory=tuple,
        repr=False,
    )
    next_candidate_index: int = 0


def is_transient_tactic_close_failure(result: Any) -> bool:
    """Return True when a failed tactic close did not exhaust the context.

    Context-gating callers use this to decide whether a helper/root tactic
    context can be durably skipped on future turns. A portfolio-level timeout
    before all candidates run is transient. A candidate-level timeout in an
    otherwise exhausted portfolio is a completed tactic verdict for this
    budget, while infra failures remain retryable.
    """

    if result is None or bool(getattr(result, "ok", False)):
        return False
    attempts = getattr(result, "attempts", None) or []
    if not attempts:
        exit_reason = str(getattr(result, "exit_reason", "") or "").strip().lower()
        return exit_reason == "timeout"
    try:
        candidate_count = int(getattr(result, "candidate_count", 0) or 0)
    except (TypeError, ValueError):
        candidate_count = 0
    exit_reason = str(getattr(result, "exit_reason", "") or "").strip().lower()
    if exit_reason == "timeout" and (candidate_count <= 0 or len(attempts) < candidate_count):
        return True
    if any(
        isinstance(attempt, Mapping)
        and str(attempt.get("error_type") or "") in _TRANSIENT_TACTIC_ERROR_TYPES
        for attempt in attempts
    ):
        return True
    return False


def is_transient_tactic_exception(exc: BaseException) -> bool:
    """Return True for infrastructure exceptions that should be retryable.

    Deterministic tactic actions should not permanently suppress a context or
    exhaust their action budget when the tactic portfolio itself was interrupted
    by a wall-clock/backend timeout before it could produce a Lean verdict.
    """

    if isinstance(exc, TimeoutError):
        return True
    name = type(exc).__name__
    module = type(exc).__module__
    lowered = f"{module}.{name}".lower()
    return bool(
        "timeout" in lowered
        or lowered.endswith(".readtimeout")
        or lowered.endswith(".connecttimeout")
        or lowered.endswith(".writetimeout")
        or lowered.endswith(".pooltimeout")
    )


class TacticPatternCache:
    """Run-local memory for tactic candidates that succeeded or failed.

    Cached successes are only replay hints: every replay still goes through
    Lean. Failed shapes are retired only for deterministic, helper-independent
    tactics; context-sensitive automation remains exact-key only.
    """

    _SHAPE_REPLAY_SAFE_SOURCES = {
        "intro_coercion",
        "residual_split",
        "standalone",
        "structural",
        "structural_ext",
    }

    def __init__(self, *, max_entries: int = 4096) -> None:
        self.max_entries = max(1, int(max_entries or 4096))
        self._successes: dict[str, TacticCandidate] = {}
        self._failures: dict[str, set[str]] = {}
        self._shape_successes: dict[str, list[TacticCandidate]] = {}
        self._shape_failures: dict[str, set[str]] = {}
        self._last_access: dict[str, int] = {}
        self._access_seq = 0

    def checkpoint_state(self) -> dict[str, Any]:
        """Return the exact run-local tactic memory used by future selection."""

        def candidate_record(candidate: TacticCandidate) -> dict[str, Any]:
            return {
                "proof": candidate.proof,
                "tactic": candidate.tactic,
                "source": candidate.source,
                "helper": candidate.helper,
            }

        return {
            "schema_version": 2,
            "max_entries": self.max_entries,
            "successes": {
                key: candidate_record(value)
                for key, value in self._successes.items()
            },
            "failures": {
                key: sorted(values) for key, values in self._failures.items()
            },
            "shape_successes": {
                key: [candidate_record(value) for value in values]
                for key, values in self._shape_successes.items()
            },
            "shape_failures": {
                key: sorted(values) for key, values in self._shape_failures.items()
            },
            "last_access": dict(self._last_access),
            "access_seq": self._access_seq,
        }

    def restore_checkpoint_state(self, record: Mapping[str, Any]) -> None:
        """Restore a state emitted by :meth:`checkpoint_state`."""

        if int(record.get("schema_version", 0) or 0) not in {1, 2}:
            raise ValueError("unsupported tactic-pattern checkpoint schema")

        def candidate(raw: Any) -> Optional[TacticCandidate]:
            if not isinstance(raw, Mapping):
                return None
            proof = str(raw.get("proof") or "")
            tactic = str(raw.get("tactic") or "")
            source = str(raw.get("source") or "")
            if not proof or not tactic or not source:
                return None
            helper = raw.get("helper")
            return TacticCandidate(
                proof=proof,
                tactic=tactic,
                source=source,
                helper=(str(helper) if helper is not None else None),
            )

        self.max_entries = max(1, int(record.get("max_entries", 4096) or 4096))
        self._successes = {
            str(key): item
            for key, raw in dict(record.get("successes") or {}).items()
            for item in [candidate(raw)]
            if item is not None
        }
        self._failures = {
            str(key): {str(item) for item in list(values or [])}
            for key, values in dict(record.get("failures") or {}).items()
        }
        self._shape_successes = {
            str(key): [item for raw in list(values or []) if (item := candidate(raw))]
            for key, values in dict(record.get("shape_successes") or {}).items()
        }
        self._shape_failures = {
            str(key): {str(item) for item in list(values or [])}
            for key, values in dict(record.get("shape_failures") or {}).items()
        }
        self._last_access = {
            str(key): int(value or 0)
            for key, value in dict(record.get("last_access") or {}).items()
        }
        self._access_seq = max(0, int(record.get("access_seq", 0) or 0))
        self._trim()

    @staticmethod
    def _context_value(context: Optional[Mapping[str, Any]], key: str) -> str:
        if not isinstance(context, Mapping):
            return ""
        return str(context.get(key) or "").strip()

    @staticmethod
    def key_for(
        goal_statement: str,
        preamble: str,
        helpers: Sequence[Any],
        *,
        pattern_context: Optional[Mapping[str, Any]] = None,
        suppress_solution_placeholders: bool = True,
        opaque_mode: bool = True,
        allow_official_answer_visibility: bool = False,
    ) -> str:
        helper_parts: list[str] = []
        for helper in helpers or ():
            name = _extract_helper_name(
                helper,
                suppress_solution_placeholders=suppress_solution_placeholders,
                opaque_mode=opaque_mode,
                allow_official_answer_visibility=allow_official_answer_visibility,
            ) or ""
            source_text = _helper_source_text(helper)
            source_hash = text_hash(source_text) if source_text else ""
            if isinstance(helper, Mapping):
                source_hash = source_hash or str(
                    helper.get("source_hash")
                    or helper.get("statement_hash")
                    or helper.get("proof_hash")
                    or ""
                )
            helper_parts.append(f"{name}:{source_hash}")
        normalized_goal = _normalize_statement_for_tactic_cache(goal_statement)
        scope = TacticPatternCache._context_value(pattern_context, "scope")
        mode = TacticPatternCache._context_value(pattern_context, "mode")
        context_fingerprint = "|".join(
            f"{key}={TacticPatternCache._context_value(pattern_context, key)}"
            for key in (
                "node_kind",
                "local_context_hash",
                "parent_stub_hash",
                "root_tactic_context_key",
                "tactic_timeout_s",
                "max_candidates",
                "active_root_target",
                "active_root_target_statement",
                "active_root_fallback",
            )
        )
        return ":".join(
            [
                scope,
                mode,
                text_hash(context_fingerprint),
                text_hash(normalized_goal),
                text_hash(preamble),
                text_hash("\n".join(helper_parts)),
            ]
        )

    @staticmethod
    def shape_key_for(
        goal_statement: str,
        preamble: str,
        *,
        pattern_context: Optional[Mapping[str, Any]] = None,
    ) -> str:
        scope = TacticPatternCache._context_value(pattern_context, "scope")
        mode = TacticPatternCache._context_value(pattern_context, "mode")
        shape_key = TacticPatternCache._context_value(pattern_context, "shape_key")
        if not shape_key:
            shape_key = _normalize_statement_for_tactic_cache(goal_statement)
        else:
            shape_key = _normalize_statement_for_tactic_cache(shape_key)
        shape_context = TacticPatternCache._context_value(
            pattern_context,
            "shape_context",
        )
        active_context = "|".join(
            f"{key}={TacticPatternCache._context_value(pattern_context, key)}"
            for key in (
                "active_root_target",
                "active_root_target_statement",
                "active_root_fallback",
            )
        )
        if active_context:
            shape_context = "|".join(part for part in (shape_context, active_context) if part)
        return ":".join(
            [scope, mode, text_hash(shape_key), text_hash(shape_context), text_hash(preamble)]
        )

    @staticmethod
    def candidate_from_attempt(attempt: Mapping[str, Any]) -> Optional[TacticCandidate]:
        if not isinstance(attempt, Mapping):
            return None
        proof = str(attempt.get("proof") or "").strip()
        tactic = str(attempt.get("tactic") or "").strip()
        source = str(attempt.get("source") or "").strip()
        if not proof or not tactic or not source:
            return None
        helper = str(attempt.get("helper") or "").strip() or None
        return TacticCandidate(proof=proof, tactic=tactic, source=source, helper=helper)

    @staticmethod
    def _access_key(kind: str, key: str) -> str:
        return f"{kind}:{key}"

    def _touch(self, key: str, *, kind: str = "exact") -> None:
        self._access_seq += 1
        self._last_access[self._access_key(kind, key)] = self._access_seq
        self._trim()

    def _trim(self) -> None:
        entries = [
            ("exact", key)
            for key in (set(self._successes) | set(self._failures))
        ] + [
            ("shape", key)
            for key in (set(self._shape_successes) | set(self._shape_failures))
        ]
        overflow = len(entries) - self.max_entries
        if overflow <= 0:
            return
        ordered = sorted(
            entries,
            key=lambda item: self._last_access.get(self._access_key(*item), 0),
        )
        for kind, key in ordered[:overflow]:
            if kind == "shape":
                self._shape_successes.pop(key, None)
                self._shape_failures.pop(key, None)
            else:
                self._successes.pop(key, None)
                self._failures.pop(key, None)
            self._last_access.pop(self._access_key(kind, key), None)

    def preferred_candidate(self, key: str) -> Optional[TacticCandidate]:
        candidate = self._successes.get(key)
        if candidate is not None:
            self._touch(key)
        return candidate

    def preferred_shape_candidates(self, key: str) -> list[TacticCandidate]:
        candidates = list(self._shape_successes.get(key, ()))
        if candidates:
            self._touch(key, kind="shape")
        return candidates

    def failed_proofs(self, key: str) -> set[str]:
        failures = set(self._failures.get(key, set()))
        if failures:
            self._touch(key)
        return failures

    def failed_shape_proofs(self, key: str) -> set[str]:
        del key
        return set()

    @classmethod
    def _shape_replay_safe(cls, candidate: TacticCandidate) -> bool:
        source = str(candidate.source or "").strip()
        if source not in cls._SHAPE_REPLAY_SAFE_SOURCES:
            return False
        if candidate.helper:
            return False
        proof = str(candidate.proof or "")
        if re.search(r"(?<![\w'.])[A-Za-z_][A-Za-z0-9_']*\?(?![\w'])", proof):
            return False
        return bool(proof.strip())

    @classmethod
    def _shape_failure_safe(cls, candidate: TacticCandidate) -> bool:
        """Whether failure cannot be changed by adding unrelated helpers."""

        if candidate.helper or not cls._shape_replay_safe(candidate):
            return False
        proof = " ".join(str(candidate.proof or "").split())
        return bool(
            re.match(
                r"^by\s+(?:omega|linarith|nlinarith|ring|ring_nf|norm_num|"
                r"native_decide|decide|tauto)(?:\s|$)",
                proof,
            )
        )

    @staticmethod
    def _failure_cacheable(
        *,
        error_type: str = "",
        partial_stub_validated: bool = False,
        candidate_timeout_fully_funded: bool = True,
    ) -> bool:
        if bool(partial_stub_validated):
            return False
        if str(error_type or "") == "timeout" and not bool(
            candidate_timeout_fully_funded
        ):
            return False
        return str(error_type or "") not in _NON_CACHEABLE_TACTIC_ERROR_TYPES

    def _record_success(
        self,
        key: str,
        candidate: TacticCandidate,
        *,
        pattern_context: Optional[Mapping[str, Any]] = None,
        goal_statement: str = "",
        preamble: str = "",
    ) -> dict[str, int]:
        self._successes[key] = candidate
        self._failures.get(key, set()).discard(candidate.proof)
        self._touch(key)
        out = {"successes_recorded": 1, "shape_successes_recorded": 0}
        shape_key = self.shape_key_for(
            goal_statement,
            preamble,
            pattern_context=pattern_context,
        )
        if shape_key and self._shape_replay_safe(candidate):
            existing = [
                item
                for item in self._shape_successes.get(shape_key, [])
                if item.proof != candidate.proof
            ]
            self._shape_successes[shape_key] = [candidate, *existing][:8]
            self._shape_failures.get(shape_key, set()).discard(candidate.proof)
            self._touch(shape_key, kind="shape")
            out["shape_successes_recorded"] = 1
        return out

    def record_attempt(
        self,
        key: str,
        candidate: TacticCandidate,
        *,
        ok: bool,
        error_type: str = "",
        partial_stub_validated: bool = False,
        candidate_timeout_fully_funded: bool = True,
        defer_success: bool = False,
        pattern_context: Optional[Mapping[str, Any]] = None,
        goal_statement: str = "",
        preamble: str = "",
    ) -> dict[str, int]:
        clean_key = str(key or "").strip()
        if not clean_key:
            return {}
        if ok:
            if defer_success:
                return {"successes_deferred": 1}
            return self._record_success(
                clean_key,
                candidate,
                pattern_context=pattern_context,
                goal_statement=goal_statement,
                preamble=preamble,
            )
        if not self._failure_cacheable(
            error_type=error_type,
            partial_stub_validated=partial_stub_validated,
            candidate_timeout_fully_funded=candidate_timeout_fully_funded,
        ):
            return {"failures_not_cached": 1}
        self._failures.setdefault(clean_key, set()).add(candidate.proof)
        self._touch(clean_key)
        out = {"failures_recorded": 1}
        # A failure is authoritative only for the exact goal, local context,
        # helper inventory, and tactic budget in ``clean_key``. Shape-level
        # successes remain useful because Lean rechecks them; shape failures
        # must never prune a semantically different obligation.
        return out

    def confirm_success(
        self,
        *,
        goal_statement: str,
        preamble: str,
        helpers: Sequence[Any],
        candidate: TacticCandidate,
        pattern_context: Optional[Mapping[str, Any]] = None,
        suppress_solution_placeholders: bool = True,
        opaque_mode: bool = True,
        allow_official_answer_visibility: bool = False,
    ) -> dict[str, int]:
        key = self.key_for(
            goal_statement,
            preamble,
            helpers,
            pattern_context=pattern_context,
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
        )
        return self._record_success(
            key,
            candidate,
            pattern_context=pattern_context,
            goal_statement=goal_statement,
            preamble=preamble,
        )

    def record_acceptance_veto(
        self,
        *,
        goal_statement: str,
        preamble: str,
        helpers: Sequence[Any],
        candidate: TacticCandidate,
        pattern_context: Optional[Mapping[str, Any]] = None,
        suppress_solution_placeholders: bool = True,
        opaque_mode: bool = True,
        allow_official_answer_visibility: bool = False,
    ) -> dict[str, int]:
        key = self.key_for(
            goal_statement,
            preamble,
            helpers,
            pattern_context=pattern_context,
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
        )
        existing = self._successes.get(key)
        if existing is not None and existing.proof == candidate.proof:
            self._successes.pop(key, None)
        failures = self._failures.get(key)
        if failures is not None:
            failures.discard(candidate.proof)
            if not failures:
                self._failures.pop(key, None)
        if key in self._successes or key in self._failures:
            self._touch(key)
        else:
            self._last_access.pop(self._access_key("exact", key), None)
        return {"acceptance_vetoes": 1}


class TacticCloserBackend(Protocol):
    """Swappable backend interface for deterministic loops or tactic_tree."""

    async def close(
        self,
        lean: Any,
        goal_statement: str,
        preamble: str,
        helpers: Sequence[Any],
        *,
        candidate_helpers: Optional[Sequence[Any]] = None,
        timeout_s: float,
        max_candidates: int,
        pattern_context: Optional[Mapping[str, Any]] = None,
        defer_success_cache: bool = False,
        candidate_portfolio: Optional[Sequence[TacticCandidate]] = None,
        candidate_portfolio_offset: int = 0,
        candidate_attempt_limit: int = 0,
        suppressed_proofs: Optional[Sequence[str]] = None,
        source_prefixes: Optional[Sequence[str]] = None,
        excluded_source_prefixes: Optional[Sequence[str]] = None,
        opaque_mode: bool = True,
        allow_official_answer_visibility: bool = False,
        official_answer_payload_present: Optional[bool] = None,
        attempt_observer: Optional[LeanAttemptObserver] = None,
    ) -> TacticCloseResult:
        ...


def _proof_from_tactic(tactic: str) -> str:
    return f"by\n  {tactic.strip()}"


def _proof_from_lines(lines: Sequence[str]) -> str:
    body = "\n".join(f"  {line.rstrip()}" for line in lines if line.strip())
    return f"by\n{body}"


def _helper_source_text(helper: Any) -> str:
    """Return a helper declaration body if the helper object carries one."""

    raw: Any = ""
    if isinstance(helper, Mapping):
        for key in ("source", "declaration", "code"):
            value = helper.get(key)
            if value:
                raw = value
                break
    else:
        raw = getattr(helper, "source", None) or ""
    text = str(raw or "").strip()
    if text:
        return text
    if isinstance(helper, str) and _DECL_NAME_RE.search(helper):
        return helper.strip()
    return ""


def _solution_refs_allowed(
    *,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> bool:
    return not effective_solution_placeholder_suppression(
        suppress_solution_placeholders=suppress_solution_placeholders,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )


def _answer_safety_kwargs(
    *,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> dict[str, Any]:
    return {
        "suppress_solution_placeholders": bool(suppress_solution_placeholders),
        "opaque_mode": bool(opaque_mode),
        "allow_official_answer_visibility": bool(allow_official_answer_visibility),
        "official_answer_payload_present": official_answer_payload_present,
    }


def _extract_helper_name(
    helper: Any,
    *,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> Optional[str]:
    """Return a Lean declaration name from a helper-ish object if safe."""

    source_text = _helper_source_text(helper)
    answer_safety_kwargs = _answer_safety_kwargs(
        suppress_solution_placeholders=suppress_solution_placeholders,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )
    if source_text and is_answer_unsafe_helper_source(
        source_text,
        **answer_safety_kwargs,
    ):
        return None
    allow_solution_refs = _solution_refs_allowed(**answer_safety_kwargs)

    raw: Any = helper
    if isinstance(helper, Mapping):
        for key in ("name", "decl_name", "declaration", "helper", "id"):
            value = helper.get(key)
            if value:
                raw = value
                break
    else:
        for attr in ("name", "decl_name", "declaration", "helper", "id"):
            value = getattr(helper, attr, None)
            if value:
                raw = value
                break

    text = str(raw or "").strip()
    if not text:
        return None
    if _LEAN_NAME_RE.fullmatch(text):
        if "_solution" in text and not allow_solution_refs:
            return None
        return text
    declared_name = helper_decl_name(text)
    if declared_name and _LEAN_NAME_RE.fullmatch(declared_name):
        if "_solution" in declared_name and not allow_solution_refs:
            return None
        return declared_name
    match = _DECL_NAME_RE.search(text)
    if match and _LEAN_NAME_RE.fullmatch(match.group(1)):
        name = match.group(1)
        if "_solution" in name and not allow_solution_refs:
            return None
        return name
    return None


def _dedupe_helpers(
    helpers: Sequence[Any],
    *,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> list[str]:
    seen: set[str] = set()
    names: list[str] = []
    for helper in helpers or ():
        name = _extract_helper_name(
            helper,
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
        if not name or name in seen:
            continue
        seen.add(name)
        names.append(name)
    return names


def _recent_first_helpers(names: Sequence[str]) -> list[str]:
    """Prefer newly-added helpers without dropping stable older names."""

    ordered: list[str] = []
    seen: set[str] = set()
    for name in list(names or ())[::-1]:
        if name and name not in seen:
            seen.add(name)
            ordered.append(name)
    for name in names or ():
        if name and name not in seen:
            seen.add(name)
            ordered.append(name)
    return ordered


def _helper_statements_by_name(helpers: Sequence[Any]) -> dict[str, str]:
    statements: dict[str, str] = {}
    for helper in helpers or ():
        text = _helper_source_text(helper)
        if not text:
            continue
        name = helper_decl_name(text)
        if not name or name in statements:
            continue
        statements[name] = str(helper_decl_statement(text) or "").strip()
    return statements


def _aesop_safe_rule_list(names: Sequence[str]) -> str:
    return "[" + ", ".join(
        str(name or "").strip()
        for name in names
        if str(name or "").strip()
    ) + "]"


def _find_matching_delimiter(text: str, start: int) -> int:
    open_to_close = {"(": ")", "{": "}", "[": "]"}
    opener = text[start : start + 1]
    closer = open_to_close.get(opener)
    if not closer:
        return -1
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == opener:
            depth += 1
        elif char == closer:
            depth -= 1
            if depth == 0:
                return index
    return -1


def _binder_names_from_chunk(chunk: str) -> list[str]:
    left = str(chunk or "").split(":", 1)[0]
    names: list[str] = []
    for raw in re.split(r"[\s,]+", left.strip()):
        name = raw.strip()
        if not name or name == "_" or not _LEAN_NAME_RE.match(name):
            continue
        names.append(name)
    return names


def _consume_leading_forall_binder(text: str) -> tuple[list[str], str] | None:
    raw = str(text or "").lstrip()
    if raw.startswith("∀ᶠ"):
        return None
    if raw.startswith("∀"):
        rest = raw[1:].lstrip()
    elif raw.startswith("forall "):
        rest = raw[len("forall ") :].lstrip()
    else:
        return None
    if not rest:
        return None
    names: list[str] = []
    if rest[0] in "({[":
        close = _find_matching_delimiter(rest, 0)
        if close < 0:
            return None
        names.extend(_binder_names_from_chunk(rest[1:close]))
        after = rest[close + 1 :].lstrip()
        if after.startswith(","):
            return names, after[1:].lstrip()
        return None

    depth = 0
    comma_at = -1
    for index, char in enumerate(rest):
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth = max(0, depth - 1)
        elif char == "," and depth == 0:
            comma_at = index
            break
    if comma_at < 0:
        return None
    names.extend(_binder_names_from_chunk(rest[:comma_at]))
    return names, rest[comma_at + 1 :].lstrip()


def _find_top_level_arrow(text: str) -> tuple[int, int]:
    depth = 0
    raw = str(text or "")
    index = 0
    while index < len(raw):
        char = raw[index]
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth = max(0, depth - 1)
        elif depth == 0:
            if raw.startswith("->", index):
                return index, 2
            if char == "→":
                return index, 1
        index += 1
    return -1, 0


def _unique_intro_name(name: str, used: set[str]) -> str:
    base = name if name and _LEAN_NAME_RE.match(name) and name != "_" else "h_mini_arg"
    if base not in used:
        used.add(base)
        return base
    suffix = 1
    while f"{base}_{suffix}" in used:
        suffix += 1
    unique = f"{base}_{suffix}"
    used.add(unique)
    return unique


def _intro_names_for_statement(statement: str, *, max_names: int = 12) -> list[str]:
    remaining = str(statement or "").strip()
    names: list[str] = []
    used: set[str] = set()
    arrow_count = 0
    while remaining and len(names) < max(0, int(max_names or 0)):
        parsed = _consume_leading_forall_binder(remaining)
        if parsed is not None:
            binder_names, remaining = parsed
            for name in binder_names:
                if len(names) >= max_names:
                    break
                names.append(_unique_intro_name(name, used))
            continue
        arrow_at, arrow_len = _find_top_level_arrow(remaining)
        if arrow_at < 0:
            break
        left = remaining[:arrow_at].strip()
        if not left:
            break
        arrow_count += 1
        names.append(_unique_intro_name(f"h_mini_imp_{arrow_count}", used))
        remaining = remaining[arrow_at + arrow_len :].lstrip()
    return names


def _helper_application_arities(
    helper_statement: str,
    *,
    available_intro_count: int,
) -> list[int]:
    limit = max(0, min(int(available_intro_count or 0), 6))
    if limit <= 0:
        return []
    preferred = len(_intro_names_for_statement(helper_statement, max_names=limit))
    ordered: list[int] = []
    for arity in (
        preferred,
        min(limit, preferred + 1) if preferred else 0,
        max(1, preferred - 1) if preferred else 0,
        2,
        1,
        3,
        4,
    ):
        if 0 < arity <= limit and arity not in ordered:
            ordered.append(arity)
    return ordered


def _leading_explicit_forall_binder_types(statement: str) -> list[str]:
    """Cheap type-direction guard for generated positional applications.

    This intentionally recognizes only explicit typed forall groups. Unknown
    syntax yields no authority to pair a helper with arbitrary root intros;
    Lean's broader search tactics remain available without spending one probe
    per incompatible arity.
    """

    text = str(statement or "").strip()
    if text.startswith("∀"):
        text = text[1:].lstrip()
    elif text.startswith("forall"):
        text = text[len("forall") :].lstrip()
    else:
        return []
    types: list[str] = []
    while text.startswith(("(", "{")):
        opener = text[0]
        closer = ")" if opener == "(" else "}"
        depth = 0
        close_at = -1
        for index, char in enumerate(text):
            if char == opener:
                depth += 1
            elif char == closer:
                depth -= 1
                if depth == 0:
                    close_at = index
                    break
        if close_at < 0:
            return []
        chunk = text[1:close_at]
        if ":" not in chunk:
            return []
        names, binder_type = chunk.split(":", 1)
        count = max(1, len([name for name in names.split() if name]))
        normalized_type = normalize_statement(binder_type)
        types.extend(normalized_type for _ in range(count))
        text = text[close_at + 1 :].lstrip()
    return types


def _helper_lemma_blocks(
    helpers: Sequence[Any],
    *,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> list[str]:
    """Return verified helper declarations to put in Lean's lemma context."""

    seen: set[str] = set()
    blocks: list[str] = []
    answer_safety_kwargs = _answer_safety_kwargs(
        suppress_solution_placeholders=suppress_solution_placeholders,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )
    for helper in helpers or ():
        text = _helper_source_text(helper)
        if not text:
            continue
        if is_answer_unsafe_helper_source(text, **answer_safety_kwargs):
            continue
        name = helper_decl_name(text)
        if not name or name in seen:
            continue
        seen.add(name)
        blocks.append(text)
    return blocks


def generate_tactic_candidates(
    goal_statement: str,
    helpers: Sequence[Any],
    *,
    max_candidates: int = DEFAULT_MAX_CANDIDATES,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> list[TacticCandidate]:
    """Build deterministic root-closing candidates.

    ``goal_statement`` is accepted for future tactic_tree-compatible backends;
    this deterministic backend intentionally does not inspect hidden context or
    perform oracle-style probing.
    """

    helper_names = _recent_first_helpers(
        _dedupe_helpers(
            helpers,
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
    )
    helper_statements = _helper_statements_by_name(helpers)
    candidates: list[TacticCandidate] = []
    seen_proofs: set[str] = set()
    goal_text = str(goal_statement or "")
    needs_intro_candidate = goal_text.lstrip().startswith(
        ("∀", "forall")
    ) or "→" in goal_text or "->" in goal_text
    dangerous_nat_pow_goal = looks_like_dangerous_nat_pow_tower(goal_text)
    cast_profile = detect_cast_normalization_profile(goal_text)
    finset_reindexing_profile = detect_finset_reindexing_profile(goal_text)

    def skip_for_goal(text: str) -> bool:
        return dangerous_nat_pow_goal and uses_expensive_normalizer(text)

    def add(tactic: str, *, source: str, helper: Optional[str] = None) -> None:
        if skip_for_goal(tactic):
            return
        proof = _proof_from_tactic(tactic)
        if proof in seen_proofs:
            return
        seen_proofs.add(proof)
        candidates.append(
            TacticCandidate(proof=proof, tactic=tactic, source=source, helper=helper)
        )

    def add_lines(
        lines: Sequence[str],
        *,
        tactic: str,
        source: str,
        helper: Optional[str] = None,
    ) -> None:
        if skip_for_goal(tactic) or any(skip_for_goal(line) for line in lines):
            return
        proof = _proof_from_lines(lines)
        if proof in seen_proofs:
            return
        seen_proofs.add(proof)
        candidates.append(
            TacticCandidate(proof=proof, tactic=tactic, source=source, helper=helper)
        )

    intro_tactics = (
        "omega",
        "norm_num at *; omega",
        "zify at *; omega",
        "simp_all",
        "norm_num at *",
        "norm_cast at *",
        "push_cast at *",
        "linarith",
        "nlinarith",
        "ring_nf",
        "simp_all; omega",
        "simp_all; ring_nf",
    )

    def add_intro_coercion_candidates() -> None:
        for tactic in intro_tactics:
            add_lines(
                ("intros", tactic),
                tactic=f"intros; {tactic}",
                source="intro_coercion",
            )

    def add_first_intro_candidate() -> None:
        add_lines(
            ("intros", "omega"),
            tactic="intros; omega",
            source="intro_coercion",
        )

    def add_cast_normalization_candidates() -> None:
        for script in cast_normalization_scripts(
            cast_profile,
            needs_intro=needs_intro_candidate,
        ):
            add_lines(
                script.lines,
                tactic=script.tactic,
                source=script.source,
            )

    def add_finset_reindexing_candidates() -> None:
        for script in finset_reindexing_scripts(
            finset_reindexing_profile,
            needs_intro=needs_intro_candidate,
        ):
            add_lines(
                script.lines,
                tactic=script.tactic,
                source=script.source,
            )

    def goal_prefers_standalone_first() -> bool:
        compact = " ".join(goal_text.split()).strip()
        if not compact or needs_intro_candidate or not helper_names:
            return False
        if compact == "True":
            return False
        structural_markers = ("∧", "∨", "∃", "↔")
        return not any(marker in compact for marker in structural_markers)

    def add_helper_conjunction_projection_stitch_candidates() -> None:
        if "∧" not in goal_text or not helper_names:
            return
        stitch_helpers = helper_names[:HELPER_STITCH_LIMIT]
        projection_candidate_count = 0
        for helper in stitch_helpers:
            helper_statement = str(helper_statements.get(helper, "") or "")
            if helper_statement.lstrip().startswith(("∀", "forall")):
                continue
            paths = _conjunction_projection_paths(helper_statement)
            if len(paths) < 2:
                continue
            local_conj = f"h_mini_conj_{projection_candidate_count}"
            projection_lines = [f"have {local_conj} := {helper}"]
            projection_names: list[str] = []
            for index, path in enumerate(paths):
                local = f"h_mini_conj_{projection_candidate_count}_{index}"
                projection_lines.append(f"have {local} := {local_conj}{path}")
                projection_names.append(local)
            other_helpers = [candidate for candidate in stitch_helpers if candidate != helper]
            fact_list = ", ".join([*projection_names, *other_helpers])
            add_lines(
                (
                    "classical",
                    *projection_lines,
                    "constructor",
                    f"· solve_by_elim [{fact_list}]",
                    f"· solve_by_elim [{fact_list}]",
                ),
                tactic=(
                    "classical; "
                    + "; ".join(projection_lines)
                    + f"; constructor <;> solve_by_elim [{fact_list}]"
                ),
                source="helper_stitch_conjunction_projection",
                helper=helper,
            )
            projection_candidate_count += 1
            if projection_candidate_count >= MAX_CONJUNCTION_PROJECTION_HELPERS:
                return

    def add_helper_set_ext_stitch_candidates() -> None:
        if len(helper_names) < 2:
            return
        compact_goal = " ".join(goal_text.split())
        if "=" not in compact_goal:
            return
        if not any(marker in compact_goal for marker in ("Set", "{", "∈")):
            return
        stitch_helpers = helper_names[:HELPER_SET_EXT_LIMIT]
        helper_list = ", ".join(stitch_helpers)
        helper_aesop_list = _aesop_safe_rule_list(stitch_helpers[:8])
        add_lines(
            (
                "classical",
                "ext x",
                "constructor",
                "· intro hx",
                f"  solve_by_elim [{helper_list}]",
                "· intro hx",
                f"  solve_by_elim [{helper_list}]",
            ),
            tactic=(
                "classical; ext x; constructor <;> intro hx "
                f"<;> solve_by_elim [{helper_list}]"
            ),
            source="helper_set_ext_stitch",
        )
        add_lines(
            (
                "classical",
                "ext x",
                "constructor",
                "· intro hx",
                f"  aesop (add safe {helper_aesop_list})",
                "· intro hx",
                f"  aesop (add safe {helper_aesop_list})",
            ),
            tactic=(
                "classical; ext x; constructor <;> intro hx "
                f"<;> aesop (add safe {helper_aesop_list})"
            ),
            source="helper_set_ext_stitch",
        )

    def add_helper_stitch_candidates() -> None:
        if len(helper_names) < 2:
            return
        stitch_helpers = helper_names[:HELPER_STITCH_LIMIT]
        helper_list = ", ".join(stitch_helpers)
        helper_aesop_list = _aesop_safe_rule_list(stitch_helpers[:8])
        add_lines(
            ("classical", f"solve_by_elim [{helper_list}]"),
            tactic=f"classical; solve_by_elim [{helper_list}]",
            source="helper_stitch_solve_by_elim",
        )
        add_lines(
            ("intros", f"solve_by_elim [{helper_list}]"),
            tactic=f"intros; solve_by_elim [{helper_list}]",
            source="helper_stitch_solve_by_elim",
        )
        add_lines(
            ("classical", f"aesop (add safe {helper_aesop_list})"),
            tactic=f"classical; aesop (add safe {helper_aesop_list})",
            source="helper_stitch_aesop",
        )
        add_lines(
            ("classical", f"constructor <;> solve_by_elim [{helper_list}]"),
            tactic=f"classical; constructor <;> solve_by_elim [{helper_list}]",
            source="helper_stitch_constructor",
        )
        add_lines(
            ("intros", f"constructor <;> solve_by_elim [{helper_list}]"),
            tactic=f"intros; constructor <;> solve_by_elim [{helper_list}]",
            source="helper_stitch_constructor",
        )

    def add_helper_structural_candidates() -> None:
        structural_helpers = helper_names[:HELPER_STRUCTURAL_LIMIT]
        if not structural_helpers:
            return
        pair_candidate_count = 0
        for i, left_helper in enumerate(structural_helpers):
            for j, right_helper in enumerate(structural_helpers):
                if i == j:
                    continue
                helper_pair = f"{left_helper},{right_helper}"
                add(
                    f"exact ⟨{left_helper}, {right_helper}⟩",
                    source="helper_structural_pair",
                    helper=helper_pair,
                )
                pair_candidate_count += 1
                if pair_candidate_count >= MAX_STRUCTURAL_PAIR_CANDIDATES:
                    break
                add_lines(
                    ("constructor", f"exact {left_helper}", f"exact {right_helper}"),
                    tactic=f"constructor; exact {left_helper}; exact {right_helper}",
                    source="helper_structural_pair",
                    helper=helper_pair,
                )
                pair_candidate_count += 1
                if pair_candidate_count >= MAX_STRUCTURAL_PAIR_CANDIDATES:
                    break
            if pair_candidate_count >= MAX_STRUCTURAL_PAIR_CANDIDATES:
                break

        for helper in structural_helpers:
            add(f"exact Or.inl {helper}", source="helper_structural_or", helper=helper)
            add(f"exact Or.inr {helper}", source="helper_structural_or", helper=helper)
            add_lines(
                ("left", f"exact {helper}"),
                tactic=f"left; exact {helper}",
                source="helper_structural_or",
                helper=helper,
            )
            add_lines(
                ("right", f"exact {helper}"),
                tactic=f"right; exact {helper}",
                source="helper_structural_or",
                helper=helper,
            )

        triple_count = 0
        for i in range(len(structural_helpers)):
            for j in range(i + 1, len(structural_helpers)):
                for k in range(j + 1, len(structural_helpers)):
                    h1 = structural_helpers[i]
                    h2 = structural_helpers[j]
                    h3 = structural_helpers[k]
                    add(
                        f"exact ⟨{h1}, {h2}, {h3}⟩",
                        source="helper_structural_triple",
                        helper=f"{h1},{h2},{h3}",
                    )
                    triple_count += 1
                    if triple_count >= MAX_STRUCTURAL_TRIPLE_CANDIDATES:
                        return

    def add_helper_local_context_candidates() -> None:
        local_helpers = helper_names[:HELPER_STITCH_LIMIT]
        if len(local_helpers) < 2:
            return
        have_lines = [
            f"have h_mini_{i} := {helper}"
            for i, helper in enumerate(local_helpers)
        ]
        local_names = [f"h_mini_{i}" for i in range(len(local_helpers))]
        local_list = ", ".join(local_names)
        local_aesop_list = _aesop_safe_rule_list(local_names[:8])
        prefix_tactic = "; ".join(have_lines)
        for tactic in (
            f"solve_by_elim [{local_list}]",
            f"aesop (add safe {local_aesop_list})",
            "simp_all",
            "omega",
            "linarith",
            "nlinarith",
        ):
            add_lines(
                (*have_lines, tactic),
                tactic=f"{prefix_tactic}; {tactic}",
                source="helper_local_context",
            )

    def add_helper_intro_application_candidates() -> None:
        if not needs_intro_candidate:
            return
        intro_names = _intro_names_for_statement(goal_text, max_names=12)
        if not intro_names:
            return
        intro_line = "intro " + " ".join(intro_names)
        goal_binder_types = _leading_explicit_forall_binder_types(goal_text)
        early_helpers = helper_names[: min(4, len(helper_names))]
        for helper in early_helpers:
            helper_binder_types = _leading_explicit_forall_binder_types(
                helper_statements.get(helper, "")
            )
            if (
                not goal_binder_types
                or not helper_binder_types
                or goal_binder_types[0] != helper_binder_types[0]
            ):
                continue
            arities = _helper_application_arities(
                helper_statements.get(helper, ""),
                available_intro_count=len(intro_names),
            )
            if not arities:
                continue
            arity = arities[0]
            args = " ".join(intro_names[:arity])
            add_lines(
                (intro_line, f"simpa using ({helper} {args})"),
                tactic=f"{intro_line}; simpa using ({helper} {args})",
                source="helper_intro_simpa",
                helper=helper,
            )
            add_lines(
                (intro_line, f"exact {helper} {args}"),
                tactic=f"{intro_line}; exact {helper} {args}",
                source="helper_intro_exact",
                helper=helper,
            )
        for helper in early_helpers[:2]:
            helper_binder_types = _leading_explicit_forall_binder_types(
                helper_statements.get(helper, "")
            )
            if (
                not goal_binder_types
                or not helper_binder_types
                or goal_binder_types[0] != helper_binder_types[0]
            ):
                continue
            arities = _helper_application_arities(
                helper_statements.get(helper, ""),
                available_intro_count=len(intro_names),
            )
            for arity in arities[1:4]:
                args = " ".join(intro_names[:arity])
                add_lines(
                    (intro_line, f"simpa using ({helper} {args})"),
                    tactic=f"{intro_line}; simpa using ({helper} {args})",
                    source="helper_intro_simpa",
                    helper=helper,
                )

    def add_direct_helper_preflight_candidates() -> None:
        """Try cheap direct helper closes before broad tactic portfolios."""

        def statement_identity_key(text: str) -> str:
            try:
                from .proof_state import canonicalize_lean_statement_for_identity

                return canonicalize_lean_statement_for_identity(text)
            except Exception:
                return normalize_statement(text)

        compact_goal = " ".join(goal_text.split()).strip()
        if not helper_names or not compact_goal or compact_goal == "True":
            return
        goal_key = statement_identity_key(goal_text)
        if not goal_key:
            return
        matching_helpers = [
            helper
            for helper in helper_names
            if statement_identity_key(helper_statements.get(helper, "")) == goal_key
        ]
        for helper in matching_helpers[:HELPER_DIRECT_EXACT_LIMIT]:
            add(f"exact {helper}", source="helper_exact", helper=helper)
            add(f"exact ({helper})", source="helper_exact", helper=helper)
        for helper in matching_helpers[:2]:
            add(f"simpa using {helper}", source="helper_simpa", helper=helper)

    add_direct_helper_preflight_candidates()

    if cast_profile.should_attempt:
        add_cast_normalization_candidates()
    if finset_reindexing_profile.should_attempt and not helper_names:
        add_finset_reindexing_candidates()

    if needs_intro_candidate:
        add_first_intro_candidate()
        add_helper_intro_application_candidates()
    elif goal_prefers_standalone_first():
        add("simp", source="standalone")

    for helper in helper_names[:2]:
        add(f"simpa using {helper}", source="helper_simpa", helper=helper)

    add_helper_set_ext_stitch_candidates()
    add_helper_conjunction_projection_stitch_candidates()
    add_helper_stitch_candidates()

    for helper in helper_names[:HELPER_DIRECT_EXACT_LIMIT]:
        add(f"exact {helper}", source="helper_exact", helper=helper)
        add(f"exact ({helper})", source="helper_exact", helper=helper)

    if finset_reindexing_profile.should_attempt and helper_names:
        add_finset_reindexing_candidates()

    if needs_intro_candidate:
        add_intro_coercion_candidates()

    # Required standalone tactics, in a fixed cheap-to-expensive order.
    for tactic in (
        "simp",
        "simpa",
        "norm_num",
        "omega",
        "linarith",
        "nlinarith",
        "ring_nf",
        "aesop",
        "exact?",
    ):
        add(tactic, source="standalone")

    if not needs_intro_candidate:
        add_intro_coercion_candidates()
    for helper in helper_names[2:HELPER_DIRECT_SIMPA_LIMIT]:
        add(f"simpa using {helper}", source="helper_simpa", helper=helper)
    add_helper_structural_candidates()
    add_helper_local_context_candidates()

    for helper in helper_names:
        add(f"simpa using {helper}", source="helper_simpa", helper=helper)
        add(f"exact {helper}", source="helper_exact", helper=helper)
        add(f"exact ({helper})", source="helper_exact", helper=helper)

    # Additional exact?/helper variants.  These often let Lean synthesize the
    # final use after a verified helper has been introduced into local context.
    for i, helper in enumerate(helper_names):
        local = f"h_mini_{i}"
        add_lines(
            (f"have {local} := {helper}", "exact?"),
            tactic=f"have {local} := {helper}; exact?",
            source="helper_exact_question",
            helper=helper,
        )
        add_lines(
            (f"have {local} := {helper}", f"simpa using {local}"),
            tactic=f"have {local} := {helper}; simpa using {local}",
            source="helper_local_simpa",
            helper=helper,
        )

    # A tiny structural tail is useful and deterministic, but remains secondary
    # to the required tactic set above.
    add("constructor", source="residual_split")
    for tactic in ("rfl", "trivial", "assumption", "contradiction"):
        add(tactic, source="structural")
    for tactic in ("ext <;> simp_all", "ext <;> norm_num at *"):
        add(tactic, source="structural_ext")

    cap = max(0, int(max_candidates or 0))
    return candidates[:cap] if cap else []


def generate_source_specific_tactic_candidates(
    goal_statement: str,
    helpers: Sequence[Any],
    *,
    source_prefixes: Sequence[str],
    max_candidates: int = DEFAULT_MAX_CANDIDATES,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> list[TacticCandidate]:
    """Generate candidates owned by source-specific lanes before mixed capping."""

    del helpers, suppress_solution_placeholders, opaque_mode
    del allow_official_answer_visibility
    del official_answer_payload_present
    prefixes = tuple(
        str(prefix or "").strip()
        for prefix in list(source_prefixes or ())
        if str(prefix or "").strip()
    )
    if not prefixes:
        return []
    goal_text = str(goal_statement or "")
    needs_intro_candidate = goal_text.lstrip().startswith(
        ("∀", "forall")
    ) or "→" in goal_text or "->" in goal_text
    candidates: list[TacticCandidate] = []
    seen_proofs: set[str] = set()

    def add_lines(lines: Sequence[str], *, tactic: str, source: str) -> None:
        if not any(source.startswith(prefix) for prefix in prefixes):
            return
        proof = _proof_from_lines(lines)
        if proof in seen_proofs:
            return
        seen_proofs.add(proof)
        candidates.append(TacticCandidate(proof=proof, tactic=tactic, source=source))

    if any("finset_reindexing".startswith(prefix) for prefix in prefixes):
        profile = detect_finset_reindexing_profile(goal_text)
        for script in finset_reindexing_scripts(
            profile,
            needs_intro=needs_intro_candidate,
            max_scripts=max(DEFAULT_MAX_CANDIDATES, int(max_candidates or 0)),
        ):
            add_lines(script.lines, tactic=script.tactic, source=script.source)

    cap = max(0, int(max_candidates or 0))
    return candidates[:cap] if cap else candidates


def _merge_tactic_candidates(
    first: Sequence[TacticCandidate],
    second: Sequence[TacticCandidate],
) -> list[TacticCandidate]:
    """Merge candidate lists by proof while preserving source lane priority."""

    merged: list[TacticCandidate] = []
    seen: set[str] = set()
    for candidate in [*list(first or ()), *list(second or ())]:
        proof = str(getattr(candidate, "proof", "") or "")
        if not proof or proof in seen:
            continue
        seen.add(proof)
        merged.append(candidate)
    return merged


def _accepted_kwargs(fn: Any, proposed: Mapping[str, Any]) -> dict[str, Any]:
    try:
        sig = inspect.signature(fn)
    except (TypeError, ValueError):
        return dict(proposed)
    params = sig.parameters
    if any(p.kind == inspect.Parameter.VAR_KEYWORD for p in params.values()):
        return dict(proposed)
    return {key: value for key, value in proposed.items() if key in params}


def _candidate_intended_timeout_s(
    *,
    total_timeout_s: float,
    candidate_count: int,
) -> float:
    """Return one candidate's full slice before tail-budget truncation."""

    total = max(0.1, float(total_timeout_s))
    divisor = max(1, min(int(candidate_count or 1), 4))
    budget = total / divisor
    if total >= 5.0:
        budget = max(5.0, budget)
    return budget


def _candidate_timeout_s(
    *,
    total_timeout_s: float,
    remaining_s: float,
    candidate_count: int,
) -> float:
    """Allocate enough time for one Lean check to get past Mathlib startup."""

    remaining = max(0.1, float(remaining_s))
    budget = _candidate_intended_timeout_s(
        total_timeout_s=total_timeout_s,
        candidate_count=candidate_count,
    )
    return min(remaining, budget)


def _candidate_timeout_was_fully_funded(
    *,
    allocated_timeout_s: float,
    intended_timeout_s: float,
) -> bool:
    """Treat small scheduling/setup losses as a full candidate slice."""

    intended = max(0.0, float(intended_timeout_s))
    allocation_slack = max(0.01, intended * 0.01)
    return float(allocated_timeout_s) + allocation_slack >= intended


async def _run_check(
    lean: Any,
    goal_statement: str,
    proof: str,
    preamble: str,
    lemmas: Sequence[str],
    *,
    timeout_s: float,
    attempt_observer: Optional[LeanAttemptObserver] = None,
    attempt_metadata: Optional[Mapping[str, Any]] = None,
) -> Any:
    check = getattr(lean, "check", None)
    if check is None:
        raise AttributeError("lean object has no async check(...) method")

    remaining = max(0.1, float(timeout_s))

    def backend_dispatch_observer() -> None:
        notify_lean_attempt_observer(
            attempt_observer,
            "dispatched",
            attempt_metadata,
        )

    proposed_kwargs = {
        "preamble_override": str(preamble or ""),
        "timeout_s": remaining,
        "fast_fail_timeout_s": min(remaining, max(1.0, remaining / 3.0)),
        "check_kind": "mini_tactic_closer",
        "dispatch_observer": backend_dispatch_observer,
    }
    kwargs = _accepted_kwargs(check, proposed_kwargs)
    # ``remaining`` is the checker's own budget (``timeout_s`` above). Arming
    # the lease and the wait_for with that same number made three timers race
    # one deadline: the guard fires as the checker is landing, discards the
    # result, and -- per the comment below -- a cancellation-resistant check
    # never reaches the handler at all, so the lease stays armed and the Lean
    # child is never reaped. Let the checker's own deadline land first.
    guard_timeout = outer_guard_timeout_s(remaining)
    lease = begin_process_deadline(
        deadline_monotonic=time.monotonic() + guard_timeout,
        label="mini_tactic_lean_check",
    )
    async def invoke_check() -> Any:
        result = check(goal_statement, proof, list(lemmas), **kwargs)
        if inspect.isawaitable(result):
            return await result
        return result

    try:
        result = await asyncio.wait_for(invoke_check(), timeout=guard_timeout)
    except asyncio.TimeoutError:
        # wait_for raises only after the awaited check has acknowledged
        # cancellation and settled.  A cancellation-resistant check never
        # reaches this branch, leaving the lease armed for the supervisor.
        lease.settle_timeout()
        raise
    except asyncio.CancelledError:
        lease.abandon("mini_tactic_lean_check_externally_cancelled")
        raise
    except BaseException:
        lease.close()
        raise
    lease.close()
    return result


def _diagnostic_from_parsed_or_output(
    *,
    parsed: Any,
    output: str,
    error_type: str,
) -> str:
    """Prefer structured Lean errors over raw output that may start with warnings."""

    error_diagnostics = [
        diagnostic
        for diagnostic in list(getattr(parsed, "diagnostics", []) or [])
        if str(getattr(diagnostic, "severity", "") or "") == "error"
    ]
    for diagnostic in error_diagnostics:
        message = str(
            getattr(diagnostic, "message", "")
            or getattr(diagnostic, "summary", "")
            or ""
        ).strip()
        if not message:
            continue
        preview = diagnostic_preview(message, canonical_error=error_type)
        if preview:
            return preview
    return diagnostic_preview(output, canonical_error=error_type)


def _attempt_from_result(
    *,
    index: int,
    candidate: TacticCandidate,
    result: Any,
    elapsed_s: float,
) -> TacticAttempt:
    parsed = getattr(result, "parsed", None)
    output = str(getattr(result, "output", "") or "")
    error_type = (
        "infra_failure"
        if bool(getattr(parsed, "infra_failure", False))
        else canonical_error_type(parsed)
    )
    diagnostic = _diagnostic_from_parsed_or_output(
        parsed=parsed,
        output=output,
        error_type=error_type,
    )
    remaining_goals = (
        _remaining_goals_from_parsed(parsed)
        if error_type == "unsolved_goals"
        else []
    )
    partial_stub_validated = bool(
        remaining_goals and _partial_stub_is_residual_safe(candidate, parsed)
    )
    return TacticAttempt(
        index=index,
        ok=bool(getattr(result, "ok", False)),
        proof=candidate.proof,
        tactic=candidate.tactic,
        source=candidate.source,
        helper=candidate.helper,
        elapsed_s=round(float(elapsed_s), 3),
        returncode=getattr(result, "returncode", None),
        error_type=error_type,
        diagnostic=diagnostic,
        output_preview=output[:OUTPUT_PREVIEW_CHARS],
        remaining_goals=remaining_goals,
        partial_proof_stub=candidate.proof if partial_stub_validated else "",
        partial_stub_validated=partial_stub_validated,
    )


def _partial_stub_is_residual_safe(candidate: TacticCandidate, parsed: Any) -> bool:
    """Whether a failed tactic proof is safe to reuse as a residual prefix."""

    if int(getattr(parsed, "unsolved_goal_count", 0) or 0) <= 0:
        return False
    proof = str(candidate.proof or "").strip()
    source = str(candidate.source or "").strip()
    lower = proof.lower()
    if not proof.startswith("by"):
        return False
    if re.search(r"\b(?:sorry|admit|exact\?|set_option|guard_target)\b", lower):
        return False
    body_lines = [
        line.strip()
        for line in proof.splitlines()[1:]
        if line.strip() and not line.strip().startswith("--")
    ]
    if source.startswith("finset_reindexing"):
        if (
            len(body_lines) == 2
            and body_lines[0].startswith(("intro", "intros"))
        ):
            body_lines = [body_lines[1]]
        if len(body_lines) == 1 and re.fullmatch(
            r"apply\s+Finset\.(?:sum|prod)_congr",
            body_lines[0],
        ):
            return True
    if source == "cast_normalization_guard_probe":
        if body_lines and body_lines[0].startswith(("intro", "intros")):
            body_lines = body_lines[1:]
        cast_rewrite_steps = {
            "repeat rw [Nat.cast_choose]",
            "repeat rw [Nat.cast_sub]",
        }
        return bool(body_lines) and all(
            line in cast_rewrite_steps for line in body_lines
        )
    if len(body_lines) != 1:
        return False
    body = body_lines[0]
    if ";" in body or "<;>" in body or " all_goals " in f" {body} ":
        return False
    if body == "constructor" and source in {"residual_split", "structural"}:
        return True
    if re.fullmatch(r"apply\s+[A-Za-z_][A-Za-z0-9_'.]*(?:\s+.*)?", body):
        return source in {"residual_split", "decl_application", "apply"}
    return False


def _remaining_goals_from_parsed(parsed: Any) -> list[dict[str, Any]]:
    goals: list[dict[str, Any]] = []
    for goal in list(getattr(parsed, "remaining_goals", []) or [])[:5]:
        target = str(getattr(goal, "target", "") or "").strip()
        if not target:
            continue
        hypotheses = [
            str(item)
            for item in list(getattr(goal, "hypotheses", []) or [])[:12]
            if str(item or "").strip()
        ]
        goals.append({"target": target, "hypotheses": hypotheses})
    return goals


class DeterministicTacticBackend:
    """Small answer-safe candidate loop.

    The only Lean context used here is ``preamble`` via ``preamble_override``
    plus caller-supplied verified helper declarations.  That keeps the checker
    on the same answer-safe surface visible to the model while still allowing
    previously Lean-accepted helpers to close later goals.
    """

    def __init__(self, *, pattern_cache: Optional[TacticPatternCache] = None) -> None:
        self.pattern_cache = pattern_cache

    async def close(
        self,
        lean: Any,
        goal_statement: str,
        preamble: str,
        helpers: Sequence[Any],
        *,
        candidate_helpers: Optional[Sequence[Any]] = None,
        timeout_s: float,
        max_candidates: int,
        pattern_context: Optional[Mapping[str, Any]] = None,
        defer_success_cache: bool = False,
        candidate_portfolio: Optional[Sequence[TacticCandidate]] = None,
        candidate_portfolio_offset: int = 0,
        candidate_attempt_limit: int = 0,
        suppressed_proofs: Optional[Sequence[str]] = None,
        source_prefixes: Optional[Sequence[str]] = None,
        excluded_source_prefixes: Optional[Sequence[str]] = None,
        suppress_solution_placeholders: bool = True,
        opaque_mode: bool = True,
        allow_official_answer_visibility: bool = False,
        official_answer_payload_present: Optional[bool] = None,
        attempt_observer: Optional[LeanAttemptObserver] = None,
    ) -> TacticCloseResult:
        started = time.monotonic()
        deadline = started + max(0.0, float(timeout_s))
        prefixes = tuple(
            str(prefix or "").strip()
            for prefix in list(source_prefixes or ())
            if str(prefix or "").strip()
        )
        excluded_prefixes = tuple(
            str(prefix or "").strip()
            for prefix in list(excluded_source_prefixes or ())
            if str(prefix or "").strip()
        )
        reused_portfolio = candidate_portfolio is not None
        if reused_portfolio:
            candidates: Sequence[TacticCandidate] = tuple(candidate_portfolio or ())
        else:
            generation_cap = int(max_candidates)
            generation_helpers = (
                tuple(candidate_helpers)
                if candidate_helpers is not None
                else helpers
            )
            source_specific_candidates: list[TacticCandidate] = []
            if prefixes:
                source_specific_candidates = generate_source_specific_tactic_candidates(
                    goal_statement,
                    generation_helpers,
                    source_prefixes=prefixes,
                    max_candidates=max(
                        DEFAULT_MAX_CANDIDATES,
                        int(max_candidates or 0),
                    ),
                    suppress_solution_placeholders=suppress_solution_placeholders,
                    opaque_mode=opaque_mode,
                    allow_official_answer_visibility=allow_official_answer_visibility,
                    official_answer_payload_present=official_answer_payload_present,
                )
            if (prefixes or excluded_prefixes) and generation_cap > 0:
                generation_cap = max(generation_cap, DEFAULT_MAX_CANDIDATES)
            candidates = generate_tactic_candidates(
                goal_statement,
                generation_helpers,
                max_candidates=generation_cap,
                suppress_solution_placeholders=suppress_solution_placeholders,
                opaque_mode=opaque_mode,
                allow_official_answer_visibility=allow_official_answer_visibility,
                official_answer_payload_present=official_answer_payload_present,
            )
            if source_specific_candidates:
                candidates = _merge_tactic_candidates(
                    source_specific_candidates,
                    candidates,
                )
            if prefixes:
                candidates = [
                    candidate
                    for candidate in candidates
                    if any(
                        str(candidate.source or "").startswith(prefix)
                        for prefix in prefixes
                    )
                ]
            if excluded_prefixes:
                candidates = [
                    candidate
                    for candidate in candidates
                    if not any(
                        str(candidate.source or "").startswith(prefix)
                        for prefix in excluded_prefixes
                    )
                ]
            if max_candidates > 0:
                candidates = candidates[: int(max_candidates)]
        pattern_key = ""
        cache_metadata: dict[str, Any] = {
            "enabled": bool(self.pattern_cache is not None),
            "scope": (
                str((pattern_context or {}).get("scope") or "")
                if isinstance(pattern_context, Mapping)
                else ""
            ),
            "lookups": 0,
            "exact_success_hits": 0,
            "shape_success_hits": 0,
            "failed_filtered": 0,
            "all_candidates_pruned": 0,
            "cap_preserved_misses": 0,
            "failures_recorded": 0,
            "failures_not_cached": 0,
            "successes_recorded": 0,
            "shape_successes_recorded": 0,
            "successes_deferred": 0,
            "acceptance_vetoes": 0,
            "suppressed_filtered": 0,
        }

        def add_cache_stats(stats: Mapping[str, Any]) -> None:
            for key, value in dict(stats or {}).items():
                if key not in cache_metadata:
                    continue
                try:
                    cache_metadata[key] = int(cache_metadata.get(key, 0) or 0) + int(
                        value or 0
                    )
                except Exception:
                    pass

        if self.pattern_cache is not None and reused_portfolio:
            pattern_key = self.pattern_cache.key_for(
                goal_statement,
                preamble,
                helpers,
                pattern_context=pattern_context,
                suppress_solution_placeholders=suppress_solution_placeholders,
                opaque_mode=opaque_mode,
                allow_official_answer_visibility=allow_official_answer_visibility,
            )
        if self.pattern_cache is not None and not reused_portfolio:
            pattern_key = self.pattern_cache.key_for(
                goal_statement,
                preamble,
                helpers,
                pattern_context=pattern_context,
                suppress_solution_placeholders=suppress_solution_placeholders,
                opaque_mode=opaque_mode,
                allow_official_answer_visibility=allow_official_answer_visibility,
            )
            shape_key = self.pattern_cache.shape_key_for(
                goal_statement,
                preamble,
                pattern_context=pattern_context,
            )
            cache_metadata["lookups"] = 1
            cache_metadata["exact_key_hash"] = text_hash(pattern_key)
            cache_metadata["shape_key_hash"] = text_hash(shape_key)
            preferred = self.pattern_cache.preferred_candidate(pattern_key)
            failed_proofs = self.pattern_cache.failed_proofs(pattern_key)
            failed_proofs.update(
                self.pattern_cache.failed_shape_proofs(shape_key)
            )
            candidate_by_proof = {candidate.proof: candidate for candidate in candidates}
            promoted: list[TacticCandidate] = []
            if preferred is not None and preferred.proof in candidate_by_proof:
                promoted.append(candidate_by_proof[preferred.proof])
                cache_metadata["exact_success_hits"] = 1
            elif preferred is not None:
                cache_metadata["cap_preserved_misses"] = 1
            for shape_candidate in self.pattern_cache.preferred_shape_candidates(
                shape_key
            ):
                if shape_candidate.proof in failed_proofs:
                    continue
                if shape_candidate.proof not in candidate_by_proof:
                    cache_metadata["cap_preserved_misses"] = int(
                        cache_metadata.get("cap_preserved_misses", 0) or 0
                    ) + 1
                    continue
                if any(item.proof == shape_candidate.proof for item in promoted):
                    continue
                promoted.append(candidate_by_proof[shape_candidate.proof])
                cache_metadata["shape_success_hits"] = int(
                    cache_metadata.get("shape_success_hits", 0) or 0
                ) + 1
            filtered = [
                candidate
                for candidate in candidates
                if candidate.proof not in failed_proofs
                and not any(item.proof == candidate.proof for item in promoted)
            ]
            cache_metadata["failed_filtered"] = len(candidates) - len(
                [candidate for candidate in candidates if candidate.proof not in failed_proofs]
            )
            candidates = [*promoted, *filtered]
            if not candidates and candidate_by_proof:
                cache_metadata["all_candidates_pruned"] = 1
        suppressed = (
            {
                str(proof or "").strip()
                for proof in list(suppressed_proofs or ())
                if str(proof or "").strip()
            }
            if not reused_portfolio
            else set()
        )
        if suppressed and not reused_portfolio:
            before_suppression = len(candidates)
            candidates = [
                candidate for candidate in candidates if candidate.proof not in suppressed
            ]
            cache_metadata["suppressed_filtered"] = (
                before_suppression - len(candidates)
            )
        candidates = tuple(candidates)
        requested_candidate_start = max(
            0,
            int(candidate_portfolio_offset or 0),
        )
        candidate_start = min(len(candidates), requested_candidate_start)
        if (
            not reused_portfolio
            and requested_candidate_start > 0
            and requested_candidate_start >= len(candidates)
        ):
            # Cursor-only continuations intentionally regenerate the ranked
            # portfolio. A corrupt checkpoint or future generator change must
            # never turn an oversized cursor into a zero-check "exhausted"
            # receipt that permanently suppresses this proof context.
            candidate_start = 0
            cache_metadata["invalid_candidate_portfolio_offset_reset"] = (
                requested_candidate_start
            )
        if reused_portfolio and candidate_start:
            # A resumed portfolio advances past candidates vetoed by the
            # caller.  Preserve the historical suppression telemetry without
            # rebuilding or filtering the reusable portfolio.
            cache_metadata["suppressed_filtered"] = candidate_start
        notify_lean_attempt_observer(
            attempt_observer,
            "portfolio",
            {"candidate_count": len(candidates) - candidate_start},
        )
        lemma_blocks = _helper_lemma_blocks(
            helpers,
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
        attempts: list[TacticAttempt] = []
        attempt_limit = max(0, int(candidate_attempt_limit or 0))
        candidate_stop = (
            min(len(candidates), candidate_start + attempt_limit)
            if attempt_limit > 0
            else len(candidates)
        )

        for index in range(candidate_start, candidate_stop):
            candidate = candidates[index]
            remaining = deadline - time.monotonic()
            if remaining <= 0.0:
                return TacticCloseResult(
                    ok=False,
                    proof=None,
                    attempts=[asdict(a) for a in attempts],
                    candidate_count=len(candidates),
                    timeout_s=float(timeout_s),
                    elapsed_s=round(time.monotonic() - started, 3),
                    exit_reason="timeout",
                    cache_metadata=dict(cache_metadata),
                    candidate_portfolio=candidates,
                    next_candidate_index=index,
                )

            attempt_started = time.monotonic()
            candidate_timeout = _candidate_timeout_s(
                total_timeout_s=float(timeout_s),
                remaining_s=remaining,
                candidate_count=len(candidates),
            )
            candidate_intended_timeout = _candidate_intended_timeout_s(
                total_timeout_s=float(timeout_s),
                candidate_count=len(candidates),
            )
            candidate_timeout_fully_funded = _candidate_timeout_was_fully_funded(
                allocated_timeout_s=candidate_timeout,
                intended_timeout_s=candidate_intended_timeout,
            )
            notify_lean_attempt_observer(
                attempt_observer,
                "started",
                {
                    "index": index,
                    "proof": candidate.proof,
                    "tactic": candidate.tactic,
                    "source": candidate.source,
                    "helper": candidate.helper,
                },
            )
            try:
                result = await _run_check(
                    lean,
                    goal_statement,
                    candidate.proof,
                    preamble,
                    lemma_blocks,
                    timeout_s=candidate_timeout,
                    attempt_observer=attempt_observer,
                    attempt_metadata={
                        "index": index,
                        "proof": candidate.proof,
                        "tactic": candidate.tactic,
                        "source": candidate.source,
                        "helper": candidate.helper,
                    },
                )
                attempt = _attempt_from_result(
                    index=index,
                    candidate=candidate,
                    result=result,
                    elapsed_s=time.monotonic() - attempt_started,
                )
            except asyncio.CancelledError:
                notify_lean_attempt_observer(
                    attempt_observer,
                    "finished",
                    {
                        "index": index,
                        "ok": False,
                        "proof": candidate.proof,
                        "tactic": candidate.tactic,
                        "source": candidate.source,
                        "helper": candidate.helper,
                        "elapsed_s": round(time.monotonic() - attempt_started, 3),
                        "error_type": "cancelled",
                        "exception": "CancelledError",
                        "cancelled": True,
                    },
                )
                raise
            except asyncio.TimeoutError:
                attempt = TacticAttempt(
                    index=index,
                    ok=False,
                    proof=candidate.proof,
                    tactic=candidate.tactic,
                    source=candidate.source,
                    helper=candidate.helper,
                    elapsed_s=round(time.monotonic() - attempt_started, 3),
                    error_type="timeout",
                    diagnostic="mini tactic closer timeout",
                    exception="asyncio.TimeoutError",
                )
            except Exception as exc:
                attempt = TacticAttempt(
                    index=index,
                    ok=False,
                    proof=candidate.proof,
                    tactic=candidate.tactic,
                    source=candidate.source,
                    helper=candidate.helper,
                    elapsed_s=round(time.monotonic() - attempt_started, 3),
                    error_type="exception",
                    diagnostic=str(exc)[:OUTPUT_PREVIEW_CHARS],
                    exception=type(exc).__name__,
                )
            notify_lean_attempt_observer(
                attempt_observer,
                "finished",
                asdict(attempt),
            )
            attempts.append(attempt)
            if self.pattern_cache is not None:
                add_cache_stats(
                    self.pattern_cache.record_attempt(
                        pattern_key,
                        candidate,
                        ok=attempt.ok,
                        error_type=attempt.error_type,
                        partial_stub_validated=attempt.partial_stub_validated,
                        candidate_timeout_fully_funded=candidate_timeout_fully_funded,
                        defer_success=defer_success_cache,
                        pattern_context=pattern_context,
                        goal_statement=goal_statement,
                        preamble=preamble,
                    )
                )
            if attempt.ok:
                return TacticCloseResult(
                    ok=True,
                    proof=attempt.proof,
                    attempts=[asdict(a) for a in attempts],
                    candidate_count=len(candidates),
                    timeout_s=float(timeout_s),
                    elapsed_s=round(time.monotonic() - started, 3),
                    exit_reason="solved",
                    cache_metadata=dict(cache_metadata),
                    candidate_portfolio=candidates,
                    next_candidate_index=index + 1,
                )
            if (
                attempt.error_type == "timeout"
                and not candidate_timeout_fully_funded
            ):
                # A continuation receives a fresh deadline.  Resume at this
                # candidate: it has not yet received a meaningful verdict.
                return TacticCloseResult(
                    ok=False,
                    proof=None,
                    attempts=[asdict(a) for a in attempts],
                    candidate_count=len(candidates),
                    timeout_s=float(timeout_s),
                    elapsed_s=round(time.monotonic() - started, 3),
                    exit_reason="timeout",
                    cache_metadata=dict(cache_metadata),
                    candidate_portfolio=candidates,
                    next_candidate_index=index,
                )

        if candidate_stop < len(candidates):
            return TacticCloseResult(
                ok=False,
                proof=None,
                attempts=[asdict(a) for a in attempts],
                candidate_count=len(candidates),
                timeout_s=float(timeout_s),
                elapsed_s=round(time.monotonic() - started, 3),
                exit_reason="candidate_quantum_exhausted",
                cache_metadata=dict(cache_metadata),
                candidate_portfolio=candidates,
                next_candidate_index=candidate_stop,
            )

        return TacticCloseResult(
            ok=False,
            proof=None,
            attempts=[asdict(a) for a in attempts],
            candidate_count=len(candidates),
            timeout_s=float(timeout_s),
            elapsed_s=round(time.monotonic() - started, 3),
            exit_reason="exhausted",
            cache_metadata=dict(cache_metadata),
            candidate_portfolio=candidates,
            next_candidate_index=len(candidates),
        )


async def try_close_with_tactics(
    lean: Any,
    goal_statement: str,
    preamble: str,
    helpers: Sequence[Any],
    *,
    candidate_helpers: Optional[Sequence[Any]] = None,
    timeout_s: float = DEFAULT_TIMEOUT_S,
    max_candidates: int = DEFAULT_MAX_CANDIDATES,
    backend: Optional[TacticCloserBackend] = None,
    pattern_cache: Optional[TacticPatternCache] = None,
    pattern_context: Optional[Mapping[str, Any]] = None,
    defer_success_cache: bool = False,
    candidate_portfolio: Optional[Sequence[TacticCandidate]] = None,
    candidate_portfolio_offset: int = 0,
    candidate_attempt_limit: int = 0,
    suppressed_proofs: Optional[Sequence[str]] = None,
    source_prefixes: Optional[Sequence[str]] = None,
    excluded_source_prefixes: Optional[Sequence[str]] = None,
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
    attempt_observer: Optional[LeanAttemptObserver] = None,
) -> TacticCloseResult:
    """Try to close a Lean goal with deterministic tactic candidates.

    Args:
        lean: Object exposing ``async check(statement, proof, lemmas, ...)``.
        goal_statement: Lean proposition/type checked as ``example : ...``.
        preamble: Prompt-visible, answer-safe Lean preamble.  This is passed as
            ``preamble_override``.
        helpers: Existing verified helper names or helper-like records. Full
            verified declaration blocks are passed as Lean lemma context.
        candidate_helpers: Optional semantic-fact-deduplicated inventory used
            only for candidate generation. Lean replay still receives every
            declaration in ``helpers`` so dependent proof names remain valid.
        timeout_s: Total wall-clock budget for the candidate loop.
        max_candidates: Deterministic cap on generated candidates.
        backend: Optional swappable backend, e.g. a future tactic_tree adapter.
        pattern_cache: Optional run-local cache that prioritizes tactics that
            already worked for the same normalized goal/preamble/helper set.
        pattern_context: Optional structured scope/shape metadata for
            proof-state-native cache lookup.
        defer_success_cache: If true, successful candidates are reported as
            pending and the caller must confirm after its authoritative
            acceptance path succeeds.
        candidate_attempt_limit: Maximum settled candidates to check from the
            portfolio cursor. Zero leaves the candidate loop unlimited.
        suppressed_proofs: Per-call proof bodies to skip without writing them
            into the cache's terminal failure set.
        source_prefixes: Optional source prefixes used to restrict the generated
            portfolio for specialized lanes.
        excluded_source_prefixes: Optional source prefixes removed from the
            generated portfolio after a dedicated lane has already exhausted
            them.

    Returns:
        ``TacticCloseResult`` with ``ok``, ``proof``, and structured
        ``attempts`` records.
    """

    closer = backend or DeterministicTacticBackend(pattern_cache=pattern_cache)
    proposed_kwargs = {
        "candidate_helpers": (
            tuple(candidate_helpers) if candidate_helpers is not None else None
        ),
        "timeout_s": float(timeout_s),
        "max_candidates": int(max_candidates),
        "pattern_context": pattern_context,
        "defer_success_cache": bool(defer_success_cache),
        "candidate_portfolio": (
            tuple(candidate_portfolio)
            if candidate_portfolio is not None
            else None
        ),
        "candidate_portfolio_offset": max(
            0,
            int(candidate_portfolio_offset or 0),
        ),
        "candidate_attempt_limit": max(0, int(candidate_attempt_limit or 0)),
        "suppressed_proofs": tuple(suppressed_proofs or ()),
        "source_prefixes": tuple(source_prefixes or ()),
        "excluded_source_prefixes": tuple(excluded_source_prefixes or ()),
        "suppress_solution_placeholders": bool(suppress_solution_placeholders),
        "opaque_mode": bool(opaque_mode),
        "allow_official_answer_visibility": bool(allow_official_answer_visibility),
        "official_answer_payload_present": official_answer_payload_present,
        "attempt_observer": attempt_observer,
    }
    return await closer.close(
        lean,
        str(goal_statement or "").strip(),
        str(preamble or ""),
        list(helpers or ()),
        **_accepted_kwargs(closer.close, proposed_kwargs),
    )


__all__ = [
    "DEFAULT_MAX_CANDIDATES",
    "DEFAULT_TIMEOUT_S",
    "HELPER_STITCH_LIMIT",
    "HELPER_STRUCTURAL_LIMIT",
    "DeterministicTacticBackend",
    "TacticAttempt",
    "TacticCandidate",
    "TacticCloseResult",
    "TacticCloserBackend",
    "TacticPatternCache",
    "generate_tactic_candidates",
    "is_transient_tactic_close_failure",
    "is_transient_tactic_exception",
    "try_close_with_tactics",
]
