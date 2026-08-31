"""Goal-conditioned Lean-state search for Mini.

The deterministic tactic portfolio remains Mini's first, cheap closer.  This
module is the bounded frontier-search fallback: it asks a model for tactics
conditioned on the *current* Lean goals, replays every prefix through Lean,
uses structural plus online-learned value estimates, keeps a diverse beam,
and backtracks through checked reserve states.

Search nodes and bottleneck records are diagnostics.  Only a final full Lean
check followed by Mini's existing helper-acceptance boundary can create proof
evidence.
"""

from __future__ import annotations

import asyncio
import hashlib
import json
import logging
import re
import time
import weakref
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Any, Awaitable, Callable, Dict, List, Optional, Sequence, Tuple

from .lean_parser import LeanGoalState, extract_goal_state_features
from .deadline_guard import (
    await_with_strict_deadline,
    create_result_only_deadline_task,
    outer_guard_timeout_s,
)
from .llm_usage import (
    call_with_optional_usage_callback,
    metered_or_plain_call,
    notify_provider_dispatch_observer,
    provider_dispatch_observer,
)
from .llm_error_policy import classify_llm_exception
from .math_utils import clamp_probability
from .mini_runtime_defaults import (
    DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
    DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
)
from .mini_tactic_closer import generate_tactic_candidates
from .mini_prompt_support import tactic_gen_multi_messages
from .proof_dossier import is_answer_unsafe_statement_text
from .runtime_context import (
    hard_timeout_writeback_allowed,
    mark_runtime_owned_callback,
)
from .request_gate import formal_provider_exclusive_scope
from .search import _await_with_hard_timeout
from .search_utils import tactics_to_proof
from .tactic_tree import (
    TacticNode,
    TacticNodeStatus,
    TacticBeamState,
    TacticOperationTimeout,
    TacticPolicyBatch,
    TacticSearchResult,
    TacticTree,
    make_score_fn,
    parse_multi_tactic_response,
    tactic_tree_beam_search,
)


# Formal-state policy calls produce a handful of short Lean tactics, not a
# proof narrative.  Giving this phase the prover role's full completion and
# hidden-reasoning budget can turn one 120-second search quantum into a
# multi-minute generation which contains no executable tactic.  These are
# independent capability bounds; planning and ordinary proof authoring retain
# their configured model budgets.
_PROVIDER_LOCKS: "weakref.WeakKeyDictionary[Any, weakref.WeakKeyDictionary[Any, asyncio.Lock]]" = (
    weakref.WeakKeyDictionary()
)
_FALLBACK_PROVIDER_LOCKS: "weakref.WeakKeyDictionary[Any, asyncio.Lock]" = (
    weakref.WeakKeyDictionary()
)
_LEAN_LOCKS: "weakref.WeakKeyDictionary[Any, weakref.WeakKeyDictionary[Any, asyncio.Lock]]" = (
    weakref.WeakKeyDictionary()
)
_FALLBACK_LEAN_LOCKS: "weakref.WeakKeyDictionary[Any, asyncio.Lock]" = (
    weakref.WeakKeyDictionary()
)
_LEAN_LATE_TAILS: "weakref.WeakKeyDictionary[asyncio.Lock, Dict[str, Any]]" = (
    weakref.WeakKeyDictionary()
)
_LEAN_LATE_TAIL_QUARANTINE_GRACE_S = 300.0
_LEAN_LOCK_ADMISSION_TIMEOUT_S = 1.0
_OWNED_LEAN_LOCK: ContextVar[Optional[asyncio.Lock]] = ContextVar(
    "ensemble_prover_owned_lean_lock",
    default=None,
)
_LOGGER = logging.getLogger(__name__)


class _ProviderAdmissionDeferred(asyncio.TimeoutError):
    """The quantum ended before this request reached provider dispatch."""


# Provider calls need enough wall-clock runway to establish a connection and
# emit a useful structured tactic.  Dispatching into a one-to-three second tail
# repeatedly consumes the durable per-state attempt ledger without giving the
# provider a viable chance to answer.  Keep the floor small and never demand
# more than the phase's configured provider timeout.
_MIN_PROVIDER_DISPATCH_WINDOW_S = 5.0
_MANDATORY_REASONING_EXPLICIT_MIN_TOKENS = 48_000


def _formal_policy_provider_configs(client: Any) -> List[Any]:
    configs: List[Any] = []
    seen_configs: set[int] = set()
    seen_values: set[int] = set()

    def visit(value: Any) -> None:
        if value is None or id(value) in seen_values:
            return
        seen_values.add(id(value))
        cfg = getattr(value, "cfg", None)
        if cfg is None and hasattr(value, "model"):
            cfg = value
        if cfg is not None and id(cfg) not in seen_configs:
            seen_configs.add(id(cfg))
            configs.append(cfg)
        for nested_cfg in list(getattr(value, "configs", ()) or ()):
            visit(nested_cfg)
        for child in list(getattr(value, "clients", ()) or ()):
            visit(child)
        for member in list(getattr(value, "members", ()) or ()):
            visit(member)
            visit(getattr(member, "client", None))
            visit(getattr(member, "cfg", None))

    visit(client)
    return configs


def _formal_policy_provider_max_tokens(client: Any, configured_cap: int) -> int:
    """Return the operator-owned formal-policy cap without silent expansion."""

    return max(1, int(configured_cap or 1))


def _formal_policy_has_mandatory_unbounded_reasoning(client: Any) -> bool:
    for provider_cfg in _formal_policy_provider_configs(client):
        model = str(getattr(provider_cfg, "model", "") or "").lower()
        model = model.rsplit("/", 1)[-1]
        base_url = str(getattr(provider_cfg, "base_url", "") or "").lower()
        if model.startswith("qwen3.8-max") or (
            model.startswith("deepseek-v4-") and "openrouter" in base_url
        ):
            return True
    return False


def _provider_lock(client: Any) -> asyncio.Lock:
    """Serialize calls for one client, including cancellation-resistant tails.

    A timed-out provider coroutine may suppress cancellation and keep running
    after its search owner has returned. Holding this lock until that coroutine
    actually exits prevents a later child/session from stacking another call on
    the same mutable client and corrupting request attribution or cost state.
    """

    from .mini_session.session import _dispatch_capability_identity

    client = _dispatch_capability_identity(client)
    loop = asyncio.get_running_loop()
    try:
        by_loop = _PROVIDER_LOCKS.get(client)
        if by_loop is None:
            by_loop = weakref.WeakKeyDictionary()
            _PROVIDER_LOCKS[client] = by_loop
        lock = by_loop.get(loop)
        if lock is None:
            lock = asyncio.Lock()
            by_loop[loop] = lock
        return lock
    except TypeError:
        # Some adapter objects are not weak-referenceable/hashable. Serialize
        # those conservatively per loop without retaining the adapter.
        lock = _FALLBACK_PROVIDER_LOCKS.get(loop)
        if lock is None:
            lock = asyncio.Lock()
            _FALLBACK_PROVIDER_LOCKS[loop] = lock
        return lock


def _lean_lock(lean: Any) -> asyncio.Lock:
    """Serialize cancellation-resistant tails for one Lean adapter and loop."""

    from .mini_session.session import _dispatch_capability_identity

    lean = _dispatch_capability_identity(lean)
    loop = asyncio.get_running_loop()
    try:
        by_loop = _LEAN_LOCKS.get(lean)
        if by_loop is None:
            by_loop = weakref.WeakKeyDictionary()
            _LEAN_LOCKS[lean] = by_loop
        lock = by_loop.get(loop)
        if lock is None:
            lock = asyncio.Lock()
            by_loop[loop] = lock
        return lock
    except TypeError:
        lock = _FALLBACK_LEAN_LOCKS.get(loop)
        if lock is None:
            lock = asyncio.Lock()
            _FALLBACK_LEAN_LOCKS[loop] = lock
        return lock


def _late_tail_clear_callback(lock: asyncio.Lock, state: Dict[str, Any]) -> Any:
    """Once-only late-tail registry clearer, usable as a done-callback.

    Must be a named module-level factory: an unauthenticated inline lambda is
    dropped after the action boundary, leaving a settled tail marked forever.
    """

    def clear_if_current(_done: "asyncio.Future[Any]" = None) -> None:
        current = _LEAN_LATE_TAILS.get(lock)
        if current is state:
            _LEAN_LATE_TAILS.pop(lock, None)

    return clear_if_current


def currently_owns_lean_lock(lean: Any) -> bool:
    """True when this task already holds the live generation's Lean lock."""

    return _OWNED_LEAN_LOCK.get() is _lean_lock(_live_lean_generation(lean))


def bind_owned_lean_lock(lock: asyncio.Lock) -> Any:
    """Mark this task as the Lean lock owner until the token is reset."""

    return _OWNED_LEAN_LOCK.set(lock)


def reset_owned_lean_lock(token: Any) -> None:
    """Drop the task-local Lean lock ownership binding."""

    _OWNED_LEAN_LOCK.reset(token)


def _mark_lean_late_tail(
    lock: asyncio.Lock,
    task: "asyncio.Future[Any]",
    *,
    operation_label: str,
    release_lock: Optional[Callable[..., Any]] = None,
) -> None:
    """Record one timed-out owner until its result-only tail settles."""

    if task.done():
        return
    state = {
        "task": task,
        "poisoned_since_monotonic": time.monotonic(),
        "operation_label": str(operation_label or "lean_operation"),
        "release_lock": release_lock,
    }
    _LEAN_LATE_TAILS[lock] = state
    task.add_done_callback(
        mark_runtime_owned_callback(_late_tail_clear_callback(lock, state))
    )


def _lean_late_tail_status(lean: Any) -> Dict[str, Any]:
    """Return durable health for the shared adapter lease on this loop."""

    lock = _lean_lock(lean)
    state = _LEAN_LATE_TAILS.get(lock)
    if not state:
        return {
            "occupied": bool(lock.locked()),
            "late_tail": False,
            "quarantine_due": False,
            "age_s": 0.0,
            "operation_label": "",
        }
    task = state.get("task")
    if task is None or task.done():
        _LEAN_LATE_TAILS.pop(lock, None)
        return {
            "occupied": bool(lock.locked()),
            "late_tail": False,
            "quarantine_due": False,
            "age_s": 0.0,
            "operation_label": "",
        }
    age_s = max(
        0.0,
        time.monotonic()
        - float(state.get("poisoned_since_monotonic", 0.0) or 0.0),
    )
    return {
        "occupied": bool(lock.locked()),
        "late_tail": True,
        "quarantine_due": age_s >= _LEAN_LATE_TAIL_QUARANTINE_GRACE_S,
        "age_s": age_s,
        "operation_label": str(state.get("operation_label") or ""),
    }


def _formal_lean_admission_timeout_s(
    lean: Any,
    *,
    quantum_deadline: float,
) -> float:
    """Bound lock queueing after a cancelled owner still holds Lean.

    A leftover tail from a previous claim/quantum must not consume this
    quantum's full 120s admission window. If that tail finishes quickly,
    a short admission still lets another candidate run.
    """

    remaining = max(0.0, float(quantum_deadline) - time.monotonic())
    if _lean_late_tail_status(lean).get("late_tail"):
        return min(remaining, float(_LEAN_LOCK_ADMISSION_TIMEOUT_S))
    return remaining


def _abandon_quarantined_lean_tail(lean: Any) -> bool:
    """Detach the exact revoked result-only Lean tail from loop shutdown."""

    lock = _lean_lock(lean)
    state = _LEAN_LATE_TAILS.get(lock)
    if not state:
        return False
    task = state.get("task")
    _LEAN_LATE_TAILS.pop(lock, None)
    if task is None or task.done():
        return False
    from .deadline_guard import _RESULT_ONLY_DEADLINE_TASKS, _ABANDONED_DEADLINE_TASKS

    _RESULT_ONLY_DEADLINE_TASKS.discard(task)
    _ABANDONED_DEADLINE_TASKS.discard(task)
    return True


def _safe_release_lean_lock(lock: asyncio.Lock) -> None:
    """Release a serialization lock that another waiter may already have stolen."""

    if not lock.locked():
        return
    try:
        lock.release()
    except RuntimeError:
        return


def _once_only_lock_release(lock: asyncio.Lock) -> Any:
    """Once-only release for one owned lock, usable as a done-callback.

    Must be a named module-level factory, not an inline lambda: only callables
    on ``_TRUSTED_RUNTIME_CALLBACKS`` authenticate, and an unauthenticated
    ``mark_runtime_owned_callback`` is a silent no-op -- MiniSession then
    rewrites the callback to a no-op once the action boundary closes, so the
    lock is never released and every later consumer defers forever with no
    error and no log line.

    Captures exactly one ``asyncio.Lock`` and one list used as the once-only
    flag, which is what the ``lock_release`` policy admits.
    """

    released: list[bool] = []

    def release_lock_once(_task: Any = None) -> None:
        if released:
            return
        released.append(True)
        _safe_release_lean_lock(lock)

    return release_lock_once


def _live_lean_generation(lean: Any) -> Any:
    """Follow a recycled LeanRunner handle to the published generation."""

    current = getattr(lean, "current_generation", None)
    if callable(current):
        try:
            live = current()
        except Exception:
            live = None
        if live is not None:
            return live
    return lean


def _recycle_live_session_lean_for_discarded_tail(lean: Any) -> bool:
    """Install a fresh LeanRunner when a discarded tail still owns the adapter."""

    try:
        from .lean_runner import LeanRunner
        from .mini_session.session import (
            _LIVE_MINI_SESSION_REFS,
            _LIVE_MINI_SESSION_REFS_LOCK,
            _dispatch_capability_identity,
        )
    except Exception:
        return False
    identity = _dispatch_capability_identity(lean)
    if identity is None:
        return False
    with _LIVE_MINI_SESSION_REFS_LOCK:
        sessions = [ref() for ref in list(_LIVE_MINI_SESSION_REFS)]
    status = _lean_late_tail_status(lean)
    health = {
        "operation_label": str(status.get("operation_label") or ""),
        "age_s": float(status.get("age_s") or 0.0),
        "recycle_reason": "discarded_late_tail_blocked_submitted_proof",
    }
    for session in sessions:
        if session is None:
            continue
        session_lean = getattr(session, "lean", None)
        if _dispatch_capability_identity(session_lean) != identity:
            continue
        runner = _live_lean_generation(session_lean)
        if not isinstance(runner, LeanRunner) and not isinstance(
            session_lean, LeanRunner
        ):
            continue
        try:
            return bool(session._recycle_quarantined_lean_capability(health))
        except Exception:
            _LOGGER.exception(
                "Failed to recycle Lean generation blocked by a discarded tail"
            )
            return False
    return False


def _prepare_lean_lock_for_new_check(
    lean: Any,
    *,
    release_unrecyclable_tail: bool = True,
) -> bool:
    """Unstick a discarded late tail so a submitted proof can use Lean.

    Formal-state search can asyncio-cancel a check, detach the wrapper, and
    drop the result while the wrapper still holds the shared lock. The
    scheduler recycle path only runs between actions, so ``verify_with_lean``
    parked forever behind a zombie with no Lean child. The result was already
    discarded: recycle the runner when a session owns it, otherwise release
    the leaked lock. A live owner that is not a late tail is left alone.

    Intra-search FSS candidates must not force-release: overlapping the still
    running adapter is worse than deferring until admission expires. Prove-turn
    waiters pass ``release_unrecyclable_tail=True`` so a submitted proof is
    not parked on a non-recyclable dummy/zombie lock.
    """

    live = _live_lean_generation(lean)
    status = _lean_late_tail_status(live)
    if not status.get("late_tail"):
        return False
    if _recycle_live_session_lean_for_discarded_tail(live):
        return True
    if not release_unrecyclable_tail:
        return False
    lock = _lean_lock(live)
    state = _LEAN_LATE_TAILS.get(lock) or {}
    release_lock = state.get("release_lock")
    _abandon_quarantined_lean_tail(live)
    # Consume the owner's once-only release. A raw unlock leaves the
    # detached finally/done-callback live, and that second release unlocks
    # whoever acquired after the steal.
    if callable(release_lock):
        try:
            release_lock()
        except Exception:
            _safe_release_lean_lock(lock)
    else:
        _safe_release_lean_lock(lock)
    _LOGGER.warning(
        "released discarded Lean late tail so a new check can proceed "
        "(operation=%s age_s=%.3f)",
        str(status.get("operation_label") or "lean_operation"),
        float(status.get("age_s") or 0.0),
    )
    return True


async def acquire_prepared_lean_lock(
    lean: Any,
    *,
    admission_timeout_s: Optional[float] = None,
    deadline_elapsed: Optional[Callable[[], bool]] = None,
    deadline_monotonic: float = 0.0,
    poll_s: float = 0.1,
    release_unrecyclable_tail: bool = False,
) -> Tuple[Any, asyncio.Lock]:
    """Acquire the live generation's lock after unsticking a discarded tail.

    A finite ``admission_timeout_s`` is a lock wait, not Lean work: miss it
    and the caller defers. ``None`` waits for a live owner, but polls prepare
    so a recycled generation is not waited on the abandoned lock. Soft-policy
    verify/try_lean must not invent a 1s admission cap: that discarded a
    finished proof waiting behind a live owner. Intra-search keeps the default
    False so a still-running adapter is not overlapped.

    Force-release of a non-recyclable tail is only for unbounded prove-turn
    waits. A conversation-turn deadline must defer instead of overlapping the
    still-running checker it just detached.
    """

    owned = _OWNED_LEAN_LOCK.get()
    if owned is not None:
        live = _live_lean_generation(lean)
        if _lean_lock(live) is owned:
            return live, owned

    started = time.monotonic()
    poll = max(0.01, float(poll_s or 0.1))
    steal_unrecyclable_tail = bool(
        release_unrecyclable_tail
        and admission_timeout_s is None
        and float(deadline_monotonic or 0.0) <= 0.0
    )

    def admission_remaining() -> Optional[float]:
        if admission_timeout_s is None:
            return None
        return max(0.0, float(admission_timeout_s) - (time.monotonic() - started))

    def timed_out() -> bool:
        if deadline_elapsed is not None and deadline_elapsed():
            return True
        remaining = admission_remaining()
        return remaining is not None and remaining <= 0.0

    while True:
        if timed_out():
            raise asyncio.TimeoutError("lean lock admission deferred")
        _prepare_lean_lock_for_new_check(
            lean,
            release_unrecyclable_tail=steal_unrecyclable_tail,
        )
        live = _live_lean_generation(lean)
        lock = _lean_lock(live)
        acquire_task = asyncio.create_task(lock.acquire())
        acquired = False
        try:
            while True:
                if timed_out():
                    raise asyncio.TimeoutError("lean lock admission deferred")
                remaining = admission_remaining()
                wait_s = poll if remaining is None else min(poll, remaining)
                done, _pending = await asyncio.wait(
                    {acquire_task},
                    timeout=wait_s,
                )
                if acquire_task not in done:
                    prepared = _prepare_lean_lock_for_new_check(
                        lean,
                        release_unrecyclable_tail=steal_unrecyclable_tail,
                    )
                    generation_moved = (
                        _lean_lock(_live_lean_generation(lean)) is not lock
                    )
                    if prepared or generation_moved:
                        if not acquire_task.done():
                            acquire_task.cancel()
                        got = False
                        try:
                            got = bool(await acquire_task)
                        except (asyncio.CancelledError, Exception):
                            got = False
                        if got:
                            _safe_release_lean_lock(lock)
                        break
                    continue
                acquire_task.result()
                acquired = True
                if timed_out():
                    _safe_release_lean_lock(lock)
                    acquired = False
                    raise asyncio.TimeoutError("lean lock admission deferred")
                live = _live_lean_generation(lean)
                if _lean_lock(live) is not lock:
                    _safe_release_lean_lock(lock)
                    acquired = False
                    break
                return live, lock
        except BaseException:
            if not acquired:
                if not acquire_task.done():
                    acquire_task.cancel()
                got = False
                try:
                    got = bool(await acquire_task)
                except (asyncio.CancelledError, Exception):
                    got = False
                if got:
                    _safe_release_lean_lock(lock)
            elif lock is not None:
                _safe_release_lean_lock(lock)
            raise


async def _run_serialized_lean_operation(
    lean: Any,
    operation: Any,
    *,
    operation_timeout_s: float,
    admission_timeout_s: Optional[float] = None,
) -> Any:
    """Wait for an abandoned tail, then start a fresh operation watchdog.

    Lock queueing is governed by the beam's outer absolute search deadline.
    The per-operation watchdog begins only after this operation owns Lean, so
    a prior cancellation-resistant tail cannot consume the next candidate's
    own execution allowance.
    """

    if currently_owns_lean_lock(lean):
        return await operation()

    if admission_timeout_s is None:
        admission_timeout_s = _LEAN_LOCK_ADMISSION_TIMEOUT_S
    admission = max(0.0, float(admission_timeout_s or 0.0))
    if admission <= 0.0:
        raise asyncio.TimeoutError("formal Lean admission deferred")
    try:
        _live, lock = await acquire_prepared_lean_lock(
            lean,
            admission_timeout_s=admission,
            release_unrecyclable_tail=False,
        )
    except asyncio.TimeoutError as exc:
        raise asyncio.TimeoutError("formal Lean admission deferred") from exc

    release_owned_lock = _once_only_lock_release(lock)

    async def run_with_owned_lock() -> Any:
        token = bind_owned_lean_lock(lock)
        try:
            return await operation()
        finally:
            reset_owned_lean_lock(token)
            release_owned_lock()

    operation_task = create_result_only_deadline_task(run_with_owned_lock())
    # Cancellation before the task's first timeslice skips the coroutine's
    # ``finally``.  This callback is the authoritative once-only release for
    # that edge; a cancellation-resistant tail keeps the lease until it has
    # actually stopped using Lean.
    operation_task.add_done_callback(
        mark_runtime_owned_callback(release_owned_lock)
    )
    operation_timeout = max(0.0, float(operation_timeout_s or 0.0))
    # Callers pass the checker's own budget here and also forward it as the
    # check's ``timeout_s``, so arming this guard with it verbatim made the
    # two race; only the checker's copy kills and reaps. Zero still means "no
    # outer guard at all" -- see DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
    # where a 15s knife detached the wrapper, discarded a late result and left
    # the lock held with no Lean child. Never arm a guard that was disabled.
    try:
        return await await_with_strict_deadline(
            operation_task,
            timeout_s=(
                outer_guard_timeout_s(operation_timeout)
                if operation_timeout > 0.0
                else None
            ),
            operation_label="formal_state_lean_operation",
            operation_ownership="result_only",
        )
    except (asyncio.TimeoutError, asyncio.CancelledError):
        if not operation_task.done():
            _mark_lean_late_tail(
                lock,
                operation_task,
                operation_label="formal_state_lean_operation",
                release_lock=release_owned_lock,
            )
        raise


async def _run_serialized_provider_operation(
    client: Any,
    operation: Any,
    *,
    admission_timeout_s: Optional[float] = None,
    operation_timeout_s: Optional[float] = None,
    absolute_deadline: Optional[float] = None,
) -> Any:
    """Admit and watchdog one provider operation without overlapping tails.

    Lock admission is bounded before any provider work starts.  After
    admission, the phase-local watchdog cancels the metered call.  The cost
    controller conservatively settles dispatched requests with missing usage,
    and ``_await_with_hard_timeout`` retains a cancellation-resistant tail
    under this lock, so another formal request cannot overlap it or corrupt
    usage attribution.
    """

    lock = _provider_lock(client)
    if admission_timeout_s is None:
        await lock.acquire()
    else:
        admission = max(0.0, float(admission_timeout_s or 0.0))
        if admission <= 0.0:
            raise _ProviderAdmissionDeferred("formal provider admission deferred")
        try:
            await asyncio.wait_for(lock.acquire(), timeout=admission)
        except asyncio.TimeoutError as exc:
            raise _ProviderAdmissionDeferred(
                "formal provider admission deferred"
            ) from exc

    release_owned_lock = _once_only_lock_release(lock)

    async def run_with_owned_lock() -> Any:
        try:
            with formal_provider_exclusive_scope():
                return await operation()
        finally:
            release_owned_lock()

    timeout = max(0.0, float(operation_timeout_s or 0.0))
    if absolute_deadline is not None:
        timeout = min(
            timeout,
            max(0.0, float(absolute_deadline) - time.monotonic()),
        )
    if timeout <= 0.0:
        release_owned_lock()
        raise _ProviderAdmissionDeferred("formal provider deadline elapsed")
    operation_task = asyncio.create_task(run_with_owned_lock())
    # A task cancelled before its coroutine body gets a first timeslice does
    # not execute ``finally``.  The callback is therefore the authoritative
    # once-only release path for that edge case; for a cancellation-resistant
    # provider tail it fires only after the tail really ends.
    operation_task.add_done_callback(
        mark_runtime_owned_callback(release_owned_lock)
    )
    return await _await_with_hard_timeout(
        operation_task,
        timeout=timeout,
        cancel_grace=0.0,
    )


@dataclass(frozen=True)
class FormalStateSearchConfig:
    """Bounded, per-proof-state search policy.

    ``operation_timeout_s`` is an optional in-flight Lean asyncio bound.
    Zero waits for the live check; the search quantum still yields between
    steps via ``total_timeout_s``. Tactic generation has its own output,
    reasoning, and wall-clock bounds because it is a compact structured phase;
    it must not inherit an arbitrary proof-authoring completion budget.
    """

    enabled: bool = True
    total_timeout_s: float = DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S
    operation_timeout_s: float = DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S
    provider_timeout_s: float = DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S
    provider_max_tokens: int = DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS
    provider_reasoning_effort: str = (
        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
    )
    provider_max_attempts: int = 2
    provider_retry_backoff_s: float = 5.0
    beam_width: int = 4
    max_steps: int = 8
    max_candidates_per_state: int = 6
    deterministic_candidates_per_state: int = 4
    backtrack_limit: int = 8
    # Consecutive completed search quanta without kernel-facing or diagnostic
    # improvement. Zero explicitly disables this progress governor.
    max_no_improvement_quanta: int = 6
    # Consecutive completed quanta with ZERO complete candidates and no
    # substantive rank improvement (novelty-only churn). A much tighter
    # governor than the stall window above: a lane that never produces a
    # checkable candidate switches strategy after this many quanta instead of
    # paying the full window (MP-FU-008). Zero explicitly disables.
    max_zero_yield_quanta: int = 2
    value_weight: float = 0.25
    novelty_weight: float = 0.15
    model_temperature: float = 0.25

    def normalized(self) -> "FormalStateSearchConfig":
        total = max(0.0, float(self.total_timeout_s or 0.0))
        operation = max(0.0, float(self.operation_timeout_s or 0.0))
        provider = max(0.0, float(self.provider_timeout_s or 0.0))
        if provider <= 0.0:
            provider = DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S
        if total > 0.0:
            provider = min(provider, total)
        reasoning = (
            str(
                self.provider_reasoning_effort
                or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
            )
            .strip()
            .lower()
            or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
        )
        return FormalStateSearchConfig(
            enabled=bool(self.enabled and total > 0.0),
            total_timeout_s=total,
            operation_timeout_s=operation,
            provider_timeout_s=provider,
            provider_max_tokens=max(
                1,
                int(
                    self.provider_max_tokens
                    or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS
                ),
            ),
            provider_reasoning_effort=reasoning,
            provider_max_attempts=max(1, int(self.provider_max_attempts or 1)),
            provider_retry_backoff_s=max(
                0.0, float(self.provider_retry_backoff_s or 0.0)
            ),
            beam_width=max(1, int(self.beam_width or 1)),
            max_steps=max(1, int(self.max_steps or 1)),
            max_candidates_per_state=max(
                1, int(self.max_candidates_per_state or 1)
            ),
            deterministic_candidates_per_state=max(
                0, int(self.deterministic_candidates_per_state or 0)
            ),
            backtrack_limit=max(0, int(self.backtrack_limit or 0)),
            max_no_improvement_quanta=max(
                0, int(self.max_no_improvement_quanta or 0)
            ),
            max_zero_yield_quanta=max(
                0, int(self.max_zero_yield_quanta or 0)
            ),
            value_weight=max(0.0, float(self.value_weight or 0.0)),
            novelty_weight=max(0.0, float(self.novelty_weight or 0.0)),
            model_temperature=clamp_probability(
                self.model_temperature,
                default=0.25,
            ),
        )


def _tactic_family(tactic: str) -> str:
    clean = str(tactic or "").strip()
    clean = re.sub(r"^(?:all_goals|first|repeat|try)\s+", "", clean)
    match = re.match(r"([A-Za-z_][A-Za-z0-9_'.]*)", clean)
    return str(match.group(1) if match else "other")


@dataclass
class OnlineTacticValueModel:
    """Small run-local beta model over tactic families and Lean progress.

    It learns only from actual Lean transition outcomes.  The prior is
    intentionally conservative and the structural progress term remains
    visible, so sparse online evidence cannot dominate the search.
    """

    family_successes: Dict[str, float] = field(default_factory=dict)
    family_failures: Dict[str, float] = field(default_factory=dict)
    observations: int = 0

    def observe(
        self,
        _statement: str,
        tactic: str,
        ok: Optional[bool],
        _error_type: str,
        goal_count: int,
    ) -> None:
        family = _tactic_family(tactic)
        if ok is True:
            reward = 1.0
        elif ok is False:
            reward = 0.0
        else:
            # A Lean-accepted nonterminal transition is weak positive evidence.
            reward = 0.35 if int(goal_count or 0) > 0 else 0.5
        self.family_successes[family] = float(
            self.family_successes.get(family, 0.0)
        ) + reward
        self.family_failures[family] = float(
            self.family_failures.get(family, 0.0)
        ) + (1.0 - reward)
        self.observations += 1

    def predict(self, node: TacticNode, _statement: str) -> float:
        family = _tactic_family(str(node.tactic or ""))
        successes = float(self.family_successes.get(family, 0.0))
        failures = float(self.family_failures.get(family, 0.0))
        empirical = (1.0 + successes) / (2.0 + successes + failures)
        progress = clamp_probability(
            getattr(node.features, "progress_ratio", 0.0),
            default=0.0,
        )
        return clamp_probability(0.55 * progress + 0.45 * empirical, default=0.0)

    def to_record(self) -> Dict[str, Any]:
        return {
            "kind": "online_beta_tactic_family_v1",
            "observations": int(self.observations),
            "family_successes": dict(sorted(self.family_successes.items())),
            "family_failures": dict(sorted(self.family_failures.items())),
        }

    @classmethod
    def from_record(cls, record: Dict[str, Any]) -> "OnlineTacticValueModel":
        data = dict(record or {})
        if str(data.get("kind") or "") != "online_beta_tactic_family_v1":
            raise ValueError("unsupported formal-search value-model record")

        def finite_counts(raw: Any) -> Dict[str, float]:
            out: Dict[str, float] = {}
            for key, value in dict(raw or {}).items():
                number = float(value)
                if number < 0.0 or number != number or number in (float("inf"), float("-inf")):
                    raise ValueError("invalid formal-search value-model count")
                out[str(key)] = number
            return out

        observations = int(data.get("observations", 0) or 0)
        if observations < 0:
            raise ValueError("invalid formal-search observation count")
        return cls(
            family_successes=finite_counts(data.get("family_successes")),
            family_failures=finite_counts(data.get("family_failures")),
            observations=observations,
        )


@dataclass(frozen=True)
class FormalStateSearchCheckpoint:
    """Durable state for one frozen theorem/helper/Lean-goal context."""

    context_hash: str
    beam_state: TacticBeamState
    value_model_record: Dict[str, Any]
    policy_retry_records: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    schema_version: int = 2

    def to_record(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "context_hash": str(self.context_hash),
            "beam_state": self.beam_state.to_record(),
            "value_model": dict(self.value_model_record),
            "policy_retries": {
                str(key): dict(value)
                for key, value in sorted(self.policy_retry_records.items())
            },
        }

    @classmethod
    def from_record(cls, record: Dict[str, Any]) -> "FormalStateSearchCheckpoint":
        data = dict(record or {})
        schema_version = int(data.get("schema_version", 0) or 0)
        if schema_version not in {1, 2}:
            raise ValueError("unsupported formal-state checkpoint schema")
        context_hash = str(data.get("context_hash") or "")
        if not context_hash:
            raise ValueError("formal-state checkpoint has no context hash")
        value_record = dict(data.get("value_model") or {})
        OnlineTacticValueModel.from_record(value_record)
        beam_state = TacticBeamState.from_record(
            dict(data.get("beam_state") or {})
        )
        tree = TacticTree.from_execution_record(beam_state.tree_record)
        unknown_ids = (
            set(beam_state.beam_node_ids)
            | set(beam_state.reserve_node_ids)
            | set(beam_state.recovery_node_ids)
        ) - set(tree.nodes)
        if unknown_ids:
            raise ValueError("formal-state checkpoint frontier references missing nodes")
        beam_ids = tuple(beam_state.beam_node_ids)
        reserve_ids = tuple(beam_state.reserve_node_ids)
        recovery_ids = tuple(beam_state.recovery_node_ids)
        if len(beam_ids) != len(set(beam_ids)) or len(reserve_ids) != len(
            set(reserve_ids)
        ) or len(recovery_ids) != len(set(recovery_ids)):
            raise ValueError("formal-state checkpoint has duplicate frontier owners")
        if (
            set(beam_ids) & set(reserve_ids)
            or set(beam_ids) & set(recovery_ids)
            or set(reserve_ids) & set(recovery_ids)
        ):
            raise ValueError("formal-state checkpoint beam/reserve overlap")
        if any(
            tree.nodes[node_id].status != TacticNodeStatus.OPEN
            for node_id in (*beam_ids, *reserve_ids, *recovery_ids)
        ):
            raise ValueError("formal-state checkpoint schedules a non-open node")
        retry_records: Dict[str, Dict[str, Any]] = {}
        raw_retries = data.get("policy_retries", {})
        if not isinstance(raw_retries, dict):
            raise ValueError("invalid formal-state policy retry records")
        for raw_key, raw_record in raw_retries.items():
            key = str(raw_key or "").strip()
            if not key or not isinstance(raw_record, dict):
                raise ValueError("invalid formal-state policy retry record")
            attempts = int(raw_record.get("attempts", 0) or 0)
            next_retry_at = float(raw_record.get("next_retry_at", 0.0) or 0.0)
            last_intent_at = float(raw_record.get("last_intent_at", 0.0) or 0.0)
            if attempts < 0 or next_retry_at < 0.0 or last_intent_at < 0.0:
                raise ValueError("invalid formal-state policy retry counters")
            retry_records[key] = {
                "attempts": attempts,
                "next_retry_at": next_retry_at,
                "last_intent_at": last_intent_at,
                "last_kind": str(raw_record.get("last_kind") or "")[:160],
                "inflight": bool(raw_record.get("inflight", False)),
                "exhausted": bool(raw_record.get("exhausted", False)),
            }
        return cls(
            context_hash=context_hash,
            beam_state=beam_state,
            value_model_record=value_record,
            policy_retry_records=retry_records,
            schema_version=max(1, schema_version),
        )

    @classmethod
    def from_record_repairing_frontier(
        cls,
        record: Dict[str, Any],
        *,
        beam_width: Optional[int] = None,
    ) -> "FormalStateSearchCheckpoint":
        """Decode a checkpoint, repairing only legacy scheduler ownership.

        Schema, tree, model, and context corruption remain fatal.  The narrow
        recovery handles checkpoints written by the former snapshot bug:
        closed/duplicate owners and OPEN tree nodes orphaned from both queues.
        """

        try:
            decoded = cls.from_record(record)
        except ValueError as exc:
            message = str(exc)
            repairable = {
                "formal-state checkpoint has duplicate frontier owners",
                "formal-state checkpoint beam/reserve overlap",
                "formal-state checkpoint schedules a non-open node",
            }
            if message not in repairable:
                raise
            data = dict(record or {})
            context_hash = str(data.get("context_hash") or "")
            value_record = dict(data.get("value_model") or {})
            retry_records = dict(data.get("policy_retries") or {})
            OnlineTacticValueModel.from_record(value_record)
            beam_state = TacticBeamState.from_record(
                dict(data.get("beam_state") or {})
            )
        else:
            context_hash = decoded.context_hash
            value_record = dict(decoded.value_model_record)
            retry_records = dict(decoded.policy_retry_records)
            beam_state = decoded.beam_state
        beam_state = beam_state.canonicalized_frontier(
            recover_unowned_open_nodes=True,
            max_active_beam_nodes=beam_width,
        )
        repaired = cls(
            context_hash=context_hash,
            beam_state=beam_state,
            value_model_record=value_record,
            policy_retry_records=retry_records,
        )
        # Re-run the strict validator so recovery can never weaken the trust
        # boundary it is intended to satisfy.
        return cls.from_record(repaired.to_record())


@dataclass
class FormalStateSearchRun:
    result: TacticSearchResult
    events: List[Dict[str, Any]] = field(default_factory=list)
    context_hash: str = ""
    value_model_record: Dict[str, Any] = field(default_factory=dict)
    checkpoint: Optional[FormalStateSearchCheckpoint] = None


def _context_hash(
    *,
    statement: str,
    preamble: str,
    helpers: Sequence[str],
    initial_goals: Sequence[LeanGoalState],
    retrieval_hints: Sequence[str] = (),
    proof_idea_context_digest: str = "",
) -> str:
    payload = {
        "statement": str(statement or ""),
        "preamble": str(preamble or ""),
        "helpers": [str(item or "") for item in helpers],
        "goals": [
            {
                "target": str(goal.target or ""),
                "hypotheses": [str(item or "") for item in goal.hypotheses],
            }
            for goal in initial_goals
        ],
        "retrieval_hints": [str(item or "") for item in retrieval_hints],
        "proof_idea_context_digest": str(proof_idea_context_digest or ""),
    }
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=False, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _formal_policy_identity(client: Any, cfg: FormalStateSearchConfig) -> str:
    """Bind retry memory to the concrete provider policy that created it."""

    raw_configs = _formal_policy_provider_configs(client)
    targets = []
    for provider_cfg in raw_configs:
        if provider_cfg is None:
            continue
        targets.append(
            {
                "base_url": str(getattr(provider_cfg, "base_url", "") or ""),
                "model": str(getattr(provider_cfg, "model", "") or ""),
                "max_tokens": int(
                    getattr(provider_cfg, "max_tokens", 0) or 0
                ),
                "reasoning_effort": str(
                    getattr(provider_cfg, "reasoning_effort", "") or ""
                ),
                "thinking_enabled": bool(
                    getattr(provider_cfg, "thinking_enabled", False)
                ),
            }
        )
    if not targets:
        targets.append(
            {
                "client_type": (
                    f"{type(client).__module__}.{type(client).__qualname__}"
                )
            }
        )
    payload = {
        "targets": targets,
        "provider_timeout_s": float(cfg.provider_timeout_s),
        "provider_max_tokens": int(cfg.provider_max_tokens),
        "effective_provider_max_tokens": _formal_policy_provider_max_tokens(
            client,
            cfg.provider_max_tokens,
        ),
        "provider_reasoning_effort": str(cfg.provider_reasoning_effort),
        "provider_max_attempts": int(cfg.provider_max_attempts),
        "provider_retry_backoff_s": float(cfg.provider_retry_backoff_s),
        "total_timeout_s": float(cfg.total_timeout_s),
        "operation_timeout_s": float(cfg.operation_timeout_s),
        "beam_width": int(cfg.beam_width),
        "max_steps": int(cfg.max_steps),
        "max_candidates_per_state": int(cfg.max_candidates_per_state),
        "deterministic_candidates_per_state": int(
            cfg.deterministic_candidates_per_state
        ),
        "backtrack_limit": int(cfg.backtrack_limit),
        "max_no_improvement_quanta": int(cfg.max_no_improvement_quanta),
        "max_zero_yield_quanta": int(cfg.max_zero_yield_quanta),
        "value_weight": float(cfg.value_weight),
        "novelty_weight": float(cfg.novelty_weight),
        "model_temperature": float(cfg.model_temperature),
    }
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=False, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _merge_candidates(
    deterministic: Sequence[Tuple[str, float]],
    learned: Sequence[Tuple[str, float]],
    *,
    limit: int,
) -> List[Tuple[str, float]]:
    merged: List[Tuple[str, float]] = []
    seen: set[str] = set()
    # Preserve at least one cheap candidate when available, then interleave
    # learned and deterministic policies without allowing duplicates to spend
    # Lean checks twice.
    lanes = [list(deterministic), list(learned)]
    lane_index = 0
    while any(lanes) and len(merged) < max(1, int(limit or 1)):
        lane = lanes[lane_index % len(lanes)]
        lane_index += 1
        if not lane:
            continue
        tactic, prior = lane.pop(0)
        clean = str(tactic or "").strip()
        # Tactics are executable Lean text. Internal whitespace in string
        # literals, quotations, and layout-sensitive syntax is semantic.
        canonical = clean
        lowered = canonical.lower()
        if (
            not canonical
            or canonical in seen
            or lowered in {"sorry", "admit", "by sorry", "by admit"}
        ):
            continue
        seen.add(canonical)
        merged.append((clean, clamp_probability(prior, default=0.5)))
    return merged


def _heal_inflight_policy_retry_records(
    policy_retry_records: Dict[str, Dict[str, Any]],
    cfg: "FormalStateSearchConfig",
    *,
    now: float,
) -> None:
    """Rewrite still-inflight provider records to a backed-off interrupted state.

    A record left ``inflight`` means a provider dispatch was interrupted (outer
    timeout / abandoned lease) before it could clear or back off.  Publishing
    that raw ledger (``next_retry_at=0.0``) as a checkpoint would make the
    scheduler re-dispatch immediately on the next quantum; heal it to
    ``interrupted_after_provider_dispatch`` with exponential backoff instead.
    Applied both on entry (crash recovery) and before emitting the final
    checkpoint (clean mid-provider timeout).
    """

    for retry_record in policy_retry_records.values():
        if not bool(retry_record.get("inflight", False)):
            continue
        attempts = max(0, int(retry_record.get("attempts", 0) or 0))
        retry_record["inflight"] = False
        retry_record["last_kind"] = "interrupted_after_provider_dispatch"
        retry_record["exhausted"] = attempts >= cfg.provider_max_attempts
        if not retry_record["exhausted"]:
            retry_record["next_retry_at"] = max(
                float(retry_record.get("next_retry_at", 0.0) or 0.0),
                now + cfg.provider_retry_backoff_s * (2 ** max(0, attempts - 1)),
            )


async def run_goal_conditioned_formal_search(
    *,
    client: Any,
    lean: Any,
    statement: str,
    initial_goals: Sequence[LeanGoalState],
    preamble: str,
    helpers: Sequence[str],
    config: FormalStateSearchConfig,
    value_model: Optional[OnlineTacticValueModel] = None,
    cost_controller: Optional[Any] = None,
    role: str = "prove",
    suppress_solution_placeholders: bool = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
    checkpoint: Optional[FormalStateSearchCheckpoint] = None,
    retrieval_hints: Sequence[str] = (),
    proof_idea_context: str = "",
    proof_idea_context_digest: str = "",
    progress_callback: Optional[
        Callable[
            [str, FormalStateSearchCheckpoint, Dict[str, Any]],
            Awaitable[None],
        ]
    ] = None,
    reservation_callback: Optional[Callable[[Any], Awaitable[None]]] = None,
) -> FormalStateSearchRun:
    """Run serial, replay-based search over exact Lean-reported goal states."""

    cfg = config.normalized()
    if not cfg.enabled:
        raise ValueError("formal-state search is disabled")
    if client is None:
        raise ValueError("formal-state search requires a prover client")
    provider_max_tokens = _formal_policy_provider_max_tokens(
        client,
        cfg.provider_max_tokens,
    )
    mandatory_reasoning_lane_disabled = bool(
        _formal_policy_has_mandatory_unbounded_reasoning(client)
        and int(cfg.provider_max_tokens)
        < _MANDATORY_REASONING_EXPLICIT_MIN_TOKENS
    )
    goals = list(initial_goals)
    if not goals:
        raise ValueError("formal-state search requires at least one initial goal")
    quantum_started_at = time.monotonic()
    quantum_deadline = quantum_started_at + cfg.total_timeout_s
    lean_lock_blocked_for_quantum = False
    events: List[Dict[str, Any]] = []
    helper_blocks = [str(item or "").strip() for item in helpers if str(item or "").strip()]
    retrieval_names = tuple(
        dict.fromkeys(
            str(item or "").strip()
            for item in retrieval_hints
            if str(item or "").strip()
        )
    )
    context_hash = _context_hash(
        statement=statement,
        preamble=preamble,
        helpers=helper_blocks,
        initial_goals=goals,
        retrieval_hints=retrieval_names,
        proof_idea_context_digest=proof_idea_context_digest,
    )
    policy_identity = _formal_policy_identity(client, cfg)
    resume_state: Optional[TacticBeamState] = None
    policy_retry_records: Dict[str, Dict[str, Any]] = {}
    policy_intent_states: Dict[str, TacticBeamState] = {}
    if checkpoint is not None:
        if str(checkpoint.context_hash or "") != context_hash:
            raise ValueError("formal-state checkpoint context mismatch")
        resume_state = checkpoint.beam_state
        tree = TacticTree.from_execution_record(
            resume_state.tree_record,
            expected_statement=str(statement or ""),
        )
        model = OnlineTacticValueModel.from_record(
            checkpoint.value_model_record
        )
        policy_retry_records = {
            str(key): dict(value)
            for key, value in checkpoint.policy_retry_records.items()
        }
    else:
        model = value_model or OnlineTacticValueModel()
        tree = TacticTree(
            str(statement or ""),
            goals,
            max_depth=cfg.max_steps,
        )

    # Entry heal: recover a record left inflight by a crash/abandon in a prior
    # quantum before it could clear or back off.
    _heal_inflight_policy_retry_records(policy_retry_records, cfg, now=time.time())

    def policy_request_key(
        current_goals: Sequence[LeanGoalState],
        tactics_so_far: Sequence[str],
    ) -> str:
        payload = {
            "state": tree.goal_state_key(current_goals),
            "prefix": [str(item or "") for item in tactics_so_far],
            "policy_identity": policy_identity,
            "proof_idea_context_digest": str(proof_idea_context_digest or ""),
        }
        return hashlib.sha256(
            json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8")
        ).hexdigest()

    async def durable_progress(
        event: str,
        beam_state: TacticBeamState,
        payload: Dict[str, Any],
    ) -> None:
        if str(event) == "policy_intent":
            node = tree.nodes.get(str(payload.get("node_id") or ""))
            if node is not None:
                key = policy_request_key(node.goals, node.tactics_from_root)
                policy_intent_states[key] = beam_state
        if progress_callback is None:
            return
        await progress_callback(
            str(event),
            FormalStateSearchCheckpoint(
                context_hash=context_hash,
                beam_state=beam_state,
                value_model_record=model.to_record(),
                policy_retry_records=policy_retry_records,
            ),
            dict(payload or {}),
        )

    def observe_transition(
        observed_statement: str,
        tactic: str,
        ok: Optional[bool],
        error_type: str,
        goal_count: int,
    ) -> None:
        model.observe(observed_statement, tactic, ok, error_type, goal_count)
        if str(error_type or "") == "kernel_completion_rejected":
            events.append(
                {
                    "event": "kernel_completion_rejected",
                    "tactic": str(tactic or ""),
                    "goal_count": int(goal_count or 0),
                }
            )

    async def generate(
        search_statement: str,
        current_goals: List[LeanGoalState],
        tactics_so_far: Tuple[str, ...],
    ) -> TacticPolicyBatch:
        primary_target = str(current_goals[0].target or search_statement)
        deterministic_raw = generate_tactic_candidates(
            primary_target,
            helper_blocks,
            max_candidates=max(1, cfg.deterministic_candidates_per_state),
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
        deterministic = [
            (str(candidate.tactic or ""), 0.45)
            for candidate in deterministic_raw[: cfg.deterministic_candidates_per_state]
            if str(candidate.tactic or "").strip()
        ]
        context_lemmas = "\n\n".join(helper_blocks[-12:])
        if retrieval_names:
            context_lemmas = "\n\n".join(
                item
                for item in (
                    context_lemmas,
                    "Retrieved declarations available in this Lean environment:\n"
                    + "\n".join(f"- {name}" for name in retrieval_names[-32:]),
                )
                if item
            )
        messages = tactic_gen_multi_messages(
            search_statement,
            current_goals,
            tactics_so_far,
            num_candidates=cfg.max_candidates_per_state,
            context_lemmas=context_lemmas,
        )
        if proof_idea_context:
            messages.append(
                {
                    "role": "user",
                    "content": proof_idea_context,
                    "pinned": True,
                    "preserve_context": True,
                    "required_atomic_context": True,
                    "formal_policy_cognition_context": True,
                    "context_digest": str(proof_idea_context_digest or ""),
                    "_required_prompt_context": {
                        "kind": "formal_policy_cognition",
                        "units": [
                            "selected_core",
                            "current_attempt",
                            "current_residual",
                        ],
                        "context_digest": str(
                            proof_idea_context_digest or ""
                        ),
                    },
                }
            )
        learned: List[Tuple[str, float]] = []
        provider_error = ""
        provider_error_kind = ""
        provider_admission_deferred = False
        provider_capability_degraded = False
        provider_dispatch_checkpoint_lock = asyncio.Lock()

        request_key = policy_request_key(current_goals, tactics_so_far)
        retry_record = policy_retry_records.setdefault(
            request_key,
            {
                "attempts": 0,
                "next_retry_at": 0.0,
                "last_intent_at": 0.0,
                "last_kind": "",
                "inflight": False,
                "exhausted": False,
            },
        )

        async def persist_policy_dispatch(_details: Any = None) -> None:
            # ModelPool leaves can reach the concrete transport boundary
            # concurrently.  Every concrete exposure is a paid attempt and
            # therefore receives its own serialized forced WAL barrier before
            # transport.  Counting only the first leaf made the documented
            # provider_max_attempts ceiling multiplicative with hidden adapter
            # retries/fallbacks.
            async with provider_dispatch_checkpoint_lock:
                current_time = time.time()
                retry_record["attempts"] = int(
                    retry_record.get("attempts", 0) or 0
                ) + 1
                retry_record["last_intent_at"] = current_time
                retry_record["inflight"] = True
                retry_record["last_kind"] = "provider_dispatch_intent"
                beam_state = policy_intent_states.get(request_key)
                if beam_state is None:
                    if progress_callback is not None:
                        raise RuntimeError(
                            "provider dispatch has no durable policy-intent state"
                        )
                    return
                await durable_progress(
                    "provider_dispatch_intent",
                    beam_state,
                    {
                        "policy_request_key": request_key,
                        "attempt": int(retry_record["attempts"]),
                        "policy_identity": policy_identity,
                    },
                )

        async def invoke_policy_client(usage_callback: Any) -> Any:
            # Production wrappers/clients notify at their concrete HTTP or
            # opaque-leaf boundary. For arbitrary adapters the method entry is
            # the strongest available dispatch boundary.
            if not bool(
                getattr(client, "supports_transport_dispatch_marker", False)
            ):
                await notify_provider_dispatch_observer()
            return await call_with_optional_usage_callback(
                client.chat,
                messages,
                usage_callback=usage_callback,
                temperature_override=cfg.model_temperature,
                max_tokens_override=provider_max_tokens,
                reasoning_effort_override=cfg.provider_reasoning_effort,
                request_timeout_override_s=cfg.provider_timeout_s,
                operation_timeout_override_s=cfg.provider_timeout_s,
                required_keywords=(
                    "max_tokens_override",
                    "reasoning_effort_override",
                    "request_timeout_override_s",
                    "operation_timeout_override_s",
                ),
            )

        async def call_provider() -> Any:
            with provider_dispatch_observer(persist_policy_dispatch):
                return await metered_or_plain_call(
                    cost_controller=cost_controller,
                    client=client,
                    messages=messages,
                    role=str(role or "prove"),
                    scope="mini_session",
                    action_id="formal_state_search",
                    call_kind="goal_conditioned_tactic_generation",
                    # Cost admission and the transport must use the same cap.
                    # Requiring the client keyword above prevents silent
                    # under-reservation if an adapter lacks phase controls.
                    max_tokens_override=provider_max_tokens,
                    candidate_count=cfg.max_candidates_per_state,
                    metadata={
                        "formal_state_search": True,
                        "policy_request_key": request_key,
                        "policy_identity": policy_identity,
                        "formal_policy_provider_timeout_s": float(
                            cfg.provider_timeout_s
                        ),
                        "formal_policy_provider_max_tokens": int(
                            provider_max_tokens
                        ),
                        "formal_policy_reasoning_effort": str(
                            cfg.provider_reasoning_effort
                        ),
                        # This logical invocation may use only the paid
                        # attempts which its durable request ledger has not
                        # already consumed.  The transport observer above
                        # checkpoints each admitted leaf independently.
                        "provider_dispatch_max_attempts": max(
                            1,
                            int(cfg.provider_max_attempts)
                            - int(retry_record.get("attempts", 0) or 0),
                        ),
                        "proof_idea_context_digest": str(
                            proof_idea_context_digest or ""
                        ),
                    },
                    on_reserved=reservation_callback,
                    invoke=invoke_policy_client,
                )

        exhausted = bool(retry_record.get("exhausted", False)) or bool(
            not retry_record.get("inflight", False)
            and int(retry_record.get("attempts", 0) or 0)
            >= cfg.provider_max_attempts
        )
        backed_off = bool(
            not retry_record.get("inflight", False)
            and time.time()
            < float(retry_record.get("next_retry_at", 0.0) or 0.0)
        )
        if exhausted:
            retry_record["exhausted"] = True
            provider_error_kind = "provider_retry_exhausted"
        elif backed_off:
            provider_error = "provider retry backoff active"
            provider_error_kind = "provider_retry_backoff"
        provider_dispatched = bool(not exhausted and not backed_off)
        if provider_dispatched and mandatory_reasoning_lane_disabled:
            provider_dispatched = False
            provider_capability_degraded = True
            provider_error = (
                "mandatory reasoning provider requires an explicit formal "
                "policy completion envelope"
            )
            provider_error_kind = "provider_mandatory_reasoning_unbounded"
            retry_record["exhausted"] = True
            retry_record["last_kind"] = provider_error_kind
        try:
            raw = None
            if provider_dispatched:
                remaining_quantum_s = max(
                    0.0,
                    quantum_deadline - time.monotonic(),
                )
                minimum_dispatch_window_s = min(
                    _MIN_PROVIDER_DISPATCH_WINDOW_S,
                    max(0.0, float(cfg.provider_timeout_s or 0.0)),
                    max(0.0, float(cfg.total_timeout_s or 0.0)) * 0.90,
                )
                if remaining_quantum_s < minimum_dispatch_window_s:
                    raise _ProviderAdmissionDeferred(
                        "formal provider quantum has no viable dispatch window"
                    )
                raw = await _run_serialized_provider_operation(
                    client,
                    call_provider,
                    admission_timeout_s=remaining_quantum_s,
                    operation_timeout_s=min(
                        cfg.provider_timeout_s,
                        remaining_quantum_s,
                    ),
                    absolute_deadline=quantum_deadline,
                )
            if not hard_timeout_writeback_allowed():
                return TacticPolicyBatch((), complete=False, retryable_kind="abandoned_lease")
            learned = parse_multi_tactic_response(str(raw or "")) if raw is not None else []
            learned = [
                (tactic, prior)
                for tactic, prior in learned
                if not is_answer_unsafe_statement_text(
                    tactic,
                    suppress_solution_placeholders=suppress_solution_placeholders,
                    opaque_mode=opaque_mode,
                    allow_official_answer_visibility=(
                        allow_official_answer_visibility
                    ),
                    official_answer_payload_present=(
                        official_answer_payload_present
                    ),
                )
            ]
        except _ProviderAdmissionDeferred as exc:
            provider_admission_deferred = True
            provider_error_kind = "provider_admission_deferred"
            provider_error = f"{type(exc).__name__}: {exc}"[:500]
        except Exception as exc:
            classification = classify_llm_exception(exc)
            if classification.kind == "provider_capability_conflict":
                # A phase-critical cap/reasoning/deadline keyword cannot be
                # silently dropped, but it also must not abort deterministic
                # formal search.  Permanently disable only this learned-policy
                # request key and retain the cheap tactic portfolio.
                provider_capability_degraded = True
                provider_error_kind = "provider_capability_conflict"
                provider_error = f"{type(exc).__name__}: {exc}"[:500]
                retry_record["inflight"] = False
                retry_record["exhausted"] = True
                retry_record["last_kind"] = provider_error_kind
            elif not bool(classification.retryable):
                raise
            else:
                provider_error_kind = (
                    type(exc).__name__
                    if isinstance(exc, TimeoutError)
                    else str(classification.kind or type(exc).__name__)
                )
                provider_error = f"{type(exc).__name__}: {exc}"[:500]
        if (
            not provider_error
            and provider_dispatched
            and not learned
        ):
            # A transport-successful response with no executable tactic is
            # not evidence that this Lean state is mathematically exhausted.
            # Keep the learned lane in the durable provider retry path even
            # when cheap deterministic candidates are available. Those may
            # execute in this quantum, but cannot certify provider success or
            # suppress a wrapper fallback/later bounded attempt.
            provider_error = "provider returned no parseable tactic candidates"
            provider_error_kind = "empty_or_unparseable_policy"
        if retry_record.get("inflight", False):
            if provider_error:
                attempts = int(retry_record.get("attempts", 0) or 0)
                retry_record["inflight"] = False
                retry_record["last_kind"] = provider_error_kind
                retry_record["exhausted"] = attempts >= cfg.provider_max_attempts
                if not retry_record["exhausted"]:
                    retry_record["next_retry_at"] = (
                        time.time()
                        + cfg.provider_retry_backoff_s
                        * (2 ** max(0, attempts - 1))
                    )
            else:
                policy_retry_records.pop(request_key, None)
        elif (
            provider_error
            and not backed_off
            and not provider_admission_deferred
            and not provider_capability_degraded
        ):
            # A pre-dispatch infrastructure failure spends no provider attempt,
            # but it still receives durable backoff so the scheduler cannot
            # hot-loop while the local capability/cost boundary is unavailable.
            retry_record["last_kind"] = provider_error_kind
            retry_record["next_retry_at"] = (
                time.time() + cfg.provider_retry_backoff_s
            )
        candidates = _merge_candidates(
            deterministic,
            learned,
            limit=cfg.max_candidates_per_state,
        )
        if not hard_timeout_writeback_allowed():
            return TacticPolicyBatch((), complete=False, retryable_kind="abandoned_lease")
        events.append(
            {
                "event": "policy_generated",
                "state_key": tree.goal_state_key(current_goals),
                "depth": len(tactics_so_far),
                "deterministic_candidates": len(deterministic),
                "learned_candidates": len(learned),
                "selected_candidates": len(candidates),
                "provider_error": provider_error,
                "provider_error_kind": provider_error_kind,
                "provider_capability_degraded": provider_capability_degraded,
            }
        )
        return TacticPolicyBatch(
            tuple(candidates),
            complete=bool(
                exhausted or provider_capability_degraded or not provider_error
            ),
            retryable_kind=(provider_error_kind if provider_error else ""),
        )

    async def sorry_check(
        search_statement: str,
        tactics: Tuple[str, ...],
    ) -> Tuple[List[LeanGoalState], Any, Any, bool]:
        nonlocal lean_lock_blocked_for_quantum
        proof = tactics_to_proof(tactics)
        async def call_lean_transition() -> Any:
            return await lean.check_with_sorry_raw(
                    search_statement,
                    proof,
                    helper_blocks,
                    preamble_override=preamble,
                    timeout_s=cfg.operation_timeout_s or None,
                )

        if lean_lock_blocked_for_quantum:
            raise TacticOperationTimeout("lean_lock_occupied")
        try:
            parsed, output, returncode = await _run_serialized_lean_operation(
                lean,
                call_lean_transition,
                operation_timeout_s=cfg.operation_timeout_s,
                admission_timeout_s=_formal_lean_admission_timeout_s(
                    lean,
                    quantum_deadline=quantum_deadline,
                ),
            )
        except asyncio.TimeoutError as exc:
            if "admission deferred" in str(exc) and _lean_late_tail_status(
                lean
            ).get("late_tail"):
                lean_lock_blocked_for_quantum = True
            raise TacticOperationTimeout("lean_transition") from exc
        if not hard_timeout_writeback_allowed():
            # The evaluator owning this operation has abandoned its lease.
            # Return data for stack unwinding only; do not publish telemetry.
            remaining = list(getattr(parsed, "remaining_goals", []) or [])
            features = extract_goal_state_features(remaining, goals, parsed)
            return remaining, features, parsed, False
        remaining = list(getattr(parsed, "remaining_goals", []) or [])
        features = extract_goal_state_features(remaining, goals, parsed)
        complete = bool(
            getattr(parsed, "ok", False)
            and not remaining
            and int(getattr(parsed, "sorry_count", 0) or 0) == 0
        )
        events.append(
            {
                "event": "lean_transition",
                "depth": len(tactics),
                "tactic": str(tactics[-1] if tactics else ""),
                "returncode": int(returncode or 0),
                "goal_count": len(remaining),
                "complete": complete,
                "infra_failure": bool(getattr(parsed, "infra_failure", False)),
                "timeout": bool(getattr(parsed, "timeout", False)),
                "output_hash": hashlib.sha256(
                    str(output or "").encode("utf-8")
                ).hexdigest(),
            }
        )
        return remaining, features, parsed, complete

    async def full_check(search_statement: str, proof: str) -> Tuple[bool, str]:
        nonlocal lean_lock_blocked_for_quantum
        async def call_lean_final_check() -> Any:
            return await lean.check(
                    search_statement,
                    proof,
                    helper_blocks,
                    preamble_override=preamble,
                    timeout_s=cfg.operation_timeout_s or None,
                    check_kind="formal_state_search_final",
                )

        if lean_lock_blocked_for_quantum:
            raise TacticOperationTimeout("lean_lock_occupied")
        try:
            checked = await _run_serialized_lean_operation(
                lean,
                call_lean_final_check,
                operation_timeout_s=cfg.operation_timeout_s,
                admission_timeout_s=_formal_lean_admission_timeout_s(
                    lean,
                    quantum_deadline=quantum_deadline,
                ),
            )
        except asyncio.TimeoutError as exc:
            if "admission deferred" in str(exc) and _lean_late_tail_status(
                lean
            ).get("late_tail"):
                lean_lock_blocked_for_quantum = True
            raise TacticOperationTimeout("lean_final_check") from exc
        return bool(getattr(checked, "ok", False)), str(
            getattr(checked, "output", "") or ""
        )

    def continue_at_structural_cutpoint(_progress: Any) -> Tuple[bool, str]:
        """Yield a spent quantum only after the current operation is durable."""

        if lean_lock_blocked_for_quantum:
            return False, "formal_lean_lock_occupied_after_timeout"
        if time.monotonic() >= quantum_deadline:
            return False, "formal_quantum_complete"
        return True, ""

    result = await tactic_tree_beam_search(
        tree,
        generate,
        sorry_check,
        full_check,
        make_score_fn(None),
        beam_width=cfg.beam_width,
        max_steps=cfg.max_steps,
        max_candidates_per_node=cfg.max_candidates_per_state,
        # The beam's wall timeout cancels its current awaitable and discards a
        # late result. Formal policy generations are capability operations, so
        # enforce the quantum only through the safe structural callback below.
        time_limit=float("inf"),
        value_fn=model.predict,
        value_weight=cfg.value_weight,
        novelty_weight=cfg.novelty_weight,
        backtrack_limit=cfg.backtrack_limit,
        cancel_grace_s=0.0,
        should_continue=continue_at_structural_cutpoint,
        feedback_fn=observe_transition,
        resume_state=resume_state,
        durable_progress_fn=durable_progress,
    )
    events.append(
        {
            "event": "search_finished",
            "solved": bool(result.solved),
            "exit_reason": str(result.exit_reason or ""),
            "nodes_created": int(result.nodes_created),
            "nodes_expanded": int(result.nodes_expanded),
            "lean_checks": int(result.lean_checks),
            "backtracks": int(result.backtracks),
            "bottleneck_count": len(result.bottlenecks),
            "operation_timeouts": int(result.operation_timeouts),
            "infrastructure_failures": int(result.infrastructure_failures),
            "completion_rejections": int(result.completion_rejections),
        }
    )
    # A provider dispatch interrupted by the outer budget leaves its record
    # inflight with next_retry_at=0.0.  Heal it BEFORE publishing so the
    # scheduler backs off instead of re-dispatching immediately next quantum.
    _heal_inflight_policy_retry_records(policy_retry_records, cfg, now=time.time())
    next_checkpoint = (
        FormalStateSearchCheckpoint(
            context_hash=context_hash,
            beam_state=result.resume_state,
            value_model_record=model.to_record(),
            policy_retry_records=policy_retry_records,
        )
        if result.resume_state is not None and not result.solved
        else None
    )
    return FormalStateSearchRun(
        result=result,
        events=events,
        context_hash=context_hash,
        value_model_record=model.to_record(),
        checkpoint=next_checkpoint,
    )


__all__ = [
    "FormalStateSearchConfig",
    "FormalStateSearchCheckpoint",
    "FormalStateSearchRun",
    "OnlineTacticValueModel",
    "run_goal_conditioned_formal_search",
]
