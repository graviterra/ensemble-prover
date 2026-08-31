"""Strict monotonic-deadline awaiting for external operations.

Some adapters catch ``CancelledError`` and may even return a late success.
``asyncio.wait_for`` waits for such a coroutine to finish cancellation, so it
cannot by itself enforce a controller wall deadline. This module keeps the
controller bounded while cancelling and observing the abandoned operation.
"""

from __future__ import annotations

import asyncio
import contextlib
import contextvars
import inspect
import logging
import threading
import time
import weakref
from typing import Any, Awaitable, Literal, Optional, TypeVar

from .runtime_context import mark_runtime_owned_callback


T = TypeVar("T")
_LOGGER = logging.getLogger(__name__)
_CANCELLATION_RETRY_ATTEMPTS = 2
_CANCELLATION_RETRY_DELAY_S = 0.005

# Headroom for an outer abandonment guard wrapping an operation that already
# bounds itself with the same number.
#
# Arming both with one value makes the two timers race. The inner budget is
# normally the only one that can reclaim anything -- it kills the process,
# reaps the child, releases the lock, returns partial results -- while the
# outer guard can merely cancel and detach. So a guard win discards a result
# that was about to land AND strands whatever the inner budget would have
# freed. The guard exists to catch an operation that never returns at all, so
# it must expire strictly after the deadline that does the real work.
#
# Purely proportional, with a cap. Deliberately NO absolute floor: a fixed
# floor is enormous relative to a sub-second operation, and it broke three
# different callers by pushing the guard past an enclosing budget -- a 0.01s
# boundary probe, a 0.05s falsification instance inside a 1.0s engine, and a
# strict-boundary detach test. A small operation has no Lean process to reap,
# so it needs no fixed headroom; only large budgets do, and the fraction
# already gives them 25%. The cap is sized off the checker's documented
# teardown (_killed_process_reap_timeout_s 30.0 plus poll granularity).
# Never shrink these to bound work -- the inner budget is the cap.
_OUTER_GUARD_HEADROOM_CAP_S = 35.0
_OUTER_GUARD_HEADROOM_FRACTION = 0.25


def outer_guard_headroom_s(inner_timeout_s: float) -> float:
    """Headroom to add to a guard wrapping a self-bounding operation."""

    try:
        inner = max(0.0, float(inner_timeout_s))
    except (TypeError, ValueError):
        return 0.0
    return min(_OUTER_GUARD_HEADROOM_CAP_S, inner * _OUTER_GUARD_HEADROOM_FRACTION)


def outer_guard_timeout_s(
    inner_timeout_s: Optional[float],
) -> Optional[float]:
    """Guard budget that lets ``inner_timeout_s`` land first.

    ``None`` and zero mean the caller deliberately runs this operation with no
    outer guard at all -- the documented choice for Lean work, where an outer
    knife cannot reclaim anything and only detaches, discarding a late success
    and stranding the lock. Preserve that: never convert "no guard" into a
    guard, however small.
    """

    if inner_timeout_s is None:
        return None
    inner = max(0.0, float(inner_timeout_s or 0.0))
    if inner <= 0.0:
        return None
    return inner + outer_guard_headroom_s(inner)
_OWNED_CANCELLATION_JOIN_TIMEOUT_S = 5.0
_ABANDONED_DEADLINE_TASKS: set[asyncio.Future[Any]] = set()
_ABANDONED_DEADLINE_TASK_SCOPES: dict[asyncio.Future[Any], str] = {}
_ABANDONED_DEADLINE_TASK_OWNERSHIP: dict[asyncio.Future[Any], str] = {}
_RESULT_ONLY_DEADLINE_TASKS: "weakref.WeakSet[asyncio.Future[Any]]" = (
    weakref.WeakSet()
)
_ABANDONED_DEADLINE_SCOPE_COUNTS: dict[str, int] = {}
_DEADLINE_OPERATION_SCOPE: contextvars.ContextVar[str] = contextvars.ContextVar(
    "mini_deadline_operation_scope",
    default="",
)
_DEADLINE_SCOPE_ABORT_ON_DETACH: contextvars.ContextVar[bool] = (
    contextvars.ContextVar(
        "mini_deadline_scope_abort_on_detach",
        default=False,
    )
)
_RESULT_ONLY_DEADLINE_DESCENDANT_SCOPE: contextvars.ContextVar[bool] = (
    contextvars.ContextVar(
        "mini_result_only_deadline_descendant_scope",
        default=False,
    )
)


class DispatchScopeDetached(BaseException):
    """A bound transaction lost exclusive mutation authority.

    This deliberately bypasses ordinary ``except Exception`` recovery inside
    an action. Once a strict-deadline child is detached, the action may no
    longer continue doing mathematical/provider work and settle hours later;
    only the owning MiniSession transaction boundary may quiesce and restore
    its exact pre-dispatch authority.
    """


def _raise_deadline_expired_for_scope(*, detached: bool) -> None:
    scope_id = _DEADLINE_OPERATION_SCOPE.get()
    if detached and scope_id and _DEADLINE_SCOPE_ABORT_ON_DETACH.get():
        raise DispatchScopeDetached(
            f"strict deadline detached work in dispatch scope {scope_id}"
        )
    raise asyncio.TimeoutError


class _DaemonOperationFuture(asyncio.Future[Any]):
    """Completion handle whose worker cannot be cancelled in-process.

    Cancelling an ordinary asyncio Future marks it done immediately even
    though the daemon thread is still running.  Keeping this handle pending
    until the worker publishes lets cancellation barriers truthfully wait for
    shared-state mutation to stop (or escalate to process containment).
    """

    def cancel(self, msg: Any = None) -> bool:
        del msg
        return False


@contextlib.contextmanager
def bind_deadline_operation_scope(
    scope_id: str,
    *,
    abort_on_detach: bool = False,
):
    """Bind detached deadline work to one scheduler dispatch scope."""

    token = _DEADLINE_OPERATION_SCOPE.set(str(scope_id or "").strip())
    abort_token = _DEADLINE_SCOPE_ABORT_ON_DETACH.set(bool(abort_on_detach))
    try:
        yield
    finally:
        _DEADLINE_SCOPE_ABORT_ON_DETACH.reset(abort_token)
        _DEADLINE_OPERATION_SCOPE.reset(token)


def _consume_task_exception(task: "asyncio.Future[Any]") -> None:
    """Retrieve a detached task's terminal exception without surfacing it."""

    if task.cancelled():
        return
    try:
        task.exception()
    except BaseException:
        pass


def _release_abandoned_task(task: "asyncio.Future[Any]") -> None:
    _ABANDONED_DEADLINE_TASKS.discard(task)
    _ABANDONED_DEADLINE_TASK_SCOPES.pop(task, None)
    _ABANDONED_DEADLINE_TASK_OWNERSHIP.pop(task, None)
    _consume_task_exception(task)


def _run_sync_in_daemon(
    operation: Any, *args: Any, **kwargs: Any
) -> "asyncio.Future[Any]":
    """Bridge an unbounded sync adapter without holding process shutdown open."""

    loop = asyncio.get_running_loop()
    future: "asyncio.Future[Any]" = _DaemonOperationFuture(loop=loop)

    def publish_result(
        value: Any = None, error: Optional[BaseException] = None
    ) -> None:
        if future.done():
            if error is None and inspect.iscoroutine(value):
                value.close()
            return
        if (
            error is None
            and future in _ABANDONED_DEADLINE_TASKS
            and inspect.iscoroutine(value)
        ):
            value.close()
            value = None
        if error is None:
            future.set_result(value)
        else:
            future.set_exception(error)

    # This callback can only resolve the private Future returned by this
    # bridge.  The task awakened by that Future remains visible to the action
    # child-task tracker, so tracking the callback itself adds no mutation
    # safety.  Worse, a late/duplicate result-publication exception was
    # classified as detached action work and caused completed recursive
    # sessions to restore an hours-old checkpoint.  Mark it as event-loop
    # plumbing just like MiniSession's own daemon-worker bridge.
    publish_result = mark_runtime_owned_callback(publish_result)

    def runner() -> None:
        try:
            value = operation(*args, **kwargs)
        except BaseException as exc:
            try:
                loop.call_soon_threadsafe(publish_result, None, exc)
            except RuntimeError:
                pass
        else:
            try:
                loop.call_soon_threadsafe(publish_result, value)
            except RuntimeError:
                if inspect.iscoroutine(value):
                    value.close()

    thread = threading.Thread(target=runner, daemon=True)
    thread.start()
    return future


def _retry_cancel_abandoned_task(
    task: "asyncio.Future[Any]", attempts_left: int
) -> None:
    """Retry a detached cancellation without putting it on the caller's path."""

    if task.done() or attempts_left <= 0:
        return
    task.cancel()
    try:
        task.get_loop().call_later(
            _CANCELLATION_RETRY_DELAY_S,
            _retry_cancel_abandoned_task,
            task,
            attempts_left - 1,
        )
    except (AttributeError, RuntimeError):
        pass


_consume_task_exception = mark_runtime_owned_callback(
    _consume_task_exception
)
_release_abandoned_task = mark_runtime_owned_callback(
    _release_abandoned_task
)
_retry_cancel_abandoned_task = mark_runtime_owned_callback(
    _retry_cancel_abandoned_task
)


def detach_task_from_loop_shutdown(task: "asyncio.Future[Any]") -> bool:
    """Stop ``asyncio.run`` from joining a revoked cancellation-resistant task.

    Python's runner cancels and gathers every registered task before closing
    the loop. A task that already ignored cancellation would otherwise keep
    shutdown open forever. The task can remain scheduled while this loop is
    live; it is no longer a shutdown join target after publication authority
    was revoked.
    """

    detached = False
    candidates = [task]
    source = getattr(task, "_mini_source_task", None)
    if isinstance(source, asyncio.Future) and source is not task:
        candidates.append(source)
    unregister = getattr(asyncio.tasks, "_unregister_task", None)
    for candidate in candidates:
        if not isinstance(candidate, asyncio.Task):
            continue
        try:
            if callable(unregister):
                unregister(candidate)
            else:  # pragma: no cover - current supported CPython exposes helper.
                scheduled = getattr(asyncio.tasks, "_scheduled_tasks", None)
                discard = getattr(scheduled, "discard", None)
                if not callable(discard):
                    continue
                discard(candidate)
            setattr(candidate, "_log_destroy_pending", False)
            detached = True
        except BaseException:
            continue
    return detached


def _cancel_and_abandon(
    task: "asyncio.Future[Any]",
    *,
    operation_label: str = "deadline_operation",
    timeout_s: Optional[float] = None,
    deadline_expired: bool = True,
    invalidate_bound_scope: bool = True,
    operation_ownership: Literal["transaction_state", "result_only"] = (
        "transaction_state"
    ),
) -> None:
    """Cancel now and observe late completion without extending the deadline.

    Cleanup deliberately never awaits the cancelled task: ``wait_for`` style
    cancellation draining lets a cancellation-suppressing adapter consume the
    controller's entire remaining wall budget.  The retry callbacks are only
    best-effort hygiene; a late value remains unobservable either way.
    """

    if task.done():
        return
    # Mutation-owning work is cancelled repeatedly below because stopping its
    # writes is part of the transaction barrier.  Result-only work has already
    # lost publication authority; once cancellation has reached it, injecting
    # another CancelledError can interrupt its adapter/resource cleanup and
    # release a serialization lease before cleanup actually settles.
    cancelling = getattr(task, "cancelling", None)
    cancellation_already_requested = bool(
        callable(cancelling) and int(cancelling() or 0) > 0
    )
    if (
        operation_ownership == "transaction_state"
        or not cancellation_already_requested
    ):
        task.cancel()
    _ABANDONED_DEADLINE_TASKS.add(task)
    scope_id = _DEADLINE_OPERATION_SCOPE.get()
    _ABANDONED_DEADLINE_TASK_SCOPES[task] = scope_id
    _ABANDONED_DEADLINE_TASK_OWNERSHIP[task] = operation_ownership
    if operation_ownership == "result_only":
        _RESULT_ONLY_DEADLINE_TASKS.add(task)
    if scope_id and invalidate_bound_scope:
        # A task can suppress cancellation, mutate its owner, and finish before
        # the owner reaches its quiescence barrier.  The live-task set alone
        # therefore cannot prove that a dispatch was mutation-isolated.  Keep
        # a per-scope monotone incident count until the dispatch consumes it.
        _ABANDONED_DEADLINE_SCOPE_COUNTS[scope_id] = (
            int(_ABANDONED_DEADLINE_SCOPE_COUNTS.get(scope_id, 0) or 0) + 1
        )
    task.add_done_callback(_release_abandoned_task)
    detach_task_from_loop_shutdown(task)
    if operation_ownership == "transaction_state":
        _retry_cancel_abandoned_task(task, _CANCELLATION_RETRY_ATTEMPTS)
    if deadline_expired:
        _LOGGER.warning(
            "deadline expired: operation=%s timeout_s=%s; operation cancelled "
            "and detached, late result discarded",
            str(operation_label or "deadline_operation"),
            ("disabled" if timeout_s is None else f"{max(0.0, float(timeout_s)):.3f}"),
        )
    else:
        _LOGGER.info(
            "operation cancelled by caller: operation=%s; child detached, "
            "late result discarded",
            str(operation_label or "deadline_operation"),
        )


async def _cancel_join_or_abandon_for_timeout(
    task: "asyncio.Future[Any]",
    *,
    operation_label: str,
    timeout_s: Optional[float],
    operation_ownership: Literal["transaction_state", "result_only"],
) -> bool:
    """Cancel an owned operation, briefly join it, then classify authority.

    Expected bounded failures must remain ordinary ``TimeoutError`` so their
    callers can durably advance cursors and retry other mathematics. Only a
    child that survives a small, repeated cancellation join loses the owning
    dispatch's exclusive mutation authority and needs transaction abort.
    """

    if task.done():
        return False
    task.cancel()
    done, _pending = await asyncio.wait(
        {task},
        timeout=(
            _OWNED_CANCELLATION_JOIN_TIMEOUT_S
            if operation_ownership == "transaction_state"
            else _CANCELLATION_RETRY_DELAY_S
        ),
    )
    if task in done:
        _consume_task_exception(task)
        _LOGGER.warning(
            "deadline expired: operation=%s timeout_s=%s; operation "
            "cancelled and joined, late result discarded",
            str(operation_label or "deadline_operation"),
            (
                "disabled"
                if timeout_s is None
                else f"{max(0.0, float(timeout_s)):.3f}"
            ),
        )
        # A child that accepted cancellation is an ordinary TimeoutError.
        # Treating a successful join as detachment recycled finished proofs
        # after the 1s Lean-lock wait joined.
        return False
    _cancel_and_abandon(
        task,
        operation_label=operation_label,
        timeout_s=timeout_s,
        invalidate_bound_scope=(operation_ownership == "transaction_state"),
        operation_ownership=operation_ownership,
    )
    return True


async def drain_abandoned_deadline_tasks(
    *,
    timeout_s: float = 5.0,
    scope_id: Optional[str] = None,
) -> dict[str, int]:
    """Join detached deadline tasks so their side effects stop mutating state.

    This is the session cancellation barrier's drain step: it runs only at
    teardown, after new-work admission is closed. Late results stay discarded
    (nothing here makes them observable); the drain only bounds WHEN detached
    work stops touching the filesystem and providers. Tasks that outlive the
    timeout remain detached — process-level teardown is the backstop.
    """

    loop = asyncio.get_running_loop()
    selected_scope = None if scope_id is None else str(scope_id or "").strip()
    pending = [
        task
        for task in list(_ABANDONED_DEADLINE_TASKS)
        if not task.done()
        and task.get_loop() is loop
        and (
            selected_scope is None
            or _ABANDONED_DEADLINE_TASK_SCOPES.get(task, "") == selected_scope
        )
        and (
            selected_scope is None
            or _ABANDONED_DEADLINE_TASK_OWNERSHIP.get(
                task,
                "transaction_state",
            )
            == "transaction_state"
        )
    ]
    if not pending:
        return {"drained": 0, "still_pending": 0}
    for task in pending:
        task.cancel()
    done, still_pending = await asyncio.wait(
        pending,
        timeout=max(0.0, float(timeout_s)),
    )
    if still_pending:
        for task in still_pending:
            detach_task_from_loop_shutdown(task)
        _LOGGER.warning(
            "cancellation barrier: %d detached deadline task(s) still pending "
            "after %.3fs drain; leaving detached for process-level teardown",
            len(still_pending),
            max(0.0, float(timeout_s)),
        )
    return {"drained": len(done), "still_pending": len(still_pending)}


def abandoned_deadline_scope_count(
    scope_id: str,
    *,
    consume: bool = False,
) -> int:
    """Return deadline detachments observed in one scheduler dispatch scope.

    Completed detached tasks are deliberately retained in this counter until
    the owner reaches its commit barrier.  ``consume`` releases the unique
    dispatch id after the owner has either committed or rolled back.
    """

    clean = str(scope_id or "").strip()
    if not clean:
        return 0
    if consume:
        return int(_ABANDONED_DEADLINE_SCOPE_COUNTS.pop(clean, 0) or 0)
    return int(_ABANDONED_DEADLINE_SCOPE_COUNTS.get(clean, 0) or 0)


def deadline_task_is_result_only(task: "asyncio.Future[Any]") -> bool:
    """Whether ``task`` is an audited result-only operation or descendant.

    The MiniSession child tracker uses this exact registry instead of trying
    to infer ownership from coroutine names. Result-only tails retain their
    adapter/resource lease, but never receive staged or live transaction state
    and therefore do not participate in mutation quiescence.
    """

    return bool(task in _RESULT_ONLY_DEADLINE_TASKS)


def create_result_only_deadline_task(
    awaitable: Awaitable[T],
) -> "asyncio.Future[T]":
    """Create an audited result-only task whose descendants share its scope.

    Capability adapters such as Lean may create pipe-reader and reap tasks.
    Those descendants own only the adapter result/resource lease, never the
    caller's proof transaction.  Bind the scope at task construction so the
    MiniSession router can authenticate each exact descendant it observes.
    """

    token = _RESULT_ONLY_DEADLINE_DESCENDANT_SCOPE.set(True)
    try:
        task = asyncio.ensure_future(awaitable)
    finally:
        _RESULT_ONLY_DEADLINE_DESCENDANT_SCOPE.reset(token)
    _RESULT_ONLY_DEADLINE_TASKS.add(task)
    return task


def register_inherited_result_only_deadline_task(
    task: "asyncio.Future[Any]",
) -> bool:
    """Register an exact task created inside an audited result-only scope."""

    if not _RESULT_ONLY_DEADLINE_DESCENDANT_SCOPE.get():
        return False
    _RESULT_ONLY_DEADLINE_TASKS.add(task)
    return True


async def await_with_strict_deadline(
    awaitable: Awaitable[T],
    *,
    timeout_s: Optional[float] = None,
    deadline_monotonic: float = 0.0,
    operation_label: str = "deadline_operation",
    operation_ownership: Literal["transaction_state", "result_only"] = (
        "transaction_state"
    ),
) -> T:
    """Await an operation without accepting or waiting for a late result.

    ``timeout_s`` bounds this operation; ``deadline_monotonic`` additionally
    bounds it by the controller's absolute clock. On expiry, the operation is
    cancelled and detached so an adapter that suppresses cancellation cannot
    delay the controller or make its eventual result observable. A coroutine
    that suppresses cancellation forever cannot be force-killed by asyncio;
    callers that require process-level teardown must isolate such adapters in
    a process boundary.
    """

    if operation_ownership not in {"transaction_state", "result_only"}:
        if inspect.iscoroutine(awaitable):
            awaitable.close()
        raise ValueError(f"invalid deadline operation ownership: {operation_ownership}")
    task = asyncio.ensure_future(awaitable)
    task.add_done_callback(_consume_task_exception)
    timeout_cleanup_completed = False
    effective_timeout_s: Optional[float] = None
    try:
        expires_at: Optional[float] = None
        now = time.monotonic()
        if timeout_s is not None:
            timeout = max(0.0, float(timeout_s))
            if timeout <= 0.0:
                effective_timeout_s = 0.0
                detached = await _cancel_join_or_abandon_for_timeout(
                    task,
                    operation_label=operation_label,
                    timeout_s=effective_timeout_s,
                    operation_ownership=operation_ownership,
                )
                timeout_cleanup_completed = True
                _raise_deadline_expired_for_scope(
                    detached=(detached and operation_ownership == "transaction_state")
                )
            expires_at = now + timeout
        if deadline_monotonic > 0.0:
            deadline = float(deadline_monotonic)
            if deadline <= now:
                effective_timeout_s = 0.0
                detached = await _cancel_join_or_abandon_for_timeout(
                    task,
                    operation_label=operation_label,
                    timeout_s=effective_timeout_s,
                    operation_ownership=operation_ownership,
                )
                timeout_cleanup_completed = True
                _raise_deadline_expired_for_scope(
                    detached=(detached and operation_ownership == "transaction_state")
                )
            expires_at = deadline if expires_at is None else min(expires_at, deadline)
        if expires_at is None:
            # Keep caller cancellation at the controller boundary. A direct
            # ``await task`` injects cancellation into the child and lets a
            # cancellation-suppressing adapter consume the caller's stop by
            # returning normally. Shield first; the outer handler then owns
            # cancellation, detachment accounting, and rollback.
            return await asyncio.shield(task)
        effective_timeout_s = max(0.0, expires_at - now)
        remaining = expires_at - time.monotonic()
        if remaining <= 0.0:
            detached = await _cancel_join_or_abandon_for_timeout(
                task,
                operation_label=operation_label,
                timeout_s=effective_timeout_s,
                operation_ownership=operation_ownership,
            )
            timeout_cleanup_completed = True
            _raise_deadline_expired_for_scope(
                detached=(detached and operation_ownership == "transaction_state")
            )
        done, _pending = await asyncio.wait({task}, timeout=remaining)
        if task not in done:
            detached = await _cancel_join_or_abandon_for_timeout(
                task,
                operation_label=operation_label,
                timeout_s=effective_timeout_s,
                operation_ownership=operation_ownership,
            )
            timeout_cleanup_completed = True
            _raise_deadline_expired_for_scope(
                detached=(detached and operation_ownership == "transaction_state")
            )
        try:
            result = task.result()
        except asyncio.CancelledError as exc:
            raise asyncio.TimeoutError from exc
        # A task can finish after its wait wakes but before the result is read.
        if time.monotonic() >= expires_at:
            # The task is already done, so ``_cancel_and_abandon`` would
            # intentionally ignore it.  Its writes nevertheless occurred
            # after authority expired.  Publish the same per-scope integrity
            # incident used for a live detachment so the owning transaction
            # rolls those writes back at its commit barrier.
            scope_id = _DEADLINE_OPERATION_SCOPE.get()
            if scope_id and operation_ownership == "transaction_state":
                _ABANDONED_DEADLINE_SCOPE_COUNTS[scope_id] = (
                    int(_ABANDONED_DEADLINE_SCOPE_COUNTS.get(scope_id, 0) or 0)
                    + 1
                )
            _raise_deadline_expired_for_scope(
                detached=(operation_ownership == "transaction_state")
            )
        return result
    except BaseException as exc:
        if not timeout_cleanup_completed and not task.done():
            _cancel_and_abandon(
                task,
                operation_label=operation_label,
                timeout_s=effective_timeout_s,
                deadline_expired=not isinstance(exc, asyncio.CancelledError),
                invalidate_bound_scope=(operation_ownership == "transaction_state"),
                operation_ownership=operation_ownership,
            )
        raise


async def invoke_with_strict_deadline(
    operation: Any,
    *args: Any,
    guard_timeout_s: Optional[float] = None,
    guard_deadline_monotonic: float = 0.0,
    operation_ownership: Literal["transaction_state", "result_only"] = (
        "transaction_state"
    ),
    **kwargs: Any,
) -> Any:
    """Invoke sync or async external code under the same deadline contract.

    A synchronous adapter runs in the default worker pool so it cannot block
    the event loop past the wall deadline. The worker itself cannot be killed
    by Python, but its late value is never made observable by the caller.
    """

    if guard_timeout_s is not None and float(guard_timeout_s) <= 0.0:
        raise asyncio.TimeoutError
    if guard_deadline_monotonic > 0.0 and time.monotonic() >= float(
        guard_deadline_monotonic
    ):
        raise asyncio.TimeoutError

    expires_at = (
        time.monotonic() + float(guard_timeout_s)
        if guard_timeout_s is not None
        else 0.0
    )
    if guard_deadline_monotonic > 0.0:
        expires_at = (
            float(guard_deadline_monotonic)
            if expires_at <= 0.0
            else min(expires_at, float(guard_deadline_monotonic))
        )

    def remaining_timeout() -> Optional[float]:
        if expires_at <= 0.0:
            return None
        return max(0.0, expires_at - time.monotonic())

    if inspect.iscoroutinefunction(operation):
        result = operation(*args, **kwargs)
    else:
        result = await await_with_strict_deadline(
            _run_sync_in_daemon(operation, *args, **kwargs),
            timeout_s=remaining_timeout(),
            deadline_monotonic=guard_deadline_monotonic,
            operation_ownership=operation_ownership,
        )
    if inspect.isawaitable(result):
        return await await_with_strict_deadline(
            result,
            timeout_s=remaining_timeout(),
            deadline_monotonic=guard_deadline_monotonic,
            operation_ownership=operation_ownership,
        )
    if guard_deadline_monotonic > 0.0 and time.monotonic() >= float(
        guard_deadline_monotonic
    ):
        raise asyncio.TimeoutError
    return result
