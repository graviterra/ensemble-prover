"""Runtime context shared across search tasks and writeback surfaces."""

from __future__ import annotations

import asyncio
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
import functools
from functools import wraps
import inspect
import logging
import threading
from typing import Any, Callable, Iterator, Optional, TypeVar, cast
import weakref


logger = logging.getLogger(__name__)

_CallbackT = TypeVar("_CallbackT", bound=Callable[..., Any])
_RUNTIME_LIFECYCLE_CALLBACK_ACTIVE: ContextVar[bool] = ContextVar(
    "ensemble_prover_runtime_lifecycle_callback_active",
    default=False,
)
_TRANSPORT_RECEIPT_OBSERVER_TASKS: "weakref.WeakSet[asyncio.Task[Any]]" = (
    weakref.WeakSet()
)
_TRANSPORT_RECEIPT_OBSERVER_TASKS_LOCK = threading.RLock()
_TRANSPORT_REQUEST_TASKS: "weakref.WeakSet[asyncio.Future[Any]]" = (
    weakref.WeakSet()
)
_TRANSPORT_REQUEST_TASKS_LOCK = threading.RLock()
_TRANSPORT_REQUEST_DESCENDANT_SCOPE: ContextVar[bool] = ContextVar(
    "ensemble_prover_transport_request_descendant_scope",
    default=False,
)
_RUNTIME_LIFECYCLE_CALLBACKS: "weakref.WeakSet[Callable[..., Any]]" = (
    weakref.WeakSet()
)
_AUTHENTICATED_RUNTIME_LIFECYCLE_CALLBACKS: (
    "weakref.WeakSet[Callable[..., Any]]"
) = weakref.WeakSet()
_RUNTIME_LIFECYCLE_CALLBACKS_LOCK = threading.RLock()
# Callback exemption is an exact capability list, never module provenance.
# ``future`` adapters may capture only the private Future they resolve; all
# other admitted functions are non-capturing exception/registry observers.
_TRUSTED_RUNTIME_CALLBACKS = {
    ("ensemble_prover.deadline_guard", "_consume_task_exception"): "none",
    ("ensemble_prover.deadline_guard", "_release_abandoned_task"): "none",
    ("ensemble_prover.deadline_guard", "_retry_cancel_abandoned_task"): "none",
    ("ensemble_prover.lean_runner", "_consume_future_exception"): "none",
    (
        "ensemble_prover.mathematical_retrieval.async_runtime",
        "_consume_task_result",
    ): "none",
    ("ensemble_prover.models", "_consume_task_exception"): "none",
    ("ensemble_prover.persistent_verifier", "_consume_task_exception"): "none",
    (
        "ensemble_prover.mini_session.factory",
        "_consume_sample_task_exception",
    ): "none",
    ("ensemble_prover.search", "_consume_future_exception"): "none",
    ("ensemble_prover.subprocess_cleanup", "_consume_future_exception"): "none",
    (
        "ensemble_prover.deadline_guard",
        "_run_sync_in_daemon.<locals>.publish_result",
    ): "future",
    (
        "ensemble_prover.mini_session.session",
        "_run_operation_sync_in_daemon.<locals>.publish_result",
    ): "future",
    (
        "ensemble_prover.search",
        "_await_with_hard_timeout.<locals>._mark_late_result_discarded",
    ): "hard_timeout_lease",
    (
        "ensemble_prover.mini_formal_state_search",
        "_once_only_lock_release.<locals>.release_lock_once",
    ): "lock_release",
    (
        "ensemble_prover.mini_formal_state_search",
        "_late_tail_clear_callback.<locals>.clear_if_current",
    ): "late_tail_clear",
    (
        "ensemble_prover.mini_session.turn.tool_loop",
        "_run_sync_abandonment_safe.<locals>.publish_result",
    ): "future",
    (
        "ensemble_prover.mini_session.turn.tool_loop",
        "_call_llm_with_tools_one_round_impl.<locals>."
        "await_with_elapsed_budget.<locals>.consume_late_task_result",
    ): "none",
    (
        "ensemble_prover.mini_session.actions.conversation_turn",
        "_run_policy_helper_quarantine.<locals>.consume_late_salvage_result",
    ): "none",
}


def runtime_lifecycle_callback_active() -> bool:
    """Whether task observation is runtime bookkeeping, not an owner join."""

    return bool(_RUNTIME_LIFECYCLE_CALLBACK_ACTIVE.get())


def create_runtime_lifecycle_task(
    awaitable: Any,
    *,
    name: Optional[str] = None,
) -> "asyncio.Task[Any]":
    """Create ordinary lifecycle work without transaction exemption.

    This compatibility helper deliberately carries no MiniSession ownership
    privilege. Code invoked by an action remains action-owned even if it calls
    this public function. The sole exempt lifecycle is the authenticated
    transport-receipt observer constructed by the private factory below.
    """

    return asyncio.create_task(awaitable, name=name)


def _create_transport_receipt_observer_task(
    awaitable: Any,
    *,
    name: str,
) -> "asyncio.Task[Any]":
    """Compatibility shim with no transaction ownership privilege.

    The real OpenAI observer is created in ``models`` and admitted only after
    its exact coroutine code is authenticated by the registry below. Merely
    importing and calling this underscore helper cannot mint that ownership.
    """

    return asyncio.create_task(awaitable, name=name)


def _transport_receipt_observer_coroutine_authenticated(
    task: "asyncio.Task[Any]",
) -> bool:
    candidates = [task]
    source = getattr(task, "_mini_source_task", None)
    if isinstance(source, asyncio.Task) and source is not task:
        candidates.append(source)
    for candidate in candidates:
        try:
            coroutine = candidate.get_coro()
        except (AttributeError, RuntimeError):
            continue
        code = getattr(coroutine, "cr_code", None)
        filename = str(getattr(code, "co_filename", "") or "").replace(
            "\\", "/"
        )
        qualname = str(getattr(code, "co_qualname", "") or "")
        if (
            filename.endswith("/ensemble_prover/models.py")
            and qualname.endswith(
                "OpenAICompatClient._post_with_retry."
                "<locals>._observe_transport_receipt"
            )
        ):
            return True
    return False


def register_transport_receipt_observer_task(
    task: "asyncio.Task[Any]",
) -> None:
    """Register only the exact OpenAI transport observer coroutine."""

    if not _transport_receipt_observer_coroutine_authenticated(task):
        raise PermissionError(
            "runtime receipt ownership requires the exact OpenAI observer"
        )
    with _TRANSPORT_RECEIPT_OBSERVER_TASKS_LOCK:
        _TRANSPORT_RECEIPT_OBSERVER_TASKS.add(task)
        source = getattr(task, "_mini_source_task", None)
        if isinstance(source, asyncio.Task):
            _TRANSPORT_RECEIPT_OBSERVER_TASKS.add(source)


def transport_receipt_observer_task_owned(task: "asyncio.Future[Any]") -> bool:
    """Return whether ``task`` has exact authenticated receipt ownership."""

    with _TRANSPORT_RECEIPT_OBSERVER_TASKS_LOCK:
        return task in _TRANSPORT_RECEIPT_OBSERVER_TASKS


def transport_receipt_observer_current_task_owned() -> bool:
    """Check exact current-task ownership without propagating to descendants."""

    # ``loop.call_soon_threadsafe`` is also invoked by asyncio's subprocess
    # waitpid helper threads.  Those threads have no running event loop and
    # therefore no current Task; absence of a Task is simply absence of this
    # narrowly authenticated ownership, not an exceptional condition.
    try:
        task = asyncio.current_task()
    except RuntimeError:
        return False
    return bool(
        task is not None and transport_receipt_observer_task_owned(task)
    )


def _transport_request_registrar_authenticated() -> bool:
    """Admit only the OpenAI post retry that owns the concrete HTTP task."""

    frame = inspect.currentframe()
    try:
        while frame is not None:
            filename = str(frame.f_code.co_filename or "").replace("\\", "/")
            qualname = str(
                getattr(frame.f_code, "co_qualname", frame.f_code.co_name) or ""
            )
            if (
                filename.endswith("/ensemble_prover/models.py")
                and "OpenAICompatClient._post_with_retry" in qualname
            ):
                return True
            frame = frame.f_back
    finally:
        del frame
    return False


def register_transport_request_task(task: "asyncio.Future[Any]") -> None:
    """Register the concrete HTTP transport task for mutation-boundary exemption."""

    if not _transport_request_registrar_authenticated():
        raise PermissionError(
            "runtime request ownership requires OpenAICompatClient._post_with_retry"
        )
    with _TRANSPORT_REQUEST_TASKS_LOCK:
        _TRANSPORT_REQUEST_TASKS.add(task)
        source = getattr(task, "_mini_source_task", None)
        if isinstance(source, asyncio.Future):
            _TRANSPORT_REQUEST_TASKS.add(source)


@contextmanager
def transport_request_descendant_scope() -> Iterator[None]:
    """Mark HTTP descendants created under an in-flight provider post."""

    token = _TRANSPORT_REQUEST_DESCENDANT_SCOPE.set(True)
    try:
        yield
    finally:
        _TRANSPORT_REQUEST_DESCENDANT_SCOPE.reset(token)


def register_inherited_transport_request_task(
    task: "asyncio.Future[Any]",
) -> bool:
    """Register an exact task created inside an audited transport request."""

    if not _TRANSPORT_REQUEST_DESCENDANT_SCOPE.get():
        return False
    with _TRANSPORT_REQUEST_TASKS_LOCK:
        _TRANSPORT_REQUEST_TASKS.add(task)
        source = getattr(task, "_mini_source_task", None)
        if isinstance(source, asyncio.Future):
            _TRANSPORT_REQUEST_TASKS.add(source)
    return True


def transport_request_task_owned(task: "asyncio.Future[Any]") -> bool:
    """Return whether ``task`` is the concrete in-flight HTTP transport."""

    with _TRANSPORT_REQUEST_TASKS_LOCK:
        return task in _TRANSPORT_REQUEST_TASKS


def detach_future_from_asyncio_run_shutdown(
    future: "asyncio.Future[Any]",
) -> None:
    """Keep a cancellation-resistant transport tail from hosting ``asyncio.run``.

    HTTP/anyio adapters can swallow cancellation and survive ``aclose``.  The
    worker watchdog then kills the process during loop shutdown.  Drop only
    shutdown ownership; the task may still unwind in the background.
    """

    def observe(completed: "asyncio.Future[Any]") -> None:
        if completed.cancelled():
            return
        try:
            completed.exception()
        except BaseException:
            pass

    candidates = [future]
    source = getattr(future, "_mini_source_task", None)
    if isinstance(source, asyncio.Future) and source is not future:
        candidates.append(source)
    for candidate in candidates:
        try:
            candidate.add_done_callback(observe)
        except (AttributeError, RuntimeError):
            pass
        if not isinstance(candidate, asyncio.Task):
            continue
        unregister = getattr(asyncio.tasks, "_unregister_task", None)
        try:
            if callable(unregister):
                unregister(candidate)
            else:
                scheduled = getattr(asyncio.tasks, "_scheduled_tasks", None)
                discard = getattr(scheduled, "discard", None)
                if callable(discard):
                    discard(candidate)
            setattr(candidate, "_log_destroy_pending", False)
        except BaseException:
            continue


def is_runtime_owned_callback(callback: Callable[..., Any]) -> bool:
    """Check authenticated identity provenance for one lifecycle callback."""

    with _RUNTIME_LIFECYCLE_CALLBACKS_LOCK:
        return callback in _AUTHENTICATED_RUNTIME_LIFECYCLE_CALLBACKS


def _runtime_callback_has_internal_provenance(callback: Callable[..., Any]) -> bool:
    """Authenticate one exact, capability-confined lifecycle adapter."""

    target: Any = callback
    # Bound methods and partials can capture MiniSession even when their
    # underlying function was defined in an audited module.
    if isinstance(target, functools.partial):
        return False
    bound_to = getattr(target, "__self__", None)
    if bound_to is not None:
        # One exception: a built-in set mutator bound to a plain set is
        # runtime task-set bookkeeping. It cannot reach MiniSession state --
        # it only removes an entry from a set it is already bound to -- and it
        # is the shape this function's own docstring calls out. Dropping it
        # after a boundary closes leaks the registry entry it exists to clear.
        return (
            type(bound_to) is set
            and getattr(target, "__name__", "") in {"discard", "remove"}
        )
    function = target
    if not inspect.isfunction(function):
        return False
    module = inspect.getmodule(function)
    module_name = str(getattr(module, "__name__", "") or "")
    policy = _TRUSTED_RUNTIME_CALLBACKS.get(
        (module_name, str(getattr(function, "__qualname__", "") or ""))
    )
    if policy is None:
        return False
    try:
        source_file = inspect.getsourcefile(function)
        module_file = inspect.getsourcefile(module)
    except (OSError, TypeError):
        return False
    if not (source_file and module_file and source_file == module_file):
        return False
    closure = tuple(function.__closure__ or ())
    if policy == "none":
        return not closure
    try:
        captured = tuple(cell.cell_contents for cell in closure)
    except ValueError:
        return False
    if policy == "future":
        return bool(captured) and all(
            isinstance(value, asyncio.Future) for value in captured
        )
    if policy == "hard_timeout_lease":
        return bool(captured) and all(
            isinstance(value, HardTimeoutLease) for value in captured
        )
    if policy == "lock_release":
        # Exactly one lock plus one list acting as the once-only flag. Nothing
        # else may be captured, so the callback cannot reach MiniSession state.
        return bool(captured) and all(
            isinstance(value, (asyncio.Lock, list)) for value in captured
        )
    if policy == "late_tail_clear":
        # Exactly the per-adapter lock plus the late-tail state dict. Nothing
        # else may be captured, so the callback cannot reach MiniSession state.
        return (
            len(captured) == 2
            and any(isinstance(value, asyncio.Lock) for value in captured)
            and any(isinstance(value, dict) for value in captured)
        )
    return False


def mark_runtime_owned_callback(
    callback: _CallbackT,
    *,
    expect_unauthenticated: bool = False,
) -> _CallbackT:
    """Mark a lifecycle callback that cannot access MiniSession state.

    MiniSession treats callbacks scheduled by an action as transaction-owned
    by default. Infrastructure may opt out only for narrow lifecycle callbacks
    (exception consumption, lock release, runtime task-set cleanup) whose sole
    authority is an external adapter or the task/future passed to them.

    Python built-in bound methods such as ``set.discard`` do not allow custom
    attributes, so return a small marked wrapper for those shapes.
    """

    with _RUNTIME_LIFECYCLE_CALLBACKS_LOCK:
        if callback in _RUNTIME_LIFECYCLE_CALLBACKS:
            return callback
    authenticated = _runtime_callback_has_internal_provenance(callback)

    @wraps(callback)
    def runtime_callback(*args: Any, **kwargs: Any) -> Any:
        token = _RUNTIME_LIFECYCLE_CALLBACK_ACTIVE.set(True)
        try:
            return callback(*args, **kwargs)
        finally:
            _RUNTIME_LIFECYCLE_CALLBACK_ACTIVE.reset(token)

    if not authenticated and not expect_unauthenticated:
        # Fail loud. Only the authenticated set is consulted by
        # ``is_runtime_owned_callback``, so an unauthenticated marking is a
        # silent no-op: the caller believes its lifecycle callback is exempt
        # while MiniSession still treats it as droppable action work and
        # rewrites it to a no-op after the boundary closes. That is how lock
        # releases and future resolutions went missing, each time as a
        # permanent 0%-CPU stall with no error and no log line.
        logger.error(
            "mark_runtime_owned_callback: %s.%s is not in "
            "_TRUSTED_RUNTIME_CALLBACKS; it will still be dropped after an "
            "action boundary closes. Add it to the allowlist or the callback "
            "will silently never run.",
            getattr(callback, "__module__", "?"),
            getattr(callback, "__qualname__", repr(callback)),
        )

    with _RUNTIME_LIFECYCLE_CALLBACKS_LOCK:
        _RUNTIME_LIFECYCLE_CALLBACKS.add(runtime_callback)
        if authenticated:
            _AUTHENTICATED_RUNTIME_LIFECYCLE_CALLBACKS.add(runtime_callback)
    return cast(_CallbackT, runtime_callback)


@dataclass
class HardTimeoutLease:
    """Shared cancellation lease for one hard-timeout-wrapped task.

    The lease is intentionally mutable and stored in a ContextVar before task
    creation. If the task outlives its cancellation grace, writeback paths can
    observe ``abandoned=True`` and refuse to mutate shared solver state.
    """

    timeout_s: float
    cancel_grace_s: float
    cancel_requested: bool = False
    abandoned: bool = False
    recovered_after_timeout: bool = False
    late_result_discarded: bool = False


class RuntimeCapabilityRevokedError(RuntimeError):
    """A detached runtime tail attempted to use revoked shared authority."""

    mini_runtime_capability_revoked = True


_CURRENT_HARD_TIMEOUT_LEASE: ContextVar[Optional[HardTimeoutLease]] = ContextVar(
    "ensemble_prover_current_hard_timeout_lease",
    default=None,
)


def current_hard_timeout_lease() -> Optional[HardTimeoutLease]:
    return _CURRENT_HARD_TIMEOUT_LEASE.get()


def hard_timeout_writeback_allowed() -> bool:
    lease = current_hard_timeout_lease()
    return lease is None or not bool(lease.abandoned)


def require_hard_timeout_capability_active(operation: str) -> None:
    """Reject new shared work after the current hard-timeout lease is fenced."""

    if hard_timeout_writeback_allowed():
        return
    raise RuntimeCapabilityRevokedError(
        f"runtime capability was revoked before {str(operation or 'operation')}"
    )


def hard_timeout_metric_write_allowed(key: object) -> bool:
    if hard_timeout_writeback_allowed():
        return True
    return str(key or "").startswith("search_hard_timeout_")
