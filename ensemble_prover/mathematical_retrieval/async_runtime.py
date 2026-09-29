"""Strict async boundaries for synchronous or cancellation-resistant work."""

from __future__ import annotations

import asyncio
import contextvars
import threading
import time
from collections.abc import Awaitable, Callable
from typing import Any, TypeVar

from ..runtime_context import mark_runtime_owned_callback


_T = TypeVar("_T")
_WORKER_SLOTS = threading.BoundedSemaphore(8)


class RetrievalWorkerCapacityError(RuntimeError):
    """Raised when every bounded detached retrieval worker is occupied."""


def _consume_task_result(task: asyncio.Task[Any]) -> None:
    if task.cancelled():
        return
    try:
        task.exception()
    except (asyncio.CancelledError, Exception):
        pass


async def await_strict_timeout(
    awaitable: Awaitable[_T],
    *,
    timeout_s: float,
) -> _T:
    """Return at the timeout even when the awaited adapter ignores cancellation."""

    deadline = time.monotonic() + max(0.0, float(timeout_s))
    task = asyncio.ensure_future(awaitable)
    try:
        done, _pending = await asyncio.wait(
            {task},
            timeout=max(0.0, deadline - time.monotonic()),
        )
    except BaseException:
        task.cancel()
        task.add_done_callback(mark_runtime_owned_callback(_consume_task_result))
        raise
    if task not in done or time.monotonic() >= deadline:
        task.cancel()
        task.add_done_callback(mark_runtime_owned_callback(_consume_task_result))
        raise TimeoutError("retrieval operation timed out")
    return task.result()


async def run_sync_abandonment_safe(
    call: Callable[[], _T],
    *,
    timeout_s: float,
    deadline_exhausted: Callable[[], bool] | None = None,
) -> _T:
    """Run bounded daemon work without tying loop shutdown to a stuck thread."""

    if not _WORKER_SLOTS.acquire(blocking=False):
        raise RetrievalWorkerCapacityError(
            "retrieval worker capacity exhausted"
        )
    loop = asyncio.get_running_loop()
    future: asyncio.Future[_T] = loop.create_future()
    submission_context = contextvars.copy_context()

    def publish(ok: bool, value: Any) -> None:
        if future.done():
            return
        if ok:
            future.set_result(value)
        else:
            future.set_exception(value)

    def worker() -> None:
        try:
            try:
                # Match asyncio.to_thread: the synchronous adapter executes in
                # the exact submitting Context, not merely its completion
                # callback. This also gives each parallel sample the correct
                # operation-owner token inside retrieval code itself.
                outcome = (True, submission_context.run(call))
            except BaseException as exc:
                outcome = (False, exc)
        finally:
            _WORKER_SLOTS.release()
        if loop.is_closed():
            return
        try:
            # Worker threads do not inherit ContextVars.  Preserve the exact
            # submitting operation so a loop shared by parallel MiniSession
            # samples can route this completion to its own transaction
            # tracker instead of treating it as an ambiguous external write.
            loop.call_soon_threadsafe(
                publish,
                *outcome,
                context=submission_context,
            )
        except RuntimeError:
            pass

    try:
        # Construct AND start inside the release guard: if the Thread(...)
        # constructor itself raises (e.g. MemoryError / OS thread limit), the
        # already-acquired worker slot must be released, or it leaks forever.
        thread = threading.Thread(
            target=worker,
            name="mini-mathematical-retrieval",
            daemon=True,
        )
        thread.start()
    except BaseException:
        _WORKER_SLOTS.release()
        raise

    def _exhausted() -> bool:
        if deadline_exhausted is None:
            return False
        try:
            return bool(deadline_exhausted())
        except Exception:
            return True

    deadline = time.monotonic() + max(0.0, float(timeout_s))
    try:
        while True:
            if _exhausted():
                future.cancel()
                raise TimeoutError("retrieval deadline exhausted")
            remaining = deadline - time.monotonic()
            if remaining <= 0.0:
                future.cancel()
                raise TimeoutError("retrieval operation timed out")
            done, _pending = await asyncio.wait(
                {future},
                timeout=min(0.02, remaining),
            )
            if future in done:
                # Re-check BOTH deadlines before accepting the result: the
                # callback (or wall clock) may have expired during the wait even
                # though the work happened to finish in the same poll.
                if _exhausted():
                    future.cancel()
                    raise TimeoutError("retrieval deadline exhausted")
                if time.monotonic() >= deadline:
                    future.cancel()
                    raise TimeoutError("retrieval operation timed out")
                return future.result()
    except BaseException:
        future.cancel()
        raise
