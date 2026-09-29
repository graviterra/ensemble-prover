"""Bounded, cancellation-safe cleanup for killable asyncio subprocesses."""

from __future__ import annotations

import asyncio
import logging
import os
import signal
from collections.abc import Callable, Iterable
from typing import Any

from .runtime_context import mark_runtime_owned_callback

_DEFAULT_REAP_TIMEOUT_S = 5.0
_DEFAULT_AUXILIARY_JOIN_TIMEOUT_S = 1.0


def _consume_future_exception(future: "asyncio.Future[Any]") -> None:
    if future.cancelled():
        return
    try:
        future.exception()
    except BaseException:
        pass


_consume_future_exception = mark_runtime_owned_callback(
    _consume_future_exception
)


def close_subprocess_pipe_transports(proc: asyncio.subprocess.Process) -> None:
    """Disconnect local pipe transports without touching private exit state."""

    transport = getattr(proc, "_transport", None)
    if transport is None:
        return
    for pipe_fd in (0, 1, 2):
        try:
            pipe = transport.get_pipe_transport(pipe_fd)
            if pipe is not None:
                pipe.close()
        except Exception:
            # Cleanup must remain bounded even for alternate transports.
            pass


def request_process_termination_nowait(
    proc: asyncio.subprocess.Process,
    *,
    kill_process_group: bool = False,
    close_pipes: Callable[[asyncio.subprocess.Process], None] | None = None,
    log: logging.Logger | None = None,
) -> bool:
    """Request termination and disconnect pipes without stealing wait status."""

    pid = getattr(proc, "pid", None)
    termination_requested = False
    if kill_process_group and pid is not None:
        try:
            os.killpg(int(pid), signal.SIGKILL)
            termination_requested = True
        except (ProcessLookupError, PermissionError):
            pass
        except Exception:
            if log is not None:
                log.exception("Failed to terminate subprocess group pid=%s", pid)
    if not termination_requested:
        try:
            proc.kill()
            termination_requested = True
        except ProcessLookupError:
            termination_requested = True
        except Exception:
            if log is not None:
                log.exception("Failed to terminate subprocess pid=%s", pid)
    try:
        (close_pipes or close_subprocess_pipe_transports)(proc)
    except Exception:
        if log is not None:
            log.exception("Failed to close subprocess pipe transports")
    return termination_requested


async def _terminate_and_reap_process_once(
    proc: asyncio.subprocess.Process,
    *,
    wait_task: "asyncio.Future[Any] | None",
    auxiliary_tasks: Iterable["asyncio.Future[Any]"],
    kill_process_group: bool,
    reap_timeout_s: float,
    auxiliary_join_timeout_s: float,
    close_pipes: Callable[[asyncio.subprocess.Process], None] | None,
    log: logging.Logger | None,
) -> bool:
    loop = asyncio.get_running_loop()
    timeout_s = max(0.01, float(reap_timeout_s))
    deadline = loop.time() + timeout_s

    pid = getattr(proc, "pid", None)
    request_process_termination_nowait(
        proc,
        kill_process_group=kill_process_group,
        close_pipes=close_pipes,
        log=log,
    )

    auxiliaries = {
        task
        for task in auxiliary_tasks
        if task is not None
    }
    active_wait = wait_task
    if active_wait is not None and not active_wait.done():
        # A pending waiter belongs to the operation being cancelled. Detach it
        # with the other operation children and create a fresh cleanup-owned
        # waiter; cancellation-sensitive adapters may otherwise leave the old
        # task pending even after the process transport has settled.
        auxiliaries.add(active_wait)
        active_wait = None
    if active_wait is None or active_wait.cancelled():
        active_wait = asyncio.ensure_future(proc.wait())
    auxiliaries.discard(active_wait)
    for task in auxiliaries:
        if not task.done():
            task.cancel()

    # First give cancellation-dependent readers a short chance to settle
    # after pipe close. A resistant reader must not consume the process's
    # entire reap window, so only the process waiter receives the remainder.
    all_tasks = {active_wait, *auxiliaries}
    done, pending = await asyncio.wait(
        all_tasks,
        timeout=min(
            max(0.0, float(auxiliary_join_timeout_s)),
            max(0.0, deadline - loop.time()),
        ),
    )
    for task in done - {active_wait}:
        _consume_future_exception(task)
    for task in pending - {active_wait}:
        task.add_done_callback(_consume_future_exception)

    def process_wait_settled(task: "asyncio.Future[Any]") -> bool:
        settled = getattr(proc, "returncode", None) is not None
        try:
            task.result()
        except (ChildProcessError, ProcessLookupError):
            return True
        except asyncio.CancelledError:
            return settled
        except BaseException:
            # Kill/reap cleanup never replaces the operation's primary error.
            return settled
        return True

    process_settled = getattr(proc, "returncode", None) is not None
    if active_wait in done:
        process_settled = process_wait_settled(active_wait)

    if not process_settled and not active_wait.done() and loop.time() < deadline:
        done, _pending = await asyncio.wait(
            {active_wait},
            timeout=max(0.0, deadline - loop.time()),
        )
        if active_wait in done:
            process_settled = process_wait_settled(active_wait)

    if not process_settled and active_wait.done():
        # Close the race where the waiter completes immediately after
        # asyncio.wait reports it pending. Observe that completion before
        # deciding whether a replacement waiter is required.
        process_settled = process_wait_settled(active_wait)

    # A caller-owned waiter can be cancelled independently. Give asyncio's
    # child watcher one fresh bounded waiter before declaring the generation
    # unsettled; never call os.waitpid behind that watcher's back.
    if not process_settled and active_wait.done() and loop.time() < deadline:
        active_wait = asyncio.ensure_future(proc.wait())
        done, _pending = await asyncio.wait(
            {active_wait},
            timeout=max(0.0, deadline - loop.time()),
        )
        if active_wait in done:
            process_settled = process_wait_settled(active_wait)

    if process_settled:
        if not active_wait.done():
            active_wait.cancel()
            active_wait.add_done_callback(_consume_future_exception)
        else:
            _consume_future_exception(active_wait)
        return True

    # Do not call waitpid here: asyncio's child watcher owns that exit status.
    # Stealing it can strand the transport in exactly the state this timeout
    # is intended to escape. The watcher remains responsible for OS reaping
    # after this stale local waiter is detached.
    active_wait.cancel()
    active_wait.add_done_callback(_consume_future_exception)
    transport_settled = getattr(proc, "returncode", None) is not None
    if log is not None:
        log.error(
            "Killed subprocess pid=%s did not settle its asyncio transport "
            "within %.1fs; transport_settled=%s; detaching stale wait and "
            "discarding this process generation",
            pid,
            timeout_s,
            transport_settled,
        )
    return bool(transport_settled)


async def terminate_and_reap_process(
    proc: asyncio.subprocess.Process,
    *,
    wait_task: "asyncio.Future[Any] | None" = None,
    auxiliary_tasks: Iterable["asyncio.Future[Any]"] = (),
    kill_process_group: bool = False,
    reap_timeout_s: float = _DEFAULT_REAP_TIMEOUT_S,
    auxiliary_join_timeout_s: float = _DEFAULT_AUXILIARY_JOIN_TIMEOUT_S,
    close_pipes: Callable[[asyncio.subprocess.Process], None] | None = None,
    log: logging.Logger | None = None,
) -> bool:
    """Kill and reap without allowing cancellation or a transport wedge to hang."""

    cleanup = asyncio.ensure_future(
        _terminate_and_reap_process_once(
            proc,
            wait_task=wait_task,
            auxiliary_tasks=auxiliary_tasks,
            kill_process_group=kill_process_group,
            reap_timeout_s=reap_timeout_s,
            auxiliary_join_timeout_s=auxiliary_join_timeout_s,
            close_pipes=close_pipes,
            log=log,
        )
    )
    cancel_exc: asyncio.CancelledError | None = None
    while not cleanup.done():
        try:
            await asyncio.shield(cleanup)
        except asyncio.CancelledError as exc:
            if cancel_exc is None:
                cancel_exc = exc
    if cancel_exc is not None:
        # Cancellation is the caller-visible result even if best-effort
        # cleanup itself also faulted after cancellation was requested.
        try:
            cleanup.result()
        except BaseException:
            pass
        raise cancel_exc
    return bool(cleanup.result())


async def communicate_with_hard_timeout(
    proc: asyncio.subprocess.Process,
    input_data: bytes | None = None,
    *,
    timeout_s: float,
    cleanup_timeout_s: float = _DEFAULT_REAP_TIMEOUT_S,
    kill_process_group: bool = False,
    close_pipes: Callable[[asyncio.subprocess.Process], None] | None = None,
    log: logging.Logger | None = None,
) -> tuple[bytes, bytes]:
    """Run ``communicate`` against a real wall-clock timeout.

    ``asyncio.wait_for(proc.communicate())`` may exceed its timeout while it
    waits for transport cancellation. This adapter owns the communicate task
    explicitly and hands that task to the same bounded process cleanup path.
    """

    communicate_awaitable = (
        proc.communicate()
        if input_data is None
        else proc.communicate(input_data)
    )
    communicate_task = asyncio.create_task(communicate_awaitable)
    try:
        done, _pending = await asyncio.wait(
            {communicate_task},
            timeout=max(0.0, float(timeout_s)),
        )
    except asyncio.CancelledError:
        await terminate_and_reap_process(
            proc,
            auxiliary_tasks=(communicate_task,),
            kill_process_group=kill_process_group,
            reap_timeout_s=cleanup_timeout_s,
            close_pipes=close_pipes,
            log=log,
        )
        raise
    if communicate_task not in done:
        await terminate_and_reap_process(
            proc,
            auxiliary_tasks=(communicate_task,),
            kill_process_group=kill_process_group,
            reap_timeout_s=cleanup_timeout_s,
            close_pipes=close_pipes,
            log=log,
        )
        raise asyncio.TimeoutError
    try:
        return communicate_task.result()
    except BaseException:
        await terminate_and_reap_process(
            proc,
            auxiliary_tasks=(communicate_task,),
            kill_process_group=kill_process_group,
            reap_timeout_s=cleanup_timeout_s,
            close_pipes=close_pipes,
            log=log,
        )
        raise
