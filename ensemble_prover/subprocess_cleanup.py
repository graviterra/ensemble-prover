"""Bounded, cancellation-safe cleanup for killable asyncio subprocesses."""

from __future__ import annotations

import asyncio
import logging
import os
import signal
import sys
from collections.abc import Callable, Iterable
from typing import Any

from .runtime_context import mark_runtime_owned_callback

_DEFAULT_REAP_TIMEOUT_S = 5.0
_DEFAULT_AUXILIARY_JOIN_TIMEOUT_S = 1.0
_EXIT_DELIVERY_GRACE_S = 0.1
_LOOP_TIMING_INTERVAL_S = 0.05


def _log_cleanup_exception(
    log: logging.Logger | None, message: str, *args: Any
) -> None:
    if log is not None:
        try:
            log.exception(message, *args)
        except Exception:
            # Diagnostic sinks cannot replace termination/pipe-close outcomes.
            pass


def _process_cleanup_state(
    proc: asyncio.subprocess.Process,
    loop: asyncio.AbstractEventLoop,
) -> dict[str, Any]:
    """Capture exit delivery evidence without reaping or modifying the transport."""

    pid = getattr(proc, "pid", None)
    state: dict[str, Any] = {
        "pid": pid,
        "returncode": getattr(proc, "returncode", None),
        "os_process_state": "unavailable",
        "watcher_type": "unavailable",
        "watcher_thread_alive": None,
        "direct_exit_callback_queued": None,
    }
    if sys.platform.startswith("linux") and type(pid) is int and pid > 0:
        try:
            with open(f"/proc/{pid}/stat", encoding="ascii") as stat_file:
                stat = stat_file.read(4096)
            # A process name can contain spaces and closing parentheses.
            fields = stat.rpartition(") ")[2].split()
            if fields:
                state["os_process_state"] = fields[0]
        except FileNotFoundError:
            state["os_process_state"] = "absent"
        except (OSError, UnicodeError):
            pass
    # Do not call get_child_watcher(): on some runtimes that creates or replaces
    # a watcher. These optional observations never become cleanup authority.
    policy = getattr(asyncio.events, "_event_loop_policy", None)
    watcher = getattr(policy, "_watcher", None)
    if watcher is not None:
        state["watcher_type"] = type(watcher).__name__
        threads = getattr(watcher, "_threads", None)
        if isinstance(threads, dict):
            thread = threads.get(pid)
            state["watcher_thread_alive"] = bool(thread and thread.is_alive())
    transport = getattr(proc, "_transport", None)
    ready = getattr(loop, "_ready", None)
    if transport is not None and ready is not None:
        # Bound diagnostics even if unrelated callbacks have flooded the loop.
        # Earlier watcher/call_soon hops can still be queued when this is False.
        state["direct_exit_callback_queued"] = False if len(ready) <= 128 else None
        for index, handle in enumerate(ready):
            if index >= 128:
                break
            callback = getattr(handle, "_callback", None)
            if (
                getattr(callback, "__self__", None) is transport
                and getattr(callback, "__name__", "") == "_process_exited"
            ):
                state["direct_exit_callback_queued"] = True
                break
    return state


def _consume_future_exception(future: "asyncio.Future[Any]") -> None:
    if future.cancelled():
        return
    try:
        future.exception()
    except BaseException:
        pass


_consume_future_exception = mark_runtime_owned_callback(_consume_future_exception)


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
            _log_cleanup_exception(
                log, "Failed to terminate subprocess group pid=%s", pid
            )
    if not termination_requested:
        try:
            proc.kill()
            termination_requested = True
        except ProcessLookupError:
            termination_requested = True
        except Exception:
            _log_cleanup_exception(log, "Failed to terminate subprocess pid=%s", pid)
    try:
        (close_pipes or close_subprocess_pipe_transports)(proc)
    except Exception:
        _log_cleanup_exception(log, "Failed to close subprocess pipe transports")
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
    started = loop.time()
    deadline = started + timeout_s
    max_wait_overrun_s = 0.0
    delivery_grace_used = False
    state_before_grace = None

    async def timed_wait(
        tasks: set[asyncio.Future[Any]],
        timeout: float,
    ) -> tuple[set[asyncio.Future[Any]], set[asyncio.Future[Any]]]:
        """Join within one deadline and measure delayed loop resumption.

        Wait overruns are a lower bound on loop delay, not process exit delay.
        Polling uses asyncio's own timer callbacks, retaining action ownership
        without introducing a privileged application callback or monitor task.
        """

        nonlocal max_wait_overrun_s
        stop = loop.time() + max(0.0, timeout)
        done = {task for task in tasks if task.done()}
        pending = tasks - done
        while pending and loop.time() < stop:
            interval = min(_LOOP_TIMING_INTERVAL_S, stop - loop.time())
            before = loop.time()
            newly_done, pending = await asyncio.wait(pending, timeout=interval)
            max_wait_overrun_s = max(
                max_wait_overrun_s,
                loop.time() - before - interval,
            )
            done.update(newly_done)
        return done, pending

    pid = getattr(proc, "pid", None)
    termination_requested = request_process_termination_nowait(
        proc,
        kill_process_group=kill_process_group,
        close_pipes=close_pipes,
        log=log,
    )

    auxiliaries = {task for task in auxiliary_tasks if task is not None}
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
    done, pending = await timed_wait(
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
        done, _pending = await timed_wait(
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
        done, _pending = await timed_wait(
            {active_wait},
            timeout=max(0.0, deadline - loop.time()),
        )
        if active_wait in done:
            process_settled = process_wait_settled(active_wait)

    if not process_settled:
        # The OS watcher may have reaped while synchronous work prevented its
        # multi-hop exit callback from running. An expired wall-clock allowance
        # must not immediately freeze a False result ahead of queued delivery.
        # Grant one small window, never renew it, and keep the watcher as the
        # sole owner of waitpid. Pipes or a resistant waiter need not settle if
        # the transport has already received the exit status.
        delivery_grace_used = True
        if log is not None:
            try:
                state_before_grace = _process_cleanup_state(proc, loop)
            except Exception:
                # Optional diagnostics cannot replace the cleanup result.
                pass
        grace_deadline = loop.time() + min(_EXIT_DELIVERY_GRACE_S, timeout_s)
        for _ in range(8):
            await asyncio.sleep(0)
            process_settled = getattr(proc, "returncode", None) is not None
            if not process_settled and active_wait.done():
                process_settled = process_wait_settled(active_wait)
            if process_settled or loop.time() >= grace_deadline:
                break
        while not process_settled and loop.time() < grace_deadline:
            remaining = max(0.0, grace_deadline - loop.time())
            if active_wait.done():
                # Independent waiter cancellation must not truncate delivery
                # of the watcher's status. Observe the same fixed grace window
                # without renewing it or creating more operation-owned waiters.
                interval = min(_LOOP_TIMING_INTERVAL_S, remaining)
                before = loop.time()
                await asyncio.sleep(interval)
                max_wait_overrun_s = max(
                    max_wait_overrun_s, loop.time() - before - interval
                )
            else:
                await timed_wait({active_wait}, timeout=remaining)
            process_settled = getattr(proc, "returncode", None) is not None
            if not process_settled and active_wait.done():
                process_settled = process_wait_settled(active_wait)

    def record_cleanup(outcome: str, *, settled: bool) -> None:
        if log is None:
            return
        try:
            evidence = {
                **_process_cleanup_state(proc, loop),
                "state_before_grace": state_before_grace,
                "termination_requested": termination_requested,
                "reap_timeout_s": timeout_s,
                "cleanup_elapsed_s": loop.time() - started,
                "max_wait_overrun_s": max_wait_overrun_s,
                "delivery_grace_used": delivery_grace_used,
                "transport_settled": getattr(proc, "returncode", None) is not None,
                "outcome": outcome,
            }
            emit = log.warning if settled else log.error
            emit(
                "Subprocess cleanup pid=%s outcome=%s returncode=%s "
                "termination_requested=%s os_process_state=%s "
                "watcher_type=%s watcher_thread_alive=%s direct_exit_callback_queued=%s "
                "reap_timeout_s=%.3f "
                "cleanup_elapsed_s=%.3f max_wait_overrun_s=%.3f "
                "delivery_grace_used=%s state_before_grace=%s",
                pid,
                outcome,
                evidence["returncode"],
                termination_requested,
                evidence["os_process_state"],
                evidence["watcher_type"],
                evidence["watcher_thread_alive"],
                evidence["direct_exit_callback_queued"],
                timeout_s,
                evidence["cleanup_elapsed_s"],
                max_wait_overrun_s,
                delivery_grace_used,
                state_before_grace,
                extra={"subprocess_cleanup": evidence},
            )
        except Exception:
            # A diagnostic adapter or logging sink must never change settlement.
            pass

    if process_settled:
        if not active_wait.done():
            active_wait.cancel()
            active_wait.add_done_callback(_consume_future_exception)
        else:
            _consume_future_exception(active_wait)
        if delivery_grace_used or max_wait_overrun_s >= _LOOP_TIMING_INTERVAL_S:
            record_cleanup("exit_status_received", settled=True)
        return True

    # Do not call waitpid here: asyncio's child watcher owns that exit status.
    # Stealing it can strand the transport in exactly the state this timeout
    # is intended to escape. The watcher remains responsible for OS reaping
    # after this stale local waiter is detached.
    active_wait.cancel()
    active_wait.add_done_callback(_consume_future_exception)
    transport_settled = getattr(proc, "returncode", None) is not None
    record_cleanup("exit_status_unavailable", settled=False)
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
    # The shield's final wakeup can deliver an exit callback after the inner
    # snapshot. Observe that status before returning a stale False to the caller.
    return bool(cleanup.result()) or getattr(proc, "returncode", None) is not None


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
        proc.communicate() if input_data is None else proc.communicate(input_data)
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
