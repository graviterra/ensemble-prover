"""Cancellation-cooperative worker bridge without detached executor tasks."""

from __future__ import annotations

import asyncio
import threading
from collections.abc import Callable
from typing import Any, TypeVar


_T = TypeVar("_T")


async def run_cancellable_worker(
    function: Callable[..., _T],
    /,
    *args: Any,
    cancellation_event: threading.Event,
    **kwargs: Any,
) -> _T:
    """Run blocking work and join it before propagating cancellation.

    ``asyncio.to_thread`` cannot stop its worker and may leave mutation-capable
    work running after the owning MiniSession has ended.  This bridge gives
    the blocking function an explicit cancellation event and synchronously
    joins the worker on cancellation, making late publication impossible.
    """

    completed = threading.Event()
    result: list[_T] = []
    failure: list[BaseException] = []

    def invoke() -> None:
        try:
            result.append(
                function(
                    *args,
                    **kwargs,
                    cancellation_event=cancellation_event,
                )
            )
        except BaseException as exc:
            failure.append(exc)
        finally:
            completed.set()

    worker = threading.Thread(
        target=invoke,
        name="mini-theory-cancellable-worker",
        daemon=False,
    )
    start_returned = False
    try:
        worker.start()
        start_returned = True
        while not completed.is_set():
            await asyncio.sleep(0.01)
        worker.join()
    except BaseException as primary:
        # ``Thread.start`` can report an external stop after the OS thread was
        # created but before the call returned. ``ident`` remains non-None for
        # a thread that started and already finished, so it distinguishes that
        # post-effect window from a true pre-start failure without calling
        # ``join`` on an unstarted thread.
        started = bool(start_returned or worker.ident is not None)
        if started:
            cancellation_event.set()
            join_errors: list[BaseException] = []
            while worker.is_alive():
                try:
                    worker.join()
                except BaseException as join_error:
                    join_errors.append(join_error)
            for join_error in join_errors:
                primary.add_note(
                    "Mini theory worker join also failed while preserving the "
                    f"external stop: {type(join_error).__name__}: {join_error}"
                )
        raise
    if failure:
        raise failure[0]
    return result[0]
