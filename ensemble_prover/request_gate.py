"""Shared/exclusive leases for model clients with mutable compatibility telemetry."""

from __future__ import annotations

import asyncio
from contextlib import asynccontextmanager, contextmanager
from contextvars import ContextVar
from typing import AsyncIterator, Iterator


_FORMAL_PROVIDER_EXCLUSIVE: ContextVar[bool] = ContextVar(
    "formal_provider_exclusive", default=False
)


@contextmanager
def formal_provider_exclusive_scope() -> Iterator[None]:
    token = _FORMAL_PROVIDER_EXCLUSIVE.set(True)
    try:
        yield
    finally:
        _FORMAL_PROVIDER_EXCLUSIVE.reset(token)


def formal_provider_exclusive_requested() -> bool:
    return bool(_FORMAL_PROVIDER_EXCLUSIVE.get())


class AsyncSharedExclusiveGate:
    """Allow concurrent ordinary calls while isolating formal-search tails."""

    def __init__(self) -> None:
        self._condition = asyncio.Condition()
        self._readers = 0
        self._writer = False
        self._writers_waiting = 0

    async def _acquire_shared(self) -> None:
        async with self._condition:
            await self._condition.wait_for(
                lambda: not self._writer and self._writers_waiting == 0
            )
            self._readers += 1

    async def _release_shared(self) -> None:
        async with self._condition:
            self._readers -= 1
            self._condition.notify_all()

    async def _acquire_exclusive(self) -> None:
        async with self._condition:
            self._writers_waiting += 1
            acquired = False
            try:
                await self._condition.wait_for(
                    lambda: not self._writer and self._readers == 0
                )
                self._writer = True
                acquired = True
            finally:
                self._writers_waiting -= 1
                if not acquired:
                    self._condition.notify_all()

    async def _release_exclusive(self) -> None:
        async with self._condition:
            self._writer = False
            self._condition.notify_all()

    async def _complete_release(self, release_coro) -> None:
        """Finish counter cleanup even if repeated cancellation hits finally."""

        task = asyncio.create_task(release_coro)
        cancellation: asyncio.CancelledError | None = None
        while not task.done():
            try:
                await asyncio.shield(task)
            except asyncio.CancelledError as exc:
                # Cleanup must finish or a leaked reader/writer count can
                # poison this client permanently. Remember cancellation that
                # first arrives during __aexit__ and propagate it afterwards.
                cancellation = exc
                continue
        task.result()
        if cancellation is not None:
            raise cancellation

    @asynccontextmanager
    async def hold(self, *, exclusive: bool) -> AsyncIterator[None]:
        if exclusive:
            await self._acquire_exclusive()
        else:
            await self._acquire_shared()
        try:
            yield
        finally:
            if exclusive:
                await self._complete_release(self._release_exclusive())
            else:
                await self._complete_release(self._release_shared())


__all__ = [
    "AsyncSharedExclusiveGate",
    "formal_provider_exclusive_requested",
    "formal_provider_exclusive_scope",
]
