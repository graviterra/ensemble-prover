"""Task-local ownership of nested scheduler execution intervals.

Action admission uses inclusive occupancy. Resource rollups use the exclusive
part after removing the union of child operation intervals, including children
which remain live when the parent settles.
"""

from __future__ import annotations

import asyncio
import time
from contextlib import contextmanager
from contextvars import ContextVar, Token
from dataclasses import dataclass, field
from typing import Callable, Iterator
from typing import Any

from .action import ActionBudget


@dataclass
class ExecutionServiceFrame:
    session_id: str
    dispatch_id: str
    started: float
    operation_id: str = "action_service"
    parent: ExecutionServiceFrame | None = None
    finished: float | None = None
    children: list[ExecutionServiceFrame] = field(default_factory=list)
    detached_tasks: set[asyncio.Future[Any]] = field(default_factory=set, repr=False)
    detached_settlement_armed: bool = False

    def __post_init__(self) -> None:
        if self.parent is not None:
            self.parent.children.append(self)

    def settle(self, ended: float) -> None:
        if self.finished is None:
            self.finished = max(self.started, ended)

    def nested_intervals(self, ended: float) -> list[tuple[float, float]]:
        limit = min(ended, self.finished) if self.finished is not None else ended
        intervals = sorted(
            (
                max(self.started, child.started),
                min(limit, child.finished if child.finished is not None else limit),
            )
            for child in self.children
            if child.started < limit
        )
        merged: list[tuple[float, float]] = []
        for start, stop in intervals:
            if stop <= start:
                continue
            if merged and start <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(stop, merged[-1][1]))
            else:
                merged.append((start, stop))
        return merged

    def nested_seconds(self, ended: float) -> float:
        return sum(stop - start for start, stop in self.nested_intervals(ended))

    def ownership(self) -> dict[str, str]:
        return {
            "session_id": self.session_id,
            "parent_session_id": self.parent.session_id if self.parent else "",
            "parent_dispatch_id": self.parent.dispatch_id if self.parent else "",
            "parent_operation_id": self.parent.operation_id if self.parent else "",
            "timing_scope": "inclusive_admission_exclusive_wall_service",
        }


_CURRENT_FRAME: ContextVar[ExecutionServiceFrame | None] = ContextVar(
    "mini_execution_service_frame",
    default=None,
)


def current_execution_service_frame() -> ExecutionServiceFrame | None:
    return _CURRENT_FRAME.get()


def activate_execution_service_frame(frame: ExecutionServiceFrame) -> Token:
    return _CURRENT_FRAME.set(frame)


def reset_execution_service_frame(token: Token) -> None:
    _CURRENT_FRAME.reset(token)


def record_execution_observation(
    dossier: Any,
    action_id: str,
    receipt: dict[str, Any],
    *,
    count_dispatch: bool = True,
) -> None:
    """Separate dispatch occupancy prediction from exclusive resource totals."""
    observations = getattr(dossier, "action_value_observations", None)
    record_execution_metrics(
        observations, action_id, receipt, count_dispatch=count_dispatch
    )


def record_execution_metrics(
    observations: Any,
    action_id: str,
    receipt: dict[str, Any],
    *,
    count_dispatch: bool,
) -> None:
    """Update the resource-only observation map without session authority."""
    if not isinstance(observations, dict):
        return
    observed = observations.setdefault(action_id, {})
    observed["service_dispatches"] = float(
        observed.get("service_dispatches", 0.0)
    ) + int(count_dispatch)
    observed["service_seconds"] = (
        float(observed.get("service_seconds", 0.0)) + receipt["service_seconds"]
    )
    observed["elapsed_seconds"] = (
        float(observed.get("elapsed_seconds", 0.0)) + receipt["elapsed_seconds"]
    )
    observed["seconds"] = (
        float(observed.get("seconds", 0.0)) + receipt["elapsed_seconds"]
    )


@dataclass
class DetachedExecutionSettlement:
    """A late task may settle resource records, without a reference to MiniSession."""

    action_id: str
    budget: ActionBudget
    observations: dict[str, Any] | None
    frame: ExecutionServiceFrame
    pending: set[asyncio.Future[Any]]
    initial_receipt_key: str
    registry: list[DetachedExecutionSettlement] = field(repr=False)
    receipt: dict[str, Any] | None = None

    def complete(self, task: asyncio.Future[Any]) -> None:
        self.pending.discard(task)
        if self.pending or self.receipt is not None:
            return
        ended = time.monotonic()
        self.frame.settle(ended)
        receipt, fresh = self.budget.record_execution(
            dispatch_id=self.frame.dispatch_id,
            operation_id=self.frame.operation_id,
            elapsed_seconds=max(0.0, ended - self.frame.started),
            nested_seconds=self.frame.nested_seconds(ended),
            productive=False,
            disposition="detached_tail_settled",
            details={
                "accounting_scope": "inclusive_admission_exclusive_wall_service",
                "nested_intervals_seconds": [
                    [start - self.frame.started, stop - self.frame.started]
                    for start, stop in self.frame.nested_intervals(ended)
                ],
            },
            ownership=self.frame.ownership(),
        )
        self.receipt = receipt
        self.budget.settle_execution_tail(self.initial_receipt_key)
        if fresh:
            record_execution_metrics(
                self.observations,
                self.action_id,
                receipt,
                count_dispatch=False,
            )
        # Pending callbacks own the runtime group strongly until settlement.
        # Once its receipt is committed, discard the resource-only registry
        # entry so completed frame trees and replaced budgets can be freed.
        for index, settlement in enumerate(self.registry):
            if settlement is self:
                del self.registry[index]
                break


def detached_execution_callback(
    settlement: DetachedExecutionSettlement,
) -> Callable[[asyncio.Future[Any]], None]:
    """Build the authenticated callback around its narrow resource capability."""
    from ..runtime_context import mark_runtime_owned_callback

    def complete(task: asyncio.Future[Any]) -> None:
        settlement.complete(task)

    return mark_runtime_owned_callback(complete)


@contextmanager
def bind_execution_service_frame(frame: ExecutionServiceFrame) -> Iterator[None]:
    token = _CURRENT_FRAME.set(frame)
    try:
        yield
    finally:
        _CURRENT_FRAME.reset(token)
