"""Bounded, process-local reuse of fresh checks within one memory allocation.

Serialized profiles carry no authority. These receipts are issued only by the
live capture path and bind the original result object to its checked context.
"""
from __future__ import annotations

import hashlib
import json
import weakref
from collections import OrderedDict
from dataclasses import dataclass
from typing import Any, Callable

_MAX_ENTRIES = 64
_MAX_BYTES = 4 * 1024 * 1024


def _receipts(live: Any, *, create: bool = False) -> OrderedDict[int, _Receipt]:
    cache = getattr(live, "_memory_semantic_receipts", None)
    if cache is None and create:
        cache = OrderedDict()
        live._memory_semantic_receipts = cache
    return cache if cache is not None else OrderedDict()


def _record(record: Any) -> bytes:
    return json.dumps(record.to_record(), sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode()


def _digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _budget_binding(budget: Any) -> tuple[Any, ...]:
    return (budget.owner_id, budget.deadline_monotonic, budget.max_probes,
            budget.max_heartbeats, budget.memory_mb, budget.remaining_tokens,
            budget.remaining_cost, id(budget.provider_owner), budget.concurrency,
            id(budget.cancellation_event))


@dataclass(frozen=True)
class _Pending:
    runner: Any
    live: Any
    budget: Any
    budget_binding: tuple[Any, ...]
    probes_used: int
    context_digest: str
    guard: Callable[[], bool]

    def current(self, runner: Any, budget: Any, context: str) -> bool:
        from ensemble_prover.mini_recursive import _live_lean_capability_for_new_work

        try:
            budget.check_cancelled()
            return (runner is self.runner and budget is self.budget
                    and _budget_binding(budget) == self.budget_binding
                    and budget.probes_used >= self.probes_used
                    and budget.remaining_s() > 0
                    and _digest(context.encode()) == self.context_digest
                    and _live_lean_capability_for_new_work(runner) is self.live
                    and self.guard())
        except Exception:
            return False


@dataclass(frozen=True)
class _Receipt:
    result: Any
    record_digest: str
    weight: int
    pending: _Pending


def begin_check(runner: Any, budget: Any, context: str) -> _Pending | None:
    """Capture the environment before semantic work, or disable reuse."""
    from ensemble_prover.lean_runner import LeanRunner
    from ensemble_prover.mini_recursive import _live_lean_capability_for_new_work
    from ensemble_prover.verified_helper_contract import helper_contract_context_guard
    from .budget import MemoryBudget

    live = _live_lean_capability_for_new_work(runner)
    if not isinstance(live, LeanRunner) or type(budget) is not MemoryBudget:
        return None
    try:
        pending = _Pending(runner, live, budget, _budget_binding(budget),
                           budget.probes_used, _digest(context.encode()),
                           helper_contract_context_guard(live))
        return pending if pending.current(runner, budget, context) else None
    except Exception:
        return None


def issue(result: Any, pending: _Pending | None, *, context: str) -> None:
    if pending is None or not result.complete:
        return
    if not pending.current(pending.runner, pending.budget, context):
        return
    payload = _record(result)
    weight = len(payload)
    if weight > _MAX_BYTES:
        return
    # Weak result references prevent the registry from keeping entire source
    # records alive. Count their full encoded size conservatively regardless.
    receipts = _receipts(pending.live, create=True)
    receipts[id(result)] = _Receipt(weakref.ref(result), _digest(payload), weight, pending)
    for key, receipt in tuple(receipts.items()):
        if receipt.result() is None:
            del receipts[key]
    while len(receipts) > _MAX_ENTRIES or sum(r.weight for r in receipts.values()) > _MAX_BYTES:
        receipts.popitem(last=False)


def current_receipt(result: Any, runner: Any, budget: Any, context: str) -> Callable[[], bool] | None:
    from ensemble_prover.mini_recursive import _live_lean_capability_for_new_work

    receipt = _receipts(_live_lean_capability_for_new_work(runner)).get(id(result))
    if receipt is None or receipt.result() is not result:
        return None

    def current() -> bool:
        try:
            return (receipt.result() is result
                    and _digest(_record(result)) == receipt.record_digest
                    and receipt.pending.current(runner, budget, context))
        except Exception:
            return False

    return current if current() else None
