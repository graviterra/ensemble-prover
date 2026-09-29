"""Frontier-driven proof-session scheduler and its public action contracts.

``MiniSession`` owns the dossier, proof state, conversation, budgets, and
execution scope. It selects typed ``Action`` work from the proof frontier,
applies ``MiniOutcome`` records, and manages scheduler-owned ``RepairTicket``
and ``ActionBudget`` state.
"""

from importlib import import_module
from typing import Any

__all__ = [
    "Action",
    "ActionBudget",
    "MiniOutcome",
    "MiniSession",
    "RepairTicket",
]


_LAZY_EXPORTS = {
    "Action": (".action", "Action"),
    "ActionBudget": (".action", "ActionBudget"),
    "MiniOutcome": (".action", "MiniOutcome"),
    "RepairTicket": (".action", "RepairTicket"),
    "MiniSession": (".session", "MiniSession"),
}


def __getattr__(name: str) -> Any:
    target = _LAZY_EXPORTS.get(name)
    if target is None:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    module_name, attribute_name = target
    value = getattr(import_module(module_name, __name__), attribute_name)
    globals()[name] = value
    return value


def __dir__() -> list[str]:
    return sorted({*globals(), *__all__})
