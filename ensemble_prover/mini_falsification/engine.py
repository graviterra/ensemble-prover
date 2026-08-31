"""Engine protocol and fail-closed execution context."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Protocol, Sequence

from .model import FalsificationFinding, TargetKind
from .policy import FalsificationPolicy


@dataclass(frozen=True)
class FalsificationContext:
    statement: str
    target_kind: TargetKind
    preamble: str = ""
    helpers: Sequence[Any] = ()
    local_hypotheses: tuple[str, ...] = ()
    cursor: Mapping[str, Any] = field(default_factory=dict)
    policy: FalsificationPolicy = field(default_factory=FalsificationPolicy)
    # Operational wall-clock boundary for this engine invocation.  Candidate
    # loops use it to shorten an inner Lean probe before the enclosing engine
    # watchdog can win the race and detach Lean cleanup.  It is deliberately
    # absent from semantic policy/cursor identity.
    deadline_monotonic: float = 0.0
    # Mutable progress sink: index-cursor engines record each COMPLETED check
    # here so the service can preserve the completed prefix when the outer
    # engine watchdog cancels mid-batch (previously all partial progress was
    # replaced by checks_run=0 / no cursor, restarting from witness zero).
    progress: dict = field(default_factory=dict)


class FalsificationEngine(Protocol):
    name: str

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding: ...
