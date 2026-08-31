"""SalvagedAssemblyAction — wraps `_try_proof_state_salvaged_helper_assembly`.

Reconnects salvaged helper names (from a prior failed turn's
``HelperSalvager.salvage`` result) to open child nodes in the proof_state
graph, then runs assembly fixpoint.
"""

from __future__ import annotations

import time
from typing import Any, ClassVar, FrozenSet, Sequence

from ..action import MiniOutcome


class SalvagedAssemblyAction:
    id: str = "salvaged_assembly"
    priority: int = 70
    cost_estimate_s: float = 5.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})

    def __init__(
        self,
        *,
        helper_names: Sequence[str] = (),
        phase: str = "salvaged_assembly",
        timeout_s: float = 30.0,
        max_nodes: int = 3,
    ) -> None:
        self._helper_names = tuple(helper_names)
        self.phase = str(phase or "salvaged_assembly")
        self.timeout_s = float(timeout_s or 0.0)
        self.max_nodes = int(max_nodes or 0)


    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0 or self.max_nodes <= 0:
            return False
        if session.dossier is None or session.proof_state is None or session.lean is None:
            return False
        if not self._helper_names:
            return False
        return True

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.proof_state_executor import _try_proof_state_salvaged_helper_assembly

        started = time.monotonic()
        ok, proof, helpers = await _try_proof_state_salvaged_helper_assembly(
            conv=session.conv,
            lean=session.lean,
            dossier=session.dossier,
            proof_state=session.proof_state,
            helper_names=list(self._helper_names),
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=int(getattr(session, "iteration", 0)),
            timeout_s=self.timeout_s,
            max_nodes=self.max_nodes,
            proof_cache=session.proof_cache,
            phase=self.phase,
        )
        cost = time.monotonic() - started
        return MiniOutcome(
            action_id=self.id,
            solved=bool(ok),
            proof=proof if ok else None,
            helpers_added=tuple(helpers or ()),
            progress=bool(ok or helpers),
            cost_seconds=cost,
            metadata={"phase": self.phase},
        )
