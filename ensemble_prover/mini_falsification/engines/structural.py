"""Fast structural-obstruction checks for unsupported conjecture shapes."""

from __future__ import annotations

import time
from typing import Any

from ...finite_claim_check import falsify_claim_by_structural_obstructions
from ..engine import FalsificationContext
from ..model import CounterexampleCandidate, FalsificationFinding, FalsificationOutcome


class StructuralObstructionEngine:
    name = "structural"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        started = time.monotonic()
        result = falsify_claim_by_structural_obstructions(context.statement)
        if not result.falsified:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                elapsed_s=time.monotonic() - started,
            )
        candidate = CounterexampleCandidate(
            engine=self.name,
            explanation=result.reason,
            metadata={
                "obstruction_kind": result.obstruction_kind,
                "obstruction_detail": result.obstruction_detail,
            },
        )
        return FalsificationFinding(
            self.name,
            FalsificationOutcome.REFUTED,
            reason=result.reason,
            candidates=(candidate,),
            elapsed_s=time.monotonic() - started,
        )
