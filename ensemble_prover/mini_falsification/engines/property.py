"""Seeded property-based falsification for visible integer binders."""

from __future__ import annotations

import random
from typing import Any

from ..engine import FalsificationContext
from ..generators import binder_domain, leading_forall_binders
from ..model import FalsificationFinding, FalsificationOutcome
from .common import check_witnesses


class PropertyGenerationEngine:
    name = "property"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        binders, _body = leading_forall_binders(context.statement)
        domains = [binder_domain(binder.type_text) for binder in binders]
        if not binders or any(
            domain not in {"nat", "pnat", "int"} for domain in domains
        ):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "requires visible Nat/PNat/Int forall binders",
            )
        raw_start = context.cursor.get("next_index", 0)
        start_index = (
            max(0, raw_start)
            if isinstance(raw_start, int) and not isinstance(raw_start, bool)
            else 0
        )
        witnesses: list[tuple[str, ...]] = []
        for example_index in range(
            start_index,
            start_index + context.policy.max_property_examples,
        ):
            row: list[str] = []
            for binder_index, domain in enumerate(domains):
                rng = random.Random(
                    f"{context.policy.random_seed}:{example_index}:{binder_index}"
                )
                magnitude = max(16, 2 + example_index * 2)
                value = rng.randint(-magnitude, magnitude)
                if domain in {"nat", "pnat"}:
                    value = abs(value)
                if domain == "pnat":
                    value = max(1, value)
                    row.append(f"({value} : ℕ+)")
                elif domain == "nat":
                    row.append(f"({value} : ℕ)")
                else:
                    row.append(f"({value} : ℤ)")
            witnesses.append(tuple(row))
        return await check_witnesses(
            engine=self.name,
            context=context,
            lean=lean,
            witnesses=tuple(witnesses),
            explanation="seeded property-based boundary and random generation",
            cursor_window=True,
        )
