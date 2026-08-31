"""Bounded numeric witness search with Lean replay at the trust boundary."""

from __future__ import annotations

import math
from typing import Any

from ..engine import FalsificationContext
from ..generators import binder_domain, leading_forall_binders, product_window
from ..model import FalsificationFinding, FalsificationOutcome
from .common import check_witnesses, safe_cursor_start


class BoundedNumericEngine:
    name = "numeric"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        binders, _body = leading_forall_binders(context.statement)
        domains = [binder_domain(item.type_text) for item in binders]
        if not binders or any(
            domain not in {"nat", "int", "rat"} for domain in domains
        ):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "requires visible numeric forall binders",
            )
        term_domains: list[tuple[str, ...]] = []
        for domain in domains:
            if domain == "nat":
                term_domains.append(
                    tuple(
                        f"({value} : ℕ)"
                        for value in (16, 31, 127, 1024, 0, 1, 2, 3, 4, 5, 7, 11)
                    )
                )
            elif domain == "int":
                term_domains.append(
                    tuple(
                        f"({value} : ℤ)"
                        for value in (
                            16,
                            -16,
                            127,
                            -127,
                            0,
                            1,
                            -1,
                            2,
                            -2,
                            3,
                            -3,
                            7,
                        )
                    )
                )
            else:
                term_domains.append(
                    tuple(
                        f"({value} : ℚ)"
                        for value in (
                            "1/3",
                            "-1/3",
                            "101/17",
                            "-101/17",
                            "0",
                            "1",
                            "-1",
                            "2",
                            "-2",
                            "1 / 2",
                            "-1 / 2",
                            "3 / 2",
                        )
                    )
                )
        total = math.prod(len(items) for items in term_domains)
        start = safe_cursor_start(context, total)
        witnesses = product_window(
            term_domains,
            start=start,
            limit=min(
                context.policy.max_numeric_examples,
                context.policy.max_candidates_per_engine,
            ),
        )
        return await check_witnesses(
            engine=self.name,
            context=context,
            lean=lean,
            witnesses=witnesses,
            total_domain_size=total,
            explanation="bounded numerical stress values; Lean exact replay avoids floating-point authority",
            cursor_window=True,
        )
