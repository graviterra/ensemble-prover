"""Bounded exhaustive falsification over finite binder domains."""

from __future__ import annotations

import math
from typing import Any

from ..engine import FalsificationContext
from ..generators import (
    binder_domain,
    deterministic_terms,
    leading_forall_binders,
    product_window,
)
from ..model import FalsificationFinding, FalsificationOutcome
from .common import check_witnesses, safe_cursor_start


class FiniteEnumerationEngine:
    name = "finite"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        binders, _body = leading_forall_binders(context.statement)
        if not binders:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "no visible leading forall binders",
            )
        domains = [binder_domain(binder.type_text) for binder in binders]
        if any(
            domain not in {"bool", "fin", "nat", "pnat", "prop"} for domain in domains
        ):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "binder domain is not finite-enumeration compatible",
            )
        terms = [
            deterministic_terms(domain, binder.type_text)
            for domain, binder in zip(domains, binders)
        ]
        # A bounded proof-term portfolio cannot establish exhaustive coverage.
        # It may produce a certified counterexample, never a proof of truth.
        complete = all(domain in {"bool", "fin"} for domain in domains)
        total = math.prod(len(items) for items in terms)
        start = safe_cursor_start(context, total)
        batch_limit = min(
            context.policy.max_finite_checks,
            context.policy.max_candidates_per_engine,
        )
        witnesses = product_window(terms, start=start, limit=batch_limit)
        return await check_witnesses(
            engine=self.name,
            context=context,
            lean=lean,
            witnesses=witnesses,
            complete_domain=complete,
            total_domain_size=total,
            explanation="deterministic finite-domain enumeration",
            cursor_window=True,
        )
