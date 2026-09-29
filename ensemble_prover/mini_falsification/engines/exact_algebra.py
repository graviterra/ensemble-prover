"""Exact-value falsification for algebraic numeric domains."""

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


class ExactAlgebraEngine:
    name = "exact_algebra"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        binders, body = leading_forall_binders(context.statement)
        domains = [binder_domain(item.type_text) for item in binders]
        supported_domains = {"int", "rat", "real", "complex"}
        if not binders or any(domain not in supported_domains for domain in domains):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "requires visible Int/Rat/Real/Complex forall binders",
            )
        if not any(
            token in body
            for token in ("=", "≠", "<", "≤", ">", "≥", "+", "-", "*", "^", "/")
        ):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "body is not recognized as an algebraic relation",
            )
        term_domains = [
            deterministic_terms(domain, binder.type_text)
            for domain, binder in zip(domains, binders)
        ]
        total = math.prod(len(items) for items in term_domains)
        start = safe_cursor_start(context, total)
        witnesses = product_window(
            term_domains,
            start=start,
            limit=min(
                context.policy.max_finite_checks,
                context.policy.max_candidates_per_engine,
            ),
        )
        complex_replay = (
            "norm_num [pow_succ] <;> ring_nf <;> norm_num [Complex.I_mul_I]",
        )
        return await check_witnesses(
            engine=self.name,
            context=context,
            lean=lean,
            witnesses=witnesses,
            total_domain_size=total,
            explanation=(
                "exact integer/rational/real/complex substitution checked by Lean"
            ),
            cursor_window=True,
            extra_tactics_by_witness=tuple(
                complex_replay if "complex" in domains else () for _ in witnesses
            ),
            candidate_metadata={
                "algebraic_domains": tuple(domains),
                "complex_exact_replay": "complex" in domains,
            },
        )
