"""Boolean enumeration and native-SMT candidate generation with Lean replay."""

from __future__ import annotations

import asyncio
from dataclasses import replace
import json
import time
from typing import Any

from ..engine import FalsificationContext
from ..generators import binder_domain, leading_forall_binders, product_window
from ..model import FalsificationFinding, FalsificationOutcome
from ..smt import (
    SmtTranslationError,
    model_value_to_lean,
    run_smt_query,
    translate_universal_statement,
)
from .common import check_witnesses, safe_cursor_start


class SatSmtEngine:
    """Exhaustive Bool search plus conservative native-SMT candidate search.

    Native solver output is never proof evidence.  A SAT model is only a source
    of concrete Lean witness terms; the shared Lean replay boundary must prove
    the negated instance before this engine can return ``REFUTED``.  UNSAT and
    UNKNOWN therefore remain advisory and cannot establish the conjecture.
    """

    name = "sat_smt"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        binders, _body = leading_forall_binders(context.statement)
        if binders and all(binder_domain(item.type_text) == "bool" for item in binders):
            total = 2 ** len(binders)
            start = safe_cursor_start(context, total)
            batch_limit = min(
                context.policy.max_finite_checks,
                context.policy.max_candidates_per_engine,
            )
            witnesses = product_window(
                [("false", "true")] * len(binders),
                start=start,
                limit=batch_limit,
            )
            return await check_witnesses(
                engine=self.name,
                context=context,
                lean=lean,
                witnesses=witnesses,
                complete_domain=True,
                total_domain_size=total,
                explanation="complete propositional assignment enumeration",
                cursor_window=True,
            )

        started = time.monotonic()
        try:
            translation = translate_universal_statement(context.statement)
        except SmtTranslationError as exc:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                f"conservative SMT translation rejected statement: {exc}",
                elapsed_s=time.monotonic() - started,
            )

        raw_prior_index = context.cursor.get("next_index", 0)
        prior_index = (
            max(0, raw_prior_index)
            if isinstance(raw_prior_index, int)
            and not isinstance(raw_prior_index, bool)
            else 0
        )
        if (
            str(context.cursor.get("plan_hash") or "") == translation.query_hash
            and prior_index >= 1
            and context.cursor.get("resume_recheck_due") is not True
        ):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.INCONCLUSIVE,
                "identical SMT query already exhausted under this environment",
                elapsed_s=time.monotonic() - started,
                cursor={"plan_hash": translation.query_hash, "next_index": 1},
            )

        try:
            query = await run_smt_query(
                translation,
                timeout_s=context.policy.operation_timeout_s,
            )
        except TimeoutError:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.TRANSIENT_FAILURE,
                "SMT subprocess watchdog expired and the worker was killed",
                elapsed_s=time.monotonic() - started,
                error_kind="timeout",
            )
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.TRANSIENT_FAILURE,
                f"SMT subprocess failed: {type(exc).__name__}: {exc}"[:500],
                elapsed_s=time.monotonic() - started,
                error_kind="infrastructure",
            )

        raw_results = query.get("results") or ()
        results = [dict(item) for item in raw_results if isinstance(item, dict)]
        statuses = {
            str(item.get("backend") or ""): str(item.get("status") or "error")
            for item in results
        }
        diagnostic = {
            "query_hash": translation.query_hash,
            "backends": statuses,
            "versions": {
                str(item.get("backend") or ""): str(item.get("version") or "")
                for item in results
            },
            "errors": {
                str(item.get("backend") or ""): str(item.get("error") or "")[:300]
                for item in results
                if item.get("status") == "error"
            },
            "disagreement": len(set(statuses.values()) & {"sat", "unsat"}) > 1,
        }
        sat_results = [item for item in results if item.get("status") == "sat"]
        conversion_errors: list[str] = []
        for result in sat_results:
            values = result.get("values")
            if not isinstance(values, dict):
                conversion_errors.append(
                    f"{result.get('backend', 'solver')}: missing model values"
                )
                continue
            try:
                witness = tuple(
                    model_value_to_lean(str(values.get(binder.smt_name) or ""), binder)
                    for binder in translation.binders
                )
            except SmtTranslationError as exc:
                conversion_errors.append(f"{result.get('backend', 'solver')}: {exc}")
                continue
            finding = await check_witnesses(
                engine=self.name,
                context=context,
                lean=lean,
                witnesses=(witness,),
                explanation=(
                    f"{result.get('backend', 'SMT')} SAT model replayed and "
                    "proved as a concrete Lean counterexample"
                ),
                cursor_window=True,
            )
            if finding.candidates:
                candidate = replace(
                    finding.candidates[0],
                    metadata={
                        **dict(finding.candidates[0].metadata),
                        "smt": diagnostic,
                    },
                )
                # If full-negation certification later fails, a future pass
                # must be allowed to replay/retry this valid instance.
                return replace(finding, candidates=(candidate,), cursor={})
            if finding.outcome is FalsificationOutcome.TRANSIENT_FAILURE:
                return finding

        if not results or any(item.get("status") == "error" for item in results):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.TRANSIENT_FAILURE,
                reason=(
                    "one or more SMT backends failed before a Lean-checked candidate was found; "
                    f"diagnostics={json.dumps(diagnostic, sort_keys=True)}"
                )[:1000],
                elapsed_s=time.monotonic() - started,
                error_kind="infrastructure",
            )
        if all(item.get("status") in {"unsat", "unknown"} for item in results):
            reason = "SMT found no candidate; UNSAT/UNKNOWN is advisory and not proof evidence"
        elif conversion_errors:
            reason = "SMT models were unusable: " + "; ".join(conversion_errors)
        else:
            reason = "SMT backends produced no replayable candidate"
        return FalsificationFinding(
            self.name,
            FalsificationOutcome.INCONCLUSIVE,
            reason=f"{reason}; diagnostics={json.dumps(diagnostic, sort_keys=True)}"[
                :1000
            ],
            elapsed_s=time.monotonic() - started,
            cursor={"plan_hash": translation.query_hash, "next_index": 1},
        )
