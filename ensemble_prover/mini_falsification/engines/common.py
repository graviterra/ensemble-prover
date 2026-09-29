"""Common implementation for typed, bounded Lean witness enumeration."""

from __future__ import annotations

import time
from typing import Any, Sequence

from ..engine import FalsificationContext
from ..generators import instantiate_binders
from ..lean_check import (
    check_concrete_negation,
    instance_probe_is_miss,
    instance_probe_is_unconsumed,
)
from ..model import (
    CounterexampleCandidate,
    FalsificationFinding,
    FalsificationOutcome,
)
from ..policy import instance_probe_timeout_s


def safe_cursor_start(context: FalsificationContext, total_domain_size: int) -> int:
    """Return a cursor compatible with the engine's actual finite domain.

    Index-only cursors from older checkpoints remain usable when bounded.
    Once a cursor declares ``domain_size``, however, that identity must match
    the domain the live engine just constructed.  Otherwise starting at its
    index could silently skip witnesses from a different/stale search plan.
    """

    raw_start = context.cursor.get("next_index", 0)
    if not isinstance(raw_start, int) or isinstance(raw_start, bool):
        return 0
    start = max(0, raw_start)
    total = max(0, int(total_domain_size))
    claimed_total = context.cursor.get("domain_size")
    if claimed_total is not None and (
        not isinstance(claimed_total, int)
        or isinstance(claimed_total, bool)
        or claimed_total != total
    ):
        return 0
    return 0 if start > total else start


async def check_witnesses(
    *,
    engine: str,
    context: FalsificationContext,
    lean: Any,
    witnesses: Sequence[Sequence[str]],
    complete_domain: bool = False,
    total_domain_size: int | None = None,
    explanation: str = "",
    cursor_window: bool = False,
    extra_tactics_by_witness: Sequence[Sequence[str]] = (),
    candidate_metadata: dict[str, Any] | None = None,
    transient_cursor_extras: dict[str, Any] | None = None,
) -> FalsificationFinding:
    started = time.monotonic()
    checks = 0
    # Merged into every PROGRESS-SINK cursor publication.  Engines whose
    # resume validation needs plan identity (graph: cursor_schema/plan_hash/
    # catalog_hash/domain_size) pass it here — without it a watchdog-
    # cancelled batch persisted a schema-less {"next_index": N} cursor that
    # resume rejected and the dossier merge then pinned forever.
    progress_cursor_extras = dict(transient_cursor_extras or {})
    if total_domain_size is not None:
        # The COMPLETED cursor carries domain_size; transient publications
        # must too, or the dossier merge reads None vs D as a plan-identity
        # mismatch and silently drops the completed prefix of any batch
        # cancelled AFTER a previously completed one.
        progress_cursor_extras.setdefault("domain_size", int(total_domain_size))

    def progress_cursor(next_index: int, *, exhausted: bool = False) -> dict[str, Any]:
        """Build one identity-complete cursor for every witness-loop exit."""

        return {
            **progress_cursor_extras,
            "next_index": max(0, int(next_index)),
            **({"exhausted": True} if exhausted else {}),
        }

    candidates: list[CounterexampleCandidate] = []
    if total_domain_size is not None:
        # Use the same validated origin the engine used to construct its
        # finite witness window. Otherwise a stale domain cursor can make the
        # engine slice from zero while this shared loop labels that witness as
        # a later index and republishes poisoned progress.
        start_index = safe_cursor_start(context, total_domain_size)
    else:
        raw_start = context.cursor.get("next_index", 0)
        start_index = (
            max(0, raw_start)
            if isinstance(raw_start, int) and not isinstance(raw_start, bool)
            else 0
        )
    all_witnesses = list(witnesses)
    bounded = (
        all_witnesses[: context.policy.max_candidates_per_engine]
        if cursor_window
        else all_witnesses[
            start_index : start_index + context.policy.max_candidates_per_engine
        ]
    )
    for offset, witness in enumerate(bounded):
        concrete = instantiate_binders(context.statement, witness)
        if not concrete:
            continue
        # Completed-prefix progress for the outer watchdog: if THIS check is
        # cancelled, the service publishes the prefix cursor instead of
        # discarding the batch. Absolute indexing (start_index + offset)
        # matches the loop's own in-loop transient convention in both cursor
        # modes (windowed witness lists are pre-sliced but absolutely
        # indexed).
        context.progress.update(
            {
                "checks_run": checks,
                "cursor": progress_cursor(start_index + offset),
            }
        )
        ok, output, error_kind = await check_concrete_negation(
            lean,
            concrete_statement=concrete,
            preamble=context.preamble,
            helpers=context.helpers,
            timeout_s=instance_probe_timeout_s(context.policy),
            deadline_monotonic=context.deadline_monotonic,
            extra_tactics=(
                extra_tactics_by_witness[offset]
                if offset < len(extra_tactics_by_witness)
                else ()
            ),
        )
        if instance_probe_is_unconsumed(error_kind):
            return FalsificationFinding(
                engine=engine,
                outcome=FalsificationOutcome.INCONCLUSIVE,
                reason=output[:500],
                checks_run=checks,
                elapsed_s=time.monotonic() - started,
                cursor=progress_cursor(start_index + offset),
                error_kind="timeout",
            )
        checks += 1
        if instance_probe_is_miss(error_kind):
            # The probe used its budget and did not close. Advance; idle
            # coverage can try later witnesses. Do not classify this as a
            # backend crash.
            ok = False
            error_kind = ""
        if error_kind:
            return FalsificationFinding(
                engine=engine,
                outcome=FalsificationOutcome.TRANSIENT_FAILURE,
                reason=output[:500],
                checks_run=checks,
                elapsed_s=time.monotonic() - started,
                cursor=progress_cursor(start_index + offset),
                error_kind=error_kind,
            )
        if ok:
            candidates.append(
                CounterexampleCandidate(
                    engine=engine,
                    witness_terms=tuple(witness),
                    concrete_statement=concrete,
                    explanation=explanation
                    or "Lean proved the negated concrete instance",
                    complete_domain=complete_domain,
                    metadata={
                        "instance_lean_output": output[:800],
                        **dict(candidate_metadata or {}),
                    },
                )
            )
            return FalsificationFinding(
                engine=engine,
                outcome=FalsificationOutcome.REFUTED,
                reason=f"counterexample candidate at witness {tuple(witness)}",
                candidates=tuple(candidates),
                checks_run=checks,
                elapsed_s=time.monotonic() - started,
                cursor=progress_cursor(start_index + offset + 1),
            )
        context.progress.update(
            {
                "checks_run": checks,
                "cursor": progress_cursor(start_index + offset + 1),
            }
        )
    searched_through = start_index + len(bounded)
    domain_exhausted = total_domain_size is not None and searched_through >= max(
        0, int(total_domain_size)
    )
    # This subsystem establishes refutations.  Exhaustive no-hit observations
    # are useful search evidence, but are not Lean proofs of the quantified
    # proposition and therefore never cross the mathematical trust boundary.
    outcome = FalsificationOutcome.INCONCLUSIVE
    return FalsificationFinding(
        engine=engine,
        outcome=outcome,
        reason=(
            "complete finite domain contained no counterexample (advisory only)"
            if complete_domain and domain_exhausted
            else "bounded search found no counterexample"
        ),
        checks_run=checks,
        elapsed_s=time.monotonic() - started,
        cursor=progress_cursor(searched_through, exhausted=domain_exhausted),
    )
