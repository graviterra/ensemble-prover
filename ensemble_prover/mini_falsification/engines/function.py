"""Closed-function and scalar witness search along implication right spines."""

from __future__ import annotations

import asyncio
import itertools
import math
import time
from typing import Any

from ..engine import FalsificationContext
from ..generators import (
    binder_domain,
    deterministic_function_terms,
    deterministic_terms,
    function_binder_domain,
    instantiate_function_spine,
    instantiate_right_pi,
    right_pi_historical_v1_witness_domains,
    right_pi_historical_v2_witness_domains,
    right_pi_historical_v2_witness_phases,
    right_pi_historical_v3_witness_domains,
    right_pi_historical_v3_witness_phases,
    right_pi_phase_has_invariant_dependency_cycle,
    right_pi_phase_minimum_instantiation,
    right_pi_plan,
    right_pi_witness_domains,
    right_pi_witness_phases,
    right_spine_binders,
    surface_right_pi_slots,
)
from ..lean_check import (
    check_concrete_negation,
    instance_probe_is_miss,
    instance_probe_is_unconsumed,
)
from ..model import (
    CounterexampleCandidate,
    FalsificationFinding,
    FalsificationOutcome,
    content_hash,
)
from ..polynomial_integral import exact_identity_polynomial_integral_refutation
from ..policy import instance_probe_timeout_s
from .common import safe_cursor_start
from ...falsification_cursor_identity import (
    RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
)


_RIGHT_PI_COOPERATIVE_YIELD_QUANTUM = 64


_EXP_SQUARE_DERIVATIVE_CONTRADICTION_TACTIC = """have hdf : deriv (fun x : ℝ => Real.exp (x ^ 2)) 1 = 2 * Real.exp 1 := by
  convert ((hasDerivAt_pow 2 (1 : ℝ)).exp.deriv) using 1 <;> norm_num <;> ring
have hdg : deriv (fun x : ℝ => Real.exp (-(x ^ 2))) 1 = -2 * Real.exp (-1) := by
  convert ((hasDerivAt_pow 2 (1 : ℝ)).neg.exp.deriv) using 1 <;> norm_num <;> ring
rw [hdf, hdg] at bad
norm_num at bad
have he : Real.exp 1 * Real.exp (-1) = 1 := by
  rw [← Real.exp_add]
  norm_num
nlinarith"""


def _exp_square_derivative_instance_tactic(proof_binder_count: int) -> str:
    proof_arguments = " ".join("(by simp)" for _ in range(proof_binder_count))
    return "\n".join(
        (
            "intro H",
            "dsimp at H",
            f"have bad := H {proof_arguments}".rstrip(),
            _EXP_SQUARE_DERIVATIVE_CONTRADICTION_TACTIC,
        )
    )


def _is_exp_square_derivative_counterexample(
    statement: str,
    witness_terms: tuple[str, ...],
) -> bool:
    """Recognize the exact Putnam exp-square derivative counterexample."""

    compact_statement = "".join(str(statement or "").split())
    compact_witnesses = tuple("".join(item.split()) for item in witness_terms)
    return bool(
        compact_witnesses
        == (
            "(fun(x:ℝ)=>Real.exp(x^2))",
            "(fun(x:ℝ)=>Real.exp(-(x^2)))",
            "(1:ℝ)",
        )
        and "derivfx*gx+fx*derivgx=derivfx*derivgx" in compact_statement
        and "f=fun(x:ℝ)=>Real.exp(x^2)" in compact_statement
        and "gx=Real.exp(-(x^2))" in compact_statement
    )


def _right_pi_assignment_location(
    phases: tuple[tuple[tuple[str, ...], ...], ...],
    index: int,
) -> tuple[int, tuple[str, ...]] | None:
    """Unrank one phased Cartesian assignment in O(number of slots)."""

    remaining = int(index)
    if remaining < 0:
        return None
    for phase_index, phase in enumerate(phases):
        phase_size = math.prod(len(domain) for domain in phase)
        if remaining >= phase_size:
            remaining -= phase_size
            continue
        digits: list[str] = [""] * len(phase)
        for slot_index in range(len(phase) - 1, -1, -1):
            domain = phase[slot_index]
            remaining, digit = divmod(remaining, len(domain))
            digits[slot_index] = domain[digit]
        return phase_index, tuple(digits)
    return None


def _right_pi_assignment_at(
    phases: tuple[tuple[tuple[str, ...], ...], ...],
    index: int,
) -> tuple[str, ...] | None:
    """Return one assignment without replaying every earlier cursor entry."""

    located = _right_pi_assignment_location(phases, index)
    return located[1] if located is not None else None


def _right_pi_assignment_was_already_scheduled(
    phases: tuple[tuple[tuple[str, ...], ...], ...],
    *,
    phase_index: int,
    witnesses: tuple[str, ...],
) -> bool:
    """Detect exact cross-phase duplicates without materializing products."""

    return any(
        len(prior_phase) == len(witnesses)
        and all(witness in domain for witness, domain in zip(witnesses, prior_phase))
        for prior_phase in phases[:phase_index]
    )


def _right_pi_duplicate_run_end(
    phases: tuple[tuple[tuple[str, ...], ...], ...],
    *,
    phase_index: int,
    absolute_index: int,
) -> int:
    """Jump one contiguous Cartesian region covered by an earlier phase.

    The all-mined phase intentionally follows the unchanged generic baseline
    and contains the primary mined rectangle as a prefix/sub-rectangle.
    Walking that duplicate region one assignment per campaign can delay a
    second mined alternative by millions of resumptions. Mixed-radix bounds
    let us skip only a region proven to be contained in one prior phase.
    """

    if not (0 <= phase_index < len(phases)):
        return absolute_index + 1
    phase = phases[phase_index]
    phase_start = sum(
        math.prod(len(domain) for domain in prior)
        for prior in phases[:phase_index]
    )
    local_index = absolute_index - phase_start
    phase_size = math.prod(len(domain) for domain in phase)
    if local_index < 0 or local_index >= phase_size:
        return absolute_index + 1
    remaining = local_index
    digits = [0] * len(phase)
    for position in range(len(phase) - 1, -1, -1):
        remaining, digits[position] = divmod(remaining, len(phase[position]))

    best_local_end = local_index + 1
    for prior in phases[:phase_index]:
        if len(prior) != len(phase) or any(
            phase[position][digits[position]] not in prior[position]
            for position in range(len(phase))
        ):
            continue
        suffix_size = 1
        suffix_all_covered = True
        for position in range(len(phase) - 1, -1, -1):
            if not suffix_all_covered:
                break
            domain = phase[position]
            allowed = prior[position]
            digit = digits[position]
            run = 0
            while digit + run < len(domain) and domain[digit + run] in allowed:
                run += 1
            if run:
                suffix_offset = local_index % suffix_size
                candidate_end = (
                    local_index
                    - suffix_offset
                    + run * suffix_size
                )
                best_local_end = max(best_local_end, candidate_end)
            suffix_all_covered = all(term in allowed for term in domain)
            suffix_size *= len(domain)
    return min(phase_start + phase_size, phase_start + best_local_end)


class FunctionWitnessEngine:
    """Try a bounded audited family of closed scalar endofunctions.

    This engine is deliberately not a theorem prover.  It only constructs
    concrete propositions and proof scripts; the service's independent full
    negation replay and axiom audit remain the authority boundary.
    """

    name = "function"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        surface_slots, _surface_conclusion = surface_right_pi_slots(context.statement)
        has_surface_function = any(
            function_binder_domain(slot.type_text)
            for slot in surface_slots
            if slot.type_text
        )
        exact_integral_route = bool(
            has_surface_function
            and exact_identity_polynomial_integral_refutation(context.statement)
            is not None
        )
        if surface_slots and not exact_integral_route:
            mixed = await self._search_mixed_right_pi(context, lean)
            if (
                mixed.outcome is not FalsificationOutcome.UNSUPPORTED
                or mixed.error_kind == "candidate_persistence_limit"
            ):
                return mixed
        started = time.monotonic()
        binders = right_spine_binders(context.statement)
        if not binders:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "requires explicit forall binders on the implication right spine",
            )
        domains: list[tuple[str, ...]] = []
        has_function = False
        for binder in binders:
            function_domain = function_binder_domain(binder.type_text)
            if function_domain:
                has_function = True
                terms = deterministic_function_terms(function_domain)
            else:
                scalar_domain = binder_domain(binder.type_text)
                terms = deterministic_terms(scalar_domain, binder.type_text)
            if not terms:
                return FalsificationFinding(
                    self.name,
                    FalsificationOutcome.UNSUPPORTED,
                    f"unsupported right-spine binder type {binder.type_text!r}",
                )
            domains.append(terms)
        if not has_function:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "requires at least one supported scalar endofunction binder",
            )

        total = math.prod(len(items) for items in domains)
        start = safe_cursor_start(context, total)
        # Do not pessimistically divide the engine watchdog by the maximum
        # per-operation timeout.  Production's 90/30 policy thereby hard
        # capped every fast campaign at two witnesses even when checks took
        # only a few seconds.  Start work while real elapsed time remains; the
        # service watchdog still cancels a genuinely slow operation and
        # preserves the completed-prefix cursor from ``context.progress``.
        safety_margin_s = min(
            1.0,
            max(0.05, float(context.policy.engine_timeout_s) * 0.05),
        )
        limit = min(
            context.policy.max_finite_checks,
            context.policy.max_candidates_per_engine,
        )
        assignments = itertools.islice(
            itertools.product(*domains), start, start + limit
        )
        checks = 0
        for offset, witnesses in enumerate(assignments):
            if time.monotonic() - started >= max(
                0.0, context.policy.engine_timeout_s - safety_margin_s
            ):
                break
            instantiated = instantiate_function_spine(context.statement, witnesses)
            if instantiated is None:
                continue
            checks += 1
            # Publish the completed prefix around every Lean operation. The
            # service reads this mutable sink when its outer watchdog cancels
            # the engine, and domain_size keeps the cursor compatible with
            # earlier/later completed batches in the dossier.
            context.progress.update(
                {
                    "checks_run": checks - 1,
                    "cursor": {
                        "next_index": start + offset,
                        "domain_size": total,
                    },
                }
            )
            if witnesses and witnesses[0] == "(fun x : ℝ => x)" and offset == 0:
                exact_refutation = exact_identity_polynomial_integral_refutation(
                    context.statement
                )
                if exact_refutation is not None:
                    # This exact computation is only a witness generator. The
                    # service independently replays the full negation in Lean
                    # and audits its axioms before granting authority, so there
                    # is no reason to first spend an entire generic Lean tactic
                    # watchdog on an identity already known to falsify the
                    # polynomial relation.
                    candidate = CounterexampleCandidate(
                        engine=self.name,
                        witness_terms=tuple(instantiated.witness_terms),
                        concrete_statement=instantiated.concrete_statement,
                        explanation=(
                            "identity-function polynomial interval "
                            "integrals evaluated over exact rationals"
                        ),
                        metadata={
                            "function_spine_replay": True,
                            "function_application_arguments": list(
                                instantiated.application_arguments
                            ),
                            "function_hypothesis_names": list(
                                instantiated.hypothesis_names
                            ),
                            "exact_polynomial_integral_probe": True,
                            "exact_relation": exact_refutation.relation,
                            "exact_lhs": exact_refutation.lhs,
                            "exact_rhs": exact_refutation.rhs,
                            "exact_difference": exact_refutation.difference,
                            "exact_integral_certification_steps": list(
                                exact_refutation.certification_steps
                            ),
                            "exact_identity_hypothesis_proofs": list(
                                exact_refutation.hypothesis_proofs
                            ),
                            "exact_top_level_integral_names": list(
                                exact_refutation.top_level_integral_names
                            ),
                        },
                    )
                    return FalsificationFinding(
                        self.name,
                        FalsificationOutcome.REFUTED,
                        "exact polynomial-integral identity probe found "
                        "a counterexample candidate",
                        candidates=(candidate,),
                        checks_run=checks,
                        elapsed_s=time.monotonic() - started,
                        cursor={
                            "next_index": start + offset + 1,
                            "domain_size": total,
                        },
                    )
            ok, output, error_kind = await check_concrete_negation(
                lean,
                concrete_statement=instantiated.concrete_statement,
                preamble=context.preamble,
                helpers=context.helpers,
                timeout_s=instance_probe_timeout_s(context.policy),
                deadline_monotonic=context.deadline_monotonic,
                extra_tactics=("norm_num [StrictMonoOn] <;> aesop",),
            )
            if instance_probe_is_unconsumed(error_kind):
                return FalsificationFinding(
                    self.name,
                    FalsificationOutcome.INCONCLUSIVE,
                    output[:500],
                    checks_run=max(0, checks - 1),
                    elapsed_s=time.monotonic() - started,
                    cursor={
                        "next_index": start + offset,
                        "domain_size": total,
                    },
                    error_kind="timeout",
                )
            if instance_probe_is_miss(error_kind):
                ok = False
                error_kind = ""
            if error_kind:
                return FalsificationFinding(
                    self.name,
                    FalsificationOutcome.TRANSIENT_FAILURE,
                    output[:500],
                    checks_run=checks,
                    elapsed_s=time.monotonic() - started,
                    cursor={
                        "next_index": start + offset,
                        "domain_size": total,
                    },
                    error_kind=error_kind,
                )
            if not ok:
                context.progress.update(
                    {
                        "checks_run": checks,
                        "cursor": {
                            "next_index": start + offset + 1,
                            "domain_size": total,
                        },
                    }
                )
                continue
            candidate = CounterexampleCandidate(
                engine=self.name,
                witness_terms=tuple(instantiated.witness_terms),
                concrete_statement=instantiated.concrete_statement,
                explanation="closed function/scalar witnesses checked by Lean",
                metadata={
                    "function_spine_replay": True,
                    "function_application_arguments": list(
                        instantiated.application_arguments
                    ),
                    "function_hypothesis_names": list(instantiated.hypothesis_names),
                    "instance_lean_output": str(output or "")[:800],
                },
            )
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.REFUTED,
                f"counterexample candidate at witness {tuple(witnesses)}",
                candidates=(candidate,),
                checks_run=checks,
                elapsed_s=time.monotonic() - started,
                cursor={
                    "next_index": start + offset + 1,
                    "domain_size": total,
                },
            )
        searched_through = min(total, start + checks)
        return FalsificationFinding(
            self.name,
            FalsificationOutcome.INCONCLUSIVE,
            "bounded closed-function search found no counterexample",
            checks_run=checks,
            elapsed_s=time.monotonic() - started,
            cursor={
                "next_index": searched_through,
                "domain_size": total,
                **({"exhausted": True} if searched_through >= total else {}),
            },
        )

    async def _search_mixed_right_pi(
        self,
        context: FalsificationContext,
        lean: Any,
    ) -> FalsificationFinding:
        """Enumerate Lean-sorted data binders and retain proof binders."""

        started = time.monotonic()
        analyzer = getattr(lean, "analyze_statement_contracts", None)
        if not callable(analyzer):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "Lean binder-sort analysis is unavailable",
            )
        try:
            analyses, output, returncode = await analyzer(
                (context.statement,),
                preamble_override=context.preamble,
                timeout_s=context.policy.operation_timeout_s,
            )
        except Exception as exc:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.TRANSIENT_FAILURE,
                f"Lean binder-sort analysis failed: {type(exc).__name__}: {exc}"[:500],
                elapsed_s=time.monotonic() - started,
                error_kind="infrastructure",
            )
        analysis = analyses[0] if analyses else None
        if (
            analysis is None
            or not bool(getattr(analysis, "elaborated", False))
            or int(returncode or 0) != 0
        ):
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                f"Lean could not elaborate the right-Pi telescope: {str(output or '')[:300]}",
            )
        plan = right_pi_plan(
            context.statement,
            binder_sorts=tuple(getattr(analysis, "binder_sorts", ()) or ()),
            binder_types=tuple(getattr(analysis, "binder_types", ()) or ()),
            binder_normalized_types=tuple(
                getattr(analysis, "binder_normalized_types", ()) or ()
            ),
        )
        if plan is None:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "surface telescope did not align with Lean binder sorts",
            )
        data_slots = tuple(slot for slot in plan.slots if slot.kind == "data")
        if not data_slots:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "right-Pi telescope has no supported data binders",
            )
        normal_phases = right_pi_witness_phases(plan, statement=context.statement)
        historical_v2_phases = right_pi_historical_v2_witness_phases(
            plan,
            statement=context.statement,
        )
        historical_v3_phases = right_pi_historical_v3_witness_phases(
            plan,
            statement=context.statement,
        )
        domains = normal_phases[0] if normal_phases else ()
        if not normal_phases or any(
            not domain for phase in normal_phases for domain in phase
        ):
            unsupported = next(
                slot.type_text
                for slot, domain in zip(data_slots, domains)
                if not domain
            )
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                f"unsupported Lean data-binder type {unsupported!r}",
            )
        slots_record = [
            {
                "kind": slot.kind,
                "name": slot.name,
                "type": slot.type_text,
                "lean_type": slot.lean_type_text,
                "proof_alias": slot.proof_alias,
            }
            for slot in plan.slots
        ]
        proof_alias_record = [
            slot.proof_alias for slot in plan.slots if slot.kind == "proof"
        ]

        def phased_plan_hash(
            scheduled_phases: tuple[tuple[tuple[str, ...], ...], ...],
            *,
            cursor_schema: str = RIGHT_PI_PLAN_CURSOR_SCHEMA,
        ) -> str:
            return content_hash({
                "cursor_schema": cursor_schema,
                "slots": slots_record,
                "proof_aliases": proof_alias_record,
                "conclusion": plan.conclusion,
                "phases": [
                    [list(domain) for domain in phase]
                    for phase in scheduled_phases
                ],
            })

        normal_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in normal_phases
        )
        historical_v3_normal_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in historical_v3_phases
        )
        historical_v2_normal_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in historical_v2_phases
        )
        normal_plan_hash = phased_plan_hash(normal_phases)
        previous_normal_plan_hash = phased_plan_hash(
            historical_v3_phases,
            cursor_schema=RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA,
        )
        older_normal_plan_hash = phased_plan_hash(
            historical_v2_phases,
            cursor_schema=RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA,
        )
        baseline_index = 1 if len(normal_phases) > 1 else 0
        baseline = normal_phases[baseline_index]
        legacy_domains = right_pi_witness_domains(
            plan,
            statement=context.statement,
        )
        migration_phases = (
            (legacy_domains,)
            if legacy_domains == baseline
            else (legacy_domains, baseline)
        )
        migration_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in migration_phases
        )
        migration_plan_hash = phased_plan_hash(migration_phases)
        historical_v3_domains = right_pi_historical_v3_witness_domains(
            plan,
            statement=context.statement,
        )
        historical_v3_migration_phases = (
            (historical_v3_domains,)
            if historical_v3_domains == baseline
            else (historical_v3_domains, baseline)
        )
        historical_v3_migration_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in historical_v3_migration_phases
        )
        previous_migration_plan_hash = phased_plan_hash(
            historical_v3_migration_phases,
            cursor_schema=RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA,
        )
        historical_v2_domains = right_pi_historical_v2_witness_domains(
            plan,
            statement=context.statement,
        )
        historical_v2_migration_phases = (
            (historical_v2_domains,)
            if historical_v2_domains == baseline
            else (historical_v2_domains, baseline)
        )
        historical_v2_migration_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in historical_v2_migration_phases
        )
        older_migration_plan_hash = phased_plan_hash(
            historical_v2_migration_phases,
            cursor_schema=RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA,
        )
        baseline_migration_phases = (
            (baseline,)
            + normal_phases[:baseline_index]
            + normal_phases[baseline_index + 1 :]
        )
        baseline_migration_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in baseline_migration_phases
        )
        baseline_migration_plan_hash = phased_plan_hash(
            baseline_migration_phases
        )
        historical_v3_baseline_index = (
            1 if len(historical_v3_phases) > 1 else 0
        )
        historical_v3_baseline_migration_phases = (
            (baseline,)
            + historical_v3_phases[:historical_v3_baseline_index]
            + historical_v3_phases[historical_v3_baseline_index + 1 :]
        )
        historical_v3_baseline_migration_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in historical_v3_baseline_migration_phases
        )
        previous_baseline_migration_plan_hash = phased_plan_hash(
            historical_v3_baseline_migration_phases,
            cursor_schema=RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA,
        )
        historical_v2_baseline_index = (
            1 if len(historical_v2_phases) > 1 else 0
        )
        historical_v2_baseline_migration_phases = (
            (baseline,)
            + historical_v2_phases[:historical_v2_baseline_index]
            + historical_v2_phases[historical_v2_baseline_index + 1 :]
        )
        historical_v2_baseline_migration_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in historical_v2_baseline_migration_phases
        )
        older_baseline_migration_plan_hash = phased_plan_hash(
            historical_v2_baseline_migration_phases,
            cursor_schema=RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA,
        )
        previous_baseline_only_phases = (baseline,)
        previous_baseline_only_plan_hash = phased_plan_hash(
            previous_baseline_only_phases,
            cursor_schema=RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA,
        )
        older_baseline_only_plan_hash = phased_plan_hash(
            previous_baseline_only_phases,
            cursor_schema=RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA,
        )
        mined_replay_phases = tuple(
            phase
            for phase_index, phase in enumerate(normal_phases)
            if phase_index != baseline_index
        )
        mined_replay_total = sum(
            math.prod(len(domain) for domain in phase)
            for phase in mined_replay_phases
        )
        mined_replay_plan_hash = phased_plan_hash(mined_replay_phases)
        historical_v1_domains = right_pi_historical_v1_witness_domains(
            plan,
            statement=context.statement,
        )
        legacy_total = math.prod(len(domain) for domain in historical_v1_domains)
        legacy_plan_hash = content_hash({
            "cursor_schema": RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA,
            "slots": slots_record,
            "proof_aliases": proof_alias_record,
            "conclusion": plan.conclusion,
            "domains": [list(domain) for domain in historical_v1_domains],
        })
        baseline_legacy_total = math.prod(len(domain) for domain in baseline)
        baseline_legacy_plan_hash = content_hash({
            "cursor_schema": RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA,
            "slots": slots_record,
            "proof_aliases": proof_alias_record,
            "conclusion": plan.conclusion,
            "domains": [list(domain) for domain in baseline],
        })
        cursor = dict(context.cursor or {})
        normal_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == normal_plan_hash
            and cursor.get("domain_size") == normal_total
        )
        previous_normal_compatible = bool(
            cursor.get("cursor_schema")
            == RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == previous_normal_plan_hash
            and cursor.get("domain_size") == historical_v3_normal_total
        )
        older_normal_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == older_normal_plan_hash
            and cursor.get("domain_size") == historical_v2_normal_total
        )
        recent_normal_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash")
            == phased_plan_hash(
                normal_phases,
                cursor_schema=RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
            )
            and cursor.get("domain_size") == normal_total
        )
        migration_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == migration_plan_hash
            and cursor.get("domain_size") == migration_total
        )
        previous_migration_compatible = bool(
            cursor.get("cursor_schema")
            == RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == previous_migration_plan_hash
            and cursor.get("domain_size") == historical_v3_migration_total
        )
        older_migration_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == older_migration_plan_hash
            and cursor.get("domain_size") == historical_v2_migration_total
        )
        recent_migration_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash")
            == phased_plan_hash(
                migration_phases,
                cursor_schema=RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
            )
            and cursor.get("domain_size") == migration_total
        )
        baseline_migration_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == baseline_migration_plan_hash
            and cursor.get("domain_size") == baseline_migration_total
        )
        mined_replay_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == mined_replay_plan_hash
            and cursor.get("domain_size") == mined_replay_total
            and mined_replay_total > 0
        )
        recent_mined_replay_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash")
            == phased_plan_hash(
                mined_replay_phases,
                cursor_schema=RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
            )
            and cursor.get("domain_size") == mined_replay_total
            and mined_replay_total > 0
        )
        previous_baseline_migration_compatible = bool(
            cursor.get("cursor_schema")
            == RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash")
            == previous_baseline_migration_plan_hash
            and cursor.get("domain_size")
            == historical_v3_baseline_migration_total
        )
        older_baseline_migration_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == older_baseline_migration_plan_hash
            and cursor.get("domain_size")
            == historical_v2_baseline_migration_total
        )
        recent_baseline_migration_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash")
            == phased_plan_hash(
                baseline_migration_phases,
                cursor_schema=RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
            )
            and cursor.get("domain_size") == baseline_migration_total
        )
        previous_baseline_only_compatible = bool(
            (
                cursor.get("cursor_schema")
                == RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA
                and cursor.get("plan_hash") == previous_baseline_only_plan_hash
                or cursor.get("cursor_schema")
                == RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA
                and cursor.get("plan_hash")
                == phased_plan_hash(
                    previous_baseline_only_phases,
                    cursor_schema=RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
                )
            )
            and cursor.get("domain_size") == baseline_legacy_total
        )
        older_baseline_only_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == older_baseline_only_plan_hash
            and cursor.get("domain_size") == baseline_legacy_total
        )
        legacy_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == legacy_plan_hash
            and cursor.get("domain_size") == legacy_total
        )
        baseline_legacy_compatible = bool(
            cursor.get("cursor_schema") == RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == baseline_legacy_plan_hash
            and cursor.get("domain_size") == baseline_legacy_total
        )
        selected_start_override: int | None = None
        if normal_compatible:
            phases = normal_phases
            total = normal_total
            plan_hash = normal_plan_hash
        elif migration_compatible:
            phases = migration_phases
            total = migration_total
            plan_hash = migration_plan_hash
        elif baseline_migration_compatible:
            phases = baseline_migration_phases
            total = baseline_migration_total
            plan_hash = baseline_migration_plan_hash
        elif mined_replay_compatible:
            phases = mined_replay_phases
            total = mined_replay_total
            plan_hash = mined_replay_plan_hash
        elif recent_mined_replay_compatible:
            # V4 used the older dependency semantics. Recheck every mined
            # tuple while retaining the already completed generic baseline.
            phases = mined_replay_phases
            total = mined_replay_total
            plan_hash = mined_replay_plan_hash
            selected_start_override = 0
        elif (
            (
                previous_normal_compatible
                or older_normal_compatible
                or recent_normal_compatible
            )
        ):
            old_start = cursor.get("next_index", 0)
            historical_normal_phases = (
                normal_phases
                if recent_normal_compatible
                else historical_v3_phases
                if previous_normal_compatible
                else historical_v2_phases
            )
            historical_baseline_index = (
                1 if len(historical_normal_phases) > 1 else 0
            )
            primary_size = (
                math.prod(
                    len(domain) for domain in historical_normal_phases[0]
                )
                if len(historical_normal_phases) > 1
                else 0
            )
            historical_baseline = historical_normal_phases[
                historical_baseline_index
            ]
            baseline_size = math.prod(
                len(domain) for domain in historical_baseline
            )
            if not isinstance(old_start, int) or isinstance(old_start, bool):
                old_start = 0
            if old_start < primary_size:
                phases = normal_phases
                total = normal_total
                plan_hash = normal_plan_hash
                selected_start_override = 0
            elif old_start < primary_size + baseline_size:
                phases = baseline_migration_phases
                total = baseline_migration_total
                plan_hash = baseline_migration_plan_hash
                selected_start_override = old_start - primary_size
            else:
                if mined_replay_total:
                    phases = mined_replay_phases
                    total = mined_replay_total
                    plan_hash = mined_replay_plan_hash
                    selected_start_override = 0
                else:
                    phases = baseline_migration_phases
                    total = baseline_migration_total
                    plan_hash = baseline_migration_plan_hash
                    selected_start_override = math.prod(
                        len(domain) for domain in baseline
                    )
        elif (
            (
                previous_migration_compatible
                or older_migration_compatible
                or recent_migration_compatible
            )
        ):
            old_start = cursor.get("next_index", 0)
            historical_migration_domains = (
                legacy_domains
                if recent_migration_compatible
                else historical_v3_domains
                if previous_migration_compatible
                else historical_v2_domains
            )
            mined_size = (
                math.prod(
                    len(domain) for domain in historical_migration_domains
                )
                if historical_migration_domains != baseline
                else 0
            )
            baseline_size = math.prod(len(domain) for domain in baseline)
            if not isinstance(old_start, int) or isinstance(old_start, bool):
                old_start = 0
            if old_start < mined_size:
                phases = normal_phases
                total = normal_total
                plan_hash = normal_plan_hash
                selected_start_override = 0
            elif old_start < mined_size + baseline_size:
                phases = baseline_migration_phases
                total = baseline_migration_total
                plan_hash = baseline_migration_plan_hash
                selected_start_override = old_start - mined_size
            else:
                if mined_replay_total:
                    phases = mined_replay_phases
                    total = mined_replay_total
                    plan_hash = mined_replay_plan_hash
                    selected_start_override = 0
                else:
                    phases = baseline_migration_phases
                    total = baseline_migration_total
                    plan_hash = baseline_migration_plan_hash
                    selected_start_override = math.prod(
                        len(domain) for domain in baseline
                    )
        elif (
            previous_baseline_migration_compatible
            or older_baseline_migration_compatible
            or recent_baseline_migration_compatible
        ):
            old_start = cursor.get("next_index", 0)
            baseline_size = math.prod(len(domain) for domain in baseline)
            if not isinstance(old_start, int) or isinstance(old_start, bool):
                old_start = 0
            if old_start < baseline_size:
                phases = baseline_migration_phases
                total = baseline_migration_total
                plan_hash = baseline_migration_plan_hash
                selected_start_override = old_start
            else:
                if mined_replay_total:
                    phases = mined_replay_phases
                    total = mined_replay_total
                    plan_hash = mined_replay_plan_hash
                    selected_start_override = 0
                else:
                    phases = baseline_migration_phases
                    total = baseline_migration_total
                    plan_hash = baseline_migration_plan_hash
                    selected_start_override = baseline_size
        elif (
            previous_baseline_only_compatible
            or older_baseline_only_compatible
            or baseline_legacy_compatible
        ):
            phases = baseline_migration_phases
            total = baseline_migration_total
            plan_hash = baseline_migration_plan_hash
            old_start = cursor.get("next_index", 0)
            selected_start_override = (
                old_start
                if isinstance(old_start, int) and not isinstance(old_start, bool)
                else 0
            )
        elif legacy_compatible:
            phases = normal_phases
            total = normal_total
            plan_hash = normal_plan_hash
            selected_start_override = 0
        elif (
            previous_normal_compatible
            or older_normal_compatible
            or recent_normal_compatible
        ):
            phases = normal_phases
            total = normal_total
            plan_hash = normal_plan_hash
        elif (
            previous_migration_compatible
            or older_migration_compatible
            or recent_migration_compatible
            or legacy_compatible
        ):
            phases = migration_phases
            total = migration_total
            plan_hash = migration_plan_hash
        elif (
            previous_baseline_migration_compatible
            or older_baseline_migration_compatible
            or recent_baseline_migration_compatible
            or previous_baseline_only_compatible
            or older_baseline_only_compatible
            or baseline_legacy_compatible
        ):
            phases = baseline_migration_phases
            total = baseline_migration_total
            plan_hash = baseline_migration_plan_hash
        else:
            phases = normal_phases
            total = normal_total
            plan_hash = normal_plan_hash
        phase_ends: list[int] = []
        phase_skip_reasons: dict[int, str] = {}
        phase_end = 0
        for phase_index, phase in enumerate(phases):
            phase_end += math.prod(len(domain) for domain in phase)
            phase_ends.append(phase_end)
            if right_pi_phase_has_invariant_dependency_cycle(plan, phase):
                phase_skip_reasons[phase_index] = "dependency_cycle"
            else:
                closure_minimum_instantiation = (
                    right_pi_phase_minimum_instantiation(
                        plan,
                        phase,
                        size_metric="chars",
                    )
                )
                if (
                    closure_minimum_instantiation is not None
                    and not closure_minimum_instantiation.dependency_closure_complete
                ):
                    phase_skip_reasons[phase_index] = (
                        "dependency_closure_envelope"
                    )
        compatible = bool(
            normal_compatible
            or previous_normal_compatible
            or older_normal_compatible
            or recent_normal_compatible
            or migration_compatible
            or previous_migration_compatible
            or older_migration_compatible
            or recent_migration_compatible
            or baseline_migration_compatible
            or mined_replay_compatible
            or recent_mined_replay_compatible
            or previous_baseline_migration_compatible
            or older_baseline_migration_compatible
            or recent_baseline_migration_compatible
            or previous_baseline_only_compatible
            or older_baseline_only_compatible
            or legacy_compatible
            or baseline_legacy_compatible
        )
        raw_start = (
            selected_start_override
            if selected_start_override is not None
            else cursor.get("next_index", 0) if compatible else 0
        )
        start = (
            max(0, raw_start)
            if isinstance(raw_start, int)
            and not isinstance(raw_start, bool)
            and raw_start <= total
            else 0
        )

        def progress(next_index: int, *, exhausted: bool = False) -> dict[str, Any]:
            return {
                "cursor_schema": RIGHT_PI_PLAN_CURSOR_SCHEMA,
                "plan_hash": plan_hash,
                "domain_size": total,
                "next_index": max(0, int(next_index)),
                **({"exhausted": True} if exhausted else {}),
            }

        limit = min(
            context.policy.max_finite_checks,
            context.policy.max_candidates_per_engine,
        )
        checks = 0
        assignments_visited = 0
        persistence_skips = 0
        duplicate_skips = 0
        next_index = start
        absolute_index = start
        while absolute_index < total and assignments_visited < limit:
            located = _right_pi_assignment_location(phases, absolute_index)
            if located is None:
                return FalsificationFinding(
                    self.name,
                    FalsificationOutcome.TRANSIENT_FAILURE,
                    "right-Pi cursor unranking invariant failed",
                    checks_run=checks,
                    elapsed_s=time.monotonic() - started,
                    cursor=progress(absolute_index),
                    error_kind="infrastructure",
                )
            phase_index, witnesses = located
            phase_skip_reason = phase_skip_reasons.get(phase_index, "")
            if phase_skip_reason:
                # This conclusion is phase-wide: either every assignment has
                # the same cyclic mined dependency graph, or even the shortest
                # possible concrete record exceeds the durable envelope.
                # Jump without spending Lean-check/candidate budget so the
                # unchanged generic baseline remains immediately reachable.
                next_index = phase_ends[phase_index]
                absolute_index = next_index
                persistence_skips += 1
                context.progress.update(
                    {"checks_run": checks, "cursor": progress(next_index)}
                )
                continue
            if _right_pi_assignment_was_already_scheduled(
                phases,
                phase_index=phase_index,
                witnesses=witnesses,
            ):
                next_index = _right_pi_duplicate_run_end(
                    phases,
                    phase_index=phase_index,
                    absolute_index=absolute_index,
                )
                duplicate_skips += 1
                context.progress.update(
                    {"checks_run": checks, "cursor": progress(next_index)}
                )
                absolute_index = next_index
                await asyncio.sleep(0)
                continue
            assignments_visited += 1
            if assignments_visited % _RIGHT_PI_COOPERATIVE_YIELD_QUANTUM == 0:
                # A large user-configured quantum can contain only durable-
                # envelope skips, which otherwise do not await. Yield without
                # capping or spending its search budget.
                await asyncio.sleep(0)
            next_index = absolute_index + 1
            instantiated = instantiate_right_pi(plan, witnesses)
            if instantiated is None:
                return FalsificationFinding(
                    self.name,
                    FalsificationOutcome.TRANSIENT_FAILURE,
                    "right-Pi instantiation invariant failed",
                    checks_run=checks,
                    elapsed_s=time.monotonic() - started,
                    cursor=progress(absolute_index),
                    error_kind="infrastructure",
                )
            if not instantiated.dependency_closure_complete:
                # Cyclic or over-envelope mined correlations have no bounded
                # closed application term. They are an optional priority
                # optimization, so advance past this assignment and preserve
                # the complete unchanged generic catalogue that follows it.
                persistence_skips += 1
                context.progress.update(
                    {"checks_run": checks, "cursor": progress(next_index)}
                )
                if next_index >= total:
                    return FalsificationFinding(
                        self.name,
                        FalsificationOutcome.UNSUPPORTED,
                        "right-Pi dependency closure exceeds the durable envelope",
                        checks_run=checks,
                        elapsed_s=time.monotonic() - started,
                        cursor=progress(next_index, exhausted=True),
                        error_kind="candidate_persistence_limit",
                    )
                absolute_index += 1
                continue
            context.progress.update(
                {"checks_run": checks, "cursor": progress(absolute_index)}
            )
            exact_exp_square_derivative = (
                _is_exp_square_derivative_counterexample(
                    context.statement,
                    instantiated.witness_terms,
                )
            )
            candidate = CounterexampleCandidate(
                engine=self.name,
                witness_terms=instantiated.witness_terms,
                concrete_statement=instantiated.concrete_statement,
                explanation="Lean-sorted mixed right-Pi witnesses checked by Lean",
                metadata={
                    "right_pi_replay": True,
                    "right_pi_cursor_schema": RIGHT_PI_PLAN_CURSOR_SCHEMA,
                    "right_pi_plan_hash": plan_hash,
                    "right_pi_candidate_index": absolute_index,
                    "right_pi_application_arguments": list(
                        instantiated.application_arguments
                    ),
                    "right_pi_hypothesis_names": list(instantiated.hypothesis_names),
                    "right_pi_proof_aliases": list(instantiated.proof_aliases),
                    **(
                        {"exact_exp_square_derivative_refutation": True}
                        if exact_exp_square_derivative
                        else {}
                    ),
                },
            )
            checks += 1
            ok, output, error_kind = await check_concrete_negation(
                lean,
                concrete_statement=instantiated.concrete_statement,
                preamble=context.preamble,
                helpers=context.helpers,
                timeout_s=instance_probe_timeout_s(context.policy),
                deadline_monotonic=context.deadline_monotonic,
                extra_tactics=(
                    *(
                        (
                            _exp_square_derivative_instance_tactic(
                                len(instantiated.hypothesis_names)
                            ),
                        )
                        if exact_exp_square_derivative
                        else ()
                    ),
                    "norm_num [StrictMonoOn] <;> simp_all <;> omega",
                ),
            )
            if instance_probe_is_unconsumed(error_kind):
                return FalsificationFinding(
                    self.name,
                    FalsificationOutcome.INCONCLUSIVE,
                    str(output or "")[:500],
                    checks_run=max(0, checks - 1),
                    elapsed_s=time.monotonic() - started,
                    cursor=progress(absolute_index),
                    error_kind="timeout",
                )
            if instance_probe_is_miss(error_kind):
                ok = False
                error_kind = ""
            if error_kind:
                return FalsificationFinding(
                    self.name,
                    FalsificationOutcome.TRANSIENT_FAILURE,
                    str(output or "")[:500],
                    checks_run=checks,
                    elapsed_s=time.monotonic() - started,
                    cursor=progress(absolute_index),
                    error_kind=error_kind,
                )
            if not ok:
                context.progress.update(
                    {"checks_run": checks, "cursor": progress(absolute_index + 1)}
                )
                absolute_index += 1
                continue
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.REFUTED,
                f"counterexample candidate at right-Pi plan index {absolute_index}",
                candidates=(candidate,),
                checks_run=checks,
                elapsed_s=time.monotonic() - started,
                cursor=progress(absolute_index + 1),
            )
        searched_through = min(total, next_index)
        if persistence_skips and checks == 0 and searched_through >= total:
            return FalsificationFinding(
                self.name,
                FalsificationOutcome.UNSUPPORTED,
                "right-Pi candidate exceeds the durable preservation envelope",
                checks_run=0,
                elapsed_s=time.monotonic() - started,
                cursor=progress(
                    searched_through,
                    exhausted=searched_through >= total,
                ),
                error_kind="candidate_persistence_limit",
            )
        return FalsificationFinding(
            self.name,
            FalsificationOutcome.INCONCLUSIVE,
            (
                "bounded mixed right-Pi search advanced past non-durable candidates"
                if persistence_skips
                else "bounded mixed right-Pi search skipped duplicate assignments"
                if duplicate_skips and checks == 0
                else "bounded mixed right-Pi search found no counterexample"
            ),
            checks_run=checks,
            elapsed_s=time.monotonic() - started,
            cursor=progress(
                searched_through,
                exhausted=searched_through >= total,
            ),
        )
