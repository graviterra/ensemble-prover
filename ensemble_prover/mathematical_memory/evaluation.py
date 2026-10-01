"""Frozen matched-budget evaluation with current proof checks and source exclusions.

This module supplies reproducible manifests and trials. Fixture correctness is
not an empirical usefulness result; rollout remains gated on measured evidence.
"""

from __future__ import annotations
import asyncio
import inspect
import math
import time
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Awaitable, Callable, Mapping, Sequence

from .budget import MemoryBudget
from .catalog import MemoryCatalog, MemoryUnavailable
from .model import (
    EligibilityPolicy,
    EvidenceReference,
    GenerationPin,
    content_digest,
    integer,
    text,
)


class EvaluationVariant(str, Enum):
    EXISTING = "existing"
    PROFILE = "profile"
    EXPERIENCE = "experience"
    GENERALIZATION = "generalization"


_VERIFIED_ROOT = object()


@dataclass(frozen=True)
class EvaluationCase:
    case_id: str
    target_statement: str
    problem_id: str
    family_id: str
    split: str = "held_out"
    excluded_source_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        for field_name in ("case_id", "target_statement", "problem_id", "family_id"):
            text(getattr(self, field_name), field_name)
        if self.split not in {"training", "held_out"}:
            raise ValueError("unknown evaluation split")
        if not isinstance(self.excluded_source_ids, (tuple, list)):
            raise ValueError("excluded sources require a sequence")
        object.__setattr__(self, "excluded_source_ids", tuple(self.excluded_source_ids))
        for source in self.excluded_source_ids:
            text(source, "excluded source")

    def to_record(self) -> dict[str, Any]:
        return {
            "case_id": self.case_id,
            "target_statement": self.target_statement,
            "problem_id": self.problem_id,
            "family_id": self.family_id,
            "split": self.split,
            "excluded_source_ids": self.excluded_source_ids,
        }


@dataclass(frozen=True)
class FrozenEvaluationManifest:
    model_id: str
    toolchain_id: str
    budget_seconds: float
    initial_pin: GenerationPin
    initial_source_ids: tuple[str, ...]
    corpus_event_digests: tuple[str, ...]
    visible_scopes: tuple[tuple[str, str], ...]
    cases: tuple[EvaluationCase, ...]
    repetitions: int = 1
    primary_endpoint: str = "verified_root_solves"
    regression_margin: float = 0.0
    uncertainty_method: str = "paired_predeclared"
    provider_token_cap: int = 0
    provider_cost_cap: float = 0.0
    policy_version: int = 1
    chronology_campaign_id: str = ""
    chronology_cutoff: int | None = None
    manifest_id: str = ""
    schema_version: int = 1

    def __post_init__(self) -> None:
        for name in (
            "model_id",
            "toolchain_id",
            "primary_endpoint",
            "uncertainty_method",
        ):
            text(getattr(self, name), name)
        if self.primary_endpoint != "verified_root_solves":
            raise ValueError(
                "only independently verified root solves are currently supported"
            )
        for name in ("budget_seconds", "provider_cost_cap", "regression_margin"):
            value = getattr(self, name)
            if type(value) not in (int, float) or not math.isfinite(value) or value < 0:
                raise ValueError(f"invalid {name}")
        if self.budget_seconds <= 0 or self.regression_margin > 1:
            raise ValueError("invalid evaluation budget or regression margin")
        integer(self.repetitions, "repetitions", 1)
        integer(self.provider_token_cap, "provider token cap")
        integer(self.policy_version, "policy version", 1)
        object.__setattr__(self, "cases", tuple(self.cases))
        object.__setattr__(self, "initial_source_ids", tuple(self.initial_source_ids))
        object.__setattr__(
            self, "corpus_event_digests", tuple(self.corpus_event_digests)
        )
        object.__setattr__(
            self, "visible_scopes", tuple(tuple(item) for item in self.visible_scopes)
        )
        if not self.cases or any(
            not isinstance(case, EvaluationCase) for case in self.cases
        ):
            raise ValueError("evaluation requires typed cases")
        if len({case.case_id for case in self.cases}) != len(self.cases):
            raise ValueError("duplicate evaluation case identities")
        training = [case for case in self.cases if case.split == "training"]
        heldout = [case for case in self.cases if case.split == "held_out"]
        if not heldout:
            raise ValueError("evaluation requires held-out cases")
        for attr in ("problem_id", "family_id", "target_statement"):
            if {getattr(case, attr) for case in training}.intersection(
                getattr(case, attr) for case in heldout
            ):
                raise ValueError("training/held-out problem or family leakage")
        expected = content_digest(self.identity_payload())
        if self.manifest_id and self.manifest_id != expected:
            raise ValueError("frozen evaluation manifest identity mismatch")
        object.__setattr__(self, "manifest_id", expected)
        if self.schema_version != 1 or type(self.schema_version) is not int:
            raise ValueError("unsupported evaluation schema")
        # Validate policy, including chronology, before any runner receives it.
        self.policy_for(heldout[0])

    def identity_payload(self) -> dict[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name != "manifest_id"
        }

    def to_record(self) -> dict[str, Any]:
        return {
            **self.identity_payload(),
            "manifest_id": self.manifest_id,
            "initial_pin": self.initial_pin.to_record(),
            "cases": [case.to_record() for case in self.cases],
        }

    @classmethod
    def from_record(cls, payload: Mapping[str, Any]) -> FrozenEvaluationManifest:
        fields = dict(payload)
        fields["initial_pin"] = GenerationPin.from_record(fields["initial_pin"])
        fields["cases"] = tuple(EvaluationCase(**case) for case in fields["cases"])
        return cls(**fields)

    def policy_for(self, case: EvaluationCase) -> EligibilityPolicy:
        if case not in self.cases:
            raise ValueError("case is not in the frozen corpus")
        forbidden = set(case.excluded_source_ids)
        return EligibilityPolicy(
            allowed_source_record_ids=tuple(
                source for source in self.initial_source_ids if source not in forbidden
            ),
            excluded_problem_ids=(case.problem_id,),
            excluded_family_ids=(case.family_id,),
            visible_scopes=self.visible_scopes,
            policy_version=self.policy_version,
            chronology_campaign_id=self.chronology_campaign_id,
            chronology_cutoff=self.chronology_cutoff,
        )


def freeze_manifest(
    catalog: MemoryCatalog,
    *,
    policy: EligibilityPolicy,
    cases: Sequence[EvaluationCase],
    model_id: str,
    toolchain_id: str,
    budget_seconds: float,
    **kwargs: Any,
) -> FrozenEvaluationManifest:
    pin = catalog.generation()
    view = catalog.query(policy, pin, limit=catalog.query_scan_cap)
    if (
        not view.complete
        or view.omitted
        or any(not event.provenance.complete for event in view.events)
    ):
        raise MemoryUnavailable(
            "frozen corpus requires complete eligible event coverage and provenance"
        )
    sources = sorted(
        {
            source
            for event in view.events
            for source in event.provenance.source_record_ids
            + event.provenance.ancestry_source_ids
        }
    )
    return FrozenEvaluationManifest(
        model_id,
        toolchain_id,
        budget_seconds,
        pin,
        tuple(sources),
        tuple(event.payload_digest for event in view.events),
        policy.visible_scopes,
        tuple(cases),
        policy_version=policy.policy_version,
        chronology_campaign_id=policy.chronology_campaign_id,
        chronology_cutoff=policy.chronology_cutoff,
        **kwargs,
    )


@dataclass(frozen=True)
class TrialObservation:
    case_id: str
    variant: str
    repetition: int
    outcome: str
    wall_seconds: float
    provider_tokens: int
    provider_cost: float
    pin: GenerationPin
    proof_artifact: EvidenceReference | None = None
    diagnostic: str = ""
    verification_seal: Any = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        text(self.case_id, "trial case")
        EvaluationVariant(self.variant)
        integer(self.repetition, "repetition")
        integer(self.provider_tokens, "consumed provider tokens")
        for value in (self.wall_seconds, self.provider_cost):
            if type(value) not in (int, float) or not math.isfinite(value) or value < 0:
                raise ValueError("invalid trial resource accounting")
        if self.outcome not in {"verified_root", "inconclusive"}:
            raise ValueError("unsupported trial outcome")

    def to_record(self) -> dict[str, Any]:
        return {
            name: (
                getattr(self, name).to_record()
                if hasattr(getattr(self, name), "to_record")
                else getattr(self, name)
            )
            for name in self.__dataclass_fields__
            if name != "verification_seal"
        }


async def run_matched_trials(
    manifest: FrozenEvaluationManifest,
    catalog: MemoryCatalog,
    *,
    runner: Callable[
        [
            EvaluationCase,
            EvaluationVariant,
            FrozenEvaluationManifest,
            EligibilityPolicy,
            MemoryBudget,
        ],
        Awaitable[Mapping[str, Any]],
    ],
    verify_root: Callable[[EvaluationCase, bytes, EligibilityPolicy], Any],
    variants: Sequence[EvaluationVariant] = tuple(EvaluationVariant),
) -> tuple[TrialObservation, ...]:
    """Invoke the existing solver through an explicit budgeted adapter.

    Raw accepted/success booleans never count. The live verification callback
    must audit the exact target, environment and policy-eligible dependencies.
    This callback is a trusted controller capability, like the prover adapter;
    supplying arbitrary Python code is outside the serialized-input boundary.
    """
    if not callable(runner) or not callable(verify_root):
        raise ValueError("evaluation requires solver and current verifier adapters")
    variants = tuple(EvaluationVariant(variant) for variant in variants)
    if len(set(variants)) != len(variants):
        raise ValueError("duplicate evaluation variants")
    reports = []
    for case in manifest.cases:
        if case.split != "held_out":
            continue
        policy = manifest.policy_for(case)
        # Resolve the exact pinned population before each trial; current masks
        # may remove data but a later append cannot enter this fixed corpus.
        for repetition in range(manifest.repetitions):
            for variant in variants:
                catalog.query(policy, manifest.initial_pin, limit=1)
                started = time.monotonic()
                owner = content_digest(
                    {
                        "manifest": manifest.manifest_id,
                        "case": case.case_id,
                        "variant": variant.value,
                        "repetition": repetition,
                    }
                )
                budget = MemoryBudget(
                    owner,
                    started + manifest.budget_seconds,
                    remaining_tokens=manifest.provider_token_cap,
                    remaining_cost=manifest.provider_cost_cap,
                )
                outcome, diagnostic, ref, seal = "inconclusive", "", None, None
                tokens, cost = 0, 0.0
                try:
                    async with asyncio.timeout(budget.remaining_s()):
                        result = await runner(case, variant, manifest, policy, budget)
                        budget.check_cancelled()
                        tokens = result.get("provider_tokens", 0)
                        cost = result.get("provider_cost", 0.0)
                        integer(tokens, "actual provider tokens")
                        if (
                            type(cost) not in (int, float)
                            or not math.isfinite(cost)
                            or cost < 0
                        ):
                            raise ValueError("invalid consumed provider cost")
                        if (
                            tokens > manifest.provider_token_cap
                            or cost > manifest.provider_cost_cap
                        ):
                            raise ValueError("evaluation provider allocation exceeded")
                        proof = result.get("proof_bytes")
                        if isinstance(proof, bytes) and proof:
                            verified = verify_root(case, proof, policy)
                            if inspect.isawaitable(verified):
                                verified = await verified
                            budget.check_cancelled()
                            if verified is True:
                                ref = catalog.put_artifact(
                                    proof,
                                    kind="evaluation_root_proof",
                                    deadline_monotonic=budget.deadline_monotonic,
                                )
                                outcome = "verified_root"
                                seal = _VERIFIED_ROOT
                            else:
                                diagnostic = "independent root verification failed"
                        else:
                            diagnostic = "no independently verifiable root proof"
                except (
                    TimeoutError,
                    ValueError,
                    TypeError,
                    OSError,
                    MemoryUnavailable,
                ) as exc:
                    diagnostic = str(exc)
                reports.append(
                    TrialObservation(
                        case.case_id,
                        variant.value,
                        repetition,
                        outcome,
                        time.monotonic() - started,
                        tokens,
                        cost,
                        manifest.initial_pin,
                        ref,
                        diagnostic,
                        seal,
                    )
                )
    return tuple(reports)


def evaluation_report(
    manifest: FrozenEvaluationManifest, observations: Sequence[TrialObservation]
) -> dict[str, Any]:
    counts = {
        variant.value: {
            "verified_roots": 0,
            "inconclusive": 0,
            "wall_seconds": 0.0,
            "provider_tokens": 0,
            "provider_cost": 0.0,
        }
        for variant in EvaluationVariant
    }
    seen = set()
    heldout = {case.case_id for case in manifest.cases if case.split == "held_out"}
    for trial in observations:
        key = (trial.case_id, trial.variant, trial.repetition)
        if (
            key in seen
            or trial.case_id not in heldout
            or trial.variant not in counts
            or trial.repetition >= manifest.repetitions
            or trial.pin != manifest.initial_pin
        ):
            raise ValueError("trial does not match the frozen evaluation manifest")
        seen.add(key)
        bucket = counts[trial.variant]
        if (
            trial.outcome == "verified_root"
            and trial.proof_artifact is not None
            and trial.verification_seal is _VERIFIED_ROOT
        ):
            bucket["verified_roots"] += 1
        else:
            bucket["inconclusive"] += 1
        for field_name in ("wall_seconds", "provider_tokens", "provider_cost"):
            bucket[field_name] += getattr(trial, field_name)
    expected = len(heldout) * manifest.repetitions * len(EvaluationVariant)
    return {
        "manifest_id": manifest.manifest_id,
        "variants": counts,
        "coverage_complete": len(seen) == expected,
        "rollout_eligible": False,
        "remaining_gates": [
            "predeclared paired uncertainty analysis",
            "measured usefulness effect",
            "root regression margin",
            "median/p95 lookup overhead",
        ],
        "limitations": "Verified artifacts describe these trials only; correctness fixtures do not establish empirical transfer benefit.",
    }
