"""Explicit conjecture jobs and independently checked specialization links."""

from __future__ import annotations

import asyncio
import inspect
import threading
import uuid
from contextvars import copy_context
from functools import wraps
from dataclasses import asdict, dataclass, field
from typing import Any, Callable, Mapping, Sequence

from ..mini_theory.model import TheoryBundleCandidate, TheoryNeed
from ..mini_theory.worker import run_cancellable_worker
from ..deadline_guard import await_with_strict_deadline
from .model import EligibilityPolicy, MemoryProvenance
from .profiles import lean_call, DeclarationProfile, digest, record_digest, remaining


@dataclass(frozen=True)
class GeneralizationProposal:
    statement: str
    theorem_name: str
    instance_ids: tuple[str, ...]
    intended_consumers: tuple[str, ...] = ()
    rationale: str = ""
    assumptions: tuple[str, ...] = ()
    domain: str = "mathematical_memory"
    status: str = "proposed"
    schema_version: int = 1

    def __post_init__(self) -> None:
        if (
            self.schema_version != 1
            or not self.statement.strip()
            or not self.theorem_name.strip()
        ):
            raise ValueError(
                "generalization needs an explicit formal statement and name"
            )
        if self.status not in {
            "proposed",
            "investigating",
            "inconclusive",
            "checked_theorem",
            "checked_refutation",
        }:
            raise ValueError("unknown generalization status")
        for key in ("instance_ids", "intended_consumers", "assumptions"):
            object.__setattr__(self, key, tuple(getattr(self, key)))

    @property
    def proposal_id(self) -> str:
        record = self.to_record()
        record.pop("status")
        return record_digest(record)

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "GeneralizationProposal":
        return cls(**dict(record))


def propose_generalization(
    instances: Sequence[DeclarationProfile],
    *,
    statement: str,
    theorem_name: str,
    intended_consumers: Sequence[str] = (),
    rationale: str = "",
    assumptions: Sequence[str] = (),
    domain: str = "mathematical_memory",
) -> GeneralizationProposal:
    # Typed patterns suggest a conjecture only. The complete statement is always
    # supplied explicitly; no premise/data erasure becomes a theorem by counting.
    if any(not instance.complete for instance in instances):
        raise ValueError("generalization instances require complete typed profiles")
    return GeneralizationProposal(
        statement,
        theorem_name,
        tuple(dict.fromkeys(instance.declaration_id for instance in instances)),
        tuple(intended_consumers),
        rationale,
        tuple(assumptions),
        domain,
    )


def repeated_patterns(
    instances: Sequence[DeclarationProfile],
) -> tuple[tuple[DeclarationProfile, ...], ...]:
    groups: dict[tuple[Any, ...], list[DeclarationProfile]] = {}
    for instance in instances:
        if instance.complete:
            # This is a candidate grouping, never semantic anti-unification.
            key = (
                instance.binder_sorts,
                instance.binder_dependencies,
                instance.resolved_constants,
                instance.conclusion_dependencies,
            )
            groups.setdefault(key, []).append(instance)
    return tuple(
        tuple(group)
        for group in groups.values()
        if len({p.declaration_id for p in group}) > 1
    )


@dataclass(frozen=True)
class GeneralizationResult:
    proposal: GeneralizationProposal
    status: str
    reason: str = ""
    candidate: Any = field(default=None, repr=False)
    verification: Any = field(default=None, repr=False)
    publication: Any = field(default=None, repr=False)

    def to_record(self) -> dict[str, Any]:
        return {
            "proposal": self.proposal.to_record(),
            "status": self.status,
            "reason": self.reason,
            "bundle_id": getattr(self.candidate, "bundle_id", ""),
            "published": bool(getattr(self.publication, "published", False)),
        }


async def _bounded_worker(
    function: Callable[..., Any],
    *args: Any,
    budget: Any,
    cancellation_event: threading.Event | None = None,
    **kwargs: Any,
) -> Any:
    cancel = cancellation_event or threading.Event()
    context = copy_context()

    def invoke(*arguments: Any, **options: Any) -> Any:
        from ..mini_theory.environment import environment_fingerprint_scope

        def bounded() -> Any:
            with environment_fingerprint_scope(
                cancellation_event=cancel,
                deadline_monotonic=budget.deadline_monotonic,
            ):
                return function(*arguments, **options)

        return context.run(bounded)

    worker = asyncio.create_task(
        run_cancellable_worker(invoke, *args, cancellation_event=cancel, **kwargs)
    )
    watcher = None

    async def watch_owner() -> None:
        while True:
            budget.check_cancelled()
            await asyncio.sleep(min(0.05, remaining(budget)))

    try:
        if getattr(budget, "cancellation_event", None) is not None:
            watcher = asyncio.create_task(watch_owner())
            done, _pending = await asyncio.wait(
                (worker, watcher),
                timeout=remaining(budget),
                return_when=asyncio.FIRST_COMPLETED,
            )
            if watcher in done:
                await watcher
            if worker not in done:
                raise TimeoutError("generalization owner allocation exhausted")
            result = await worker
        else:
            result = await asyncio.wait_for(worker, timeout=remaining(budget))
        remaining(budget)
        return result
    except BaseException:
        cancel.set()
        if not worker.done():
            worker.cancel()
        await asyncio.gather(worker, return_exceptions=True)
        raise
    finally:
        if watcher is not None:
            watcher.cancel()
            await asyncio.gather(watcher, return_exceptions=True)


def _owned_generalization(function: Callable[..., Any]) -> Callable[..., Any]:
    @wraps(function)
    async def owned(*args: Any, budget: Any, **kwargs: Any) -> Any:
        from ensemble_prover.lean_runner import lean_resource_scope

        heartbeats = getattr(budget, "max_heartbeats", None)
        inherited = getattr(kwargs.get("runner"), "default_max_heartbeats", None)
        if type(inherited) is int and inherited > 0:
            heartbeats = (
                min(heartbeats, inherited) if type(heartbeats) is int else inherited
            )
        with lean_resource_scope(
            memory_mb=getattr(budget, "memory_mb", 8192),
            concurrency=getattr(budget, "concurrency", 1),
            max_heartbeats=heartbeats,
            deadline_monotonic=budget.deadline_monotonic,
        ):
            return await function(*args, budget=budget, **kwargs)

    return owned


@_owned_generalization
async def prove_generalization(
    proposal: GeneralizationProposal,
    candidate: TheoryBundleCandidate,
    library: Any,
    *,
    runner: Any,
    budget: Any,
    preamble: str | None = None,
    forbidden_target_statements: Sequence[str] = (),
    provenance: MemoryProvenance | None = None,
    policy: EligibilityPolicy | None = None,
    ancestry_validator: Callable[..., Any] | None = None,
) -> GeneralizationResult:
    if library.mode != "build":
        raise ValueError("generalization publication requires Mini theory build mode")
    if policy is not None and (provenance is None or not policy.permits(provenance)):
        return GeneralizationResult(
            proposal, "inconclusive", "source_ineligible", candidate
        )
    try:
        # The verifier rejects executable meta source before any Lean execution.
        from ensemble_prover.lean_runner import (
            current_lean_memory_limit,
            current_lean_heartbeat_limit,
        )

        memory_cap = getattr(budget, "memory_mb", 8192)
        heartbeat_cap = budget.max_heartbeats
        if current_lean_memory_limit() is not None:
            memory_cap = min(memory_cap, current_lean_memory_limit())
        if current_lean_heartbeat_limit() is not None:
            heartbeat_cap = min(heartbeat_cap, current_lean_heartbeat_limit())
        verification = await _bounded_worker(
            library.verify_candidate,
            candidate,
            budget=budget,
            forbidden_target_statements=forbidden_target_statements,
            deadline_monotonic=budget.deadline_monotonic,
            max_heartbeats=heartbeat_cap,
            memory_mb=memory_cap,
        )
        if not verification.accepted:
            return GeneralizationResult(
                proposal,
                "inconclusive",
                verification.receipt.diagnostic,
                candidate,
                verification,
            )
        name = f"{candidate.namespace}.{proposal.theorem_name}"
        _parsed, _output, code = await lean_call(
            runner,
            budget,
            lambda: runner.check_source_declaration_type_equivalence(
                candidate.source,
                name,
                proposal.statement,
                preamble_override=preamble,
                independent_expected_context=True,
                require_proposition=True,
                timeout_s=remaining(budget),
                max_heartbeats=getattr(budget, "max_heartbeats", None),
            ),
        )
        if code != 0:
            return GeneralizationResult(
                proposal,
                "inconclusive",
                "proposed_statement_not_verified",
                candidate,
                verification,
            )
        if ancestry_validator is not None:
            eligible = ancestry_validator(candidate, verification, provenance)
            if inspect.isawaitable(eligible):
                eligible = await eligible
            if eligible is not True:
                return GeneralizationResult(
                    proposal,
                    "inconclusive",
                    "dependency_ancestry_ineligible",
                    candidate,
                    verification,
                )
        remaining(budget)
        if policy is not None and not policy.permits(provenance):
            return GeneralizationResult(
                proposal,
                "inconclusive",
                "source_permission_changed",
                candidate,
                verification,
            )
        publication = await _bounded_worker(
            library.publish_verified, candidate, verification, budget=budget
        )
        return GeneralizationResult(
            proposal,
            "checked_theorem" if publication.published else "inconclusive",
            "" if publication.published else "publication_unavailable",
            candidate,
            verification,
            publication,
        )
    except TimeoutError:
        raise
    except OSError as exc:
        return GeneralizationResult(
            proposal, "inconclusive", type(exc).__name__, candidate
        )


@_owned_generalization
async def build_generalization(
    proposal: GeneralizationProposal,
    builder: Any,
    library: Any,
    *,
    runner: Any,
    budget: Any,
    imports: Sequence[str] = ("Mathlib",),
    dependency_bundle_ids: Sequence[str] = (),
    dependency_declarations: Sequence[str] = (),
    originating_root: str = "memory_research",
    **verification_kwargs: Any,
) -> GeneralizationResult:
    if library.mode != "build":
        raise ValueError("generalization jobs require Mini theory build mode")
    remaining(budget)
    if (
        getattr(budget, "remaining_tokens", None) == 0
        or getattr(budget, "remaining_cost", None) == 0
    ):
        return GeneralizationResult(
            proposal, "inconclusive", "provider_allowance_exhausted"
        )
    owner = getattr(budget, "provider_owner", None)
    if getattr(budget, "remaining_tokens", None) is not None:
        # Aggregate tokens need a reservation authority that also covers input;
        # an output-token setting cannot enforce this independent allowance.
        return GeneralizationResult(
            proposal, "inconclusive", "provider_token_allowance_not_bound"
        )
    cost_limit = getattr(budget, "remaining_cost", None)
    if cost_limit is not None:
        from ..llm_usage import CostBudgetController

        if not isinstance(owner, CostBudgetController) or not owner.budget_enabled:
            return GeneralizationResult(
                proposal, "inconclusive", "provider_cost_allowance_not_bound"
            )
        owner_remaining = owner.remaining_usd()
        if owner_remaining is None or owner_remaining > cost_limit:
            return GeneralizationResult(
                proposal, "inconclusive", "provider_cost_allowance_not_bound"
            )
        if not callable(getattr(builder, "with_cost_controller", None)):
            return GeneralizationResult(
                proposal, "inconclusive", "provider_cost_allowance_not_bound"
            )
        builder = builder.with_cost_controller(owner)
    if (
        owner is not None
        and callable(getattr(owner, "exhausted", None))
        and owner.exhausted()
    ):
        return GeneralizationResult(
            proposal, "inconclusive", "provider_owner_exhausted"
        )
    need = TheoryNeed(
        need_id=proposal.proposal_id,
        domain=proposal.domain,
        target_statement=proposal.statement,
        need_kind="theorem_family",
        mathematical_description=proposal.rationale
        or "Prove the explicit proposed theorem",
        originating_root=originating_root,
        consumer_node_id=proposal.proposal_id,
        consumer_statement=proposal.statement,
        required_name_hint=proposal.theorem_name,
        required_imports=tuple(imports),
        evidence_kind="generalization_proposal",
        evidence_payload=proposal.to_record(),
    )
    binder = getattr(builder, "with_operation_timeout", None)
    if callable(binder):
        builder = binder(remaining(budget))
    try:
        candidate = await await_with_strict_deadline(
            builder.build(
                need,
                imports=imports,
                dependency_bundle_ids=dependency_bundle_ids,
                dependency_declarations=dependency_declarations,
            ),
            timeout_s=remaining(budget),
            deadline_monotonic=budget.deadline_monotonic,
            operation_label="memory_generalization_candidate",
            operation_ownership="transaction_state",
        )
        remaining(budget)
        if candidate is None:
            return GeneralizationResult(
                proposal, "inconclusive", "candidate_unavailable"
            )
        if not set(candidate.imports).issubset(imports) or not set(
            candidate.dependency_bundle_ids
        ).issubset(dependency_bundle_ids):
            return GeneralizationResult(
                proposal,
                "inconclusive",
                "candidate_dependency_not_authorized",
                candidate,
            )
        authorized_names = {
            str(declaration).split(" :", 1)[0].strip()
            for declaration in dependency_declarations
        }
        caller_validator = verification_kwargs.pop("ancestry_validator", None)

        async def validate_dependencies(
            current: Any, verification: Any, provenance: Any
        ) -> bool:
            # The verified constant inventory is authoritative; lexical source
            # scans cannot detect indirect references through helper bodies.
            declarations = getattr(verification.receipt, "declarations", ())
            for declaration in declarations:
                for name in declaration.referenced_constants:
                    if (
                        name.startswith("MiniTheory.")
                        and not name.startswith(current.namespace + ".")
                        and name not in authorized_names
                    ):
                        return False
            if caller_validator is not None:
                permitted = caller_validator(current, verification, provenance)
                if inspect.isawaitable(permitted):
                    permitted = await permitted
                return permitted is True
            return True

        verification_kwargs["ancestry_validator"] = validate_dependencies
        return await prove_generalization(
            proposal,
            candidate,
            library,
            runner=runner,
            budget=budget,
            **verification_kwargs,
        )
    except TimeoutError:
        raise


@dataclass(frozen=True)
class SpecializationLink:
    generalized_name: str
    instance_statement: str
    instantiation: str
    kind: str
    checked: bool
    transfer_credit: bool = False
    reason: str = ""
    environment_id: str = ""
    proof_digest: str = ""
    source_ancestry: tuple[str, ...] = ()
    diagnostic: str = ""

    def to_record(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class CheckedRefutation:
    claim_statement: str
    negation_statement: str
    scope: str
    environment_id: str
    checked: bool
    proof_digest: str = ""
    reason: str = ""
    checked_result: Any = field(default=None, repr=False, compare=False)

    def to_record(self) -> dict[str, Any]:
        return {
            key: getattr(self, key)
            for key in (
                "claim_statement",
                "negation_statement",
                "scope",
                "environment_id",
                "checked",
                "proof_digest",
                "reason",
            )
        }


async def check_refutation(
    runner: Any,
    claim_statement: str,
    counterproof: str,
    *,
    budget: Any,
    scope: str = "exact_claim",
    environment_id: str = "",
    preamble: str | None = None,
    lemmas: Sequence[str] = (),
) -> CheckedRefutation:
    """Check an explicit negation without promoting a failed search to falsity."""
    if scope not in {"exact_claim", "scoped_instance"} or not claim_statement.strip():
        raise ValueError("refutation requires an exact formal claim and scope")
    negation = f"¬ ({claim_statement})"
    base = dict(
        claim_statement=claim_statement,
        negation_statement=negation,
        scope=scope,
        environment_id=environment_id,
        checked=False,
    )
    try:
        checked = await lean_call(
            runner,
            budget,
            lambda: runner.check(
                negation,
                counterproof,
                list(lemmas),
                preamble_override=preamble,
                timeout_s=remaining(budget),
                max_heartbeats=getattr(budget, "max_heartbeats", None),
            ),
        )
        remaining(budget)
        if checked.ok and getattr(checked, "axiom_audit_ok", None) is True:
            base["checked"] = True
            return CheckedRefutation(
                **base, proof_digest=digest(counterproof), checked_result=checked
            )
        return CheckedRefutation(**base, reason="counterproof_not_checked")
    except (TimeoutError, OSError) as exc:
        return CheckedRefutation(**base, reason=type(exc).__name__)


async def check_specialization(
    runner: Any,
    generalized_name: str,
    instance_statement: str,
    arguments: Sequence[str] = (),
    *,
    budget: Any,
    preamble: str | None = None,
    lemmas: Sequence[str] = (),
    environment_id: str = "",
    provenance: MemoryProvenance | None = None,
    policy: EligibilityPolicy | None = None,
    forbidden_support_ids: Sequence[str] = (),
    ancestry_validator: Callable[..., Any] | None = None,
) -> SpecializationLink:
    name, error = runner._normalize_check_term_name(generalized_name)
    term = f"@{name}" + "".join(f" ({argument})" for argument in arguments)
    base = dict(
        generalized_name=generalized_name,
        instance_statement=instance_statement,
        instantiation=term,
        kind="direct",
        checked=False,
        environment_id=environment_id,
    )
    if error:
        return SpecializationLink(**base, reason="invalid_declaration_name")
    if policy is not None and (provenance is None or not policy.permits(provenance)):
        return SpecializationLink(**base, reason="source_ineligible")
    witness = "memory_specialization_" + uuid.uuid4().hex
    context = runner._resolve_preamble(preamble) + "\n" + "\n".join(lemmas)
    # Infer the instantiated term without an expected type. The type-equivalence
    # gate compares that actual type to the instance; arbitrary logical transport
    # cannot masquerade as direct specialization.
    source = context + f"\nnoncomputable def {witness} := ({term})"
    _parsed, _output, code = await lean_call(
        runner,
        budget,
        lambda: runner.check_source_declaration_type_equivalence(
            source,
            witness,
            instance_statement,
            preamble_override=context,
            timeout_s=remaining(budget),
            max_heartbeats=getattr(budget, "max_heartbeats", None),
        ),
    )
    if code != 0:
        return SpecializationLink(
            **base,
            reason="instantiated_type_not_definitionally_equal",
            diagnostic=_output[-2000:],
        )
    proof = f"by exact ({term})"
    checked = await lean_call(
        runner,
        budget,
        lambda: runner.check(
            instance_statement,
            proof,
            list(lemmas),
            preamble_override=preamble,
            timeout_s=remaining(budget),
            max_heartbeats=getattr(budget, "max_heartbeats", None),
        ),
    )
    remaining(budget)
    if not checked.ok or getattr(checked, "axiom_audit_ok", None) is not True:
        return SpecializationLink(**base, reason="instance_proof_not_checked")
    ancestry = (
        tuple(provenance.source_record_ids + provenance.ancestry_source_ids)
        if provenance
        else ()
    )
    credit = bool(
        provenance
        and provenance.complete
        and policy
        and policy.permits(provenance)
        and not set(ancestry).intersection(forbidden_support_ids)
        and ancestry_validator
    )
    if credit:
        eligible = ancestry_validator(checked, term, provenance)
        if inspect.isawaitable(eligible):
            eligible = await eligible
        credit = eligible is True
    base["checked"] = True
    return SpecializationLink(
        **base,
        transfer_credit=credit,
        proof_digest=digest(proof),
        source_ancestry=ancestry,
    )


async def check_derived_consequence(
    runner: Any,
    generalized_name: str,
    instance_statement: str,
    bridge_proof: str,
    *,
    budget: Any,
    preamble: str | None = None,
    lemmas: Sequence[str] = (),
    environment_id: str = "",
    provenance: MemoryProvenance | None = None,
    policy: EligibilityPolicy | None = None,
    forbidden_support_ids: Sequence[str] = (),
    ancestry_validator: Callable[..., Any] | None = None,
) -> SpecializationLink:
    base = dict(
        generalized_name=generalized_name,
        instance_statement=instance_statement,
        instantiation=bridge_proof,
        kind="derived",
        checked=False,
        environment_id=environment_id,
    )
    if policy is not None and (provenance is None or not policy.permits(provenance)):
        return SpecializationLink(**base, reason="source_ineligible")
    name, error = runner._normalize_check_term_name(generalized_name)
    if error:
        return SpecializationLink(**base, reason="invalid_declaration_name")
    # A named, unused alias enables the existing sealed proof-use inventory
    # even when the theorem is imported and no local helpers were supplied.
    # The goal's actual constants must still include the generalized theorem.
    observed_lemmas = [
        *lemmas,
        f"noncomputable def memory_dependency_{uuid.uuid4().hex} := (@{name})",
    ]
    checked = await lean_call(
        runner,
        budget,
        lambda: runner.check(
            instance_statement,
            bridge_proof,
            observed_lemmas,
            preamble_override=preamble,
            timeout_s=remaining(budget),
            max_heartbeats=getattr(budget, "max_heartbeats", None),
        ),
    )
    remaining(budget)
    if not checked.ok or getattr(checked, "axiom_audit_ok", None) is not True:
        return SpecializationLink(**base, reason="bridge_not_checked")
    usage = getattr(checked, "helper_usage", None)
    if (
        usage is None
        or getattr(usage, "observed", False) is not True
        or not usage.complete
    ):
        return SpecializationLink(**base, reason="bridge_dependency_not_observed")
    from ..proof_dossier import canonical_lean_identifier

    constants = {canonical_lean_identifier(item) for item in usage.reachable_constants}
    if canonical_lean_identifier(generalized_name) not in constants:
        return SpecializationLink(
            **base, reason="bridge_does_not_use_generalized_theorem"
        )
    ancestry = (
        tuple(provenance.source_record_ids + provenance.ancestry_source_ids)
        if provenance
        else ()
    )
    credit = bool(
        provenance
        and provenance.complete
        and policy
        and policy.permits(provenance)
        and not set(ancestry).intersection(forbidden_support_ids)
        and ancestry_validator
    )
    if credit:
        eligible = ancestry_validator(checked, generalized_name, provenance)
        if inspect.isawaitable(eligible):
            eligible = await eligible
        credit = eligible is True
    base["checked"] = True
    return SpecializationLink(
        **base,
        transfer_credit=credit,
        proof_digest=digest(bridge_proof),
        source_ancestry=ancestry,
    )
