"""Exact application recipes, advisory probes, and checked continuations."""

from __future__ import annotations

import inspect
import math
import time
import uuid
from dataclasses import asdict, dataclass, field, replace
from typing import Any, Callable, Mapping, Sequence

from ..lean_runner import lean_residual_elaboration_context_hash
from .profiles import (
    lean_call,
    DeclarationProfile,
    GoalContextSnapshot,
    capture_goal,
    digest,
    record_digest,
    remaining,
)


@dataclass(frozen=True)
class OperationRecipe:
    kind: str
    declaration_name: str
    arguments: tuple[str, ...] = ()
    direction: str = "forward"
    hypothesis: str = ""
    introduce_binders: bool = False
    intro_names: tuple[str, ...] = ()
    schema_version: int = 1

    def __post_init__(self) -> None:
        if self.schema_version != 1:
            raise ValueError("unsupported application recipe schema")
        object.__setattr__(self, "arguments", tuple(self.arguments))
        object.__setattr__(self, "intro_names", tuple(self.intro_names))

    @property
    def recipe_id(self) -> str:
        return record_digest(self.to_record())

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "OperationRecipe":
        return cls(**dict(record))


@dataclass(frozen=True)
class ReductionCertificate:
    goal_id: str
    declaration_id: str
    recipe_id: str
    extraction_digest: str
    residual_statements: tuple[str, ...]
    residual_type_digests: tuple[str, ...]
    package_statement: str
    continuation_statement: str
    continuation_proof: str
    environment_id: str
    context_digest: str
    checked_source_digest: str

    def to_record(self) -> dict[str, Any]:
        return asdict(self)


_OUTCOMES = frozenset(
    {
        "not_checked",
        "unavailable",
        "probe_rejected",
        "probe_inconclusive",
        "elaborated_partial",
        "elaborated_closed",
        "checked_reduction",
        "checked_solution",
    }
)


@dataclass(frozen=True)
class ApplicationObservation:
    operation_id: str
    attempt_id: str
    goal_id: str
    declaration_id: str
    recipe: OperationRecipe
    environment_id: str
    outcome: str
    reason: str = ""
    proof_code: str = ""
    remaining_goals: tuple[str, ...] = ()
    supplied_premises: tuple[str, ...] = ()
    supplied_premises_complete: bool = False
    substitutions_complete: bool = False
    elapsed_s: float = 0.0
    operation_count: int = 0
    reduction: ReductionCertificate | None = None
    checked_result: Any = field(default=None, repr=False, compare=False)
    schema_version: int = 1

    def __post_init__(self) -> None:
        if self.schema_version != 1 or self.outcome not in _OUTCOMES:
            raise ValueError("unsupported application observation")
        if not math.isfinite(self.elapsed_s) or self.elapsed_s < 0:
            raise ValueError("invalid application elapsed time")
        if self.outcome == "checked_reduction" and self.reduction is None:
            raise ValueError("reduction outcome needs a certificate reference")

    @property
    def proof_stub(self) -> str:
        return self.proof_code

    def to_record(self) -> dict[str, Any]:
        # The current in-process checker result is never serialized as authority.
        return {
            key: value
            for key, value in {
                "schema_version": self.schema_version,
                "operation_id": self.operation_id,
                "attempt_id": self.attempt_id,
                "goal_id": self.goal_id,
                "declaration_id": self.declaration_id,
                "recipe": self.recipe.to_record(),
                "environment_id": self.environment_id,
                "outcome": self.outcome,
                "reason": self.reason,
                "proof_code": self.proof_code,
                "remaining_goals": self.remaining_goals,
                "supplied_premises": self.supplied_premises,
                "supplied_premises_complete": self.supplied_premises_complete,
                "substitutions_complete": self.substitutions_complete,
                "elapsed_s": self.elapsed_s,
                "operation_count": self.operation_count,
                "reduction": self.reduction.to_record() if self.reduction else None,
            }.items()
        }

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "ApplicationObservation":
        fields = dict(record)
        fields.pop("checked_result", None)
        fields["recipe"] = OperationRecipe.from_record(fields["recipe"])
        fields["remaining_goals"] = tuple(fields.get("remaining_goals", ()))
        fields["supplied_premises"] = tuple(fields.get("supplied_premises", ()))
        if fields.get("reduction"):
            reduction = dict(fields["reduction"])
            for key in ("residual_statements", "residual_type_digests"):
                reduction[key] = tuple(reduction[key])
            fields["reduction"] = ReductionCertificate(**reduction)
        # Historical grades are descriptive; there is no current acceptance seal.
        return cls(**fields)


async def _independent_reduction(
    runner: Any,
    goal: GoalContextSnapshot,
    profile: DeclarationProfile,
    recipe: OperationRecipe,
    proof_code: str,
    *,
    preamble: str | None,
    lemmas: Sequence[str],
    budget: Any,
) -> tuple[ReductionCertificate | None, Any]:
    extracted = await lean_call(
        runner,
        budget,
        lambda: runner.extract_typed_residual_batch(
            goal.statement,
            proof_code,
            lemmas,
            preamble_override=preamble,
            timeout_s=remaining(budget),
            max_heartbeats=getattr(budget, "max_heartbeats", None),
        ),
    )
    receipt = extracted.receipt
    if not extracted.ok or receipt is None or not receipt.goals:
        return None, None
    expected_context = lean_residual_elaboration_context_hash(
        runner,
        preamble_override=preamble,
        ordered_lemmas=lemmas,
        proof_code=proof_code,
    )
    if receipt.parent_statement_sha256 != digest(goal.statement.strip()) or (
        receipt.proof_stub_sha256 != digest(proof_code.strip())
        or receipt.elaboration_context_hash != expected_context
        or any(
            item.slot_index != index or item.slot_count != len(receipt.goals)
            for index, item in enumerate(receipt.goals)
        )
    ):
        return None, None
    statements = tuple(item.statement for item in receipt.goals)
    # These are Lean's closed, expression-validated residual types, never human
    # diagnostics. Lean elaborates the package and checks the complete replay.
    package = " ∧ ".join(f"({statement})" for statement in statements)
    continuation = f"({package}) → ({goal.statement})"
    names = [f"memory_residual_{index}" for index in range(len(statements))]
    lines = ["by", "  intro memory_package"]
    if len(names) == 1:
        lines.append(f"  have {names[0]} := memory_package")
    else:
        # Lean's conjunction constructor associates to the right.
        pattern = names[-1]
        for name in reversed(names[:-1]):
            pattern = f"⟨{name}, {pattern}⟩"
        lines.append(f"  rcases memory_package with {pattern}")
    body = proof_code.strip()
    if not body.startswith("by"):
        return None, None
    lines.extend("  " + line.lstrip() for line in body[2:].strip().splitlines())
    lines.append("  all_goals first")
    lines.extend(f"    | solve | apply {name} <;> assumption" for name in names)
    proof = "\n".join(lines)
    checked = await lean_call(
        runner,
        budget,
        lambda: runner.check(
            continuation,
            proof,
            list(lemmas),
            preamble_override=preamble,
            timeout_s=remaining(budget),
            max_heartbeats=getattr(budget, "max_heartbeats", None),
        ),
    )
    remaining(budget)
    if not checked.ok or getattr(checked, "axiom_audit_ok", None) is not True:
        return None, None
    certificate = ReductionCertificate(
        goal.goal_id,
        profile.declaration_id,
        recipe.recipe_id,
        receipt.batch_digest,
        statements,
        tuple(digest(item.canonical_expr_json) for item in receipt.goals),
        package,
        continuation,
        proof,
        goal.environment_id,
        expected_context,
        digest(continuation + "\n" + proof + "\n" + "\n".join(lemmas)),
    )
    return certificate, checked


async def prepare_and_probe(
    runner: Any,
    goal: GoalContextSnapshot,
    profile: DeclarationProfile,
    recipe: OperationRecipe,
    *,
    budget: Any,
    preamble: str | None = None,
    lemmas: Sequence[str] = (),
    acceptance: Callable[..., Any] | None = None,
    operation_id: str = "",
    attempt_id: str = "",
    certify_reduction: bool = True,
) -> ApplicationObservation:
    started = time.monotonic()
    observation = ApplicationObservation(
        operation_id or uuid.uuid4().hex,
        attempt_id or uuid.uuid4().hex,
        goal.goal_id,
        profile.declaration_id,
        recipe,
        goal.environment_id,
        "unavailable",
    )
    if not goal.complete or not profile.complete:
        return replace(observation, reason="incomplete_semantic_capture")
    if (
        profile.environment_id != goal.environment_id
        or recipe.declaration_name != profile.declaration_name
    ):
        return replace(observation, reason="identity_mismatch")
    if goal.context_digest != digest(runner._resolve_preamble(preamble)) or (
        goal.ordered_helper_digests != tuple(digest(block) for block in lemmas)
    ):
        return replace(observation, reason="context_changed_recapture_required")
    try:
        # Loaded profile booleans are advisory. Recheck the live goal expression
        # and actual declaration type before using the stored application recipe.
        fresh_goal = await capture_goal(
            runner,
            statement=goal.statement,
            source=goal.source,
            environment_id=goal.environment_id,
            source_variant=goal.source_variant,
            budget=budget,
            preamble=preamble,
            lemmas=lemmas,
        )
        if (
            not fresh_goal.complete
            or fresh_goal.exact_expr_json != goal.exact_expr_json
        ):
            return replace(observation, reason="stale_goal_capture")
        context = runner._resolve_preamble(preamble) + "\n" + "\n".join(lemmas)
        _parsed, _output, code = await lean_call(
            runner,
            budget,
            lambda: runner.check_source_declaration_type_equivalence(
                context,
                profile.declaration_name,
                profile.statement,
                preamble_override=context,
                timeout_s=remaining(budget),
                max_heartbeats=getattr(budget, "max_heartbeats", None),
            ),
        )
        if code != 0:
            return replace(observation, reason="candidate_not_current")
        budget.claim_probe()
        result = await lean_call(
            runner,
            budget,
            lambda: runner.probe_decl_application_recipe(
                goal.statement,
                profile.declaration_name,
                kind=recipe.kind,
                arguments=recipe.arguments,
                direction=recipe.direction,
                hypothesis=recipe.hypothesis,
                introduce_binders=recipe.introduce_binders,
                intro_names=recipe.intro_names,
                preamble_override=preamble,
                lemmas=lemmas,
                timeout_s=remaining(budget),
                max_heartbeats=getattr(budget, "max_heartbeats", None),
            ),
        )
        observation = replace(
            observation,
            outcome=result["outcome"],
            reason=result.get("error_kind", ""),
            proof_code=result.get("proof_code", ""),
            remaining_goals=tuple(result.get("remaining_goals", ())),
            operation_count=int(result.get("operation_count", 0)),
        )
        remaining(budget)
        if observation.outcome == "elaborated_partial" and certify_reduction:
            certificate, checked = await _independent_reduction(
                runner,
                goal,
                profile,
                recipe,
                observation.proof_code,
                preamble=preamble,
                lemmas=lemmas,
                budget=budget,
            )
            if certificate is not None:
                observation = replace(
                    observation,
                    outcome="checked_reduction",
                    reduction=certificate,
                    checked_result=checked,
                )
        elif observation.outcome == "elaborated_closed" and acceptance is not None:
            checked = await lean_call(
                runner,
                budget,
                lambda: runner.check(
                    goal.statement,
                    observation.proof_code,
                    list(lemmas),
                    preamble_override=preamble,
                    timeout_s=remaining(budget),
                    max_heartbeats=getattr(budget, "max_heartbeats", None),
                ),
            )
            remaining(budget)
            if checked.ok and getattr(checked, "axiom_audit_ok", None) is True:
                accepted = acceptance(checked, goal, profile, observation)
                if inspect.isawaitable(accepted):
                    accepted = await accepted
                if accepted is True:
                    observation = replace(
                        observation, outcome="checked_solution", checked_result=checked
                    )
    except (TimeoutError, OSError) as exc:
        # A valid completed reduction survives later advisory persistence loss,
        # but an exhausted/unknown probe cannot become a rejected theorem.
        observation = replace(
            observation, outcome="probe_inconclusive", reason=type(exc).__name__
        )
    return replace(observation, elapsed_s=time.monotonic() - started)


async def integrate_reduction(
    runner: Any,
    proof_state: Any,
    parent_node: Any,
    goal: GoalContextSnapshot,
    observation: ApplicationObservation,
    *,
    budget: Any,
    preamble: str | None = None,
    lemmas: Sequence[str] = (),
    max_goals: int = 256,
    eligibility_guard: Callable[[], bool] | None = None,
) -> tuple[list[str], int, str]:
    """Replay a current reduction through ordinary typed residual admission.

    A persisted grade never supplies executable graph obligations. The existing
    admission path extracts a fresh Lean receipt and atomically binds each slot
    to the current parent, replay stub, and ordered elaboration context.
    """
    from ..proof_state_executor import _extract_and_spawn_typed_residual_goals

    certificate = observation.reduction
    if (
        observation.outcome != "checked_reduction"
        or certificate is None
        or observation.checked_result is None
        or getattr(observation.checked_result, "ok", False) is not True
        or getattr(observation.checked_result, "axiom_audit_ok", None) is not True
    ):
        return [], 0, "memory_reduction_current_check_required"
    if (
        certificate.goal_id != goal.goal_id
        or observation.goal_id != goal.goal_id
        or certificate.declaration_id != observation.declaration_id
        or certificate.recipe_id != observation.recipe.recipe_id
        or certificate.environment_id != goal.environment_id
        or observation.environment_id != goal.environment_id
        or str(parent_node.target or "").strip() != goal.statement.strip()
        or not goal.complete
    ):
        return [], 0, "memory_reduction_identity_mismatch"
    if (
        goal.context_digest != digest(runner._resolve_preamble(preamble))
        or goal.ordered_helper_digests != tuple(digest(block) for block in lemmas)
        or certificate.context_digest
        != lean_residual_elaboration_context_hash(
            runner,
            preamble_override=preamble,
            ordered_lemmas=lemmas,
            proof_code=observation.proof_code,
        )
    ):
        return [], 0, "memory_reduction_context_changed"
    remaining(budget)

    def current_admission() -> bool:
        try:
            return eligibility_guard is None or eligibility_guard() is True
        except Exception:
            return False

    return await _extract_and_spawn_typed_residual_goals(
        lean=runner,
        proof_state=proof_state,
        parent_node=parent_node,
        parent_proof_stub=observation.proof_code,
        source=f"decl_application:mathematical_memory:{observation.operation_id}:{observation.recipe.declaration_name}",
        preamble=preamble if preamble is not None else runner.cfg.preamble_import,
        lemmas=list(lemmas),
        timeout_s=remaining(budget),
        max_goals=max_goals,
        deadline_monotonic=budget.deadline_monotonic,
        max_heartbeats=budget.max_heartbeats,
        admission_guard=current_admission,
        owner_timeout_s=min(30.0, remaining(budget) / 2),
        deadline_exhausted=lambda: (
            budget.remaining_s() <= 0
            or bool(
                budget.cancellation_event is not None
                and budget.cancellation_event.is_set()
            )
        ),
        origin_metadata={
            "kind": "decl_application",
            "decl_name": observation.recipe.declaration_name,
            "memory_operation_id": observation.operation_id,
            "memory_attempt_id": observation.attempt_id,
            "memory_recipe_id": observation.recipe.recipe_id,
            "memory_reduction_digest": record_digest(certificate.to_record()),
        },
    )
