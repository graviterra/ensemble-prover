"""Budgeted applicability and requested research within ordinary session jobs."""

from __future__ import annotations

import asyncio
import time
import uuid
import logging
from typing import Any, ClassVar, FrozenSet

from ensemble_prover.lean_runner import lean_resource_scope
from ensemble_prover.mathematical_memory.budget import MemoryBudget
from ensemble_prover.mathematical_memory.model import content_digest
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
    sanitize_lean_artifact_text,
)
from ..action import MiniOutcome

_LOG = logging.getLogger(__name__)


class MathematicalMemoryAction:
    id = "mathematical_memory"
    priority = 6
    cost_estimate_s = 1.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset(
        {"session_state", "dossier", "proof_state"}
    )

    def is_applicable(self, session: Any) -> bool:
        service = getattr(session, "mathematical_memory", None)
        if service is None:
            return False
        config = service.config
        action_budget = session.budgets.get(self.id)
        if (
            action_budget is None
            or action_budget.exhausted()
            or config.action_seconds <= 0
            or service.allocation.available() <= 0
        ):
            return False
        try:
            if service.request_store is not None and service.request_store.pending(
                limit=1
            ):
                return True
        except (OSError, ValueError, RuntimeError):
            service.health = "unavailable"
        wake = any(
            row.get("environment_id") == service.context_id()
            for row in session.mathematical_memory_state.get("wake_proposals", ())
        )
        prior_revision = session.mathematical_memory_state.get(
            "attempted_retrieval_revisions", {}
        ).get(service.context_id())
        return (
            session.lean is not None
            and config.probes_enabled
            and (
                wake
                or service.context_id()
                not in session.mathematical_memory_state.get("attempted_contexts", ())
                or prior_revision != service.retrieval_revision()
            )
        )

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        return self.is_applicable(session)

    async def run(self, session: Any) -> MiniOutcome:
        service = session.mathematical_memory
        config = service.config
        started = time.monotonic()
        action_budget = session.budgets[self.id]
        remaining = max(0.0, config.action_seconds - action_budget.total_seconds)
        if session.run_wall_clock_budget_s > 0:
            remaining = min(
                remaining,
                max(
                    0.0,
                    session.run_wall_clock_budget_s
                    - session._accrue_run_governor_elapsed(),
                ),
            )
        recursive_deadline = float(
            getattr(session, "recursive_elapsed_deadline_epoch_s", 0) or 0
        )
        if recursive_deadline > 0:
            remaining = min(remaining, max(0.0, recursive_deadline - time.time()))
        reserved = service.allocation.reserve(remaining)
        budget = MemoryBudget(
            owner_id=str(getattr(session, "_inflight_action_dispatch_id", ""))
            or session.session_activation_id,
            deadline_monotonic=started + reserved,
            max_probes=config.probe_cap,
        )
        controller = getattr(session, "cost_controller", None)
        budget.provider_owner = controller
        if controller is not None and getattr(controller, "budget_enabled", False):
            budget.remaining_cost = max(0.0, float(controller.remaining_usd()))
        with lean_resource_scope(
            memory_mb=budget.memory_mb,
            concurrency=budget.concurrency,
            max_heartbeats=budget.max_heartbeats,
            deadline_monotonic=budget.deadline_monotonic,
        ):
            request = None
            applications: list[dict[str, Any]] = []
            cards: list[dict[str, Any]] = []
            replace_observations = False
            result_candidate = None
            made_progress = False
            verdict = "observed"
            stage = "admission"
            goal_id = ""
            request_id = str((request or {}).get("request_id", ""))
            operation_id = uuid.uuid4().hex
            attempt_id = uuid.uuid4().hex
            admitted = False
            retry_event = None
            retry_recipe = None

            def settle_request(status: str, detail: str) -> None:
                try:
                    service.request_store.transition(
                        request_id,
                        status,
                        detail=detail[:512],
                        deadline_monotonic=budget.deadline_monotonic,
                    )
                except (OSError, ValueError, RuntimeError) as exc:
                    service.health = "unavailable"
                    _LOG.debug(
                        "Memory request settlement unavailable: %s", type(exc).__name__
                    )

            try:
                budget.check_cancelled()
                if service.request_store is not None:
                    pending = service.request_store.pending(
                        limit=1, deadline_monotonic=budget.deadline_monotonic
                    )
                    request = pending[0]["payload"] if pending else None
                    request_id = str((request or {}).get("request_id", ""))
                if request:
                    if (
                        request.get("policy_id") != service.policy_id
                        or request.get("environment_id") != service.context_id()
                    ):
                        raise ValueError(
                            "request policy or environment is no longer current"
                        )
                    if request.get("goal_id") != service.current_view().get("goal_id"):
                        raise ValueError("request belongs to a different captured goal")
                    if request.get("kind") in {"retry", "generalization"}:
                        if request.get("allocation_id") not in {
                            budget.owner_id,
                            config.research_allocation_id,
                            self.id,
                        }:
                            raise ValueError(
                                "request does not name this owner's allocation"
                            )
                        budget.deadline_monotonic = min(
                            budget.deadline_monotonic,
                            started + float(request["max_seconds"]),
                        )
                        if not config.probes_enabled:
                            raise ValueError(
                                "this memory mode cannot start research work"
                            )
                    if request.get("kind") == "retry":
                        from ensemble_prover.mathematical_memory.applications import (
                            OperationRecipe,
                        )

                        retry_event = service.catalog.get_event(
                            str(request.get("retry_of", "")),
                            service.policy,
                            deadline_monotonic=budget.deadline_monotonic,
                        )
                        if (
                            retry_event is None
                            or retry_event.kind != "application"
                            or any(
                                retry_event.payload.get(key) != request.get(key)
                                for key in ("candidate_id", "goal_id", "environment_id")
                            )
                        ):
                            raise ValueError(
                                "prior application is no longer eligible for this exact retry"
                            )
                        retry_recipe = OperationRecipe.from_record(
                            dict(retry_event.payload.get("recipe", {}))
                        )
                        operation_id = retry_event.operation_id
                    annotation_provenance = None
                    if (
                        request.get("kind") in {"pin", "note"}
                        or request.get("candidate_id")
                        and request.get("kind") == "generalization"
                    ):
                        annotation_provenance = service.annotation_provenance(
                            request, budget
                        )
                    service.request_store.admit(
                        request_id,
                        operation_id,
                        attempt_id,
                        deadline_monotonic=budget.deadline_monotonic,
                    )
                    admitted = True
                    service.request_store.transition(
                        request_id,
                        "running",
                        deadline_monotonic=budget.deadline_monotonic,
                    )
                    if request.get("kind") in {"pin", "note"}:
                        service.record(
                            request["kind"],
                            dict(request),
                            operation_id=operation_id,
                            attempt_id=attempt_id,
                            budget=budget,
                            provenance=annotation_provenance,
                        )
                        verdict = "annotation_recorded"
                    elif request.get("kind") == "generalization":
                        await service.prove_requested_generalization(
                            request, budget, source_provenance=annotation_provenance
                        )
                        verdict = "generalization_completed"
                if not request or request.get("kind") == "retry":
                    if not config.probes_enabled:
                        raise ValueError("application probing is disabled")
                    wake_candidate_id = ""
                    if not request:
                        queue = session.mathematical_memory_state.setdefault(
                            "wake_proposals", []
                        )
                        while queue:
                            wake = queue.pop(0)
                            if wake.get("environment_id") != service.context_id():
                                continue
                            event = service.catalog.get_event(
                                str(wake.get("event_id", "")),
                                service.policy,
                                deadline_monotonic=budget.deadline_monotonic,
                            )
                            if (
                                event is not None
                                and event.kind == "retry_proposal"
                                and event.payload.get("candidate_id")
                                == wake.get("candidate_id")
                            ):
                                wake_candidate_id = str(wake["candidate_id"])
                                break
                    pin = service.catalog.generation()
                    replace_observations = True
                    stage = "capture_goal"
                    goal = await service.capture_goal(budget)
                    goal_id = goal.goal_id
                    if not goal.complete:
                        verdict = "capture_incomplete"
                    else:
                        stage = "find_candidates"
                        candidates = await service.find_candidates(goal, budget, pin)
                        if wake_candidate_id:
                            candidates = tuple(
                                candidate
                                for candidate in candidates
                                if candidate.candidate_id == wake_candidate_id
                            )
                        if request:
                            candidates = tuple(
                                candidate
                                for candidate in candidates
                                if candidate.candidate_id == request.get("candidate_id")
                            )
                            if not candidates:
                                raise ValueError(
                                    "requested declaration is not in the eligible candidate pool"
                                )
                        for candidate in candidates[: config.prepared_candidate_cap]:
                            budget.check_cancelled()
                            if not service.candidate_eligible(candidate, budget=budget):
                                continue
                            if budget.probes_used >= config.probe_cap:
                                verdict = "probe_coverage_exhausted"
                                break
                            card = {
                                "candidate_id": candidate.candidate_id,
                                "goal_id": goal.goal_id,
                                "environment_id": service.context_id(),
                                "declaration_name": candidate.declaration_name,
                                "statement": candidate.type_text,
                                "reasons": candidate.reasons,
                                "availability": candidate.availability,
                                "outcome": "not_checked",
                            }
                            event = service.record(
                                "candidate",
                                card,
                                operation_id=operation_id,
                                attempt_id=attempt_id,
                                budget=budget,
                                provenance=service.provenance(
                                    (candidate.candidate_id,)
                                ),
                            )
                            if event is not None:
                                card["event_id"] = event.event_id
                                card["evidence"] = [
                                    reference.to_record()
                                    for reference in event.evidence
                                ]
                                cards.append(card)
                            before = service.context_id()
                            stage = "activate_candidate"
                            if not await service.activate_candidate(candidate, budget):
                                continue
                            if not service.candidate_eligible(candidate, budget=budget):
                                continue
                            if before != service.context_id():
                                # Activation changes the actual environment; one fresh
                                # capture stays inside the same allocation and cap.
                                goal = await service.capture_goal(budget)
                                goal_id = goal.goal_id
                                if not goal.complete:
                                    continue
                            if not service.application_eligible(
                                candidate.candidate_id, budget=budget
                            ):
                                continue
                            stage = "probe"
                            observation = await service.prepare_and_probe(
                                goal,
                                candidate,
                                budget,
                                recipe=retry_recipe,
                                operation_id=(
                                    operation_id if retry_event is not None else ""
                                ),
                                attempt_id=(
                                    attempt_id if retry_event is not None else ""
                                ),
                            )
                            if not service.candidate_eligible(candidate, budget=budget):
                                continue
                            payload = observation.to_record()
                            payload["candidate_id"] = candidate.candidate_id
                            payload["statement"] = goal.statement
                            payload["declaration_statement"] = candidate.type_text
                            event = service.record(
                                "application",
                                payload,
                                operation_id=observation.operation_id,
                                attempt_id=observation.attempt_id,
                                budget=budget,
                                provenance=service.application_provenance(
                                    candidate.candidate_id
                                ),
                                retry_of=(
                                    retry_event.attempt_id
                                    if retry_event is not None
                                    else ""
                                ),
                            )
                            if event is not None:
                                payload["event_id"] = event.event_id
                                payload["evidence"] = [
                                    reference.to_record()
                                    for reference in event.evidence
                                ]
                                applications.append(payload)
                            card["outcome"] = observation.outcome
                            service.record_attempt_context(
                                observation,
                                candidate.candidate_id,
                                budget,
                                retry_of=(
                                    retry_event.attempt_id
                                    if retry_event is not None
                                    else ""
                                ),
                            )
                            service.propose_repeated_patterns(budget)
                            if (
                                observation.outcome == "checked_reduction"
                                and session.proof_state is not None
                            ):
                                from ensemble_prover.mathematical_memory.applications import (
                                    integrate_reduction,
                                )

                                root = session.proof_state.nodes.get(
                                    session.proof_state.root_node_id
                                )
                                if (
                                    root is not None
                                    and root.target.strip() == goal.statement.strip()
                                ):
                                    statement, preamble, lemmas = service.context()
                                    spawned, count, status = await integrate_reduction(
                                        session.lean,
                                        session.proof_state,
                                        root,
                                        goal,
                                        observation,
                                        budget=budget,
                                        preamble=preamble,
                                        lemmas=lemmas,
                                        eligibility_guard=lambda: (
                                            service.application_eligible(
                                                candidate.candidate_id, budget=budget
                                            )
                                        ),
                                    )
                                    if spawned:
                                        service.remember_reduction(
                                            observation, candidate.candidate_id
                                        )
                                        session.proof_state.sync_to_graph(
                                            session.dossier,
                                            phase=self.id,
                                            turn_index=session.iteration,
                                        )
                                        verdict = status
                                        made_progress = bool(spawned)
                                        break
                            if observation.outcome == "elaborated_closed":
                                if not service.candidate_eligible(
                                    candidate, budget=budget
                                ):
                                    continue
                                proof = observation.proof_code
                                statement, preamble, lemmas = service.context()
                                from ensemble_prover.proof_state_executor import (
                                    _await_serialized_lean_operation,
                                )

                                stage = "ordinary_check"
                                checked = await _await_serialized_lean_operation(
                                    session.lean,
                                    lambda: session.lean.check(
                                        statement,
                                        proof,
                                        list(lemmas),
                                        preamble_override=preamble,
                                        timeout_s=budget.remaining_s(),
                                        max_heartbeats=budget.max_heartbeats,
                                    ),
                                    timeout_s=budget.remaining_s() * 0.95,
                                    deadline_monotonic=budget.deadline_monotonic,
                                )
                                budget.check_cancelled()
                                if (
                                    checked.ok
                                    and checked.axiom_audit_ok is True
                                    and service.context_id()
                                    == observation.environment_id
                                    and service.application_eligible(
                                        candidate.candidate_id, budget=budget
                                    )
                                ):
                                    from ensemble_prover.proof_dossier import (
                                        helper_decl_name,
                                    )

                                    names = tuple(
                                        filter(
                                            None,
                                            (
                                                helper_decl_name(block)
                                                for block in lemmas
                                            ),
                                        )
                                    )
                                    result_candidate = RootFinalizationCandidate(
                                        proof=proof,
                                        replay_helpers=lemmas,
                                        helper_names=names,
                                        target_statement=statement,
                                        phase=self.id,
                                        source_action_id=self.id,
                                        turn_index=session.iteration,
                                        verification_certificate=root_verification_certificate(
                                            proof=proof,
                                            accepted=True,
                                            target_statement=statement,
                                            replay_helpers=lemmas,
                                            helper_names=names,
                                            output=checked.output,
                                            phase=self.id,
                                            source=self.id,
                                        ),
                                    )
                                    service.remember_solution(
                                        {
                                            "observation": observation.to_record(),
                                            "candidate_id": candidate.candidate_id,
                                            "proof_hash": content_digest(
                                                sanitize_lean_artifact_text(proof)
                                            ),
                                            "operation_id": observation.operation_id,
                                            "attempt_id": observation.attempt_id,
                                            "environment_id": service.context_id(),
                                            "policy_id": service.policy_id,
                                        }
                                    )
                                    verdict = "checked_artifact_awaiting_acceptance"
                                    break
                        attempted = session.mathematical_memory_state.setdefault(
                            "attempted_contexts", []
                        )
                        if service.context_id() not in attempted:
                            attempted.append(service.context_id())
                        del attempted[:-256]
                        revisions = session.mathematical_memory_state.setdefault(
                            "attempted_retrieval_revisions", {}
                        )
                        revisions[service.context_id()] = service.retrieval_revision()
                        while len(revisions) > 256:
                            revisions.pop(next(iter(revisions)))
                if request:
                    settle_request("completed", verdict)
            except asyncio.CancelledError:
                if request:
                    settle_request(
                        "unresolved" if admitted else "cancelled",
                        "cancelled during execution; reconcile before retry",
                    )
                raise
            except (TimeoutError, OSError, ValueError, TypeError, RuntimeError) as exc:
                verdict = f"{type(exc).__name__}: {exc}"
                if request:
                    settle_request("unresolved" if admitted else "rejected", verdict)
            finally:
                try:
                    service.emit(
                        goal_id=goal_id,
                        applications=applications if replace_observations else None,
                        candidates=cards if replace_observations else None,
                        partial=(result_candidate is None if replace_observations
                                 else bool(service.current_view().get("partial", False))),
                        budget=budget,
                    )
                finally:
                    service.allocation.finish(reserved, time.monotonic() - started)
            return MiniOutcome(
                action_id=self.id,
                solved=result_candidate is not None,
                proof=result_candidate.proof if result_candidate else None,
                root_candidate=result_candidate,
                progress=result_candidate is not None or made_progress,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": verdict,
                    "stage": stage,
                    "memory_input_generation": (
                        pin.to_record() if "pin" in locals() else None
                    ),
                },
            )
