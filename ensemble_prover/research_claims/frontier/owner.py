"""Owner-facing frontier mutations. Each call shares the strategy transaction."""

from __future__ import annotations

from typing import Any, Callable

from ..store import ResearchStoreError
from .approaches import (
    acknowledge_receipts,
    bind_consumer,
    can_admit_review,
    dismiss_hold,
    expire_waiting,
    fork_approach,
    freeze_phase,
    hold_obligation,
    mark_served,
    mark_waiting,
    note_deferral,
    note_review_quantum,
    propose_approach,
    register_tail,
    release_shared_consumer,
    request_readmission,
    resume_packet,
    select_approach,
)
from .investigation import (
    accept_replayed_witness,
    bind_question,
    cached_source,
    interpret_experiment,
    normalize_observation,
    register_experiment,
    register_source_application,
    repeated_read,
    store_observation,
)
from .persist import load_campaign, save_campaign
from .progress import (
    active_permit,
    add_reduction,
    apply_contribution,
    claim_permit,
    consume_permit,
    expire_claims,
    merge_groups,
    mark_permits_stale,
    release_claim,
    replace_stale_permit,
    restore_unused_after_dismiss,
    settle_mathematical,
)
from .records import FrontierRefusal, digest
from .retry import (
    authorize_execution,
    authorize_lane_recovery,
    classify_failure,
    finish_lane_recovery,
    new_recovery_epoch,
    note_failure,
    note_preflight_failure,
    note_success,
)
from .status import project
from .approaches import issue_review_authorization


def verified_fact_from_artifacts(store: Any, campaign: dict[str, Any], obligation_id: str, artifacts: list[str]) -> bool:
    """Promote only owner exports whose exact proposition and environment still validate."""
    from ..proof_bridge import validate_receipt

    obligation = campaign["obligations"].get(obligation_id)
    if obligation is None:
        return False
    campaign.setdefault("checked_facts", {}).pop(obligation_id, None)
    jobs = store.jobs()
    indexed = {job["job_id"]: job for job in jobs}
    for certificate in list(campaign.get("checked_reduction_receipts", {})):
        proof_job = indexed.get(certificate)
        try:
            if proof_job is None or proof_job.get("status") != "verified":
                raise ValueError("missing checked reduction")
            validate_receipt(store, proof_job, proof_job.get("proof_receipt"))
        except (ValueError, ResearchStoreError, OSError):
            del campaign["checked_reduction_receipts"][certificate]
    for job in jobs:
        if job.get("status") != "verified" or job.get("proof_feedback") not in artifacts:
            continue
        receipt = job.get("proof_receipt")
        try:
            validate_receipt(store, job, receipt)
        except (ValueError, ResearchStoreError, OSError):
            continue
        result = receipt["root_result"]
        if (
            job.get("polarity") != "prove"
            or result.get("statement", "").strip() != obligation["proposition"].strip()
            or receipt["binding"].get("environment_id") != campaign["root"]["environment"]
            or obligation["context"] != campaign["root"]["context"]
        ):
            continue
        campaign.setdefault("checked_facts", {})[obligation_id] = {
            "root_binding": campaign["root"]["binding"],
            "identity": obligation["identity"],
            "receipt_digest": digest(receipt),
            "job_id": job["job_id"],
            "artifact_id": job["proof_feedback"],
        }
        return True
    return False


def report_scope_current(controller: Any, campaign: dict[str, Any], producer: dict[str, Any]) -> bool:
    """A report keeps the assignment of the provider response that produced it."""
    from .approaches import approach_is_held

    basis = producer.get("frontier_report_basis") or {}
    artifact = producer.get("investigation_artifact")
    state = controller.snapshot()
    run = controller.store.run_record(scheduling=True)
    attempt = state["attempts"].get(basis.get("attempt_id", ""), {})
    approach = campaign["approaches"].get(producer.get("frontier_approach_id", ""))
    if (not artifact or basis.get("report_artifact") != artifact or approach is None
            or attempt.get("consumer_id") != producer["job_id"]
            or basis.get("response_artifact") not in attempt.get("artifacts", [])
            or basis.get("binding") != attempt.get("frontier_binding")):
        return False
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    expected = {"approach_id": approach["approach_id"], "question_id": question["question_id"],
                "question_revision": question["revision"], "route_id": route["route_id"],
                "route_revision": route["revision"], "root_binding": campaign["root"]["binding"],
                "subject_revision": controller.store.get_claim(producer["claim_id"])["revision"],
                "native_target_claim_id": run.get("native_active_target_claim_id"),
                "native_context_binding": run.get("native_active_target_context_binding")}
    return not (any(basis["binding"].get(key) != value for key, value in expected.items())
                or approach_is_held(campaign, approach["approach_id"])
                or controller._blocked(state, [approach.get("subject_id") or state["root_id"]], approach.get("method", "")))


class FrontierOwner:
    def __init__(self, controller: Any):
        self.controller = controller
        self.store = controller.store

    def _mode(self, state: dict[str, Any]) -> str:
        policy = state.get("frontier_research")
        if not isinstance(policy, dict):
            return "off"
        return str(policy.get("mode", "off"))

    def _run(self, strategy_state: dict[str, Any], run: dict[str, Any], fn: Callable[[dict[str, Any]], Any]) -> Any:
        if self._mode(strategy_state) == "off":
            raise FrontierRefusal("frontier_disabled")
        campaign = load_campaign(self.store, strategy_state["owner_id"])
        if campaign is None:
            raise ResearchStoreError("missing frontier campaign")
        if campaign["policy"]["mode"] != self._mode(strategy_state):
            raise ResearchStoreError("frontier mode diverged from the strategy record")
        result = fn(campaign)
        save_campaign(self.store, strategy_state["owner_id"], run["target_id"], campaign)
        return result

    def _edit(self, fn: Callable[[dict[str, Any]], Any]) -> Any:
        with self.controller._edit() as (state, run):
            return self._run(state, run, fn)

    def campaign(self) -> dict[str, Any]:
        with self.controller.store.read_snapshot():
            state = self.controller.snapshot()
            loaded = load_campaign(self.store, state["owner_id"])
            if loaded is None:
                raise ResearchStoreError("missing frontier campaign")
            return loaded

    def project(self) -> dict[str, Any]:
        return project(self.campaign())

    def assess_report_progress(self, reviewer: dict[str, Any], *, substantive: bool, rationale: str) -> dict[str, Any]:
        """Use the assigned independent checkpoint review, never the producer's vote."""
        if type(substantive) is not bool:
            raise ValueError("substantive_progress must be boolean")
        if not substantive:
            return {"status": "unresolved", "credit_minted": False}

        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            producer_id = reviewer.get("research_reorientation_for")
            authorization = campaign["review_authorizations"].get(reviewer.get("frontier_review_authorization", ""), {})
            if (reviewer.get("role") != "review" or not producer_id or authorization.get("status") != "open"
                    or producer_id not in authorization.get("producer_ids", [])):
                raise FrontierRefusal("assigned_independent_report_review_required")
            producer = self.store.job(producer_id)
            if producer["worker"] == reviewer["worker"]:
                raise FrontierRefusal("independent_report_reviewer_required")
            if not report_scope_current(self.controller, campaign, producer):
                return {"status": "stale", "credit_minted": False}
            artifact = producer["investigation_artifact"]
            state = self.controller.snapshot()
            approach = campaign["approaches"][producer["frontier_approach_id"]]
            self.store.read_artifact(artifact)
            return apply_contribution(campaign, approach_id=approach["approach_id"],
                                      obligation_id=approach["bottleneck_obligation"], proposed_class="research_advance",
                                      subject=approach.get("subject_id") or state["root_id"], context=campaign["root"]["context"],
                                      operation_id=reviewer["job_id"], artifacts=[artifact], claim=artifact,
                                      explanation=rationale, now=self.controller.clock())

        return self._edit(run)

    def reorient_report_question(self, reviewer: dict[str, Any], directive: dict[str, Any]) -> dict[str, Any] | None:
        """Bind an independently prescribed successor without issuing new credit."""
        def run(campaign: dict[str, Any]) -> dict[str, Any] | None:
            producer_id = reviewer.get("research_reorientation_for")
            if reviewer.get("role") != "review" or not producer_id or directive.get("decision") != "investigate":
                return None
            producer = self.store.job(producer_id)
            if producer["worker"] == reviewer["worker"] or not report_scope_current(self.controller, campaign, producer):
                return None
            approach = campaign["approaches"][producer["frontier_approach_id"]]
            previous = campaign["questions"][approach["question_id"]]
            route = campaign["routes"][approach["route_id"]]
            transferable = [permit for permit in campaign["permits"].values()
                            if permit["approach_id"] == approach["approach_id"]
                            and permit["status"] in {"usable", "claimed"} and not permit.get("stale")
                            and permit["question_id"] == previous["question_id"]
                            and permit["question_revision"] == previous["revision"]
                            and permit.get("route_id") == route["route_id"]
                            and permit["route_revision"] == route["revision"]]
            question = bind_question(
                campaign, approach_id=approach["approach_id"], uncertainty=directive["first_uncertain_inference"],
                why=directive["rationale"], scope={**previous["scope"], "next_question": directive["next_question"],
                                                 "discriminating_check": directive["discriminating_check"]},
                operations=previous["admissible_operations"], changed=True,
            )
            approach["next_operation"] = directive["discriminating_check"]
            if question["question_id"] != previous["question_id"]:
                mark_permits_stale(campaign, approach["approach_id"])
                for permit in transferable:
                    replace_stale_permit(campaign, permit["permit_id"], now=self.controller.clock(), still_relevant=True,
                                         expires_at=self.controller.clock() + campaign["policy"]["permit_lease_seconds"])
            return question

        return self._edit(run)

    def propose_approach(self, **kwargs: Any) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            remaining = kwargs.pop("parent_grant_remaining", 1)
            return propose_approach(campaign, now=self.controller.clock(), parent_grant_remaining=remaining, **kwargs)
        return self._edit(run)

    def fork_approach(self, parent_id: str, **kwargs: Any) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            remaining = kwargs.pop("parent_grant_remaining", 1)
            return fork_approach(
                campaign, parent_id, now=self.controller.clock(), parent_grant_remaining=remaining, **kwargs
            )
        return self._edit(run)

    def add_reduction(self, **kwargs: Any) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            if kwargs.get("level") == "checked":
                self._validate_reduction(campaign, kwargs)
            return add_reduction(campaign, **kwargs)
        return self._edit(run)

    def _validate_reduction(self, campaign: dict[str, Any], reduction: dict[str, Any]) -> None:
        """A checked edge names a verified export job, never a worker-supplied label."""
        from ..proof_bridge import validate_receipt

        certificate = reduction.get("certificate")
        if not isinstance(certificate, str) or not certificate:
            raise FrontierRefusal("checked_reduction_requires_verified_receipt")
        jobs = {item["job_id"]: item for item in self.store.jobs()}
        job = jobs.get(certificate)
        if not job or job.get("status") != "verified" or job.get("polarity") != "prove":
            raise FrontierRefusal("checked_reduction_requires_verified_receipt")
        receipt = validate_receipt(self.store, job, job.get("proof_receipt"))
        try:
            premises = [campaign["obligations"][item] for item in reduction["antecedents"]]
            consequent = campaign["obligations"][reduction["consequent"]]
        except KeyError as exc:
            raise FrontierRefusal("unknown_obligation") from exc
        expected = " → ".join(f"({item['proposition']})" for item in [*premises, consequent])
        if (
            receipt["root_result"].get("statement", "").strip() != expected
            or receipt["binding"].get("environment_id") != campaign["root"]["environment"]
            or any(item["context"] != campaign["root"]["context"] for item in [*premises, consequent])
        ):
            raise FrontierRefusal("checked_reduction_binding_mismatch")
        campaign.setdefault("checked_reduction_receipts", {})[certificate] = {
            "root_binding": campaign["root"]["binding"],
            "antecedents": [item["identity"] for item in premises],
            "consequent": consequent["identity"],
            "receipt_digest": digest(receipt),
        }

    def bind_route(self, approach_id: str, route_id: str, reduction_id: str) -> None:
        def run(campaign: dict[str, Any]) -> None:
            approach = campaign["approaches"][approach_id]
            if route_id != approach["route_id"]:
                raise FrontierRefusal("route_approach_mismatch")
            route = campaign["routes"][approach["route_id"]]
            if reduction_id in route["reductions"]:
                return
            route["reductions"].append(reduction_id)
            route["revision"] += 1
            mark_permits_stale(campaign, approach_id)
            campaign["reductions"][reduction_id]["route_id"] = route["route_id"]
        self._edit(run)

    def apply_contribution(self, **kwargs: Any) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            if kwargs.get("proposed_class") in {"root_verified", "root_refuted"}:
                self._validate_root_outcome(campaign, kwargs["proposed_class"], kwargs.get("artifacts", []))
            if kwargs.get("proposed_class") == "formal_advance" and kwargs.get("obligation_id"):
                verified_fact_from_artifacts(self.store, campaign, kwargs["obligation_id"], kwargs.get("artifacts", []))
            return apply_contribution(campaign, now=self.controller.clock(), **kwargs)
        return self._edit(run)

    def _validate_root_outcome(self, campaign: dict[str, Any], outcome: str, artifacts: list[str] | None = None) -> None:
        from ..proof_bridge import validate_receipt

        polarity = "prove" if outcome == "root_verified" else "refute"
        for job in self.store.jobs():
            if (job.get("status") != "verified" or job.get("claim_id") != campaign["root"]["target_id"]
                    or job.get("polarity") != polarity
                    or artifacts is not None and job.get("proof_feedback") not in artifacts):
                continue
            receipt = validate_receipt(self.store, job, job.get("proof_receipt"))
            if receipt["binding"].get("environment_id") == campaign["root"]["environment"]:
                return
        raise FrontierRefusal("root_outcome_requires_verified_receipt")

    def prepare(self, approach_id: str, *, owner: str) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            permit = active_permit(campaign, approach_id)
            if permit is None:
                raise FrontierRefusal("frontier_permit_required")
            return claim_permit(
                campaign,
                permit["permit_id"],
                owner=owner,
                now=self.controller.clock(),
                lease_seconds=campaign["policy"]["permit_lease_seconds"],
            )
        return self._edit(run)

    def select(self) -> tuple[str | None, str]:
        with self.controller.store.read_snapshot():
            state = self.controller.snapshot()
            campaign = load_campaign(self.store, state["owner_id"])
            if campaign is None:
                raise ResearchStoreError("missing frontier campaign")
            return select_approach(campaign)

    def mark_served(self, approach_id: str) -> None:
        self._edit(lambda campaign: mark_served(campaign, approach_id))

    def settle(self, approach_id: str, outcome: str, *, explanation: str) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            if outcome in {"root_verified", "root_refuted"}:
                self._validate_root_outcome(campaign, outcome)
            return settle_mathematical(campaign, approach_id, outcome, now=self.controller.clock(), explanation=explanation)
        return self._edit(run)

    def hold_obligation(self, obligation_id: str, *, method: str = "") -> list[str]:
        return self._edit(lambda campaign: hold_obligation(
            campaign, obligation_id, method=method, now=self.controller.clock()
        ))

    def dismiss_hold(self, approach_id: str, obligation_id: str) -> dict[str, Any] | None:
        def run(campaign: dict[str, Any]) -> dict[str, Any] | None:
            affected = [item["approach_id"] for item in campaign["approaches"].values() if item["status"] == "held"]
            if approach_id not in affected:
                affected.append(approach_id)
            dismiss_hold(campaign, obligation_id)
            result = None
            for current in affected:
                restored = restore_unused_after_dismiss(campaign, current, now=self.controller.clock())
                if current == approach_id:
                    result = restored
            return result
        return self._edit(run)

    def replace_stale(self, permit_id: str, *, still_relevant: bool) -> dict[str, Any] | None:
        def run(campaign: dict[str, Any]) -> dict[str, Any] | None:
            return replace_stale_permit(
                campaign,
                permit_id,
                now=self.controller.clock(),
                still_relevant=still_relevant,
                expires_at=self.controller.clock() + campaign["policy"]["permit_lease_seconds"],
            )
        return self._edit(run)

    def merge_events(self, event_a: str, event_b: str, tier: str) -> None:
        self._edit(lambda campaign: merge_groups(campaign, event_a, event_b, tier))

    def expire(self) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            now = self.controller.clock()
            return {
                "claims": expire_claims(campaign, now),
                "waiting": expire_waiting(campaign, now),
            }
        return self._edit(run)

    def release_claim(self, claim_id: str) -> None:
        self._edit(lambda campaign: release_claim(campaign, claim_id, now=None))

    def defer(self, approach_id: str) -> None:
        self._edit(lambda campaign: note_deferral(campaign, approach_id))

    def freeze(self, receipt_ids: list[str]) -> None:
        self._edit(lambda campaign: freeze_phase(campaign, receipt_ids))

    def acknowledge(self, receipt_ids: list[str]) -> bool:
        return self._edit(lambda campaign: acknowledge_receipts(campaign, receipt_ids))

    def tail(self, receipt_id: str, action: str, status: str) -> dict[str, Any]:
        return self._edit(lambda campaign: register_tail(campaign, receipt_id, action, status))

    def readmit(self, approach_id: str) -> None:
        self._edit(lambda campaign: request_readmission(campaign, approach_id, now=self.controller.clock()))

    def wait(self, approach_id: str, *, until: float, dependency: str) -> None:
        def run(campaign: dict[str, Any]) -> None:
            bounded = until
            deadline = self.controller.store.run_record(scheduling=True).get("deadline")
            if type(deadline) is not bool and isinstance(deadline, (int, float)):
                bounded = min(bounded, deadline)
            mark_waiting(campaign, approach_id, until=bounded, dependency=dependency)
        self._edit(run)

    def bind_consumer(self, obligation_id: str, approach_id: str) -> None:
        self._edit(lambda campaign: bind_consumer(campaign, obligation_id, approach_id))

    def release_consumer(self, obligation_id: str, approach_id: str) -> str:
        return self._edit(lambda campaign: release_shared_consumer(campaign, obligation_id, approach_id))

    def resume(self, approach_id: str) -> dict[str, Any]:
        return resume_packet(self.campaign(), approach_id)

    def authorize_execution(self, lineage_id: str, *, lane_id: str, deadline: float | None) -> dict[str, Any]:
        return self._edit(lambda campaign: authorize_execution(
            campaign, lineage_id, lane_id=lane_id, now=self.controller.clock(), deadline=deadline
        ))

    def fail(self, lineage_id: str, kind: str, *, lane_id: str, lane_attributed: bool = False) -> str:
        scope = classify_failure(kind, lane_attributed=lane_attributed)
        return self._edit(lambda campaign: note_failure(campaign, lineage_id, scope, lane_id=lane_id))

    def preflight_failure(self, lineage_id: str) -> str:
        return self._edit(lambda campaign: note_preflight_failure(campaign, lineage_id))

    def succeed_lane(self, lane_id: str) -> None:
        self._edit(lambda campaign: note_success(campaign, lane_id))

    def recover_lane(self, lane_id: str, *, success: bool) -> None:
        def run(campaign: dict[str, Any]) -> None:
            authorize_lane_recovery(campaign, lane_id)
            finish_lane_recovery(campaign, lane_id, success=success)
        self._edit(run)

    def recovery_epoch(self, lineage_id: str, *, operator_authorized: bool, capability_change: bool = False) -> dict[str, Any]:
        return self._edit(lambda campaign: new_recovery_epoch(
            campaign,
            lineage_id,
            operator_authorized=operator_authorized,
            capability_change=capability_change,
        ))

    def observe_tool(self, **kwargs: Any) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            question_id = kwargs["binding"]["question_id"]
            from .records import digest

            coverage_key = digest({
                "question_id": question_id,
                "declared_scope": kwargs["declared_scope"],
                "owner_observed_execution": kwargs["owner_observed_execution"],
                "artifacts": kwargs["artifacts"],
                "script_reported_coverage": kwargs["script_reported_coverage"],
            })
            cached = repeated_read(campaign, question_id, coverage_key)
            if cached is not None:
                return cached
            observation = normalize_observation(**kwargs)
            return store_observation(campaign, observation)
        return self._edit(run)

    def source(self, **kwargs: Any) -> dict[str, Any]:
        return self._edit(lambda campaign: register_source_application(campaign, **kwargs))

    def cached_source(self, source_hash: str, version: str) -> dict[str, Any] | None:
        return cached_source(self.campaign(), source_hash, version)

    def experiment(self, spec: dict[str, Any]) -> dict[str, Any]:
        return self._edit(lambda campaign: register_experiment(campaign, spec))

    def interpret_experiment(self, experiment_id: str, **kwargs: Any) -> dict[str, Any]:
        return self._edit(lambda campaign: interpret_experiment(campaign, experiment_id, **kwargs))

    def accept_witness(self, experiment_id: str) -> dict[str, Any]:
        return self._edit(lambda campaign: accept_replayed_witness(campaign, experiment_id))

    def rebind_question(self, approach_id: str, *, uncertainty: str, why: str, scope: dict[str, Any], changed: bool) -> dict[str, Any]:
        return self._edit(lambda campaign: bind_question(
            campaign,
            approach_id=approach_id,
            uncertainty=uncertainty,
            why=why,
            scope=scope,
            operations=["derivation"],
            changed=changed,
        ))

    def review_authorization(self, **kwargs: Any) -> dict[str, Any]:
        def run(campaign: dict[str, Any]) -> dict[str, Any]:
            if not can_admit_review(campaign):
                raise FrontierRefusal("review_quantum_limit")
            record = issue_review_authorization(campaign, now=self.controller.clock(), **kwargs)
            note_review_quantum(campaign)
            return record
        return self._edit(run)

    def consume(self, permit_id: str, *, approach_id: str, question_revision: int, route_revision: int, provider: bool) -> dict[str, Any]:
        return self._edit(lambda campaign: consume_permit(
            campaign,
            permit_id,
            now=self.controller.clock(),
            approach_id=approach_id,
            question_revision=question_revision,
            route_revision=route_revision,
            provider=provider,
        ))
