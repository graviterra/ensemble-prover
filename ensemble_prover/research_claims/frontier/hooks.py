"""Integration points for the existing strategy and research owners.

Adaptive mode changes eligibility inside the owner transaction. Observe mode
records a hypothetical and leaves scheduling untouched. Off mode does not
enter these functions.
"""

from __future__ import annotations

from typing import Any, NoReturn

from ..store import ResearchStoreError
from .approaches import (
    approach_is_held,
    can_admit_review,
    mark_served,
    note_deferral,
    select_approach,
)
from .persist import load_campaign, save_campaign
from .progress import active_permit, apply_contribution, claim_permit, consume_permit, settle_mathematical
from .records import FrontierRefusal, digest, new_id
from .retry import authorize_execution, classify_failure, finish_lane_recovery, note_failure, note_success


def mode_of(state: dict[str, Any]) -> str:
    policy = state.get("frontier_research")
    if not isinstance(policy, dict):
        return "off"
    mode = policy.get("mode", "off")
    return mode if mode in {"off", "observe", "adaptive"} else "off"


def _yield(reason: str, *, subject_id: str = "", allocation_id: str = "") -> NoReturn:
    from ..strategy import StrategyYield

    raise StrategyYield(reason, subject_id=subject_id, allocation_id=allocation_id)


def _campaign(controller: Any, state: dict[str, Any]) -> dict[str, Any]:
    campaign = load_campaign(controller.store, state["owner_id"])
    if campaign is None:
        _yield("frontier_unavailable")
    run = controller.store.run_record(scheduling=True)
    sync_native_scope(controller, state, run, campaign)
    sync_strategy_holds(controller, state, run, campaign)
    return campaign


def _save(controller: Any, state: dict[str, Any], run: dict[str, Any], campaign: dict[str, Any]) -> None:
    save_campaign(controller.store, state["owner_id"], run["target_id"], campaign)


def phase_for_scope(campaign: dict[str, Any], target: str | None = None, context_binding: str | None = None) -> dict[str, Any]:
    """Keep late results and attention acknowledgments on their original grant."""
    if target is None or (target == campaign.get("native_active_target_claim_id")
                          and context_binding == campaign.get("native_active_target_context_binding")):
        return campaign["phase"]
    return campaign.setdefault("native_phases", {}).setdefault(digest([target, context_binding]), {
        "reviews_since_work": 0, "frozen_receipts": [], "acknowledged": [],
        "pending_review": [], "open": True, "tails": {},
    })


def sync_native_scope(controller: Any, state: dict[str, Any], run: dict[str, Any], campaign: dict[str, Any]) -> None:
    """Schedule only the exact current native grant; retain other scopes' work."""
    target = run.get("native_active_target_claim_id")
    if target is None:
        return
    from .approaches import fill_resident_slots, request_readmission

    previous = campaign.get("native_active_target_claim_id")
    context = run.get("native_active_target_context_binding")
    previous_context = campaign.get("native_active_target_context_binding")
    changed = previous != target or previous_context != context
    if changed:
        phases = campaign.setdefault("native_phases", {})
        phases[digest([previous or campaign["root"]["target_id"], previous_context])] = campaign["phase"]
        campaign["phase"] = phases.setdefault(digest([target, context]), {
            "reviews_since_work": 0, "frozen_receipts": [], "acknowledged": [],
            "pending_review": [], "open": True, "tails": {},
        })
        campaign["native_active_target_claim_id"] = target
        campaign["native_active_target_context_binding"] = context
    restore: list[dict[str, Any]] = []
    for approach in campaign["approaches"].values():
        approach_id = approach["approach_id"]
        bindings = approach.get("native_scope_bindings", [{"target": campaign["root"]["target_id"], "context": None}])
        allowed = {"target": target, "context": context} in bindings
        if not allowed and "native_suspended_status" not in approach:
            changed = True
            approach["native_suspended_status"] = approach["status"]
            if approach["status"] not in {"held", "completed", "superseded"}:
                approach["status"] = "dormant"
            for queue in ("resident", "admission_queue", "service_queue"):
                if approach_id in campaign[queue]:
                    campaign[queue].remove(approach_id)
            approach["outstanding_admission_sequence"] = None
        elif allowed and "native_suspended_status" in approach:
            changed = True
            approach["status"] = approach.pop("native_suspended_status")
            if approach["status"] not in {"held", "completed", "superseded", "paused"}:
                restore.append(approach)
    if not changed:
        return
    fill_resident_slots(campaign, now=controller.clock())
    for approach in restore:
        if approach["status"] == "waiting":
            approach["readmit_waiting"] = True
        request_readmission(campaign, approach["approach_id"], now=controller.clock())
    _save(controller, state, run, campaign)


def _bind_native_job(controller: Any, state: dict[str, Any], run: dict[str, Any], job: dict[str, Any]) -> str | None:
    target = run.get("native_active_target_claim_id")
    if target is None:
        return None
    from ..research_control import native_job_context, native_job_target

    jobs = {item["job_id"]: item for item in controller.store.jobs()}
    effective = native_job_target(job, jobs)
    fixed = job.get("frontier_native_target_claim_id", effective)
    if fixed != effective or effective != target:
        _yield("fairness")
    context = native_job_context(job, jobs)
    if context is None:
        context = run.get("native_job_contexts", {}).get(job["job_id"])
    if context is None and run.get("native_active_target_context_binding") is not None and any(
        attempt.get("consumer_id") == job["job_id"] for attempt in state["attempts"].values()
    ):
        _yield("suspended")
    if context is None:
        context = run.get("native_active_target_context_binding")
    expected = run.get("native_active_target_context_binding")
    if expected is not None and context != expected:
        _yield("suspended")
    job["frontier_native_target_claim_id"] = effective
    if context is not None:
        job["native_context_binding"] = context
    return effective


def sync_strategy_holds(
    controller: Any, state: dict[str, Any], run: dict[str, Any],
    campaign: dict[str, Any] | None = None,
) -> None:
    """Project exact owner holds into portfolio eligibility without proof credit."""
    if mode_of(state) != "adaptive":
        return
    from .approaches import fill_resident_slots, request_readmission
    from .progress import mark_permits_stale, replace_stale_permit

    current = campaign if campaign is not None else load_campaign(controller.store, state["owner_id"])
    if current is None:
        return
    now = controller.clock()
    changed = False
    restore: list[dict[str, Any]] = []
    for approach in current["approaches"].values():
        approach_id = approach["approach_id"]
        blocked = controller._blocked(state, [approach.get("subject_id") or state["root_id"]], approach.get("method", ""))
        if blocked and not approach.get("owner_scope_held"):
            changed = True
            approach["owner_scope_held"] = True
            approach["before_owner_hold"] = approach["status"]
            if approach["status"] not in {"completed", "superseded"}:
                approach["status"] = "held"
                mark_permits_stale(current, approach_id)
            for queue in ("resident", "admission_queue", "service_queue"):
                if approach_id in current[queue]:
                    current[queue].remove(approach_id)
            approach["outstanding_admission_sequence"] = None
        elif not blocked and approach.get("owner_scope_held"):
            changed = True
            approach["owner_scope_held"] = False
            approach["status"] = approach.pop("before_owner_hold", "runnable")
            if approach["status"] not in {"held", "completed", "superseded", "paused"} and not approach_is_held(current, approach_id):
                restore.append(approach)
    if not changed:
        return
    # Existing admission tickets retain precedence over restored approaches.
    fill_resident_slots(current, now=now)
    for approach in restore:
        approach_id = approach["approach_id"]
        permit = active_permit(current, approach_id)
        if permit is not None and (permit.get("stale") or now >= permit["expires_at"]):
            replace_stale_permit(
                current, permit["permit_id"], now=now, still_relevant=True,
                expires_at=now + current["policy"]["permit_lease_seconds"],
            )
        if approach.get("admitted_open") or active_permit(current, approach_id) is not None:
            if "native_suspended_status" in approach:
                continue
            if approach["status"] == "waiting" and approach.get("waiting_until", 0) > now:
                approach["readmit_waiting"] = True
            request_readmission(current, approach_id, now=now)
    _save(controller, state, run, current)


def _lineage_for_permit(approach: dict[str, Any], permit: dict[str, Any]) -> str | None:
    """Bind a retry to the lineage stamped on it. A new mathematical quantum gets its own."""
    if permit.get("kind") == "operational_retry":
        lineage = permit.get("operation_lineage")
        return lineage if isinstance(lineage, str) and lineage else None
    if permit.get("kind") == "initial_exploration" and approach.get("operation_lineage"):
        return approach["operation_lineage"]
    lineage = new_id("lineage-op")
    approach["operation_lineage"] = lineage
    return lineage


def _approach_id(job: dict[str, Any]) -> str:
    approach_id = job.get("frontier_approach_id")
    if not isinstance(approach_id, str) or not approach_id:
        _yield("frontier_permit_required")
    return approach_id


def bind_research_job(
    controller: Any,
    state: dict[str, Any],
    run: dict[str, Any],
    job: dict[str, Any],
    parent: dict[str, Any] | None = None,
) -> None:
    """Give an actual investigation a durable route before its first admission."""
    if mode_of(state) != "adaptive" or job.get("role") != "research":
        return
    campaign = _campaign(controller, state)
    native_target = _bind_native_job(controller, state, run, job)
    existing_id = job.get("frontier_approach_id")
    if existing_id:
        if existing_id not in campaign["approaches"]:
            raise ResearchStoreError("research job names an unknown frontier approach")
        if native_target is not None:
            approach = campaign["approaches"][existing_id]
            context = job.get("native_context_binding")
            if approach.get("native_scope_bindings") and approach.get("native_context_binding") != context:
                _yield("suspended")
            approach["native_context_binding"] = context
            binding = {"target": native_target, "context": context}
            bindings = approach.setdefault("native_scope_bindings", [])
            if binding not in bindings:
                bindings.append(binding)
            scopes = approach.setdefault("native_target_claim_ids", [])
            if native_target not in scopes:
                scopes.append(native_target)
            controller.store.save_job(job)
            sync_native_scope(controller, state, run, campaign)
            _save(controller, state, run, campaign)
        return
    from .approaches import propose_approach

    claim = controller.store.get_claim(job["claim_id"])
    statement = claim["spec"]["contract"]["statement"]
    from ..strategy import _digest

    subject_id = job.get("alternative_for")
    if not subject_id:
        identity = _digest({"statement": statement.strip(), "context": ""})
        subject_id = "subject-" + identity
        state["subjects"].setdefault(
            subject_id,
            controller._new_subject(subject_id, statement, controller.root_id, identity),
        )
        controller._refresh_dispositions(state)
    question = str(job.get("question") or statement).strip()
    mechanism = {
        "reduction": "Investigate the exact active native target" if native_target is not None else question,
        "objects": [_digest(claim["spec"]["contract"]), *([job.get("native_context_binding")] if native_target is not None else [])],
        "hypotheses": [],
        "quantitative_target": statement,
    }
    # Reissued identical work shares its existing allowance. A new job ID is
    # not evidence of a different mathematical approach.
    approach = next((
        item for item in campaign["approaches"].values()
        if item["mechanism"] == mechanism and item["status"] != "superseded"
    ), None)
    if approach is None:
        remaining = run["max_requests"] - run["requests_used"] - controller._reservations(state)
        approach = propose_approach(
            campaign,
            mechanism=mechanism,
            first_uncertain_inference=question,
            first_investigation=question,
            quantitative_target=statement,
            key_obligations=[_digest(claim["spec"]["contract"])],
            now=controller.clock(),
            parent_grant_remaining=remaining,
            subject_id=subject_id,
        )
        if parent and parent.get("frontier_approach_id") in campaign["approaches"]:
            approach["parent_id"] = parent["frontier_approach_id"]
    job["frontier_approach_id"] = approach["approach_id"]
    job["frontier_question_id"] = approach["question_id"]
    if native_target is not None:
        context = job.get("native_context_binding")
        approach["native_context_binding"] = context
        binding = {"target": native_target, "context": context}
        bindings = approach.setdefault("native_scope_bindings", [])
        if binding not in bindings:
            bindings.append(binding)
        scopes = approach.setdefault("native_target_claim_ids", [])
        if native_target not in scopes:
            scopes.append(native_target)
        sync_native_scope(controller, state, run, campaign)
    controller.store.save_job(job)
    _save(controller, state, run, campaign)


def authorize_prepare(
    controller: Any,
    state: dict[str, Any],
    run: dict[str, Any],
    subject_id: str,
    consumer_id: str,
    method: str,
) -> dict[str, Any]:
    """Claim a permit for a prepared allocation. No provider debit happens here."""
    campaign = _campaign(controller, state)
    job = controller.store.job(consumer_id)
    if job.get("role") == "formalization":
        prepared = _prepare_proof_handoff(controller, state, run, campaign, job, subject_id)
        if prepared is not None:
            return prepared
    approach_id = job.get("frontier_approach_id")
    if not approach_id:
        _yield("frontier_permit_required", subject_id=subject_id)
    approach = campaign["approaches"].get(approach_id)
    if approach is None:
        _yield("frontier_permit_required", subject_id=subject_id)
    if method and approach.get("method") not in {method, ""}:
        approach["method"] = method
    if approach_is_held(campaign, approach_id):
        _yield("suspended", subject_id=subject_id)
    permit = active_permit(campaign, approach_id)
    if permit is None:
        _yield("frontier_permit_required", subject_id=subject_id)
    try:
        claim = claim_permit(
            campaign,
            permit["permit_id"],
            owner=consumer_id,
            now=controller.clock(),
            lease_seconds=campaign["policy"]["permit_lease_seconds"],
        )
    except FrontierRefusal as exc:
        _yield(exc.reason, subject_id=subject_id)
    _save(controller, state, run, campaign)
    return {
        "approach_id": approach_id,
        "permit_id": permit["permit_id"],
        "claim_id": claim["claim_id"],
    }


def _research_producer(state: dict[str, Any], attempt: dict[str, Any]) -> str | None:
    allocation_id = attempt.get("allocation_id")
    if allocation_id is None:
        return attempt.get("consumer_id")
    return state["allocations"].get(allocation_id, {}).get("frontier_handoff_producer")


def research_scope_basis(campaign: dict[str, Any], job: dict[str, Any]) -> dict[str, Any]:
    """The exact question authorized for a research consumer's current quantum."""
    approach = campaign["approaches"][job["frontier_approach_id"]]
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    return {
        "root_binding": campaign["root"]["binding"], "approach_id": approach["approach_id"],
        "question_id": question["question_id"], "question_revision": question["revision"],
        "route_id": route["route_id"], "route_revision": route["revision"],
        "subject_revision": job["revision"],
    }


def has_active_proof_allocation(state: dict[str, Any], campaign: dict[str, Any], job: dict[str, Any]) -> bool:
    approach = campaign["approaches"].get(job.get("frontier_approach_id", ""), {})
    allocation = state["allocations"].get(approach.get("admitted_allocation_id", ""), {})
    binding = allocation.get("consumer_bindings", {}).get(job["job_id"], {})
    return (allocation.get("status") == "active" and not binding.get("released", True)
            and binding.get("consumer_turn") == job["turn"])


def _prepare_proof_handoff(
    controller: Any, state: dict[str, Any], run: dict[str, Any],
    campaign: dict[str, Any], job: dict[str, Any], subject_id: str,
) -> dict[str, Any] | None:
    parent_id = job.get("parent_job")
    if not parent_id:
        return None
    parent = controller.store.job(parent_id)
    approach_id = parent.get("frontier_approach_id")
    approach = campaign["approaches"].get(approach_id or "")
    if approach is None or parent.get("role") != "research":
        return None
    if (
        parent["claim_id"] != job["claim_id"] or parent["revision"] != job["revision"]
        or not parent.get("frontier_permit_consumed") or not approach.get("admitted_open")
        or (parent.get("research_control") or {}).get("closed")
        or approach_is_held(campaign, approach_id)
    ):
        _yield("frontier_permit_required", subject_id=subject_id)
    if not campaign["phase"].get("open", True):
        _yield("research_phase_deferred", subject_id=subject_id)
    handoffs = campaign.setdefault("proof_handoffs", {})
    existing = next((
        item for item in handoffs.values()
        if item["approach_id"] == approach_id and item["status"] in {"prepared", "active"}
    ), None)
    if existing is not None and existing["consumer_id"] != job["job_id"]:
        _yield("fairness", subject_id=subject_id)
    used = sum(_research_producer(state, attempt) == parent_id for attempt in state["attempts"].values())
    remaining = state["policy"]["interval_requests"] - used
    if remaining <= 0:
        _yield("research_interval_exhausted", subject_id=subject_id)
    record = existing or {
        "handoff_id": new_id("proof-handoff"), "approach_id": approach_id,
        "producer_id": parent_id, "consumer_id": job["job_id"],
        "producer_turn": parent["turn"], "producer_response": parent.get("response"),
        "producer_attempt_id": parent.get("frontier_response_attempt_id"),
        "producer_attempt_ids": [key for key, item in state["attempts"].items()
                                 if _research_producer(state, item) == parent_id],
        "status": "prepared", "ceiling": remaining,
        "question_revision": campaign["questions"][approach["question_id"]]["revision"],
        "route_revision": campaign["routes"][approach["route_id"]]["revision"],
        "expires_at": (parent.get("research_control") or {}).get("started_at", controller.clock())
        + state["policy"]["interval_seconds"],
    }
    handoffs[record["handoff_id"]] = record
    job["frontier_approach_id"] = approach_id
    controller.store.save_job(job)
    _save(controller, state, run, campaign)
    return {
        "approach_id": approach_id, "permit_id": None, "claim_id": None,
        "handoff_id": record["handoff_id"], "producer_id": parent_id,
    }


def check_handoff_admission(
    controller: Any, state: dict[str, Any], run: dict[str, Any], allocation: dict[str, Any],
) -> None:
    """A proof continuation spends the producer's remaining shared attention."""
    if not allocation.get("frontier_handoff_id"):
        return
    from ..research_control import _research_count, _reviewed_through

    campaign = _campaign(controller, state)
    handoff = campaign.get("proof_handoffs", {}).get(allocation["frontier_handoff_id"])
    if handoff is None or handoff["status"] not in {"prepared", "active"}:
        _yield("frontier_permit_required", allocation_id=allocation["allocation_id"])
    approach_id = handoff["approach_id"]
    approach = campaign["approaches"][approach_id]
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    if (
        not approach.get("admitted_open") or approach_is_held(campaign, approach_id)
        or question["revision"] != handoff["question_revision"]
        or route["revision"] != handoff["route_revision"]
        or controller.clock() >= handoff["expires_at"]
    ):
        _yield("suspended", allocation_id=allocation["allocation_id"])
    producer = handoff["producer_id"]
    used = sum(_research_producer(state, attempt) == producer for attempt in state["attempts"].values())
    if used >= state["policy"]["interval_requests"]:
        _yield("research_interval_exhausted", allocation_id=allocation["allocation_id"])
    if (
        not campaign["phase"].get("open", True)
        or _research_count(controller.store, state, run) - _reviewed_through(state, run)
        >= state["policy"]["interval_requests"]
    ):
        _yield("research_phase_deferred", allocation_id=allocation["allocation_id"])
    lane = campaign["lanes"].get("provider") or {}
    if _operation_budget_paused(campaign, approach_id) or lane.get("paused"):
        _yield("paused_operational", allocation_id=allocation["allocation_id"])
    if allocation["status"] == "active":
        campaign["history"]["provider_requests"] += 1
        campaign["history"]["costs_by_approach"][approach_id]["provider_requests"] += 1
        _save(controller, state, run, campaign)


def activate_prepared(
    controller: Any,
    state: dict[str, Any],
    run: dict[str, Any],
    allocation: dict[str, Any],
) -> None:
    """First proof admission consumes the prepared permit and the existing debit."""
    campaign = _campaign(controller, state)
    if allocation.get("frontier_handoff_id"):
        check_handoff_admission(controller, state, run, allocation)
        handoff = campaign["proof_handoffs"][allocation["frontier_handoff_id"]]
        available = run["max_requests"] - run["requests_used"] - state["policy"]["reserve_requests"] - controller._reservations(state)
        if available <= 0:
            _yield("review_reserve", allocation_id=allocation["allocation_id"])
        allocation.update(status="active", request_limit=min(handoff["ceiling"], available))
        allocation["expires_at"] = min(allocation["expires_at"], handoff["expires_at"])
        allocation["frontier_operation_lineage"] = campaign["approaches"][handoff["approach_id"]].get("operation_lineage")
        campaign["approaches"][handoff["approach_id"]]["admitted_allocation_id"] = allocation["allocation_id"]
        handoff["status"] = "active"
        _save(controller, state, run, campaign)
        return
    approach_id = allocation.get("frontier_approach_id")
    permit_id = allocation.get("frontier_permit_id")
    if not approach_id or not permit_id:
        _yield("frontier_permit_required", subject_id=allocation.get("subject_id", ""), allocation_id=allocation["allocation_id"])
    approach = campaign["approaches"][approach_id]
    if approach_is_held(campaign, approach_id):
        _yield("suspended", subject_id=allocation.get("subject_id", ""), allocation_id=allocation["allocation_id"])
    selected, _reason = select_approach(campaign)
    if selected != approach_id:
        _yield("fairness", allocation_id=allocation["allocation_id"])
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    try:
        consumed = consume_permit(
            campaign,
            permit_id,
            now=controller.clock(),
            approach_id=approach_id,
            question_revision=question["revision"],
            route_revision=route["revision"],
            provider=True,
            owner=allocation["consumer_id"],
        )
        lineage = _lineage_for_permit(approach, consumed)
        if lineage is None:
            _yield("retry_exhausted", allocation_id=allocation["allocation_id"])
        allocation["frontier_operation_lineage"] = lineage
        authorize_execution(
            campaign,
            lineage,
            lane_id="provider",
            now=controller.clock(),
            deadline=run.get("deadline"),
        )
    except FrontierRefusal as exc:
        _yield(exc.reason, allocation_id=allocation["allocation_id"])
    mark_served(campaign, approach_id)
    policy = state["policy"]
    available = (
        run["max_requests"]
        - run["requests_used"]
        - policy["reserve_requests"]
        - controller._reservations(state)
    )
    if available <= 0:
        _yield("review_reserve", allocation_id=allocation["allocation_id"])
    allocation["status"] = "active"
    allocation["request_limit"] = min(policy["interval_requests"], available)
    approach.update(admitted_allocation_id=allocation["allocation_id"], admitted_consumer_id=allocation["consumer_id"])
    _save(controller, state, run, campaign)


def authorize_control_admission(
    controller: Any,
    state: dict[str, Any],
    run: dict[str, Any],
    job: dict[str, Any],
) -> None:
    """Research and review admission. A missing permit is inadmissible."""
    from ..research_control import _allocation, _reason

    campaign = _campaign(controller, state)
    _bind_native_job(controller, state, run, job)
    if job["role"] == "review":
        authorization = campaign["review_authorizations"].get(job.get("frontier_review_authorization", ""))
        if authorization is None and job.get("strategy_review_id"):
            review = state["reviews"].get(job["strategy_review_id"])
            if review and review.get("job_id") == job["job_id"] and review.get("status") == "review_pending":
                from .approaches import issue_review_authorization

                authorization = issue_review_authorization(
                    campaign,
                    question_id="strategy:" + review["subject_id"],
                    evidence_basis=review["review_id"],
                    producer_ids=[review["author"]],
                    ceiling={"requests": min(4, state["policy"]["interval_requests"])},
                    now=controller.clock(),
                )
                job["frontier_review_authorization"] = authorization["authorization_id"]
        if authorization is None and job.get("evidence_id"):
            history = controller.store.history(job["claim_id"])
            evidence = next((
                item for item in history["evidence"]
                if item["evidence_id"] == job["evidence_id"] and item["revision"] == job["revision"]
            ), None)
            if evidence is not None:
                from .approaches import issue_review_authorization

                authorization = issue_review_authorization(
                    campaign,
                    question_id="claim:" + job["claim_id"] + ":" + str(job["revision"]),
                    evidence_basis=evidence["evidence_id"],
                    producer_ids=[job.get("parent_job") or evidence["author"]],
                    ceiling={"requests": min(4, state["policy"]["interval_requests"])},
                    now=controller.clock(),
                )
                job["frontier_review_authorization"] = authorization["authorization_id"]
        if authorization is None or authorization["status"] != "open":
            _yield("research_review_authorization_required")
        if not job.get("frontier_approach_id"):
            producers = set(authorization["producer_ids"])
            producer = next((
                current for current in controller.store.jobs()
                if (current["job_id"] in producers or current["worker"] in producers)
                and current.get("frontier_approach_id") in campaign["approaches"]
            ), None)
            if producer is not None:
                job["frontier_approach_id"] = producer["frontier_approach_id"]
                job["frontier_question_id"] = campaign["approaches"][producer["frontier_approach_id"]]["question_id"]
        authorized_jobs = {
            current["job_id"] for current in controller.store.jobs()
            if current.get("frontier_review_authorization") == authorization["authorization_id"]
        } | {job["job_id"]}
        admissions = sum(
            attempt.get("consumer_id") in authorized_jobs and attempt.get("allocation_id") is None
            for attempt in state["attempts"].values()
        )
        if admissions >= authorization["ceiling"].get("requests", 0):
            _yield("research_interval_exhausted")
        lane = campaign["lanes"].get("provider") or {}
        budget = campaign["retries"].get(job.get("frontier_operation_lineage") or "") or {}
        if budget.get("paused"):
            _yield("research_review_paused_operational")
        if lane.get("paused") and not lane.get("recovery_open"):
            _yield("research_control_deferred")
        if not job.get("frontier_review_admitted") and not can_admit_review(campaign):
            _yield("research_control_deferred")
        if not job.get("frontier_review_execution_started") or job.get("frontier_retry_pending"):
            lineage = job.setdefault("frontier_operation_lineage", new_id("lineage-review"))
            lane = campaign["lanes"].get("provider") or {}
            probe = bool(lane.get("paused") and lane.get("recovery_open"))
            try:
                authorize_execution(
                    campaign, lineage, lane_id="provider", now=controller.clock(), deadline=run.get("deadline")
                )
            except FrontierRefusal as exc:
                _yield("research_review_" + exc.reason)
            job["frontier_review_execution_started"] = True
            job["frontier_retry_pending"] = False
            job["frontier_lane_probe"] = probe
        elif lane.get("paused"):
            # A paid review's next turn remains in the same bounded execution.
            # Explicit owner recovery authorizes one causal lane probe only.
            lane["recovery_open"] = False
            job["frontier_lane_probe"] = True
        if not job.get("frontier_review_admitted") and campaign["phase"].get("open", True):
            from .approaches import note_review_quantum

            note_review_quantum(campaign)
            job["frontier_review_admitted"] = True
        controller.store.save_job(job)
        _save(controller, state, run, campaign)
        return
    if job["role"] != "research":
        return
    approach_id = _approach_id(job)
    approach = campaign["approaches"].get(approach_id)
    if approach is None:
        _yield("frontier_permit_required")
    subject_id = approach.get("subject_id") or controller.root_id
    if controller._blocked(state, [subject_id], approach.get("method", "")):
        _yield("suspended", subject_id=subject_id)
    if any(
        handoff["approach_id"] == approach_id and handoff["status"] in {"prepared", "active"}
        for handoff in campaign.get("proof_handoffs", {}).values()
    ):
        _yield("fairness")
    if job.get("frontier_permit_consumed"):
        if (approach.get("admitted_consumer_id") != job["job_id"]
                or approach.get("admitted_allocation_id") is not None
                or job.get("frontier_consumed_basis") != research_scope_basis(campaign, job)):
            _yield("stale_frontier_scope")
        if not campaign["phase"].get("open", True):
            _yield("research_phase_deferred")
        lineage = job.get("frontier_operation_lineage") or ""
        budget = campaign["retries"].get(lineage) or {}
        lane = campaign["lanes"].get("provider") or {}
        if budget.get("paused"):
            _yield("paused_operational")
        if lane.get("paused") and not lane.get("recovery_open"):
            _yield("paused_operational")
        if approach_is_held(campaign, approach_id) or not approach.get("admitted_open"):
            _yield("frontier_permit_required")
        if job.get("frontier_retry_pending") or (lane.get("paused") and lane.get("recovery_open")):
            probe = bool(lane.get("paused") and lane.get("recovery_open"))
            try:
                if job.get("frontier_retry_pending"):
                    authorize_execution(
                        campaign,
                        job.get("frontier_operation_lineage") or approach["lineage_id"],
                        lane_id="provider",
                        now=controller.clock(),
                        deadline=run.get("deadline"),
                    )
                    job["frontier_retry_pending"] = False
                if lane.get("paused"):
                    lane["recovery_open"] = False
            except FrontierRefusal as exc:
                _yield("paused_operational" if exc.reason in {"retry_exhausted", "retry_deadline", "lane_paused"} else exc.reason)
            job["frontier_lane_probe"] = probe
        campaign["history"]["provider_requests"] += 1
        campaign["history"]["costs_by_approach"][approach_id]["provider_requests"] += 1
        _save(controller, state, run, campaign)
        return
    reason = _reason(controller.store, job, state, run, controller.clock(), controller._reservations(state))
    used = _allocation(job, state).get("requests_used", 0)
    if not campaign["phase"].get("open", True) and used == 0:
        _yield("research_phase_deferred")
    if reason == "research_phase_exhausted" and used == 0:
        _yield("research_phase_deferred")
    if reason:
        _yield(reason)
    if approach_is_held(campaign, approach_id):
        _yield("suspended")
    selected, _why = select_approach(campaign)
    if selected != approach_id:
        _yield("fairness")
    permit = active_permit(campaign, approach_id)
    if permit is None or permit["status"] != "claimed":
        _yield("frontier_permit_required")
    claim = campaign["claims"].get(permit.get("claim_id") or "")
    if claim is None or claim.get("owner") != job["job_id"]:
        _yield("fairness")
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    try:
        consumed = consume_permit(
            campaign,
            permit["permit_id"],
            now=controller.clock(),
            approach_id=approach_id,
            question_revision=question["revision"],
            route_revision=route["revision"],
            provider=True,
            owner=job["job_id"],
        )
        lineage = job.get("frontier_operation_lineage") if consumed.get("kind") != "operational_retry" else None
        if consumed.get("kind") == "operational_retry" or not lineage:
            lineage = _lineage_for_permit(approach, consumed)
        if lineage is None:
            _yield("retry_exhausted")
        if not approach.get("operation_lineage"):
            approach["operation_lineage"] = lineage
        job["frontier_operation_lineage"] = lineage
        lane = campaign["lanes"].get("provider") or {}
        probe = bool(lane.get("paused") and lane.get("recovery_open"))
        authorize_execution(
            campaign, lineage, lane_id="provider", now=controller.clock(), deadline=run.get("deadline")
        )
    except FrontierRefusal as exc:
        _yield("paused_operational" if exc.reason == "lane_paused" else exc.reason)
    mark_served(campaign, approach_id)
    approach["admitted_consumer_id"] = job["job_id"]
    approach.pop("admitted_allocation_id", None)
    job["frontier_permit_consumed"] = True
    job["frontier_consumed_basis"] = research_scope_basis(campaign, job)
    job["frontier_retry_pending"] = False
    job["frontier_lane_probe"] = probe
    job["frontier_approach_allocation_id"] = approach_id
    controller.store.save_job(job)
    _save(controller, state, run, campaign)


def _acknowledge_retired_attention(
    controller: Any, state: dict[str, Any], campaign: dict[str, Any], job: dict[str, Any],
    *, receipt_ids: set[str] | None = None,
) -> bool:
    """A superseded producer relinquishes attention, never mathematical credit."""
    from .approaches import eligible

    jobs = {item["job_id"]: item for item in controller.store.jobs()}

    def scope(attempt: dict[str, Any]) -> tuple[Any, Any]:
        producer = jobs.get(_research_producer(state, attempt) or "", {})
        binding = attempt.get("frontier_binding") or {}
        return (binding.get("native_target_claim_id", producer.get("frontier_native_target_claim_id")),
                binding.get("native_context_binding", producer.get("native_context_binding")))

    changed_scopes: set[tuple[Any, Any]] = set()
    pending = False
    for receipt_id, attempt in state["attempts"].items():
        if receipt_ids is not None and receipt_id not in receipt_ids:
            continue
        if _research_producer(state, attempt) != job["job_id"] or attempt.get("frontier_phase_acknowledged"):
            continue
        target, context = scope(attempt)
        phase = phase_for_scope(campaign, target, context)
        if (attempt["status"] == "exposure_claimed"
                or phase["tails"].get(receipt_id, {}).get("status") == "running"):
            pending = True
            continue
        attempt.update(frontier_phase_frozen=True, frontier_phase_acknowledged=True, frontier_scope_retired=True)
        for field in ("frozen_receipts", "acknowledged"):
            if receipt_id not in phase[field]:
                phase[field].append(receipt_id)
        phase["pending_review"] = [current for current in phase["frozen_receipts"] if current not in phase["acknowledged"]]
        if not phase["pending_review"]:
            phase["open"] = True
        changed_scopes.add((target, context))
    if receipt_ids is None:
        job["frontier_retirement_attention_pending"] = pending
    for target, context in changed_scopes:
        count = sum(
            bool(attempt.get("frontier_phase_acknowledged")) and scope(attempt) == (target, context)
            and jobs.get(_research_producer(state, attempt) or "", {}).get("role") == "research"
            for attempt in state["attempts"].values()
        )
        if target is None:
            state["research_attention"] = {"reviewed_through": count}
        else:
            key = digest([target, context]) if context is not None else target
            state.setdefault("native_research_attention", {})[key] = count
        if not phase_for_scope(campaign, target, context).get("open", True):
            continue
        for deferred in jobs.values():
            record = deferred.get("research_control") or {}
            if (not record.get("phase_deferred") or record.get("closed")
                    or (deferred.get("frontier_native_target_claim_id"), deferred.get("native_context_binding")) != (target, context)):
                continue
            approach = campaign["approaches"].get(deferred.get("frontier_approach_id", ""))
            record["phase_deferred"] = False
            if approach is not None:
                approach["phase_deferred"] = False
                if deferred["status"] == "waiting" and not record.get("waiting_for") and approach["status"] != "waiting":
                    if approach_is_held(campaign, approach["approach_id"]):
                        deferred["last_error"] = "suspended"
                    elif eligible(campaign, approach["approach_id"]):
                        deferred.update(status="pending", last_error=None)
                    else:
                        deferred["last_error"] = "frontier_permit_required"
            controller.store.save_job(deferred)
    return pending


def reconcile_retired_allocations(controller: Any, state: dict[str, Any]) -> None:
    """Finish old receipt tails without retiring a reused producer's new work."""
    campaign = _campaign(controller, state)
    changed = False
    for record in campaign.get("retired_allocations", {}).values():
        if not record.get("attention_pending"):
            continue
        producer = controller.store.job(record["producer_id"])
        record["attention_pending"] = _acknowledge_retired_attention(
            controller, state, campaign, producer, receipt_ids=set(record["attention_receipt_ids"]),
        )
        changed = True
    if changed:
        _save(controller, state, controller.store.run_record(scheduling=True), campaign)


def _close_retired_quantum(controller: Any, campaign: dict[str, Any], approach: dict[str, Any]) -> None:
    """Close only an identified obsolete quantum; approved unused credit survives."""
    from .approaches import fill_resident_slots

    approach["admitted_open"] = False
    approach.pop("operation_lineage", None)
    approach.pop("admitted_allocation_id", None)
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    permit = active_permit(campaign, approach["approach_id"])
    current_permit = permit is not None and not permit.get("stale") and controller.clock() < permit["expires_at"] and (
        permit["question_id"] == question["question_id"] and permit["question_revision"] == question["revision"]
        and permit.get("route_id") == route["route_id"] and permit["route_revision"] == route["revision"]
    )
    if not approach_is_held(campaign, approach["approach_id"]):
        approach["status"] = "runnable" if current_permit else "paused"
        if not current_permit:
            approach["resume_condition"] = "owner_scope_revalidation"
            for queue in ("resident", "admission_queue", "service_queue"):
                if approach["approach_id"] in campaign[queue]:
                    campaign[queue].remove(approach["approach_id"])
            approach["outstanding_admission_sequence"] = None
            fill_resident_slots(campaign, now=controller.clock())


def retire_stale_research_response(
    controller: Any, state: dict[str, Any], job: dict[str, Any], reason: str,
    *, receipt_ids: set[str] | None = None, expected_allocation_id: str | None = None,
) -> bool:
    """Archive obsolete paid work without granting or settling another scope."""
    run = controller.store.run_record(scheduling=True)
    campaign = _campaign(controller, state)
    approach = campaign["approaches"].get(job.get("frontier_approach_id", ""))
    attempt = state["attempts"].get(job.get("frontier_response_attempt_id", ""), {})
    retirement_id = attempt.get("attempt_id") or digest([job["job_id"], job["turn"], job["response"]])
    campaign.setdefault("retired_responses", {})[retirement_id] = {
        "job_id": job["job_id"], "attempt_id": attempt.get("attempt_id"),
        "response_artifact": job["response"], "binding": attempt.get("frontier_binding"), "reason": reason,
    }
    job.update(status="superseded", last_error=reason, frontier_response_deferred=reason)
    job.setdefault("research_control", {}).update(closed=True, reason=reason)
    if approach is not None and approach.get("admitted_open"):
        owner = approach.get("admitted_consumer_id")
        owns_quantum = owner == job["job_id"]
        if owner is None and approach.get("operation_lineage") == job.get("frontier_operation_lineage"):
            owns_quantum = not any(
                other["job_id"] != job["job_id"] and other.get("frontier_approach_id") == approach["approach_id"]
                and other.get("frontier_permit_consumed") and not other.get("research_control", {}).get("closed")
                and other["status"] in {"pending", "running", "responded", "waiting", "tool_running"}
                for other in controller.store.jobs()
            )
        if owns_quantum and approach.get("admitted_allocation_id") in {None, expected_allocation_id}:
            _close_retired_quantum(controller, campaign, approach)
    pending = _acknowledge_retired_attention(controller, state, campaign, job, receipt_ids=receipt_ids)
    controller.store.save_job(job)
    _save(controller, state, run, campaign)
    return pending


def release_prepared(
    controller: Any,
    state: dict[str, Any],
    run: dict[str, Any],
    allocation: dict[str, Any],
) -> None:
    from .progress import release_claim

    campaign = _campaign(controller, state)
    if allocation.get("frontier_handoff_id"):
        handoff = campaign.get("proof_handoffs", {}).get(allocation["frontier_handoff_id"])
        if handoff is not None and handoff["status"] == "prepared":
            handoff["status"] = "released"
    claim_id = allocation.get("frontier_claim_id")
    if claim_id:
        release_claim(campaign, claim_id)
    allocation["status"] = "yielded"
    allocation["interval_recorded"] = True
    _save(controller, state, run, campaign)


def settle_adaptive_interval(
    controller: Any,
    state: dict[str, Any],
    allocation: dict[str, Any],
) -> None:
    """Typed settlement. Subject-wide stall counters stay unchanged."""
    run = controller.store.run_record(scheduling=True)
    campaign = _campaign(controller, state)
    approach_id = allocation.get("frontier_approach_id")
    approach = campaign["approaches"].get(approach_id or "")
    if approach is not None and allocation.get("frontier_basis"):
        consumer = allocation.get("frontier_handoff_producer") or allocation["consumer_id"]
        owns_quantum = (approach.get("admitted_allocation_id") in {None, allocation["allocation_id"]}
                        and approach.get("admitted_consumer_id") in {None, consumer})
        if allocation["frontier_basis"] != controller._frontier_allocation_basis(state, allocation) or not owns_quantum:
            allocation.update(status="superseded", interval_recorded=True,
                              generation=controller._generation(state), frontier_retired_reason="stale_frontier_scope")
            campaign.setdefault("retired_allocations", {})[allocation["allocation_id"]] = {
                "basis": allocation["frontier_basis"], "reason": "stale_frontier_scope",
                "attempt_ids": [key for key, item in state["attempts"].items()
                                if item.get("allocation_id") == allocation["allocation_id"]],
            }
            handoff = campaign.get("proof_handoffs", {}).get(allocation.get("frontier_handoff_id"))
            if handoff is not None:
                handoff["status"] = "settled"
            elif owns_quantum and approach.get("admitted_open"):
                _close_retired_quantum(controller, campaign, approach)
            _save(controller, state, run, campaign)
            if handoff is not None:
                producer = controller.store.job(handoff["producer_id"])
                record = campaign["retired_allocations"][allocation["allocation_id"]]
                receipt_ids = set(record["attempt_ids"])
                receipt_ids.update(handoff.get("producer_attempt_ids", []))
                if handoff.get("producer_attempt_id"):
                    receipt_ids.add(handoff["producer_attempt_id"])
                same_producer_response = (
                    handoff.get("producer_turn") == producer["turn"]
                    and handoff.get("producer_response") == producer.get("response")
                    and handoff.get("producer_attempt_id") == producer.get("frontier_response_attempt_id")
                )
                if owns_quantum and same_producer_response:
                    pending_attention = retire_stale_research_response(
                        controller, state, producer, "research_scope_changed", receipt_ids=receipt_ids,
                        expected_allocation_id=allocation["allocation_id"],
                    )
                    campaign = _campaign(controller, state)
                else:
                    pending_attention = _acknowledge_retired_attention(
                        controller, state, campaign, producer, receipt_ids=receipt_ids,
                    )
                campaign["retired_allocations"][allocation["allocation_id"]].update(
                    producer_id=producer["job_id"], attention_receipt_ids=sorted(receipt_ids),
                    attention_pending=pending_attention,
                )
                _save(controller, state, run, campaign)
            controller._event(state, "interval_retired", allocation_id=allocation["allocation_id"], reason="stale_frontier_scope")
            return
    progress = False
    pending = allocation.get("pending_progress_receipt")
    if (
        pending
        and state["reviews"][pending].get("status") == "progress"
        and not state["reviews"][pending].get("progress_consumed")
    ):
        progress = True
        state["reviews"][pending]["progress_consumed"] = True
    allocation.update(status="yielded", interval_recorded=True, generation=controller._generation(state))
    subject = state["subjects"][allocation["subject_id"]]
    subject["interval_sequence"] += 1
    allocation["finished_interval"] = subject["interval_sequence"]
    subject["generation"] = allocation["generation"]
    if allocation.get("frontier_handoff_id"):
        handoff = campaign.get("proof_handoffs", {}).get(allocation["frontier_handoff_id"])
        if handoff is not None:
            handoff["status"] = "settled"
    if approach_id and approach_id in campaign["approaches"]:
        related = [
            item for item in state["attempts"].values()
            if item.get("allocation_id") == allocation["allocation_id"]
        ]
        if allocation.get("frontier_revoked"):
            outcome = "route_obstruction"
        elif allocation.get("frontier_operational") or any(
            item.get("status") in {"failed", "unknown"} for item in related
        ):
            outcome = "operational_failure"
        elif progress and allocation.get("frontier_formal"):
            outcome = "formal_advance"
        elif progress:
            outcome = "research_advance"
        else:
            outcome = "inconclusive"
        try:
            settle_mathematical(
                campaign,
                approach_id,
                outcome,
                now=controller.clock(),
                explanation=allocation.get("frontier_explanation", outcome),
            )
        except FrontierRefusal as exc:
            _yield(exc.reason, allocation_id=allocation["allocation_id"])
        if campaign["approaches"][approach_id].get("admitted_allocation_id") == allocation["allocation_id"]:
            campaign["approaches"][approach_id].pop("admitted_allocation_id")
        _save(controller, state, run, campaign)
    controller._event(
        state,
        "interval_finished",
        allocation_id=allocation["allocation_id"],
        progress=progress,
        frontier_mode="adaptive",
    )


def note_observed_interval(
    controller: Any,
    state: dict[str, Any],
    allocation: dict[str, Any],
    *,
    progress: bool,
) -> None:
    """Hypothetical only. The legacy counters were already updated by the caller."""
    run = controller.store.run_record(scheduling=True)
    campaign = load_campaign(controller.store, state["owner_id"])
    if campaign is None:
        return
    campaign["hypotheticals"].append({
        "allocation_id": allocation["allocation_id"],
        "progress": progress,
        "would_reset_subject_stall": bool(progress),
        "applied": False,
    })
    _save(controller, state, run, campaign)


def note_progress(
    controller: Any,
    state: dict[str, Any],
    review: dict[str, Any],
    *,
    formal: bool,
) -> None:
    run = controller.store.run_record(scheduling=True)
    allocation = state["allocations"][review["allocation_id"]]
    approach_id = allocation.get("frontier_approach_id")
    if not approach_id:
        return
    campaign = _campaign(controller, state)
    approach = campaign["approaches"][approach_id]
    from .owner import verified_fact_from_artifacts

    verified = verified_fact_from_artifacts(
        controller.store, campaign, approach.get("bottleneck_obligation"), list(review["artifact_ids"])
    )
    proposed = "formal_advance" if verified else "research_advance"
    try:
        decision = apply_contribution(
            campaign,
            approach_id=approach_id,
            obligation_id=approach.get("bottleneck_obligation"),
            proposed_class=proposed,
            subject=allocation["subject_id"],
            context=campaign["root"]["context"],
            operation_id=review["review_id"],
            artifacts=list(review["artifact_ids"]),
            claim=review.get("rationale", proposed),
            explanation=review.get("rationale", ""),
            now=controller.clock(),
        )
    except FrontierRefusal as exc:
        _yield(exc.reason, allocation_id=allocation["allocation_id"])
    allocation["frontier_formal"] = decision["evidence_class"] == "formal_advance"
    allocation["frontier_explanation"] = decision["explanation"]
    _save(controller, state, run, campaign)


def grant_alternative(
    controller: Any,
    state: dict[str, Any],
    subject_id: str,
    job: dict[str, Any],
    artifact_id: str,
) -> None:
    """Eligibility stays on the named approach. Siblings do not renew."""
    run = controller.store.run_record(scheduling=True)
    approach_id = job.get("frontier_approach_id")
    if not approach_id:
        raise ValueError("adaptive alternative requires its named approach")
    campaign = _campaign(controller, state)
    approach = campaign["approaches"].get(approach_id)
    if approach is None:
        raise ValueError("unknown frontier approach")
    if approach.get("subject_id") and approach["subject_id"] != subject_id:
        raise ValueError("alternative approach is not bound to this subject")
    try:
        apply_contribution(
            campaign,
            approach_id=approach_id,
            obligation_id=approach.get("bottleneck_obligation"),
            proposed_class="research_advance",
            subject=subject_id,
            context=campaign["root"]["context"],
            operation_id=job["job_id"],
            artifacts=[artifact_id],
            claim=artifact_id,
            explanation="substantive alternative for the named approach",
            now=controller.clock(),
        )
    except FrontierRefusal as exc:
        raise ValueError(exc.reason) from exc
    _save(controller, state, run, campaign)


def defer_unserved(controller: Any, state: dict[str, Any], job: dict[str, Any]) -> None:
    run = controller.store.run_record(scheduling=True)
    record = job.setdefault("research_control", {})
    if record.get("closed"):
        return
    approach_id = job.get("frontier_approach_id")
    if approach_id:
        campaign = _campaign(controller, state)
        if approach_id in campaign["approaches"]:
            note_deferral(campaign, approach_id)
            _save(controller, state, run, campaign)
    record["phase_deferred"] = True
    record["closed"] = False
    job["status"] = "waiting"
    controller.store.save_job(job)


def served_receipts(controller: Any, state: dict[str, Any]) -> list[str]:
    jobs = {job["job_id"]: job for job in controller.store.jobs()}
    return [
        attempt_id
        for attempt_id, attempt in state["attempts"].items()
        if jobs.get(_research_producer(state, attempt) or "", {}).get("role") == "research"
        and not attempt.get("frontier_phase_acknowledged")
    ]


def prepare_research_claim(controller: Any, state: dict[str, Any], job: dict[str, Any]) -> None:
    """Claim a usable permit before dispatch. Preparation is not an admission."""
    if job.get("role") != "research" or job.get("frontier_permit_consumed"):
        return
    approach_id = job.get("frontier_approach_id")
    if not approach_id:
        return
    run = controller.store.run_record(scheduling=True)
    campaign = load_campaign(controller.store, state["owner_id"])
    if campaign is None or approach_id not in campaign["approaches"]:
        return
    from .progress import expire_claims, replace_stale_permit

    now = controller.clock()
    expire_claims(campaign, now)
    permit = active_permit(campaign, approach_id)
    if permit is not None and now >= permit["expires_at"]:
        approach = campaign["approaches"][approach_id]
        question = campaign["questions"][approach["question_id"]]
        route = campaign["routes"][approach["route_id"]]
        if (
            not approach_is_held(campaign, approach_id)
            and not permit.get("stale")
            and permit["question_revision"] == question["revision"]
            and permit["route_revision"] == route["revision"]
        ):
            permit = replace_stale_permit(
                campaign, permit["permit_id"], now=now, still_relevant=True,
                expires_at=now + campaign["policy"]["permit_lease_seconds"],
            )
    if permit is None or permit["status"] != "usable":
        _save(controller, state, run, campaign)
        return
    try:
        claim_permit(
            campaign,
            permit["permit_id"],
            owner=job["job_id"],
            now=now,
            lease_seconds=campaign["policy"]["permit_lease_seconds"],
        )
    except FrontierRefusal:
        _save(controller, state, run, campaign)
        return
    job["frontier_claim_id"] = permit["claim_id"]
    controller.store.save_job(job)
    _save(controller, state, run, campaign)


def settle_recovered_research(controller: Any, state: dict[str, Any]) -> None:
    """An owner restart of an open research dispatch is an operational failure."""
    if mode_of(state) != "adaptive":
        return
    campaign = load_campaign(controller.store, state["owner_id"])
    if campaign is None:
        return
    run = controller.store.run_record(scheduling=True)
    settled: set[str] = set()
    for attempt in state["attempts"].values():
        if (attempt.get("status") != "unknown" or attempt.get("allocation_id") is not None
                or attempt.get("frontier_scope_retired") or attempt.get("frontier_phase_acknowledged")):
            continue
        try:
            job = controller.store.job(attempt["consumer_id"])
        except Exception:
            continue
        if job.get("role") != "research" or not job.get("frontier_permit_consumed"):
            continue
        if attempt.get("consumer_turn") != job["turn"]:
            continue
        response_attempt = state["attempts"].get(job.get("frontier_response_attempt_id", ""), {})
        if (response_attempt.get("consumer_id") == job["job_id"]
                and response_attempt.get("consumer_turn") == job["turn"]
                and response_attempt.get("status") == "completed"
                and job.get("response") in response_attempt.get("artifacts", [])):
            continue
        if job.get("frontier_recovery_settled"):
            continue
        approach_id = job.get("frontier_approach_id")
        approach = campaign["approaches"].get(approach_id or "")
        if (approach is None or approach.get("admitted_consumer_id") != job["job_id"]
                or approach.get("admitted_allocation_id") is not None
                or (job.get("research_control") or {}).get("closed")):
            continue
        binding = attempt.get("frontier_binding") or {}
        question = campaign["questions"][approach["question_id"]]
        route = campaign["routes"][approach["route_id"]]
        if (binding.get("root_binding") != campaign["root"]["binding"]
                or binding.get("approach_id") != approach_id
                or binding.get("question_id") != question["question_id"]
                or binding.get("question_revision") != question["revision"]
                or binding.get("route_id") != route["route_id"]
                or binding.get("route_revision") != route["revision"]
                or binding.get("subject_revision") != job["revision"]):
            continue
        job["frontier_recovery_settled"] = True
        controller.store.save_job(job)
        if approach_id in settled or not approach.get("admitted_open"):
            continue
        settled.add(approach_id)
        settle_mathematical(
            campaign,
            approach_id,
            "operational_failure",
            now=controller.clock(),
            explanation="owner_recovered",
        )
    if settled:
        _save(controller, state, run, campaign)


def settle_research_job(controller: Any, state: dict[str, Any], job: dict[str, Any], reason: str) -> bool:
    """Settle a consumed research quantum without touching subject-wide stall counters."""
    if not job.get("frontier_permit_consumed"):
        return True
    approach_id = job.get("frontier_approach_id")
    run = controller.store.run_record(scheduling=True)
    campaign = _campaign(controller, state)
    if not approach_id or approach_id not in campaign["approaches"]:
        return False
    approach = campaign["approaches"][approach_id]
    if has_active_proof_allocation(state, campaign, job):
        return False
    if (approach.get("admitted_consumer_id") != job["job_id"]
            or approach.get("admitted_allocation_id") is not None
            or job.get("frontier_consumed_basis") != research_scope_basis(campaign, job)):
        retire_stale_research_response(controller, state, job, "research_scope_changed")
        return False
    if job.get("frontier_recovery_settled") or not approach.get("admitted_open"):
        return True
    if reason in {
        "provider_failure", "provider_timeout", "context_overflow", "transport",
        "research_response_ingress_rejected",
    }:
        outcome = "operational_failure"
    elif job.get("frontier_formal"):
        outcome = "formal_advance"
    elif job.get("frontier_progress"):
        outcome = "research_advance"
    else:
        outcome = "inconclusive"
    try:
        settle_mathematical(
            campaign,
            approach_id,
            outcome,
            now=controller.clock(),
            explanation=reason,
        )
    except FrontierRefusal as exc:
        _yield(exc.reason)
    _save(controller, state, run, campaign)
    return True


def record_response_tail(controller: Any, job: dict[str, Any], receipt_id: str, status: str) -> None:
    if mode_of(controller.snapshot()) != "adaptive":
        return
    with controller._edit() as (state, run):
        campaign = load_campaign(controller.store, state["owner_id"])
        if campaign is None:
            return
        from .approaches import register_tail

        receipt = state["attempts"].get(receipt_id)
        if receipt is None or receipt.get("consumer_id") != job["job_id"]:
            return
        binding = receipt.get("frontier_binding") or {}
        phase = phase_for_scope(campaign, binding.get("native_target_claim_id"), binding.get("native_context_binding"))
        try:
            register_tail({"phase": phase}, receipt_id, "late_response", "incomplete")
        except FrontierRefusal:
            return
        _save(controller, state, run, campaign)


def freeze_shared_phase(controller: Any, state: dict[str, Any], producer_id: str | None = None) -> None:
    from .approaches import freeze_phase

    run = controller.store.run_record(scheduling=True)
    campaign = _campaign(controller, state)
    if not campaign["phase"].get("open", True):
        return
    receipts = served_receipts(controller, state)
    if producer_id is not None:
        receipts = [
            receipt_id
            for receipt_id in receipts
            if _research_producer(state, state["attempts"].get(receipt_id, {})) == producer_id
        ]
    if not receipts:
        return
    for receipt_id in receipts:
        state["attempts"][receipt_id]["frontier_phase_frozen"] = True
    freeze_phase(campaign, receipts)
    _save(controller, state, run, campaign)


def acknowledge_job(controller: Any, state: dict[str, Any], job: dict[str, Any]) -> bool:
    from .approaches import acknowledge_receipts

    run = controller.store.run_record(scheduling=True)
    campaign = _campaign(controller, state)
    receipts = [
        attempt_id
        for attempt_id, attempt in state["attempts"].items()
        if _research_producer(state, attempt) == job.get("research_reorientation_for")
        and attempt.get("frontier_phase_frozen")
        and not attempt.get("frontier_phase_acknowledged")
    ]
    if not receipts:
        return bool(campaign["phase"]["open"])
    try:
        opened = acknowledge_receipts(campaign, receipts)
    except FrontierRefusal as exc:
        _yield(exc.reason)
    acknowledged = set(campaign["phase"]["acknowledged"])
    for receipt_id in receipts:
        if receipt_id in acknowledged:
            state["attempts"][receipt_id]["frontier_phase_acknowledged"] = True
    if opened:
        from ..research_control import _focused_jobs, _native_attention_key

        jobs = {item["job_id"]: item for item in _focused_jobs(controller.store, run)}
        count = sum(
            1
            for attempt in state["attempts"].values()
            if attempt.get("frontier_phase_acknowledged")
            and jobs.get(_research_producer(state, attempt) or "", {}).get("role") == "research"
        )
        target = run.get("native_active_target_claim_id")
        if target is not None:
            state.setdefault("native_research_attention", {})[_native_attention_key(state, run)] = count
        else:
            state["research_attention"] = {"reviewed_through": count}
        for current in controller.store.jobs():
            record = current.get("research_control") or {}
            if record.get("phase_deferred"):
                record["phase_deferred"] = False
                if current["status"] == "waiting":
                    current["status"] = "pending"
                controller.store.save_job(current)
    _save(controller, state, run, campaign)
    return opened


def bind_review_job(job: dict[str, Any], producer: dict[str, Any], campaign: dict[str, Any]) -> None:
    approach_id = producer.get("frontier_approach_id")
    if not approach_id or approach_id not in campaign["approaches"]:
        return
    approach = campaign["approaches"][approach_id]
    question = campaign["questions"][approach["question_id"]]
    from .approaches import issue_review_authorization

    authorization = issue_review_authorization(
        campaign,
        question_id=question["question_id"],
        evidence_basis=producer["job_id"],
        producer_ids=[producer["job_id"]],
        ceiling={"requests": 4},
        now=0,
    )
    job["frontier_approach_id"] = approach_id
    job["frontier_question_id"] = question["question_id"]
    job["frontier_review_authorization"] = authorization["authorization_id"]
    for key in ("native_target_claim_id", "native_context_binding", "frontier_native_target_claim_id"):
        if producer.get(key) is not None:
            job[key] = producer[key]


def settle_provider_failure(
    controller: Any,
    job: dict[str, Any],
    reason: str,
    *,
    lane_attributed: bool = False,
    preflight: bool = False,
    attempt_ids: list[str] | None = None,
    update_job: bool = True,
) -> str:
    with controller._edit() as (state, run):
        if mode_of(state) != "adaptive":
            return "legacy"
        campaign = _campaign(controller, state)
        current = controller.store.job(job["job_id"])
        owns_current = update_job and current["turn"] == job["turn"] and current["revision"] == job["revision"]
        receipt = None
        if attempt_ids:
            receipt = state["attempts"].get(attempt_ids[-1])
            if (receipt is None or receipt.get("consumer_id") != job["job_id"]
                    or receipt.get("consumer_turn") != job["turn"]
                    or receipt.get("status") == "completed" or receipt.get("frontier_provider_failure_recorded")):
                return "defer"
        if not owns_current and receipt is None:
            return "defer"
        approach = campaign["approaches"].get(job.get("frontier_approach_id") or "")
        lineage = (receipt or {}).get("frontier_operation_lineage")
        if not lineage and owns_current and approach is not None and job.get("role") == "research":
            lineage = approach.get("operation_lineage")
        if not isinstance(lineage, str) or not lineage:
            lineage = job.get("frontier_operation_lineage")
        if not isinstance(lineage, str) or not lineage:
            lineage = new_id("lineage-op")
        if owns_current:
            job["frontier_operation_lineage"] = lineage
            controller.store.save_job(job)
        if owns_current and approach is not None and job.get("role") == "research" and not approach.get("operation_lineage"):
            approach["operation_lineage"] = lineage
        try:
            if preflight:
                from .retry import note_preflight_failure

                decision = note_preflight_failure(campaign, lineage)
            else:
                scope = classify_failure(reason, lane_attributed=lane_attributed)
                decision = note_failure(campaign, lineage, scope, lane_id="provider")
        except FrontierRefusal:
            return "legacy"
        if receipt is not None:
            receipt["frontier_provider_failure_recorded"] = True
            receipt["frontier_failure_reason"] = reason
        probe = (receipt or {}).get("frontier_lane_probe", False) if attempt_ids is not None else job.get("frontier_lane_probe", False)
        if not preflight and probe:
            finish_lane_recovery(campaign, "provider", success=False)
        if not owns_current:
            _save(controller, state, run, campaign)
            return "defer"
        if decision == "mathematical":
            _save(controller, state, run, campaign)
            return decision
        job["frontier_retry_pending"] = decision == "retry"
        job.pop("frontier_lane_probe", None)
        if decision == "paused_operational":
            job["status"] = "waiting"
            job["last_error"] = "paused_operational"
        elif decision == "retry":
            job["status"] = "pending"
            job["last_error"] = reason
        elif decision == "defer":
            job["status"] = "waiting"
            job["last_error"] = reason
        else:
            job["status"] = "waiting"
            job["last_error"] = reason
        controller.store.save_job(job)
        _save(controller, state, run, campaign)
        return decision


def note_provider_success(controller: Any, job: dict[str, Any], *, attempt_id: str) -> None:
    if mode_of(controller.snapshot()) != "adaptive":
        return
    with controller._edit() as (state, run):
        attempt = state["attempts"].get(attempt_id, {})
        if (attempt.get("consumer_id") != job["job_id"] or attempt.get("consumer_turn") != job["turn"]
                or attempt.get("status") != "completed" or attempt.get("frontier_provider_success_recorded")):
            return
        campaign = load_campaign(controller.store, state["owner_id"])
        if campaign is None:
            return
        current = controller.store.job(job["job_id"])
        if attempt.get("frontier_lane_probe"):
            finish_lane_recovery(campaign, "provider", success=True)
        if current["turn"] == attempt["consumer_turn"] and current.pop("frontier_lane_probe", False):
            controller.store.save_job(current)
        note_success(campaign, "provider")
        attempt["frontier_provider_success_recorded"] = True
        _save(controller, state, run, campaign)


def adaptive_context(controller: Any, job: dict[str, Any]) -> dict[str, Any]:
    state = controller.snapshot()
    if mode_of(state) != "adaptive":
        return {}
    approach_id = job.get("frontier_approach_id")
    if not approach_id:
        return {"frontier_research": {"mode": "adaptive"}}
    campaign = load_campaign(controller.store, state["owner_id"])
    if campaign is None or approach_id not in campaign["approaches"]:
        return {"frontier_research": {"mode": "adaptive", "unavailable": True}}
    from .approaches import resume_packet

    approach = campaign["approaches"][approach_id]
    question = campaign["questions"][approach["question_id"]]
    observations = [
        observation for observation in campaign["observations"].values()
        if observation["binding"]["approach_id"] == approach_id
    ]
    return {"frontier_research": {
        "mode": "adaptive",
        "resume": resume_packet(campaign, approach_id),
        "question": question,
        "tools": campaign["manifest"],
        "recent_observations": observations[-8:],
    }}


def _operation_budget_paused(campaign: dict[str, Any], approach_id: str) -> bool:
    approach = campaign["approaches"].get(approach_id) or {}
    budget = campaign["retries"].get(approach.get("operation_lineage") or "")
    return bool(budget and budget.get("paused"))


def ensure_adaptive_work(integration: Any) -> bool:
    controller = integration.controller
    store = integration.store
    if store.stop_reason() or store.run_record(scheduling=True)["status"] != "running":
        return False
    jobs = store.jobs()
    if any(job["status"] in {"pending", "responded", "running", "tool_running"} for job in jobs):
        return False
    with controller._edit() as (state, run):
        campaign = _campaign(controller, state)
        lane = campaign["lanes"].get("provider") or {}
        if lane.get("paused") and not lane.get("recovery_open"):
            return False
        from .progress import expire_claims
        from .approaches import eligible, expire_waiting, fill_resident_slots, request_readmission

        now = controller.clock()
        expire_claims(campaign, now)
        expire_waiting(campaign, now)
        for approach in campaign["approaches"].values():
            approach_id = approach["approach_id"]
            paused = _operation_budget_paused(campaign, approach_id)
            if paused and approach_id in campaign["resident"]:
                approach["status"] = "paused"
                approach["blocked_reason"] = "operational_recovery_required"
                approach["resume_condition"] = "owner_authorized_recovery"
                campaign["resident"].remove(approach_id)
            elif not paused and approach.get("blocked_reason") == "operational_recovery_required":
                request_readmission(campaign, approach_id, now=now)
        fill_resident_slots(campaign, now=now)
        reviewer = next((
            job for job in store.jobs()
            if job["role"] == "review" and job["status"] == "waiting"
            and job.get("last_error") == "research_control_deferred"
            and (job.get("frontier_review_admitted") or can_admit_review(campaign))
        ), None)
        if reviewer is not None:
            reviewer.update(status="pending", last_error=None)
            store.save_job(reviewer)
            _save(controller, state, run, campaign)
            return True
        waiting = False
        for job in store.jobs():
            approach_id = job.get("frontier_approach_id")
            approach = campaign["approaches"].get(approach_id or "")
            if (
                job["status"] == "waiting"
                and approach is not None
                and approach["status"] == "waiting"
                and approach.get("waiting_until") is not None
                and now < approach["waiting_until"]
            ):
                waiting = True
        selected, _reason = select_approach(campaign)
        if selected is not None and _operation_budget_paused(campaign, selected):
            alternatives = [
                approach_id
                for approach_id in campaign["service_queue"]
                if approach_id != selected and eligible(campaign, approach_id)
            ]
            if alternatives:
                selected = alternatives[0]
        _save(controller, state, run, campaign)
        if waiting and selected is None:
            return False
        if selected is None:
            return False
        if any(
            job.get("frontier_approach_id") == selected
            and job["status"] in {"pending", "waiting", "running", "responded", "tool_running"}
            for job in store.jobs()
        ):
            from .approaches import eligible

            selected_permit = active_permit(campaign, selected)
            for job in store.jobs():
                if (
                    job.get("frontier_approach_id") == selected
                    and job["status"] == "waiting"
                    and not (job.get("research_control") or {}).get("waiting_for")
                    and eligible(campaign, selected)
                    and (
                        job.get("last_error") == "paused_operational"
                        and not _operation_budget_paused(campaign, selected)
                        or job.get("last_error") in {"fairness", "suspended", "frontier_permit_required"}
                        and not job.get("frontier_permit_consumed")
                        and (job.get("research_control") or {}).get("requests_used", 0) == 0
                        or job.get("last_error") in {
                            "stale_permit_basis", "stale_frontier_scope", "formal_authority_revoked",
                            "permit_expired", "claim_expired",
                        }
                        and not job.get("frontier_permit_consumed")
                        and selected_permit is not None
                        and selected_permit["permit_id"] != job.get("frontier_refused_permit_id")
                    )
                ):
                    job.update(status="pending", last_error=None)
                    store.save_job(job)
                    return True
            return False
        subject_id = campaign["approaches"][selected].get("subject_id") or controller.root_id
        # A waiting investigation bound to another approach keeps its dependency.
        # Do not retarget that job.
        job = store.add_job(
            run["target_id"],
            "Execute the next quantum of frontier approach " + selected + ".",
        )
        requirement = 0
        if subject_id in state["subjects"]:
            requirement = state["subjects"][subject_id]["interval_sequence"]
        job.update(
            alternative_for=subject_id,
            alternative_requirement=requirement,
            frontier_approach_id=selected,
        )
        store.save_job(job)
        return True


def native_projection(store: Any) -> dict[str, Any] | None:
    run = store.run_record(scheduling=True)
    review = run.get("strategy_review")
    if not isinstance(review, dict) or mode_of(review) != "adaptive":
        return None
    campaign = load_campaign(store, review["owner_id"])
    if campaign is None:
        return {"mode": mode_of(review), "unavailable": True}
    active = next((item["approach_id"] for item in campaign["approaches"].values() if item["status"] == "active"), None)
    return {
        "mode": mode_of(review),
        "root_binding": campaign["root"]["binding"],
        "target_id": campaign["root"]["target_id"],
        "active_approach_id": active,
        "route_ids": list(campaign["routes"]),
    }


def mark_subject_stale(controller: Any, state: dict[str, Any], subject_id: str) -> None:
    from .progress import mark_permits_stale

    run = controller.store.run_record(scheduling=True)
    campaign = load_campaign(controller.store, state["owner_id"])
    if campaign is None:
        return
    for approach in campaign["approaches"].values():
        if approach.get("subject_id") == subject_id:
            mark_permits_stale(campaign, approach["approach_id"])
    _save(controller, state, run, campaign)


def restore_subject(controller: Any, state: dict[str, Any], subject_id: str) -> None:
    from .progress import restore_unused_after_dismiss

    run = controller.store.run_record(scheduling=True)
    campaign = load_campaign(controller.store, state["owner_id"])
    if campaign is None:
        return
    for approach in list(campaign["approaches"].values()):
        if approach.get("subject_id") == subject_id:
            restore_unused_after_dismiss(campaign, approach["approach_id"], now=controller.clock())
    _save(controller, state, run, campaign)


def hypothetical_decision(controller: Any, *, explanation: str, evidence_class: str) -> None:
    with controller._edit() as (state, run):
        if mode_of(state) != "observe":
            raise ResearchStoreError("hypothetical decisions belong to observe mode")
        campaign = _campaign(controller, state)
        campaign["hypotheticals"].append({
            "explanation": explanation,
            "evidence_class": evidence_class,
            "applied": False,
        })
        _save(controller, state, run, campaign)
