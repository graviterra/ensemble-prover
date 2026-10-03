"""Resident approaches, fair service, and shared-attention continuity.

The portfolio selects among work the existing owner can already run. It does
not create a provider budget or a second debit.
"""

from __future__ import annotations

from typing import Any

from .progress import (
    _checked_certificate_matches,
    _checked_fact_matches,
    active_permit,
    add_obligation,
    add_route,
    issue_permit,
    mark_permits_stale,
    route_requires,
)
from .records import APPROACH_STATES, FrontierRefusal, digest, new_id


def _approach(state: dict[str, Any], approach_id: str) -> dict[str, Any]:
    try:
        return state["approaches"][approach_id]
    except KeyError as exc:
        raise FrontierRefusal("unknown_approach") from exc


def approach_is_held(state: dict[str, Any], approach_id: str) -> bool:
    approach = _approach(state, approach_id)
    if approach["status"] == "held" or approach.get("owner_scope_held"):
        return True
    for hold in state["scoped_holds"]:
        if not hold.get("active"):
            continue
        if hold.get("approach_id") not in {None, approach_id}:
            continue
        if hold.get("method") and hold["method"] != approach.get("method"):
            continue
        if hold.get("obligation_id") and not route_requires(state, approach.get("route_id", ""), hold["obligation_id"]):
            continue
        return True
    return False


def _fingerprint(root_binding: str, mechanism: dict[str, Any], obligations: list[str], quantitative: str) -> str:
    return digest({
        "root": root_binding,
        "mechanism": mechanism,
        "obligations": obligations,
        "quantitative": quantitative,
    })


def normalize_mechanism(mechanism: Any) -> dict[str, Any]:
    """Normalize structured scheduling identity without equating mathematics."""
    fields = {"reduction", "objects", "hypotheses", "quantitative_target"}
    if not isinstance(mechanism, dict) or set(mechanism) != fields:
        raise ValueError("approach mechanism requires reduction, objects, hypotheses and quantitative_target")
    result: dict[str, Any] = {}
    for field in ("reduction", "quantitative_target"):
        value = mechanism[field]
        if not isinstance(value, str) or not value.strip():
            raise ValueError(f"approach mechanism {field} must be nonempty text")
        result[field] = " ".join(value.split())
    for field in ("objects", "hypotheses"):
        value = mechanism[field]
        if (not isinstance(value, list) or len(value) > 64
                or any(not isinstance(item, str) or not item.strip() for item in value)):
            raise ValueError(f"approach mechanism {field} must be an array of nonempty strings")
        result[field] = sorted({" ".join(item.split()) for item in value})
    return result


def _join_service_tail(state: dict[str, Any], approach_id: str) -> None:
    queue = state["service_queue"]
    if approach_id in queue:
        queue.remove(approach_id)
    queue.append(approach_id)


def _mark_held(state: dict[str, Any], approach_id: str) -> None:
    """Record an effective hold so release and eligibility agree on the state."""
    approach = _approach(state, approach_id)
    if approach["status"] == "held":
        return
    approach["status"] = "held"
    approach["status_revision"] += 1
    approach["resume_condition"] = "appeal_or_route_revision"
    mark_permits_stale(state, approach_id)


def _leave_service(state: dict[str, Any], approach_id: str) -> None:
    """Withdraw held work from residency and service without losing its ticket.

    The admission ticket stays in the queue so releasing the hold resumes the
    work through the normal admission path in its original order. A held route
    cannot occupy a residency slot or displace viable queued work meanwhile.
    """
    for queue in ("resident", "service_queue"):
        while approach_id in state[queue]:
            state[queue].remove(approach_id)


def _admit_from_queue(state: dict[str, Any], *, now: float) -> dict[str, Any] | None:
    if len(state["resident"]) >= state["policy"]["max_resident_approaches"]:
        return None
    for index, approach_id in enumerate(state["admission_queue"]):
        approach = _approach(state, approach_id)
        if approach_is_held(state, approach_id):
            # Held work keeps its place but never consumes a residency slot or
            # displaces a viable queued approach.
            _mark_held(state, approach_id)
            continue
        del state["admission_queue"][index]
        approach["outstanding_admission_sequence"] = None
        approach["status"] = "waiting" if approach.pop("readmit_waiting", False) else "runnable"
        approach["blocked_reason"] = None
        if approach_id not in state["resident"]:
            state["resident"].append(approach_id)
        _join_service_tail(state, approach_id)
        approach["protect_until_served"] = True
        if not any(
            item["approach_id"] == approach_id and item["kind"] == "initial_exploration"
            for item in state["permits"].values()
        ):
            question = state["questions"][approach["question_id"]]
            try:
                issue_permit(
                    state,
                    kind="initial_exploration",
                    approach_id=approach_id,
                    question_id=question["question_id"],
                    question_revision=question["revision"],
                    route_revision=state["routes"][approach["route_id"]]["revision"],
                    operation=question["uncertainty"],
                    expires_at=now + state["policy"]["permit_lease_seconds"],
                    lineage_id=approach["lineage_id"],
                )
            except FrontierRefusal as exc:
                if exc.reason != "initial_permit_already_issued":
                    raise
        return approach
    return None


def fill_resident_slots(state: dict[str, Any], *, now: float) -> None:
    while len(state["resident"]) < state["policy"]["max_resident_approaches"]:
        if _admit_from_queue(state, now=now) is None:
            return


def propose_approach(
    state: dict[str, Any],
    *,
    mechanism: dict[str, Any],
    first_uncertain_inference: str,
    first_investigation: str,
    quantitative_target: str,
    key_obligations: list[str],
    now: float,
    parent_grant_remaining: int,
    method: str = "",
    subject_id: str = "",
    root_binding: str | None = None,
    difference: str = "",
) -> dict[str, Any]:
    if root_binding is not None and root_binding != state["root"]["binding"]:
        raise FrontierRefusal("root_binding_mismatch")
    if parent_grant_remaining < 1:
        raise FrontierRefusal("insufficient_grant")
    if not first_uncertain_inference.strip() or not first_investigation.strip():
        raise FrontierRefusal("approach_requires_first_question")
    required = {"reduction", "objects", "hypotheses", "quantitative_target"}
    if not isinstance(mechanism, dict) or not required <= set(mechanism):
        raise FrontierRefusal("mechanism_incomplete")
    fingerprint = _fingerprint(state["root"]["binding"], mechanism, key_obligations, quantitative_target)
    for existing in state["approaches"].values():
        if existing["fingerprint"] == fingerprint and existing["status"] != "superseded":
            raise FrontierRefusal("exact_repeat")
    bottleneck = add_obligation(
        state,
        proposition=first_uncertain_inference.strip(),
        context=state["root"]["context"],
        source_revision=state["root"].get("environment", ""),
        assumptions=list(mechanism.get("hypotheses", [])),
    )
    if state["root_obligation"] == bottleneck["obligation_id"]:
        root = add_obligation(
            state,
            proposition=state["root"]["proposition"],
            context=state["root"]["context"],
            source_revision=state["root"].get("environment", ""),
        )
        state["root_obligation"] = root["obligation_id"]
    approach_id = new_id("approach")
    question = {
        "question_id": new_id("question"),
        "revision": 1,
        "approach_id": approach_id,
        "uncertainty": first_uncertain_inference.strip(),
        "why": difference or mechanism["reduction"],
        "scope": {
            "hypotheses": list(mechanism.get("hypotheses", [])),
            "quantitative_target": quantitative_target,
        },
        "admissible_operations": ["derivation", "literature", "experiment", "lean_check"],
        "outcome_map": {
            "continue": "bounded follow-through on this inference",
            "weaken": "replace the quantitative target and fork",
            "change": "hold this approach and continue another route",
            "formalize": "submit the inference to the existing verifier",
            "unresolved": "retain the gap without mathematical exhaustion",
        },
        "lineage_key": digest({
            "approach_lineage": approach_id,
            "uncertainty": first_uncertain_inference.strip(),
            "quantitative_target": quantitative_target,
        }),
    }
    route = add_route(state, approach_id=approach_id, bottleneck=bottleneck["obligation_id"], reduction_ids=[])
    question["route_id"] = route["route_id"]
    state["questions"][question["question_id"]] = question
    lineage_id = new_id("lineage")
    approach = {
        "approach_id": approach_id,
        "lineage_id": lineage_id,
        "parent_id": None,
        "root_binding": state["root"]["binding"],
        "route_id": route["route_id"],
        "question_id": question["question_id"],
        "bottleneck_obligation": bottleneck["obligation_id"],
        "mechanism": mechanism,
        "method": method or mechanism["reduction"],
        "difference": difference,
        "fingerprint": fingerprint,
        "subject_id": subject_id,
        "status": "proposed",
        "status_revision": 1,
        "blocked_reason": None,
        "resume_condition": None,
        "inconclusive_extensions": 0,
        "unconsumed_followthrough": False,
        "admitted_open": False,
        "protect_until_served": False,
        "phase_deferred": False,
        "latest_result": "",
        "next_operation": first_investigation.strip(),
        "waiting_until": None,
        "waiting_dependency": None,
        "outstanding_admission_sequence": None,
        "service_age": state["admission_sequence"],
        "distinctness": "distinct",
    }
    if approach["status"] not in APPROACH_STATES:
        raise FrontierRefusal("unknown_approach_state")
    state["approaches"][approach_id] = approach
    state["history"]["costs_by_approach"][approach_id] = {"provider_requests": 0, "tool_admissions": 0}
    state["admission_sequence"] += 1
    approach["outstanding_admission_sequence"] = state["admission_sequence"]
    state["admission_queue"].append(approach_id)
    fill_resident_slots(state, now=now)
    if approach_id not in state["resident"]:
        if approach_is_held(state, approach_id):
            _mark_held(state, approach_id)
        else:
            approach["status"] = "dormant"
    return approach


def fork_approach(
    state: dict[str, Any],
    parent_id: str,
    *,
    mechanism: dict[str, Any],
    first_uncertain_inference: str,
    first_investigation: str,
    quantitative_target: str,
    key_obligations: list[str],
    now: float,
    parent_grant_remaining: int,
    difference: str,
) -> dict[str, Any]:
    parent = _approach(state, parent_id)
    child = propose_approach(
        state,
        mechanism=mechanism,
        first_uncertain_inference=first_uncertain_inference,
        first_investigation=first_investigation,
        quantitative_target=quantitative_target,
        key_obligations=key_obligations,
        now=now,
        parent_grant_remaining=parent_grant_remaining,
        method=mechanism.get("reduction", ""),
        subject_id=parent.get("subject_id", ""),
        difference=difference,
    )
    child["parent_id"] = parent_id
    inherited = state["history"]["costs_by_approach"][parent_id]
    state["history"]["costs_by_approach"][child["approach_id"]] = {
        "provider_requests": inherited["provider_requests"],
        "tool_admissions": inherited["tool_admissions"],
        "inherited_from": parent_id,
    }
    return child


def eligible(state: dict[str, Any], approach_id: str) -> bool:
    approach = _approach(state, approach_id)
    target = state.get("native_active_target_claim_id")
    binding = {"target": target, "context": state.get("native_active_target_context_binding")}
    if target is not None and binding not in approach.get("native_scope_bindings", [{"target": state["root"]["target_id"], "context": None}]):
        return False
    if approach_id not in state["resident"]:
        return False
    if approach["status"] not in {"runnable", "active"}:
        return False
    if approach.get("phase_deferred"):
        return False
    if approach_is_held(state, approach_id):
        return False
    budget = state["retries"].get(approach.get("operation_lineage") or "")
    if budget and budget.get("paused"):
        return False
    if approach.get("admitted_open"):
        return True
    permit = active_permit(state, approach_id)
    if permit is None or permit.get("stale"):
        return False
    question = state["questions"][approach["question_id"]]
    route = state["routes"][approach["route_id"]]
    return permit["question_revision"] == question["revision"] and permit["route_revision"] == route["revision"]


EXPLORATION_INTERVAL = 5


def _checked_closure(facts: set[str], reductions: list[dict[str, Any]]) -> set[str]:
    established = set(facts)
    changed = True
    while changed:
        changed = False
        for reduction in reductions:
            consequent = reduction["consequent"]
            if consequent not in established and all(item in established for item in reduction["antecedents"]):
                established.add(consequent)
                changed = True
    return established


def approach_priority(state: dict[str, Any], approach_id: str) -> dict[str, Any]:
    """Explain a bounded scheduling heuristic; this is not evidence or authority.

    Each current route is a separate hypergraph. Other premises of a joint
    reduction must be checked before solving its bottleneck can finish it.
    Merely proposed edges and detached historical routes give no checked bonus.
    """
    approach = _approach(state, approach_id)
    target = approach.get("bottleneck_obligation")
    components = dict(root_completion=0, reduction_completion=0, checked_obstruction=0,
                      shared_obstruction=0, discrimination=0)
    profile: dict[str, Any] = {"score": 0, "components": components, "obligation_id": target,
                               "affected_routes": [], "heuristic_only": True}
    eligible_ids = [item for item in state["service_queue"] if eligible(state, item)]
    if approach_id not in eligible_ids or not isinstance(target, str) or target not in state["obligations"]:
        return profile
    own_route = state["routes"].get(approach.get("route_id"), {})
    if (own_route.get("root_binding") != state["root"]["binding"]
            or own_route.get("root_obligation") != state.get("root_obligation")
            or own_route.get("approach_id") != approach_id):
        return profile
    facts = {item for item in state["obligations"] if _checked_fact_matches(state, item)}
    if target in facts:
        return profile
    root = state.get("root_obligation")
    if root not in state["obligations"]:
        return profile
    checked = {}
    for reduction_id, reduction in state["reductions"].items():
        antecedents = reduction.get("antecedents") or []
        consequent = reduction.get("consequent")
        if (reduction.get("level") == "checked" and not reduction.get("well_founded")
                and antecedents and consequent in state["obligations"]
                and all(item in state["obligations"] for item in antecedents)
                and _checked_certificate_matches(state, reduction.get("certificate"), antecedents, consequent)):
            checked[reduction_id] = reduction
    for candidate_id in eligible_ids:
        candidate = state["approaches"][candidate_id]
        route = state["routes"].get(candidate.get("route_id"), {})
        if (route.get("root_binding") != state["root"]["binding"]
                or route.get("root_obligation") != root
                or route.get("approach_id") != candidate_id
                or route.get("viability") in {"held", "blocked", "refuted", "superseded"}):
            continue
        reductions = [checked[item] for item in route.get("reductions", []) if item in checked]
        established = _checked_closure(facts, reductions)
        if root in established or target in established:
            continue
        needed = {root}
        changed = True
        while changed:
            changed = False
            for reduction in reductions:
                if reduction["consequent"] not in needed or reduction["consequent"] in established:
                    continue
                missing = set(reduction["antecedents"]) - established - needed
                if missing:
                    needed.update(missing)
                    changed = True
        if target not in needed or target == root:
            continue
        profile["affected_routes"].append(route["route_id"])
        components["checked_obstruction"] = 10
        hypothetical = _checked_closure(established | {target}, reductions)
        if root in hypothetical:
            components["root_completion"] = 40
        if any(reduction["consequent"] in needed - established
               and all(item in hypothetical for item in reduction["antecedents"])
               for reduction in reductions):
            components["reduction_completion"] = 25
    components["shared_obstruction"] = min(15, 5 * max(0, len(profile["affected_routes"]) - 1))
    question = state["questions"].get(approach.get("question_id"), {})
    scope = question.get("scope") if isinstance(question.get("scope"), dict) else {}
    competitors = scope.get("competing_approach_ids")
    if (isinstance(scope.get("discriminating_check"), str) and scope["discriminating_check"].strip()
            and isinstance(competitors, list)
            and len(set(item for item in competitors if isinstance(item, str)) & set(eligible_ids)) >= 2):
        components["discrimination"] = 10
    profile["score"] = sum(components.values())
    return profile


def select_approach(state: dict[str, Any]) -> tuple[str | None, str]:
    """Select without mutation, preserving admission fences and bounded fairness."""
    eligible_ids = [approach_id for approach_id in state["service_queue"] if eligible(state, approach_id)]
    if not eligible_ids:
        if any(item["status"] == "waiting" for item in state["approaches"].values()):
            return None, "waiting"
        if any(approach_is_held(state, item["approach_id"]) for item in state["approaches"].values()):
            return None, "held"
        return None, "no_eligible_approach"
    current = state["last_served"]
    others_waiting = len(eligible_ids) > 1
    cap = state["policy"]["max_consecutive_quanta"]
    adaptive = state["policy"].get("mode") == "adaptive"
    candidates = eligible_ids
    if adaptive and others_waiting and state["consecutive"].get(current, 0) >= cap:
        candidates = [item for item in eligible_ids if item != current]
    profiles = {item: approach_priority(state, item) for item in candidates} if adaptive else {}
    scheduling = state.get("scheduling", {})
    if adaptive and scheduling.get("quanta_since_exploration", 0) >= EXPLORATION_INTERVAL - 1:
        speculative = [item for item in candidates if not profiles[item]["affected_routes"]]
        return (speculative or candidates)[0], "protected_exploration"
    if (
        others_waiting
        and current in eligible_ids
        and _approach(state, current).get("unconsumed_followthrough")
        and state["consecutive"].get(current, 0) < cap
    ):
        return current, "follow_through"
    if adaptive:
        unserved = [item for item in candidates if _approach(state, item).get("protect_until_served")]
        if unserved:
            return unserved[0], "first_service"
        waiting = scheduling.get("eligible_wait", {})
        limit = max(EXPLORATION_INTERVAL, len(eligible_ids) * cap)
        overdue = [item for item in candidates if waiting.get(item, 0) >= limit]
        if overdue:
            return overdue[0], "bounded_wait"
        best = max(candidates, key=lambda item: profiles[item]["score"])
        if profiles[best]["score"] > 0:
            return best, "root_progress"
        return candidates[0], "oldest_eligible"
    return eligible_ids[0], "oldest_eligible"


def mark_served(state: dict[str, Any], approach_id: str, *, admitted: bool = False) -> None:
    """Record service; allocation counters advance only at the admission boundary."""
    if admitted and state["policy"].get("mode") == "adaptive":
        scheduling = state.setdefault("scheduling", {})
        scheduling["quanta_since_exploration"] = (scheduling.get("quanta_since_exploration", 0) + 1) % EXPLORATION_INTERVAL
        previous = scheduling.get("eligible_wait", {})
        scheduling["eligible_wait"] = {
            item: 0 if item == approach_id else previous.get(item, 0) + 1
            for item in state["service_queue"] if eligible(state, item)
        }
    if state["last_served"] == approach_id:
        state["consecutive"][approach_id] = state["consecutive"].get(approach_id, 0) + 1
    else:
        state["consecutive"][approach_id] = 1
    state["last_served"] = approach_id
    _approach(state, approach_id)["protect_until_served"] = False
    _join_service_tail(state, approach_id)
    state["phase"]["reviews_since_work"] = 0


def note_deferral(state: dict[str, Any], approach_id: str) -> None:
    approach = _approach(state, approach_id)
    if approach.get("phase_deferred"):
        return
    approach["phase_deferred"] = True
    state["history"]["deferred_dispatches"] += 1


def can_admit_review(state: dict[str, Any]) -> bool:
    # A closed shared phase still needs bounded reconciliation reviews.
    if not state["phase"].get("open", True):
        return True
    runnable = [approach_id for approach_id in state["service_queue"] if eligible(state, approach_id)]
    if not runnable:
        return True
    return state["phase"]["reviews_since_work"] < state["policy"]["max_control_quanta_between_work"]


def note_review_quantum(state: dict[str, Any]) -> None:
    if not can_admit_review(state):
        raise FrontierRefusal("review_quantum_limit")
    state["phase"]["reviews_since_work"] += 1


def review_basis_key(question_id: str, evidence_basis: str) -> str:
    return digest({"question_id": question_id, "evidence_basis": evidence_basis})


def issue_review_authorization(
    state: dict[str, Any],
    *,
    question_id: str,
    evidence_basis: str,
    producer_ids: list[str],
    ceiling: dict[str, Any],
    now: float,
) -> dict[str, Any]:
    key = review_basis_key(question_id, evidence_basis)
    for existing in state["review_authorizations"].values():
        if existing["basis_key"] == key and existing["status"] == "open":
            return existing
    record = {
        "authorization_id": new_id("review-auth"),
        "question_id": question_id,
        "evidence_basis": evidence_basis,
        "basis_key": key,
        "producer_ids": list(producer_ids),
        "ceiling": ceiling,
        "status": "open",
        "issued_at": now,
        "reusable_by_research": False,
    }
    state["review_authorizations"][record["authorization_id"]] = record
    return record


def hold_obligation(state: dict[str, Any], obligation_id: str, *, method: str = "", now: float) -> list[str]:
    """Hold only approaches whose live route requires this obligation."""
    if obligation_id not in state["obligations"]:
        raise FrontierRefusal("unknown_obligation")
    state["scoped_holds"].append({
        "hold_id": new_id("hold"),
        "obligation_id": obligation_id,
        "method": method,
        "approach_id": None,
        "active": True,
    })
    held: list[str] = []
    for approach in state["approaches"].values():
        if approach["status"] in {"superseded", "completed"}:
            continue
        if method and approach.get("method") != method:
            continue
        if not route_requires(state, approach.get("route_id", ""), obligation_id):
            continue
        approach["status"] = "held"
        approach["status_revision"] += 1
        approach["resume_condition"] = "appeal_or_route_revision"
        mark_permits_stale(state, approach["approach_id"])
        # Dormant queued work is held too. It must leave service so it cannot
        # fill a residency slot while the obligation is held, but its queued
        # admission ticket stays so release readmits it normally.
        _leave_service(state, approach["approach_id"])
        held.append(approach["approach_id"])
    fill_resident_slots(state, now=now)
    return held


def dismiss_hold(state: dict[str, Any], obligation_id: str) -> None:
    for hold in state["scoped_holds"]:
        if hold.get("obligation_id") == obligation_id and hold.get("active"):
            hold["active"] = False


def mark_waiting(
    state: dict[str, Any],
    approach_id: str,
    *,
    until: float,
    dependency: str,
) -> None:
    approach = _approach(state, approach_id)
    approach["status"] = "waiting"
    approach["waiting_until"] = until
    approach["waiting_dependency"] = dependency
    approach["status_revision"] += 1


def expire_waiting(state: dict[str, Any], now: float) -> list[str]:
    expired: list[str] = []
    for approach_id in list(state["resident"]):
        approach = state["approaches"][approach_id]
        if approach["status"] != "waiting" or approach["waiting_until"] is None:
            continue
        if now < approach["waiting_until"]:
            continue
        approach["status"] = "paused"
        approach["blocked_reason"] = "waiting_lease_expired"
        approach["resume_condition"] = approach["waiting_dependency"]
        state["resident"].remove(approach_id)
        if approach_id in state["service_queue"]:
            state["service_queue"].remove(approach_id)
        expired.append(approach_id)
    fill_resident_slots(state, now=now)
    return expired


def request_readmission(state: dict[str, Any], approach_id: str, *, now: float) -> None:
    approach = _approach(state, approach_id)
    if approach_is_held(state, approach_id):
        # Held work stays queued and out of service until its hold is released.
        _mark_held(state, approach_id)
        _leave_service(state, approach_id)
        return
    if approach.get("outstanding_admission_sequence") is None:
        state["admission_sequence"] += 1
        approach["outstanding_admission_sequence"] = state["admission_sequence"]
        if approach_id not in state["admission_queue"]:
            state["admission_queue"].append(approach_id)
    approach["blocked_reason"] = "awaiting_admission"
    approach["status"] = "paused"
    if approach_id in state["resident"]:
        state["resident"].remove(approach_id)
    fill_resident_slots(state, now=now)
    if approach_id not in state["resident"] and not approach_is_held(state, approach_id):
        approach["status"] = "paused"
        approach["blocked_reason"] = "awaiting_admission"


def freeze_phase(state: dict[str, Any], receipt_ids: list[str]) -> None:
    phase = state["phase"]
    phase["open"] = False
    phase["frozen_receipts"] = list(receipt_ids)
    acknowledged = set(phase["acknowledged"])
    phase["pending_review"] = [item for item in receipt_ids if item not in acknowledged]


def acknowledge_receipts(state: dict[str, Any], receipt_ids: list[str]) -> bool:
    phase = state["phase"]
    frozen = set(phase["frozen_receipts"])
    if any(phase["tails"].get(receipt_id, {}).get("status") == "running" for receipt_id in receipt_ids):
        return False
    for receipt_id in receipt_ids:
        if receipt_id not in frozen:
            raise FrontierRefusal("review_covers_unfrozen_receipt")
        if receipt_id in phase["acknowledged"]:
            raise FrontierRefusal("receipt_already_acknowledged")
        phase["acknowledged"].append(receipt_id)
    pending = [item for item in phase.get("pending_review", []) if item not in phase["acknowledged"]]
    phase["pending_review"] = pending
    if not pending:
        phase["open"] = True
        for approach in state["approaches"].values():
            approach["phase_deferred"] = False
        return True
    return False


def register_tail(state: dict[str, Any], receipt_id: str, action: str, status: str) -> dict[str, Any]:
    if status not in {"running", "executed", "deferred", "incomplete", "completed"}:
        raise FrontierRefusal("unknown_tail_status")
    if receipt_id not in state["phase"]["frozen_receipts"] and not state["phase"]["open"]:
        raise FrontierRefusal("tail_without_receipt")
    record = {
        "receipt_id": receipt_id,
        "action": action,
        "status": status,
        "provider_admission": False,
        "continuation_credit": False,
    }
    state["phase"]["tails"][receipt_id] = record
    return record


def resume_packet(state: dict[str, Any], approach_id: str) -> dict[str, Any]:
    approach = _approach(state, approach_id)
    question = state["questions"][approach["question_id"]]
    route = state["routes"][approach["route_id"]]
    return {
        "approach_id": approach_id,
        "question": question["uncertainty"],
        "question_revision": question["revision"],
        "route_id": route["route_id"],
        "route_revision": route["revision"],
        "first_uncertain_inference": question["uncertainty"],
        "checkpoint": approach.get("latest_result", ""),
        "next_step": approach.get("next_operation", ""),
        "root_binding": state["root"]["binding"],
        "cost": state["history"]["costs_by_approach"].get(approach_id, {}),
        "scheduling_priority": approach_priority(state, approach_id),
    }


def release_shared_consumer(state: dict[str, Any], obligation_id: str, approach_id: str) -> str:
    obligation = state["obligations"][obligation_id]
    consumers = [item for item in obligation.get("consumers", []) if item != approach_id]
    live = [
        item for item in consumers
        if state["approaches"][item]["status"] not in {"held", "superseded", "completed"}
    ]
    obligation["consumers"] = consumers
    if live:
        obligation["dispatch"] = "shared"
        return "retained"
    obligation["dispatch"] = "stopped"
    return "stopped"


def bind_consumer(state: dict[str, Any], obligation_id: str, approach_id: str) -> None:
    obligation = state["obligations"][obligation_id]
    if approach_id not in obligation["consumers"]:
        obligation["consumers"].append(approach_id)
    obligation["dispatch"] = "shared" if len(obligation["consumers"]) > 1 else "owned"
