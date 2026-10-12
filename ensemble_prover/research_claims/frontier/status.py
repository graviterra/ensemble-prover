"""Additive status projection. There is no percent-proved figure."""

from __future__ import annotations

import math
from typing import Any

from .approaches import resume_packet, select_approach


def validate_scheduling_data(state: dict[str, Any]) -> None:
    """Reject malformed scheduling inputs before the optional readiness check.

    Version validation alone does not establish container or policy types.
    Validation grants no permits and leaves every stored allowance unchanged.
    """
    from ..store import ResearchStoreError
    from .config import DEFAULTS, normalize_config

    def require(condition: bool, field: str) -> None:
        if not condition:
            raise ResearchStoreError("invalid frontier campaign scheduling data: " + field)

    policy = state.get("policy")
    require(isinstance(policy, dict) and set(DEFAULTS) <= policy.keys(), "policy")
    try:
        normalize_config(policy)
    except ValueError as exc:
        raise ResearchStoreError("invalid frontier campaign scheduling policy") from exc
    for field in ("approaches", "questions", "routes", "obligations", "reductions",
                  "permits", "claims", "entitlements", "evidence_events", "lanes", "retries"):
        records = state.get(field)
        require(isinstance(records, dict), field)
        require(all(isinstance(record, dict) for record in records.values()), field)
    for approach in state["approaches"].values():
        if approach.get("status") == "waiting":
            deadline = approach.get("waiting_until")
            require(deadline is None or type(deadline) is int
                    or type(deadline) is float and math.isfinite(deadline),
                    "approaches.waiting_until")
    for claim in state["claims"].values():
        if claim.get("status") == "held":
            expiry = claim.get("expires_at")
            require(type(expiry) is int or type(expiry) is float and math.isfinite(expiry),
                    "claims.expires_at")
    for field in ("resident", "service_queue", "admission_queue"):
        items = state.get(field)
        require(isinstance(items, list), field)
        require(all(isinstance(item, str) and item in state["approaches"] for item in items), field)
    phase = state.get("phase")
    require(isinstance(phase, dict), "phase")
    require(type(phase.get("open")) is bool, "phase.open")
    require(type(phase.get("reviews_since_work")) is int
            and phase["reviews_since_work"] >= 0, "phase.reviews_since_work")
    for field in ("frozen_receipts", "acknowledged", "pending_review"):
        require(isinstance(phase.get(field), list)
                and all(isinstance(item, str) for item in phase[field]), "phase." + field)
    require(isinstance(phase.get("tails"), dict), "phase.tails")
    for field in ("lanes", "retries"):
        for record in state[field].values():
            for flag in ("paused", "recovery_open"):
                if flag in record:
                    require(type(record[flag]) is bool, field + "." + flag)


def inconclusive_pause(state: dict[str, Any]) -> dict[str, Any] | None:
    """Explain an exhausted current investigation without granting admission."""
    if state["policy"]["mode"] != "adaptive" or select_approach(state)[0] is not None:
        return None
    target = state.get("native_active_target_claim_id")
    binding = {"target": target, "context": state.get("native_active_target_context_binding")}
    paused = []
    for approach in state["approaches"].values():
        if target is not None and binding not in approach.get(
            "native_scope_bindings", [{"target": state["root"]["target_id"], "context": None}],
        ):
            continue
        if (approach["status"] == "paused"
                and approach.get("resume_condition") == "changed_investigation"
                and approach["inconclusive_extensions"] > state["policy"]["max_no_progress"]):
            paused.append({
                "approach_id": approach["approach_id"],
                "inconclusive_extensions": approach["inconclusive_extensions"],
                "resume_condition": approach["resume_condition"],
            })
    if not paused:
        return None
    return {
        "reason": "inconclusive_allowance_exhausted",
        "max_no_progress": state["policy"]["max_no_progress"],
        "approaches": paused,
        "target_claim_id": target,
        "target_context_binding": state.get("native_active_target_context_binding"),
        "instruction": "Research is paused pending an admitted investigation change or independently reviewed progress. New proof requests, renamed questions, and helper counts do not renew its allowance. Existing proof work continues.",
    }


def _approach_view(state: dict[str, Any], approach: dict[str, Any]) -> dict[str, Any]:
    question = state["questions"].get(approach["question_id"], {})
    return {
        "approach_id": approach["approach_id"],
        "status": approach["status"],
        "method": approach.get("method", ""),
        "latest_result": approach.get("latest_result", ""),
        "first_uncertain_inference": question.get("uncertainty", ""),
        "connection": question.get("why", ""),
        "blocked_reason": approach.get("blocked_reason"),
        "resume_condition": approach.get("resume_condition"),
        "phase_deferred": bool(approach.get("phase_deferred")),
    }


def project(state: dict[str, Any]) -> dict[str, Any]:
    active = next((item for item in state["approaches"].values() if item["status"] == "active"), None)
    selected, reason = select_approach(state) if state["approaches"] else (None, "no_eligible_approach")
    selected_approach = state["approaches"].get(selected) if selected else None
    permit = None
    if selected_approach is not None:
        permit = next((
            item for item in state["permits"].values()
            if item["approach_id"] == selected and item["status"] in {"usable", "claimed"}
        ), None)
    return {
        "mode": state["policy"]["mode"],
        "progress_policy_version": state["policy"]["progress_policy_version"],
        "tool_policy_version": state["policy"]["tool_policy_version"],
        "original_target": {
            "target_id": state["root"]["target_id"],
            "binding": state["root"]["binding"],
            "proposition": state["root"]["proposition"],
            "alignment": state["root"].get("alignment", "formal_target"),
            "formal_binding": state["root"].get("formal_binding"),
            "environment": state["root"].get("environment", ""),
        },
        "active_approach": None if active is None else _approach_view(state, active),
        "obstacle": None if active is None else {
            "inference": state["questions"][active["question_id"]]["uncertainty"],
            "connection": state["questions"][active["question_id"]].get("why", ""),
            "route_id": active.get("route_id"),
        },
        "approaches": [_approach_view(state, item) for item in state["approaches"].values()],
        "research_pause": inconclusive_pause(state),
        "next_investigation": None if selected_approach is None else {
            "approach_id": selected,
            "reason": reason,
            "seeks": selected_approach.get("next_operation", ""),
            "reserved": None if permit is None else {
                "permit_id": permit["permit_id"],
                "kind": permit["kind"],
                "ceiling": permit.get("ceiling", {}),
            },
            "resume": resume_packet(state, selected_approach["approach_id"]),
        },
        "totals": {
            "verified_proof_advances": state["history"]["formal_advances"],
            "research_decisions": state["history"]["research_advances"],
            "operational_failures": state["history"]["operational_failures"],
            "resources": {
                "provider_requests": state["history"]["provider_requests"],
                "deferred_dispatches": state["history"]["deferred_dispatches"],
                "intervals": len(state["history"]["intervals"]),
            },
        },
    }


def project_from_run(store: Any, run: dict[str, Any]) -> dict[str, Any]:
    """Read-only projection. Callers inside a snapshot must not write."""
    review = run.get("strategy_review")
    if not isinstance(review, dict):
        return {"mode": "off"}
    policy = review.get("frontier_research")
    if not isinstance(policy, dict) or policy.get("mode", "off") == "off":
        return {"mode": "off"}
    from .persist import load_campaign

    state = load_campaign(store, review["owner_id"])
    if state is None:
        return {"mode": policy["mode"], "unavailable": True, "reason": "missing frontier campaign"}
    projected = project(state)
    if "percent" in projected or "proved_ratio" in projected:
        raise RuntimeError("frontier status must not publish a percent proved")
    return projected
