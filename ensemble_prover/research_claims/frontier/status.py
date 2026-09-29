"""Additive status projection. There is no percent-proved figure."""

from __future__ import annotations

from typing import Any

from .approaches import resume_packet, select_approach


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
