"""Reviewed exploration uses campaign authorization without claiming progress.

A permit makes one successor eligible for ordinary admission. It neither funds
a request nor overrides its deadline, scoped holds, fairness or retry limits.
"""

from __future__ import annotations

from typing import Any

from .approaches import approach_is_held, request_readmission
from .progress import _invalidate_permit, active_permit, issue_permit
from .records import digest


def continue_campaign_exploration(
    campaign: dict[str, Any], *, producer: dict[str, Any], reviewer: dict[str, Any], now: float,
) -> None:
    """Continue one independently reviewed report under the existing campaign.

    The owner checks the report's original scope before binding its successor.
    A report receipt can authorize this transition once, even if the review is
    replayed. An earned follow-through remains preferable to exploration.
    """
    approach_id = producer["frontier_approach_id"]
    approach = campaign["approaches"][approach_id]
    if approach_is_held(campaign, approach_id) or approach["status"] in {"completed", "superseded"}:
        return
    budget = campaign["retries"].get(approach.get("operation_lineage") or "")
    if budget and budget.get("paused"):
        return
    basis = producer["frontier_report_basis"]
    identity = digest({"report": basis["report_artifact"], "attempt": basis["attempt_id"],
                       "binding": basis["binding"]})
    continuations = campaign.setdefault("exploration_continuations", {})
    if identity in continuations:
        return
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    existing = active_permit(campaign, approach_id)
    if existing and existing["kind"] in {"formal_followthrough", "research_followthrough", "operational_retry"}:
        return
    # Replace the provisional inconclusive allowance; this authorization comes
    # from the paid, assigned review, not from a claim of mathematical success.
    if existing:
        _invalidate_permit(campaign, existing["permit_id"])
    permit = issue_permit(
        campaign, kind="campaign_exploration", approach_id=approach_id,
        question_id=question["question_id"], question_revision=question["revision"],
        route_revision=route["revision"], operation=approach["next_operation"],
        expires_at=now + campaign["policy"]["permit_lease_seconds"],
    )
    continuations[identity] = {
        "producer_id": producer["job_id"], "reviewer_id": reviewer["job_id"],
        "report_artifact": basis["report_artifact"], "attempt_id": basis["attempt_id"],
        "question_id": question["question_id"], "permit_id": permit["permit_id"],
        "progress_assessment": reviewer.get("research_progress_assessment", {"status": "unknown"}),
        "funding": "existing_campaign_authorization", "credit_minted": False,
    }
    approach["resume_condition"] = None
    approach["blocked_reason"] = None
    if approach["status"] == "paused":
        request_readmission(campaign, approach_id, now=now)
