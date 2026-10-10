"""Separate native admission slices from the owner's hard execution bounds."""

from __future__ import annotations

import math
from typing import Any, Mapping


def native_admission_deadline_only(run: Mapping[str, Any]) -> bool:
    return bool(
        run.get("native_parent_authorization") is True
        and run.get("native_grant_deadline_policy") == "admission_only"
    )


def paid_work_deadline(run: Mapping[str, Any]) -> float | None:
    """Return a persisted hard bound without renewing it at a later boundary."""
    if native_admission_deadline_only(run):
        # A missing field must not turn a malformed finite grant into unlimited
        # work. Legacy grants retain their original deadline semantics.
        deadline = run["native_grant_hard_deadline"]
    else:
        deadline = run["deadline"]
    if deadline is not None and (
        type(deadline) not in {int, float}
        or not math.isfinite(deadline)
        or deadline <= 0
    ):
        raise ValueError("invalid native research hard deadline")
    return deadline


def paid_response_deadline(
    run: Mapping[str, Any], job: Mapping[str, Any], receipt: Mapping[str, Any] | None,
) -> float | None:
    """Keep a saved tool response inside its dispatch and current owner bounds."""
    current = paid_work_deadline(run)
    if receipt is None:
        # Saved output remains replayable, but a renewed admission deadline
        # cannot establish an unknown original tool-execution allowance.
        return 0.0
    if receipt.get("native_paid_settlement") is True:
        if (
            run.get("native_parent_authorization") is not True
            or receipt.get("consumer_id") != job["job_id"]
            or receipt.get("consumer_turn") != job["turn"]
            or receipt.get("native_response_artifact") != job.get("response")
            or not job.get("response")
        ):
            raise ValueError("native paid response receipt does not match its tool request")
        original = receipt["ingress_deadline"]
    else:
        # Older native dispatches still recorded their finite execution bound.
        # Nonadaptive receipts did not archive response hashes; their exact
        # consumer turn owns every retry under that original grant.
        if (
            receipt.get("consumer_id") != job["job_id"]
            or receipt.get("consumer_turn") != job["turn"]
            or not job.get("response")
            or (receipt.get("artifacts") and job["response"] not in receipt["artifacts"])
        ):
            raise ValueError("legacy paid response receipt does not match its tool request")
        original = receipt.get("ingress_deadline")
        if original is None:
            raise ValueError("legacy paid response has no finite execution deadline")
    if original is not None and (
        type(original) not in {int, float}
        or not math.isfinite(original)
        or original <= 0
    ):
        raise ValueError("invalid native paid response deadline")
    deadlines = [value for value in (current, original) if value is not None]
    return min(deadlines) if deadlines else None
