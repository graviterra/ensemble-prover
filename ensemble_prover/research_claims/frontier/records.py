"""Identifiers and refusal type for frontier records."""

from __future__ import annotations

import hashlib
import uuid
from typing import Any

from ..model import json_text


class FrontierRefusal(ValueError):
    """A policy rejection. It is not a mathematical verdict."""

    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


def digest(value: Any) -> str:
    return hashlib.sha256(json_text(value).encode()).hexdigest()


def new_id(prefix: str) -> str:
    return f"{prefix}-{uuid.uuid4().hex}"


# These refusals require changed permission or repaired preparation, not a
# transport retry. Dispatch, waiting, and wake-up must share the same taxonomy.
PERMIT_ADMISSION_WAIT_REASONS = frozenset({
    "stale_permit_basis", "stale_frontier_scope", "formal_authority_revoked",
    "permit_expired", "claim_expired", "entitlement_invalidated",
    "distinctness_unresolved", "missing_preparation_claim", "permit_claimed_by_other",
    "permit_not_prepared", "permit_approach_mismatch", "approach_held",
    "entitlement_already_spent",
})


EVIDENCE_CLASSES = frozenset({
    "root_verified",
    "root_refuted",
    "formal_advance",
    "research_advance",
    "route_obstruction",
    "observation_only",
    "operational_failure",
})
AUTHORITY_TIERS = frozenset({"research_significance", "formal_checked"})
REDUCTION_LEVELS = frozenset({"proposed", "reviewed", "checked"})
APPROACH_STATES = frozenset({
    "proposed",
    "runnable",
    "active",
    "waiting",
    "paused",
    "held",
    "dormant",
    "superseded",
    "completed",
})
PERMIT_KINDS = frozenset({
    "initial_exploration",
    "campaign_exploration",
    "formal_followthrough",
    "research_followthrough",
    "inconclusive_extension",
    "operational_retry",
    "review",
})
