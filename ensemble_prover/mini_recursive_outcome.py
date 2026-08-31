"""Shared classification for resumable Mini recursive scheduler outcomes."""

from __future__ import annotations

from typing import Any


RESUMABLE_MINI_RECURSIVE_FAILURE_REASONS = frozenset(
    {
        "recursive_pass_quantum_yield",
        "recursive_contract_identity_pending_yield",
        "recursive_contract_identity_service_unavailable",
        "recursive_contract_identity_infrastructure_unknown",
    }
)


def is_resumable_mini_recursive_yield(reason: Any) -> bool:
    return str(reason or "").strip() in RESUMABLE_MINI_RECURSIVE_FAILURE_REASONS
