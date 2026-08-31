"""Shared classification for MiniSession runtime capability fields."""

from __future__ import annotations

from typing import Any


def _exact_text(value: Any) -> str:
    """Read text metadata without invoking a string subclass override."""

    if type(value) is str:
        return value
    if isinstance(value, str):
        return str.__str__(value)
    return ""


RUNTIME_CAPABILITY_FIELD_NAMES = frozenset(
    {
        "client",
        "clients",
        "members",
        "providers",
        "backends",
        "searcher",
        "searcher_override",
        "lean",
        "recorder",
        "proof_cache",
        "theory_library",
        "theory_candidate_builder",
        "candidate_builder",
        "lease_owner",
        "event_sink",
        "on_event",
        "_static_action_receipt_authority",
        "_recursive_lane_authority",
        "_recursive_conversation_lane_ledger",
        "_recursive_paid_no_artifact_observer",
        # Recursive actions receive a functools.partial bound to the live
        # parent MiniSession.  It is dispatch authority, not action-owned
        # mutable state.  Deep-copying it recursively clones the entire
        # session/action graph and the 214k-entry Mathlib search index before
        # the selected action can even start.
        "run_conversation_fn",
    }
)


def field_is_runtime_capability(field_name: str) -> bool:
    """Return whether a field names externally owned runtime authority."""

    clean = _exact_text(field_name).strip().lower()
    return bool(
        clean in RUNTIME_CAPABILITY_FIELD_NAMES
        or clean.endswith("_client")
        or clean.endswith("_lock")
        or clean.endswith("_event")
        or clean.endswith("_semaphore")
        or clean.endswith("_transport")
        or clean.endswith("_executor")
    )
