"""Process-local exact-content identities for reconciled helper read views.

No persisted identity grants authority. Direct replacement, removal and policy
mutation remain visible even when a caller bypasses a mutation API.
"""
from __future__ import annotations

import dataclasses
import hashlib
import json
from typing import Any

# Observational histories do not participate in helper classification or replay.
# Everything else in the dossier, including all graph facts/receipts and helper
# fields, participates. Keep this conservative until mutation ownership is closed.
_OBSERVATIONS = frozenset({
    "tool_metrics", "scratch", "attempts", "decl_applications", "accepted_proof_stubs",
    "proof_lineage_events", "proof_lineage_event_ids", "action_value_observations",
    "native_scheduler_state", "parallel_sample_proof_states", "parallel_sample_failures",
    "checked_failure_feedback", "mini_recursive_runs", "mini_falsification_cursors",
})


def _plain(value: Any) -> Any:
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return {field.name: getattr(value, field.name) for field in dataclasses.fields(value)}
    if isinstance(value, (set, frozenset)):
        return sorted(value)
    raise TypeError("unsupported mutable helper snapshot component")


def helper_revision(dossier: Any) -> str | None:
    """Hash current authoritative and derived content; unsupported adapters miss."""
    if not dataclasses.is_dataclass(dossier):
        return None
    try:
        record = {field.name: getattr(dossier, field.name) for field in dataclasses.fields(dossier)
                  if field.name not in _OBSERVATIONS}
        # This restore fence is deliberately runtime-only, but affects admission.
        record["pending_answer_receipts"] = sorted(getattr(dossier, "_checkpoint_pending_answer_receipts", ()))
        # Traverse dataclass fields directly: graph.to_record() prunes nodes and
        # refreshes branch frames, so calling it here would mutate a read view.
        # Preserve dictionary insertion order: helper/notation replay order can
        # affect elaboration even when every individual source is unchanged.
        return hashlib.sha256(json.dumps(record, default=_plain, sort_keys=False,
                                         separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()
    except (TypeError, ValueError, AttributeError):
        # Never reuse a possibly stale view when an adapter cannot be fingerprinted.
        return None
