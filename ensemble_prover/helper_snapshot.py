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


def _classification_digest(value: Any) -> str | None:
    try:
        return hashlib.sha256(json.dumps(
            value, default=_plain, sort_keys=False, separators=(",", ":"),
            ensure_ascii=False,
        ).encode()).hexdigest()
    except (TypeError, ValueError, AttributeError):
        return None


def helper_classification_context(dossier: Any) -> str | None:
    """Fingerprint shared inputs to derived quality, not proof authority.

    The complete dossier revision still governs read views and graph updates.
    Unchanged individual classifications need only their mathematical frame,
    semantic environment and visibility policy; appending an independent fact
    does not change those inputs.
    """
    return _classification_digest((
        dossier.root_statement,
        dossier.current_lean_environment_hash,
        dossier.lean_environment_plain_syntax,
        dossier.lean_environment_ancestor_hashes,
        dossier.lean_environment_content_digests,
        dossier.active_root_targets,
        dossier.active_root_classification_preamble_hash,
        dossier.suppress_solution_placeholders,
        dossier.opaque_mode,
        dossier.allow_official_answer_visibility,
        dossier.official_answer_payload_present,
    ))


def helper_classification_support(dossier: Any) -> str | None:
    """Bind premise lookup and active-root frames to the exact visible sources."""
    return _classification_digest(tuple(
        (name, helper.source, dossier._verified_helper_context_visible(helper))
        for name, helper in dossier.verified_helpers.items()
    ))


def helper_classification_revision(
    helper: Any, *, context: str | None, context_sources_are_plain: bool,
    support: str | None, requires_support: bool,
) -> str | None:
    """Include mutable outputs too, so direct edits cannot impersonate a hit."""
    if context is None or (requires_support and support is None):
        return None
    if not dataclasses.is_dataclass(helper):
        return None
    return _classification_digest((
        helper, context, context_sources_are_plain, support if requires_support else None,
    ))
