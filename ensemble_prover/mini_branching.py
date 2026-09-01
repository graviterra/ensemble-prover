"""Branching and parallel-sample utilities for the mini prover.

This module owns the small but high-impact state transitions that happen at
branch boundaries: cloning dossier state into an isolated branch, selecting the
best failed branch, and merging durable helper knowledge plus observability
back into the parent.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from dataclasses import asdict, replace
from itertools import islice
from typing import Any, Dict, List, Mapping, MutableMapping, Optional, Sequence, Set, Tuple

from .helper_salvage import (
    helper_source_hash_was_superseded,
    helper_provenance_is_trust_monotone,
    helper_uses_superseded_support,
    preflight_dependency_ordered_verified_helper_items,
)
from .llm_error_policy import is_terminal_session_failure_reason
from .proof_dossier import (
    ProofDossier,
    VerifiedHelper,
    _verified_helpers_conflicting_with_falsification,
    active_root_disproof_certificate_is_valid,
    clone_verified_helper,
    helper_decl_name,
    is_answer_unsafe_helper_source,
    propagate_invalidated_statements,
    propagate_proposed_helpers,
    selected_work_has_explicit_cognition,
    text_hash,
)
from .proof_graph import graph_node_semantic_work_key
from .proof_lineage import (
    ProofIdeaBranchProvenance,
    ProofIdeaClaimIntent,
    ProofIdeaClaimResolution,
    ProofIdeaObservation,
    ProofIdeaRecord,
    ProofIdeaStatusTransition,
    ProofLineageEnvelope,
    lineage_event_identity,
    stable_identity,
)
from .tactic_attempt_telemetry import MONOTONIC_LEAN_ATTEMPT_METRICS


def _safe_int(value: Any) -> int:
    try:
        return int(value or 0)
    except Exception:
        return 0


def _transfer_validated_falsification_state(
    dst: ProofDossier, src: ProofDossier
) -> None:
    """Replace branch-local falsification state through its trust boundary.

    Verified helpers must already be present on ``dst`` so typed negative
    evidence can be linked to the exact helper source.  The propagation helper
    validates report/certificate linkage, derives cursors from the ledger, and
    normalizes recursive child-root evidence to parent-helper scope.
    """

    dst.mini_recursive_invalidated_statement_reasons = {}
    dst.mini_recursive_invalidation_provenance = {}
    dst.mini_authoritative_negations = {}
    dst.mini_falsification_ledger = []
    dst.mini_falsification_cursors = {}
    dst.root_disproof_certificate = None
    dst.mini_falsification_pending_certificates = []
    dst.mini_falsification_certificate_replay_dispositions = {}
    dst.mini_falsification_trust_boundary_conflict_certificate_hashes = set()
    setattr(
        dst,
        "_mini_falsification_trust_boundary_conflict_certificate_hashes",
        set(),
    )
    from .mini_falsification.veto import copy_scheduler_runtime

    copy_scheduler_runtime(dst, src)
    propagate_invalidated_statements(dst, src, record_graph=False)


def _seed_proposed_helpers(dst: ProofDossier, src: ProofDossier) -> None:
    """Seed a child dossier with the parent's unverified helper proposals."""

    dst.proposed_helpers = copy.deepcopy(getattr(src, "proposed_helpers", {}) or {})
    _transfer_validated_falsification_state(dst, src)
    dst.mini_recursive_exhausted_claim_keys = set(
        getattr(src, "mini_recursive_exhausted_claim_keys", set()) or ()
    )
    dst.mini_recursive_claim_helper_bindings = copy.deepcopy(
        getattr(src, "mini_recursive_claim_helper_bindings", {}) or {}
    )
    dst.active_root_targets = copy.deepcopy(
        getattr(src, "active_root_targets", []) or []
    )
    dst.active_root_classification_preamble_hash = str(
        getattr(src, "active_root_classification_preamble_hash", "") or ""
    )
    dst.official_answer_payload_present = getattr(
        src,
        "official_answer_payload_present",
        getattr(dst, "official_answer_payload_present", None),
    )
    dst.mini_theory_snapshot = copy.deepcopy(
        getattr(src, "mini_theory_snapshot", ()) or ()
    )
    dst.mini_theory_context_hash = str(
        getattr(src, "mini_theory_context_hash", "") or ""
    )
    dst.current_lean_environment_hash = str(
        getattr(src, "current_lean_environment_hash", "") or ""
    )
    dst.lean_environment_ancestor_hashes = copy.deepcopy(
        getattr(src, "lean_environment_ancestor_hashes", {}) or {}
    )
    # The ancestry map is only interpretable alongside the recorded
    # declaration sets: without them the monotonicity guard fails open.
    dst.lean_environment_content_digests = copy.deepcopy(
        getattr(src, "lean_environment_content_digests", {}) or {}
    )
    # Eviction generation is monotone evidence that helpers were REMOVED, so a
    # clone must never lower it: taking the max keeps a branch that inherited a
    # parent's evictions from looking like a session that never had them.
    dst.verified_helper_eviction_generation = max(
        int(getattr(dst, "verified_helper_eviction_generation", 0) or 0),
        int(getattr(src, "verified_helper_eviction_generation", 0) or 0),
    )
    dst.graph_execution_projection_mode = str(
        getattr(src, "graph_execution_projection_mode", "off") or "off"
    )
    dst.graph_execution_project_environment_hash = str(
        getattr(src, "graph_execution_project_environment_hash", "") or ""
    )


def _copy_dossier_contents(dst: ProofDossier, src: ProofDossier) -> None:
    """Replace ``dst`` contents with a deep, isolated copy of ``src``."""

    source_has_typed_conflict = _parallel_sample_has_proof_disproof_conflict(src)
    dst.verified_helpers = {}
    for name, item in (src.verified_helpers or {}).items():
        if isinstance(item, VerifiedHelper):
            dst.verified_helpers[name] = clone_verified_helper(item)
        else:
            dst.verified_helpers[name] = copy.deepcopy(item)
    dst.superseded_verified_helper_hashes = copy.deepcopy(
        getattr(src, "superseded_verified_helper_hashes", {}) or {}
    )
    dst.verified_helper_source_hash_history = copy.deepcopy(
        getattr(src, "verified_helper_source_hash_history", {}) or {}
    )
    dst.theory_promotion_durable_helper_fingerprints = copy.deepcopy(
        getattr(
            src,
            "theory_promotion_durable_helper_fingerprints",
            {},
        )
        or {}
    )
    # Fix 1 follow-up (2026-05-22): the original Fix 1 commit
    # (d08b3958) added ``verified_helper_statement_aliases`` to
    # ProofDossier but did not extend ``_copy_dossier_contents`` to
    # propagate it across branch/merge boundaries. In the observed failure,
    # two helpers with byte-identical
    # canonical statements were both stored, while ``summary.json``
    # showed an empty alias map — because the session-dossier's
    # ``verified_helper_statement_aliases`` was rebuilt correctly during
    # the session, then silently dropped on the snapshot back to the
    # parent dossier. This propagation closes the gap.
    dst.verified_helper_statement_aliases = copy.deepcopy(
        getattr(src, "verified_helper_statement_aliases", {}) or {}
    )
    dst.proposed_helpers = copy.deepcopy(getattr(src, "proposed_helpers", {}) or {})
    # Falsification certificates are bound to the Lean environment in which
    # they were audited. A full dossier replacement must install that
    # environment before crossing the falsification trust boundary; otherwise
    # a valid certificate is quarantined against the destination's stale hash.
    dst.current_lean_environment_hash = str(
        getattr(src, "current_lean_environment_hash", "") or ""
    )
    dst.lean_environment_ancestor_hashes = copy.deepcopy(
        getattr(src, "lean_environment_ancestor_hashes", {}) or {}
    )
    dst.lean_environment_content_digests = copy.deepcopy(
        getattr(src, "lean_environment_content_digests", {}) or {}
    )
    # Install the source proof boundary before importing its falsification
    # ledger.  This removes stale destination proof state (which used to
    # quarantine a valid source disproof) while preserving a genuine conflict
    # owned by the source as a conflict instead of temporarily promoting its
    # negative certificate beside a later-copied proof.
    dst.final_proof = getattr(src, "final_proof", None)
    dst.final_proof_hash = getattr(src, "final_proof_hash", None)
    dst.final_replay_helpers = list(
        getattr(src, "final_replay_helpers", ()) or ()
    )
    dst.root_proof_certificate = copy.deepcopy(
        getattr(src, "root_proof_certificate", None)
    )
    dst._root_proof_finalization_receipts = set(
        getattr(src, "_root_proof_finalization_receipts", set()) or ()
    )
    _transfer_validated_falsification_state(dst, src)
    generated_conflict_hashes = set(
        getattr(
            dst,
            "mini_falsification_trust_boundary_conflict_certificate_hashes",
            set(),
        )
        or ()
    )
    source_conflict_hashes = set(
        getattr(
            src,
            "mini_falsification_trust_boundary_conflict_certificate_hashes",
            set(),
        )
        or ()
    )
    dst.mini_falsification_trust_boundary_conflict_certificate_hashes = (
        generated_conflict_hashes | source_conflict_hashes
    )
    generated_conflict_receipts = set(
        getattr(
            dst,
            "_mini_falsification_trust_boundary_conflict_certificate_hashes",
            set(),
        )
        or ()
    )
    source_conflict_receipts = set(
        getattr(
            src,
            "_mini_falsification_trust_boundary_conflict_certificate_hashes",
            set(),
        )
        or ()
    )
    setattr(
        dst,
        "_mini_falsification_trust_boundary_conflict_certificate_hashes",
        generated_conflict_receipts | source_conflict_receipts,
    )
    if source_has_typed_conflict:
        # Ledger propagation runs before the private conflict receipt is
        # restored and can therefore rematerialize the quarantined negative.
        # A typed proof/disproof conflict owns no mathematical-disproof
        # verdict, so keep its root certificate quarantined after the copy.
        dst.root_disproof_certificate = None
    dst.mini_recursive_exhausted_claim_keys = set(
        getattr(src, "mini_recursive_exhausted_claim_keys", set()) or ()
    )
    dst.mini_recursive_claim_helper_bindings = copy.deepcopy(
        getattr(src, "mini_recursive_claim_helper_bindings", {}) or {}
    )
    dst.active_root_targets = copy.deepcopy(
        getattr(src, "active_root_targets", []) or []
    )
    dst.active_root_classification_preamble_hash = str(
        getattr(src, "active_root_classification_preamble_hash", "") or ""
    )
    dst.official_answer_payload_present = getattr(
        src,
        "official_answer_payload_present",
        getattr(dst, "official_answer_payload_present", None),
    )
    dst.mini_theory_snapshot = copy.deepcopy(
        getattr(src, "mini_theory_snapshot", ()) or ()
    )
    dst.mini_theory_context_hash = str(
        getattr(src, "mini_theory_context_hash", "") or ""
    )
    # Eviction generation is monotone evidence that helpers were REMOVED, so a
    # clone must never lower it: taking the max keeps a branch that inherited a
    # parent's evictions from looking like a session that never had them.
    dst.verified_helper_eviction_generation = max(
        int(getattr(dst, "verified_helper_eviction_generation", 0) or 0),
        int(getattr(src, "verified_helper_eviction_generation", 0) or 0),
    )
    dst.graph_execution_projection_mode = str(
        getattr(src, "graph_execution_projection_mode", "off") or "off"
    )
    dst.graph_execution_project_environment_hash = str(
        getattr(src, "graph_execution_project_environment_hash", "") or ""
    )
    failure_reason = str(getattr(src, "session_failure_reason", "") or "").strip()
    if is_terminal_session_failure_reason(failure_reason):
        setattr(dst, "session_failure_reason", failure_reason)
        failure_kind = str(getattr(src, "session_failure_kind", "") or "").strip()
        if failure_kind:
            setattr(dst, "session_failure_kind", failure_kind)
        elif hasattr(dst, "session_failure_kind"):
            try:
                delattr(dst, "session_failure_kind")
            except Exception:
                setattr(dst, "session_failure_kind", "")
    else:
        source_reported_nonterminal_failure = bool(failure_reason)
        existing_reason = str(
            getattr(dst, "session_failure_reason", "") or ""
        ).strip()
        if not (
            source_reported_nonterminal_failure
            and is_terminal_session_failure_reason(existing_reason)
        ):
            for attr in ("session_failure_reason", "session_failure_kind"):
                if hasattr(dst, attr):
                    try:
                        delattr(dst, attr)
                    except Exception:
                        setattr(dst, attr, "")
    dst.attempts = copy.deepcopy(src.attempts)
    dst.scratch = copy.deepcopy(src.scratch)
    dst.accepted_proof_stubs = copy.deepcopy(
        getattr(src, "accepted_proof_stubs", [])
    )
    dst.tool_metrics = copy.deepcopy(getattr(src, "tool_metrics", {}))
    dst.decl_applications = copy.deepcopy(src.decl_applications)
    dst.mini_recursive_runs = copy.deepcopy(src.mini_recursive_runs)
    dst.proof_lineage_events = copy.deepcopy(
        getattr(src, "proof_lineage_events", []) or []
    )
    dst.proof_lineage_event_ids = set(
        getattr(src, "proof_lineage_event_ids", set()) or ()
    )
    dst.proof_ideas = copy.deepcopy(getattr(src, "proof_ideas", {}) or {})
    dst.semantic_fact_registry = copy.deepcopy(
        getattr(src, "semantic_fact_registry", {}) or {}
    )
    dst.action_value_observations = copy.deepcopy(
        getattr(src, "action_value_observations", {}) or {}
    )
    dst.parallel_sample_proof_states = copy.deepcopy(
        getattr(src, "parallel_sample_proof_states", [])
    )
    dst.parallel_sample_failures = copy.deepcopy(
        getattr(src, "parallel_sample_failures", [])
    )
    dst.final_proof = getattr(src, "final_proof", None)
    dst.final_proof_hash = src.final_proof_hash
    dst.final_replay_helpers = list(src.final_replay_helpers)
    # The verification certificate is part of the finalized proof artifact,
    # not branch-local observability.  Replace it together with the proof so a
    # successful branch cannot lose its certificate and an unsuccessful
    # branch cannot leave a stale destination certificate behind.
    dst.root_proof_certificate = copy.deepcopy(
        getattr(src, "root_proof_certificate", None)
    )
    if hasattr(dst, "proof_state_record"):
        delattr(dst, "proof_state_record")
    if hasattr(src, "proof_state_record"):
        dst.proof_state_record = copy.deepcopy(
            getattr(src, "proof_state_record") or {}
        )
    dst.proof_graph = (
        src.proof_graph.clone()
        if getattr(src, "proof_graph", None) is not None
        else None
    )
    sync_helpers = getattr(dst, "_sync_legacy_helpers_to_graph", None)
    if callable(sync_helpers):
        sync_helpers()


def _parallel_observability_snapshot(dossier: ProofDossier) -> Dict[str, Any]:
    """Capture parent telemetry that must survive sample-dossier fan-in."""

    return {
        "tool_metrics": copy.deepcopy(getattr(dossier, "tool_metrics", {}) or {}),
        "parallel_sample_proof_states": copy.deepcopy(
            getattr(dossier, "parallel_sample_proof_states", []) or []
        ),
        "parallel_sample_failures": copy.deepcopy(
            getattr(dossier, "parallel_sample_failures", []) or []
        ),
    }


def _restore_parallel_observability_snapshot(
    dossier: ProofDossier,
    snapshot: Dict[str, Any],
) -> None:
    """Merge pre-fanout parent telemetry after a sample copy overwrote it."""

    for key, value in dict(snapshot.get("tool_metrics") or {}).items():
        dossier.tool_metrics[key] = int(dossier.tool_metrics.get(key, 0) or 0) + int(
            value or 0
        )
    for record in list(snapshot.get("parallel_sample_proof_states") or []):
        copied_record = copy.deepcopy(record)
        if copied_record not in getattr(dossier, "parallel_sample_proof_states", []):
            dossier.parallel_sample_proof_states.append(copied_record)
    for record in list(snapshot.get("parallel_sample_failures") or []):
        copied_record = copy.deepcopy(record)
        if copied_record not in getattr(dossier, "parallel_sample_failures", []):
            dossier.parallel_sample_failures.append(copied_record)
    del dossier.parallel_sample_failures[:-16]


def _clear_parallel_sample_observability(dossier: ProofDossier) -> None:
    """Reset inherited telemetry so a parallel branch reports deltas only."""

    dossier.tool_metrics = {}
    dossier.parallel_sample_proof_states = []
    dossier.parallel_sample_failures = []


def _install_parallel_monotonic_metric_sink(
    sample_dossier: ProofDossier,
    parent_dossier: ProofDossier,
) -> None:
    """Mirror exact attempt audit metrics while a sample is still cancellable.

    A cancelled or abandoned task may never return its dossier to the fan-in
    loop.  Mirroring only the monotonic execution-audit keys at write time
    keeps real started/cancelled attempts visible without leaking speculative
    helpers, graph state, or ordinary branch-local metrics.
    """

    def sink(key: str, amount: int) -> None:
        if str(key or "") not in MONOTONIC_LEAN_ATTEMPT_METRICS:
            return
        parent_dossier.increment_tool_metric(str(key), int(amount))

    setattr(sample_dossier, "_monotonic_tool_metric_sink", sink)


def _parallel_monotonic_metric_snapshot(dossier: ProofDossier) -> Dict[str, int]:
    metrics = getattr(dossier, "tool_metrics", {}) or {}
    return {
        key: int(metrics.get(key, 0) or 0)
        for key in MONOTONIC_LEAN_ATTEMPT_METRICS
        if int(metrics.get(key, 0) or 0) != 0
    }


def _restore_parallel_monotonic_metric_snapshot(
    dossier: ProofDossier,
    snapshot: Mapping[str, int],
) -> None:
    for key in MONOTONIC_LEAN_ATTEMPT_METRICS:
        if key in snapshot:
            dossier.tool_metrics[key] = int(snapshot[key])


def _remaining_goal_batch_count_for_state(
    proof_state: Any,
    remaining_goals: Sequence[Any],
    *,
    limit: int,
) -> int:
    cap = max(0, int(limit or 0))
    count = 0
    for item in list(remaining_goals or []):
        if isinstance(item, dict):
            count += 1
        elif isinstance(item, str):
            rendered_count = len(
                proof_state._goals_from_rendered_text(  # noqa: SLF001
                    item,
                    max_goals=max(1, cap - count),
                )
            )
            if rendered_count:
                count += rendered_count
            elif proof_state._plain_remaining_goal_target(item):  # noqa: SLF001
                count += 1
        else:
            count += 1
        if cap and count >= cap:
            return count
    return count


_ROOT_DISPROOF_FAILURE_REASON = "root_disproved_by_audited_lean_certificate"
_ROOT_DISPROOF_FAILURE_KIND = "mathematical_disproof"


def _parallel_sample_has_root_disproof(dossier: Any) -> bool:
    """Return whether a sample owns an active, validated root certificate."""

    return active_root_disproof_certificate_is_valid(dossier)


def _ensure_parallel_root_disproof_terminal_state(dossier: Any) -> bool:
    """Restore the canonical terminal markers implied by a root certificate."""

    if not _parallel_sample_has_root_disproof(dossier):
        return False
    setattr(dossier, "session_failure_reason", _ROOT_DISPROOF_FAILURE_REASON)
    setattr(dossier, "session_failure_kind", _ROOT_DISPROOF_FAILURE_KIND)
    return True


def _mark_parallel_proof_disproof_conflict(
    dossier: Any,
    *,
    increment_metric: bool = True,
    certificate_hashes: Sequence[str] = (),
) -> None:
    """Replace externally authoritative verdict state with a conflict."""

    dossier.root_disproof_certificate = None
    setattr(dossier, "session_failure_reason", "falsification_trust_boundary_conflict")
    setattr(dossier, "session_failure_kind", "proof_disproof_conflict")
    durable_hashes = getattr(
        dossier,
        "mini_falsification_trust_boundary_conflict_certificate_hashes",
        None,
    )
    if not isinstance(durable_hashes, set):
        durable_hashes = set()
        setattr(
            dossier,
            "mini_falsification_trust_boundary_conflict_certificate_hashes",
            durable_hashes,
        )
    incoming_hashes = {
        clean_hash
        for item in certificate_hashes
        for clean_hash in [str(item or "").strip()]
        if len(clean_hash) == 64
        and all(character in "0123456789abcdef" for character in clean_hash)
    }
    new_hashes = incoming_hashes.difference(durable_hashes)
    durable_hashes.update(incoming_hashes)
    receipts = getattr(
        dossier,
        "_mini_falsification_trust_boundary_conflict_certificate_hashes",
        None,
    )
    if not isinstance(receipts, set):
        receipts = set()
        setattr(
            dossier,
            "_mini_falsification_trust_boundary_conflict_certificate_hashes",
            receipts,
        )
    receipts.update(incoming_hashes)
    if new_hashes:
        # A receipt suppresses double-counting only for hashes already added
        # by report propagation. In a mixed fan-in another quarantined hash
        # can still be new, so certificate-set cardinality—not one aggregate
        # boolean—owns the counter delta.
        _increment_dossier_metric(
            dossier,
            "mini_falsification_trust_boundary_conflicts",
            len(new_hashes),
        )


def _parallel_completed_root_disproof_certificate_hashes(
    records: Sequence[Tuple[int, Any]],
    *,
    exclude: Any = None,
) -> Set[str]:
    hashes: Set[str] = set()
    for _sample_index, dossier in records:
        if dossier is exclude or not active_root_disproof_certificate_is_valid(
            dossier,
            reject_proof_conflicts=False,
        ):
            continue
        certificate = getattr(dossier, "root_disproof_certificate", None) or {}
        certificate_hash = str(
            certificate.get("certificate_hash") or ""
        ).strip()
        if certificate_hash:
            hashes.add(certificate_hash)
    return hashes


def _snapshot_parallel_live_root_disproof(
    dossier: Any,
) -> Optional[ProofDossier]:
    """Freeze validated root-disproof authority held by a live sample.

    A proof sibling can win while this sample remains blocked after recording
    ``¬root``.  Its task result will then be absent from ordinary fan-in, so
    preserve only the already validated mathematical authority before
    cancellation can roll back or abandon the rest of its mutable state.
    """

    if not active_root_disproof_certificate_is_valid(dossier):
        return None
    snapshot = ProofDossier(
        theorem_name=str(getattr(dossier, "theorem_name", "") or ""),
        root_statement=str(getattr(dossier, "root_statement", "") or ""),
        problem_text=str(getattr(dossier, "problem_text", "") or ""),
        current_lean_environment_hash=str(
            getattr(dossier, "current_lean_environment_hash", "") or ""
        ),
    )
    _copy_dossier_contents(snapshot, dossier)
    return snapshot if active_root_disproof_certificate_is_valid(snapshot) else None


def _parallel_sample_has_valid_finalized_root_proof_artifact(dossier: Any) -> bool:
    """Validate the durable certificate installed by canonical finalization.

    A bare ``mark_solved`` call is deliberately insufficient: fan-in may only
    recover a proof from a raising/abandoned sample when the persisted artifact
    is bound to an accepted Lean verification receipt for this exact root.
    """

    proof = str(getattr(dossier, "final_proof", "") or "").strip()
    root_statement = str(getattr(dossier, "root_statement", "") or "").strip()
    theorem_name = str(getattr(dossier, "theorem_name", "") or "").strip()
    certificate = getattr(dossier, "root_proof_certificate", None)
    if not proof or not root_statement or not isinstance(certificate, dict):
        return False
    receipt_check = getattr(dossier, "has_root_proof_finalization_receipt", None)
    if not callable(receipt_check) or not receipt_check():
        return False
    proof_hash = text_hash(proof)
    root_hash = text_hash(root_statement)
    raw_replay_helpers = getattr(dossier, "final_replay_helpers", ()) or ()
    certificate_replay_helpers = certificate.get("replay_helpers")
    certificate_replay_hashes = certificate.get("replay_helper_source_hashes")
    certificate_replay_names = certificate.get("replay_helper_names")
    certificate_replay_count = certificate.get("replay_helper_count")
    if (
        isinstance(raw_replay_helpers, (str, bytes, Mapping))
        or not isinstance(raw_replay_helpers, (list, tuple))
        or not isinstance(certificate_replay_helpers, list)
        or not isinstance(certificate_replay_hashes, list)
        or not isinstance(certificate_replay_names, list)
        or isinstance(certificate_replay_count, bool)
        or not isinstance(certificate_replay_count, int)
        or certificate_replay_count < 0
    ):
        return False
    replay_helpers = tuple(
        str(block or "").strip()
        for block in raw_replay_helpers
        if str(block or "").strip()
    )
    replay_hashes = [text_hash(block) for block in replay_helpers]
    replay_names = [
        name
        for block in replay_helpers
        for name in [helper_decl_name(block)]
        if name
    ]
    verification = certificate.get("verification_certificate")
    status = certificate.get("verification_status")
    accepted_hash = str(certificate.get("accepted_proof_hash") or "").strip()
    proof_environment_hash = str(
        certificate.get("target_environment_hash") or ""
    ).strip()
    current_environment_hash = str(
        getattr(dossier, "current_lean_environment_hash", "") or ""
    ).strip()
    compatibility_check = getattr(
        dossier,
        "lean_environment_is_compatible",
        None,
    )
    environment_compatible = (
        bool(
            compatibility_check(
                proof_environment_hash,
                current_environment_hash,
            )
        )
        if callable(compatibility_check)
        else proof_environment_hash == current_environment_hash
    )
    return bool(
        certificate.get("schema_version") == 1
        and str(certificate.get("theorem_name") or "").strip() == theorem_name
        and str(certificate.get("root_statement") or "").strip() == root_statement
        and str(certificate.get("root_statement_hash") or "").strip() == root_hash
        and environment_compatible
        and str(certificate.get("proof") or "").strip() == proof
        and str(certificate.get("proof_hash") or "").strip() == proof_hash
        and str(certificate.get("artifact_proof_hash") or "").strip() == proof_hash
        and str(getattr(dossier, "final_proof_hash", "") or "").strip()
        == proof_hash
        and tuple(certificate_replay_helpers) == replay_helpers
        and certificate_replay_hashes == replay_hashes
        and certificate_replay_names == replay_names
        and certificate_replay_count == len(replay_helpers)
        and accepted_hash
        and isinstance(verification, dict)
        and verification.get("accepted") is True
        and str(verification.get("verifier") or "").strip() == "lean"
        and str(verification.get("proof_hash") or "").strip() == accepted_hash
        and str(verification.get("target_statement_hash") or "").strip()
        == root_hash
        and isinstance(status, dict)
        and status.get("ready") is True
        and str(status.get("verdict") or "").strip()
        == "root_finalization_certificate_ready"
        and str(status.get("proof_hash") or "").strip() == accepted_hash
        and str(status.get("verifier") or "").strip() == "lean"
    )


def _parallel_proof_disproof_conflict_certificate_hashes(
    dossier: Any,
) -> Set[str]:
    """Return durable conflict hashes backed by validated ledger reports."""

    durable_hashes = {
        str(item or "").strip()
        for item in (
            getattr(
                dossier,
                "mini_falsification_trust_boundary_conflict_certificate_hashes",
                set(),
            )
            or ()
        )
        if isinstance(item, str)
    }
    if not durable_hashes:
        return set()
    admission_receipts = {
        str(item or "").strip()
        for item in (
            getattr(
                dossier,
                "_mini_falsification_trust_boundary_conflict_certificate_hashes",
                set(),
            )
            or ()
        )
        if isinstance(item, str)
    }
    if not admission_receipts:
        return set()
    from .mini_falsification import (
        authoritative_certificate_record_is_valid,
        falsification_report_record_is_valid,
    )

    ledger_hashes = {
        str(certificate.get("certificate_hash") or "").strip()
        for report in getattr(dossier, "mini_falsification_ledger", ()) or ()
        if isinstance(report, Mapping)
        and falsification_report_record_is_valid(report)
        for finding in report.get("findings") or ()
        if isinstance(finding, Mapping)
        for certificate in [finding.get("certificate")]
        if isinstance(certificate, Mapping)
        and authoritative_certificate_record_is_valid(certificate)
    }
    return durable_hashes.intersection(admission_receipts, ledger_hashes)


def _parallel_sample_has_proof_disproof_conflict(dossier: Any) -> bool:
    """Validate the fail-closed terminal marker for conflicting authority.

    ``record_falsification_report`` intentionally does not install a root
    disproof beside an already finalized proof or an exact verified helper.
    It does record a monotone conflict metric, and the certifier installs this
    exact terminal marker. Fan-in must preserve that state even though there
    is no active root-disproof certificate to rank.
    """

    metrics = getattr(dossier, "tool_metrics", None)
    if not isinstance(metrics, Mapping):
        return False
    certificate_hashes = _parallel_proof_disproof_conflict_certificate_hashes(
        dossier
    )
    if not certificate_hashes:
        return False
    conflict_count = metrics.get("mini_falsification_trust_boundary_conflicts", 0)
    return bool(
        str(getattr(dossier, "session_failure_reason", "") or "").strip()
        == "falsification_trust_boundary_conflict"
        and str(getattr(dossier, "session_failure_kind", "") or "").strip()
        == "proof_disproof_conflict"
        and _safe_int(conflict_count) > 0
    )


def _parallel_sample_has_finalized_root_proof(dossier: Any) -> bool:
    """Return a recoverable proof only when no typed authority conflict exists."""

    return bool(
        not _parallel_sample_has_proof_disproof_conflict(dossier)
        and _parallel_sample_has_valid_finalized_root_proof_artifact(dossier)
    )


def _snapshot_parallel_live_root_proof(
    dossier: Any,
) -> Optional[ProofDossier]:
    """Freeze an exact Lean-finalized root proof owned by a live sample."""

    if not _parallel_sample_has_finalized_root_proof(dossier):
        return None
    snapshot = ProofDossier(
        theorem_name=str(getattr(dossier, "theorem_name", "") or ""),
        root_statement=str(getattr(dossier, "root_statement", "") or ""),
        problem_text=str(getattr(dossier, "problem_text", "") or ""),
        current_lean_environment_hash=str(
            getattr(dossier, "current_lean_environment_hash", "") or ""
        ),
    )
    _copy_dossier_contents(snapshot, dossier)
    return snapshot if _parallel_sample_has_finalized_root_proof(snapshot) else None


def _snapshot_parallel_live_proof_disproof_conflict(
    dossier: Any,
) -> Optional[ProofDossier]:
    """Freeze a validated proof/disproof trust-boundary conflict."""

    if not _parallel_sample_has_proof_disproof_conflict(dossier):
        return None
    snapshot = ProofDossier(
        theorem_name=str(getattr(dossier, "theorem_name", "") or ""),
        root_statement=str(getattr(dossier, "root_statement", "") or ""),
        problem_text=str(getattr(dossier, "problem_text", "") or ""),
        current_lean_environment_hash=str(
            getattr(dossier, "current_lean_environment_hash", "") or ""
        ),
    )
    _copy_dossier_contents(snapshot, dossier)
    return (
        snapshot
        if _parallel_sample_has_proof_disproof_conflict(snapshot)
        else None
    )


def _parallel_authoritative_failure_records(
    completed_records: Sequence[Tuple[int, ProofDossier]],
    *,
    proof_snapshots: Optional[Mapping[int, ProofDossier]] = None,
    disproof_snapshots: Mapping[int, ProofDossier],
    conflict_snapshots: Mapping[int, ProofDossier],
) -> List[Tuple[int, ProofDossier]]:
    """Dedupe fan-in records while retaining the strongest frozen authority.

    A sample can publish a disproof during cancellation and later return after
    rolling back its mutable workspace.  Its pre-rollback snapshot must
    replace, not duplicate, that task result.  A typed trust-boundary conflict
    ranks above either ordinary state or a lone disproof snapshot.
    """

    order: List[int] = []
    records: Dict[int, ProofDossier] = {}
    for sample_index, dossier in completed_records:
        if sample_index not in records:
            order.append(sample_index)
        records[sample_index] = dossier
    for snapshots in (
        proof_snapshots or {},
        disproof_snapshots,
        conflict_snapshots,
    ):
        for sample_index, dossier in sorted(snapshots.items()):
            if sample_index not in records:
                order.append(sample_index)
            records[sample_index] = dossier
    return [(sample_index, records[sample_index]) for sample_index in order]


def _begin_parallel_falsification_conflict_receipt_scope(
    dossier: Any,
    certificate_hashes: Set[str],
) -> None:
    receipts = getattr(
        dossier,
        "_mini_falsification_trust_boundary_conflict_certificate_hashes",
        None,
    )
    if not isinstance(receipts, set):
        receipts = set()
        setattr(
            dossier,
            "_mini_falsification_trust_boundary_conflict_certificate_hashes",
            receipts,
        )
    receipts.difference_update(certificate_hashes)


def _consume_parallel_falsification_conflict_receipts(
    dossier: Any,
    certificate_hashes: Set[str],
) -> bool:
    receipts = getattr(
        dossier,
        "_mini_falsification_trust_boundary_conflict_certificate_hashes",
        None,
    )
    if not isinstance(receipts, set):
        return False
    recorded = bool(receipts.intersection(certificate_hashes))
    receipts.difference_update(certificate_hashes)
    return recorded


def _resolve_parallel_root_disproof_terminal_state(dossier: Any) -> str:
    """Resolve a live root certificate to disproof or a fail-closed conflict."""

    if _parallel_sample_has_proof_disproof_conflict(dossier):
        if getattr(dossier, "root_disproof_certificate", None) is not None:
            dossier.root_disproof_certificate = None
        return "proof_disproof_conflict"
    if _ensure_parallel_root_disproof_terminal_state(dossier):
        return _ROOT_DISPROOF_FAILURE_KIND
    if not active_root_disproof_certificate_is_valid(
        dossier,
        reject_proof_conflicts=False,
    ):
        if getattr(dossier, "root_disproof_certificate", None) is not None:
            dossier.root_disproof_certificate = None
        if (
            str(getattr(dossier, "session_failure_reason", "") or "").strip()
            == _ROOT_DISPROOF_FAILURE_REASON
        ):
            for attr in ("session_failure_reason", "session_failure_kind"):
                if hasattr(dossier, attr):
                    try:
                        delattr(dossier, attr)
                    except Exception:
                        setattr(dossier, attr, "")
        return ""
    certificate = getattr(dossier, "root_disproof_certificate", None) or {}
    certificate_statement = str(certificate.get("statement") or "").strip()
    target_environment_hash = str(
        getattr(dossier, "current_lean_environment_hash", "") or ""
    ).strip()
    has_proof_conflict = bool(
        getattr(dossier, "final_proof", None)
        or getattr(dossier, "final_proof_hash", None)
        or _verified_helpers_conflicting_with_falsification(
            dossier,
            certificate_statement,
            target_environment_hash,
        )
    )
    if not has_proof_conflict:
        return ""
    _mark_parallel_proof_disproof_conflict(
        dossier,
        certificate_hashes=(
            str(certificate.get("certificate_hash") or "").strip(),
        ),
    )
    return "proof_disproof_conflict"


def _parallel_failure_score(dossier: Any) -> Tuple[int, int, int, int, int, int]:
    record = getattr(dossier, "proof_state_record", None)
    if not isinstance(record, dict):
        record = {}
    metrics = record.get("metrics")
    if not isinstance(metrics, dict):
        metrics = {}
    return (
        (
            3
            if _parallel_sample_has_proof_disproof_conflict(dossier)
            else (
                2
                if _parallel_sample_has_root_disproof(dossier)
                else 1 if bool(getattr(dossier, "final_proof_hash", None)) else 0
            )
        ),
        _safe_int(record.get("proved_nodes")),
        _safe_int(metrics.get("proved_child_nodes")),
        len(getattr(dossier, "verified_helpers", {}) or {}),
        len(getattr(dossier, "attempts", []) or []),
        -_safe_int(record.get("open_nodes"))
        - _safe_int(metrics.get("failed_child_nodes")),
    )


def _parallel_failure_sample_score(
    dossier: Any,
) -> Tuple[int, int, int, int, int, int]:
    """Compatibility alias for the session factory's older helper name."""

    return _parallel_failure_score(dossier)


def _select_parallel_failure_primary(
    records: Sequence[Tuple[int, Any]],
) -> Tuple[int, Optional[Any], Tuple[int, int, int, int, int, int]]:
    if not records:
        return -1, None, (0, 0, 0, 0, 0, 0)
    selected_index, selected_dossier = max(
        records,
        key=lambda item: (_parallel_failure_score(item[1]), -int(item[0])),
    )
    return selected_index, selected_dossier, _parallel_failure_score(selected_dossier)


def _increment_dossier_metric(dossier: Optional[ProofDossier], key: str, amount: int = 1) -> None:
    if dossier is None:
        return
    increment = getattr(dossier, "increment_tool_metric", None)
    if callable(increment):
        try:
            increment(key, amount)
            return
        except Exception:
            pass
    metrics = getattr(dossier, "tool_metrics", None)
    if isinstance(metrics, dict):
        metrics[key] = int(metrics.get(key, 0) or 0) + int(amount or 0)


def record_parallel_sample_failure(
    dossier: Optional[ProofDossier],
    *,
    sample_index: int,
    error_kind: str,
    error: str,
    stage: str,
) -> Dict[str, Any]:
    """Record bounded per-sample failure telemetry on the parent dossier."""

    entry = {
        "sample_index": int(sample_index),
        "error_kind": str(error_kind or ""),
        "error": str(error or "")[:500],
        "stage": str(stage or ""),
    }
    if dossier is not None:
        failures = getattr(dossier, "parallel_sample_failures", None)
        if not isinstance(failures, list):
            failures = []
            setattr(dossier, "parallel_sample_failures", failures)
        failures.append(dict(entry))
        del failures[:-16]
        _increment_dossier_metric(dossier, "mini_parallel_sample_failures", 1)
    return entry


def record_parallel_samples_zero_completed(
    dossier: Optional[ProofDossier],
) -> None:
    """Mark a parallel fan-out where no sample produced a mergeable dossier."""

    _increment_dossier_metric(dossier, "mini_parallel_samples_zero_completed", 1)


class _SampleAbandonGuard:
    def __init__(self) -> None:
        self.abandoned = False


class _GuardedRecorder:
    """Drop late sample telemetry after the container abandoned that task."""

    def __init__(self, recorder: Any, guard: _SampleAbandonGuard) -> None:
        self._recorder = recorder
        self._guard = guard

    def record_turn(self, record: Dict[str, Any]) -> None:
        if self._guard.abandoned or self._recorder is None:
            return
        self._recorder.record_turn(record)

    def __getattr__(self, name: str) -> Any:
        return getattr(self._recorder, name)


class _GuardedProofCache:
    """Drop late cache writes from sample tasks abandoned after drain grace."""

    def __init__(self, cache: Any, guard: _SampleAbandonGuard) -> None:
        self._cache = cache
        self._guard = guard

    @property
    def path(self) -> Any:
        return self._cache.path

    def store(self, *args: Any, **kwargs: Any) -> bool:
        if self._guard.abandoned:
            return False
        return bool(self._cache.store(*args, **kwargs))

    def begin_deadline_aware_store(self, *args: Any, **kwargs: Any) -> Any:
        """Expose reversible cache publication without bypassing abandonment."""

        if self._guard.abandoned:
            return None
        begin = getattr(self._cache, "begin_deadline_aware_store", None)
        if not callable(begin):
            return None
        receipt = begin(*args, **kwargs)
        if receipt is None:
            return None
        return _GuardedDeadlineAwareCachePublication(receipt, self._guard)

    def __getattr__(self, name: str) -> Any:
        return getattr(self._cache, name)


class _GuardedDeadlineAwareCachePublication:
    """Abort a staged cache write when a parallel sample is abandoned."""

    def __init__(self, receipt: Any, guard: _SampleAbandonGuard) -> None:
        self._receipt = receipt
        self._guard = guard

    def commit(self) -> bool:
        if self._guard.abandoned:
            self.rollback()
            return False
        return bool(self._receipt.commit())

    def finalize(self) -> bool:
        if self._guard.abandoned:
            self.rollback()
            return False
        return bool(self._receipt.finalize())

    def release(self) -> bool:
        if self._guard.abandoned:
            self.rollback()
            return False
        return bool(self._receipt.release())

    def rollback(self) -> None:
        self._receipt.rollback()


def _copy_branch_failure_observability(dst: ProofDossier, src: ProofDossier) -> None:
    """Copy failed branch telemetry without branch-local proof facts."""

    dst.attempts = copy.deepcopy(src.attempts)
    dst.tool_metrics = copy.deepcopy(getattr(src, "tool_metrics", {}))
    dst.clear_solved()
    # The prover's banked decomposition signal is observability information,
    # not branch-local proof fact, so it must flow back even when the branch
    # failed.
    propagate_proposed_helpers(dst, src)
    dst.mini_recursive_exhausted_claim_keys.update(
        set(getattr(src, "mini_recursive_exhausted_claim_keys", set()) or ())
    )
    dst.mini_recursive_claim_helper_bindings.update(
        copy.deepcopy(
            getattr(src, "mini_recursive_claim_helper_bindings", {}) or {}
        )
    )
    if hasattr(dst, "proof_state_record"):
        delattr(dst, "proof_state_record")


def merge_lean_environment_ancestry(dst: ProofDossier, src: ProofDossier) -> bool:
    """Union source Lean-environment ancestry into destination before helpers.

    Branch / sibling merges previously dropped the ancestry map that interprets
    ``verification_environment_hash`` while still importing per-node ancestor
    metadata. Union the maps (cycle-safe) so dossier and graph agree.

    Do **not** advance ``current_lean_environment_hash`` here: a parent or
    winning sample that remained in an ancestor environment must keep rejecting
    helpers verified only after a speculative extension. Current advances only
    through ``record_lean_environment`` / preamble sync on that dossier.
    """

    changed = False
    # Merge recorded environment content BEFORE any edge is considered: the
    # monotonicity check below can only refuse an inverted edge for an
    # environment whose declarations it knows.  Hash -> digest is functionally
    # deterministic, so a union cannot disagree with the destination.
    src_digests = dict(
        getattr(src, "lean_environment_content_digests", {}) or {}
    )
    if src_digests and hasattr(dst, "lean_environment_content_digests"):
        for environment, digest in src_digests.items():
            environment_hash = str(environment or "").strip()
            if not environment_hash or not digest:
                continue
            dst.lean_environment_content_digests.setdefault(
                environment_hash,
                list(digest),
            )
    omits_parent = getattr(dst, "_environment_content_omits_parent", None)
    src_map = dict(getattr(src, "lean_environment_ancestor_hashes", {}) or {})
    for child, ancestors in src_map.items():
        child_hash = str(child or "").strip()
        if not child_hash:
            continue
        existing = list(
            getattr(dst, "lean_environment_ancestor_hashes", {}).get(
                child_hash, []
            )
            or []
        )
        before = list(existing)
        for ancestor in list(ancestors or []):
            ancestor_hash = str(ancestor or "").strip()
            if (
                not ancestor_hash
                or ancestor_hash == child_hash
                or ancestor_hash in existing
            ):
                continue
            # Refuse reverse edges that would invert the lattice.
            if child_hash in dst.lean_environment_ancestors(ancestor_hash):
                continue
            # Refuse an edge whose recorded declaration sets prove the child
            # drops the ancestor's declarations.  Without this a merge could
            # re-install an edge ``record_lean_environment`` already refused.
            if callable(omits_parent) and omits_parent(
                child_hash,
                ancestor_hash,
            ):
                continue
            existing.append(ancestor_hash)
            for transitive in dst.lean_environment_ancestors(ancestor_hash):
                if (
                    transitive
                    and transitive != child_hash
                    and transitive not in existing
                    and child_hash
                    not in dst.lean_environment_ancestors(transitive)
                ):
                    existing.append(transitive)
        if existing != before:
            dst.lean_environment_ancestor_hashes[child_hash] = existing
            changed = True

    sanitize = getattr(dst, "_sanitize_lean_environment_ancestor_hashes", None)
    if callable(sanitize):
        before_map = copy.deepcopy(
            getattr(dst, "lean_environment_ancestor_hashes", {}) or {}
        )
        sanitize()
        if (
            getattr(dst, "lean_environment_ancestor_hashes", {}) or {}
        ) != before_map:
            changed = True

    refresh = getattr(dst, "_refresh_graph_nodes_for_environment", None)
    if changed and callable(refresh):
        for environment in {
            str(getattr(dst, "current_lean_environment_hash", "") or "").strip(),
            *list(getattr(dst, "lean_environment_ancestor_hashes", {}) or {}),
        }:
            if environment:
                refresh(environment)
    return changed


def _merge_verified_dossier_helpers(dst: ProofDossier, src: ProofDossier) -> int:
    """Merge only Lean-verified helper declarations from another dossier."""

    merge_lean_environment_ancestry(dst, src)
    changed = 0
    dst_tool_metrics_before = copy.deepcopy(
        getattr(dst, "tool_metrics", {}) or {}
    )
    suppressed_advisory_helpers = 0
    incoming: List[Tuple[str, Any]] = []
    incoming_items = list((getattr(src, "verified_helpers", {}) or {}).items())
    answer_safety_kwargs = {
        "opaque_mode": bool(getattr(dst, "opaque_mode", True)),
        "allow_official_answer_visibility": bool(
            getattr(dst, "allow_official_answer_visibility", False)
        ),
        "official_answer_payload_present": getattr(
            dst,
            "official_answer_payload_present",
            None,
        ),
    }
    for name, item in incoming_items:
        if is_answer_unsafe_helper_source(
            getattr(item, "source", ""),
            **answer_safety_kwargs,
        ):
            continue
        if not name:
            continue
        destination_environment = str(
            getattr(dst, "current_lean_environment_hash", "") or ""
        )
        helper_environment = str(
            getattr(item, "verification_environment_hash", "") or ""
        )
        # Production dossiers bind this receipt immediately before every
        # action and whenever imports/theory activation change. A helper
        # checked only in a speculative child environment must be re-proved in
        # the destination; blindly copying it can poison every later context.
        # Blank/blank remains compatible for old serialized dossiers and
        # narrow unit fixtures that predate receipts.
        environment_compatible = (
            dst.lean_environment_is_compatible(
                helper_environment,
                destination_environment,
            )
            if destination_environment
            else not helper_environment
        )
        if not environment_compatible:
            continue
        existing = getattr(dst, "verified_helpers", {}).get(name)
        source_hash = str(getattr(item, "source_hash", "") or "")
        existing_hash = str(getattr(existing, "source_hash", "") or "")
        if (
            existing is not None
            and existing_hash != source_hash
            and helper_source_hash_was_superseded(dst, name, source_hash)
        ):
            continue
        if helper_uses_superseded_support(dst, item):
            continue
        incoming.append((name, item))

    incoming = preflight_dependency_ordered_verified_helper_items(dst, incoming)
    for name, item in incoming:
        existing = getattr(dst, "verified_helpers", {}).get(name)
        if existing is not None and str(
            getattr(existing, "source_hash", "") or ""
        ) == str(getattr(item, "source_hash", "") or ""):
            if helper_provenance_is_trust_monotone(dst, existing, item):
                before = copy.deepcopy(existing)
                recorded = dst.record_imported_verified_helper(item)
                if recorded is not None and recorded != before:
                    changed += 1
            continue
        recorded = dst.record_imported_verified_helper(item)
        if recorded is not None:
            changed += 1
            visible = getattr(dst, "is_verified_helper_context_visible", None)
            if callable(visible) and not bool(visible(recorded)):
                suppressed_advisory_helpers += 1
                continue
    if (
        getattr(dst, "proof_graph", None) is not None
        and getattr(src, "proof_graph", None) is not None
    ):
        merge_graph_helpers = getattr(
            dst.proof_graph,
            "merge_verified_helpers_from",
            None,
        )
        if callable(merge_graph_helpers):
            merge_graph_helpers(src.proof_graph)
    if getattr(dst, "proof_graph", None) is not None:
        verified_names = set(getattr(dst, "verified_helpers", {}) or {})
        graph_helper_names = set(
            getattr(dst.proof_graph, "helper_name_to_node_id", {}) or {}
        )
        for stale_name in sorted(graph_helper_names - verified_names):
            if stale_name not in getattr(dst, "verified_helpers", {}):
                dst.proof_graph.remove_helper(stale_name)
    if hasattr(dst, "tool_metrics"):
        import_rejection_deltas = {
            key: int(value or 0) - int(dst_tool_metrics_before.get(key, 0) or 0)
            for key, value in dict(getattr(dst, "tool_metrics", {}) or {}).items()
            if str(key).startswith("mini_verified_helper_import_")
            and int(value or 0) > int(dst_tool_metrics_before.get(key, 0) or 0)
        }
        dst.tool_metrics = dst_tool_metrics_before
        for key, delta in import_rejection_deltas.items():
            dst.increment_tool_metric(key, delta)
        if suppressed_advisory_helpers:
            increment = getattr(dst, "increment_tool_metric", None)
            if callable(increment):
                increment(
                    "mini_branching_advisory_helpers_suppressed",
                    suppressed_advisory_helpers,
                )
    durable = dict(
        getattr(dst, "theory_promotion_durable_helper_fingerprints", {}) or {}
    )
    for name, fingerprint in dict(
        getattr(src, "theory_promotion_durable_helper_fingerprints", {}) or {}
    ).items():
        if name in getattr(dst, "verified_helpers", {}):
            durable[name] = copy.deepcopy(fingerprint)
    dst.theory_promotion_durable_helper_fingerprints = durable
    return changed


def _merge_dossier_helpers(
    dst: ProofDossier,
    src: ProofDossier,
    *,
    include_proposed: bool = True,
    include_accepted_stubs: bool = True,
    include_proof_ideas: bool = True,
) -> None:
    """Merge durable helper knowledge from another sample dossier."""

    _merge_proof_lineage_events(dst, src)
    if include_proof_ideas:
        _merge_branch_proof_ideas(
            dst,
            src,
            source_to_target_node_id={},
            branch_source="helper-fanin",
        )
    _merge_verified_dossier_helpers(dst, src)
    if include_proposed:
        propagate_proposed_helpers(dst, src)
    else:
        from .proof_dossier import propagate_invalidated_statements

        propagate_invalidated_statements(dst, src)
    for run in src.mini_recursive_runs:
        copied = copy.deepcopy(run)
        if copied not in dst.mini_recursive_runs:
            dst.mini_recursive_runs.append(copied)
    for target in getattr(src, "active_root_targets", []) or []:
        copied_target = copy.deepcopy(target)
        if copied_target not in getattr(dst, "active_root_targets", []):
            dst.active_root_targets.append(copied_target)
    if include_accepted_stubs:
        for stub in getattr(src, "accepted_proof_stubs", []) or []:
            copied_stub = copy.deepcopy(stub)
            if copied_stub not in getattr(dst, "accepted_proof_stubs", []):
                dst.accepted_proof_stubs.append(copied_stub)
    for key, value in dict(getattr(src, "tool_metrics", {}) or {}).items():
        if _dossier_tool_metric_is_branch_artifact(key):
            continue
        if key == "mini_falsification_trust_boundary_conflicts":
            # Conflict count is certificate-identity telemetry. The validated
            # report propagation above re-records each previously unseen hash;
            # summing the sibling's denormalized count would double-count the
            # same mathematical conflict during fan-in.
            continue
        if (
            key in MONOTONIC_LEAN_ATTEMPT_METRICS
            and callable(getattr(src, "_monotonic_tool_metric_sink", None))
        ):
            continue
        dst.tool_metrics[key] = int(dst.tool_metrics.get(key, 0) or 0) + int(
            value or 0
        )
    for record in getattr(src, "parallel_sample_proof_states", []) or []:
        copied_record = copy.deepcopy(record)
        if copied_record not in getattr(dst, "parallel_sample_proof_states", []):
            dst.parallel_sample_proof_states.append(copied_record)
    for record in getattr(src, "parallel_sample_failures", []) or []:
        copied_record = copy.deepcopy(record)
        if copied_record not in getattr(dst, "parallel_sample_failures", []):
            dst.parallel_sample_failures.append(copied_record)
    del dst.parallel_sample_failures[:-16]


def _merge_proof_lineage_events(dst: ProofDossier, src: ProofDossier) -> int:
    """Append source lineage events exactly once without transferring authority.

    The lineage ledger is observability/scheduling memory, not proof evidence.
    Fan-in therefore copies only complete schema-v1 records, never rewrites an
    existing event, and treats the durable event id as the idempotency key.
    """

    dst_events = getattr(dst, "proof_lineage_events", None)
    if not isinstance(dst_events, list):
        dst_events = []
        dst.proof_lineage_events = dst_events
    dst_ids = getattr(dst, "proof_lineage_event_ids", None)
    if not isinstance(dst_ids, set):
        dst_ids = {
            str(event.get("event_id") or "").strip()
            for event in dst_events
            if isinstance(event, Mapping)
            and str(event.get("event_id") or "").strip()
        }
        dst.proof_lineage_event_ids = dst_ids
    else:
        dst_ids.update(
            str(event.get("event_id") or "").strip()
            for event in dst_events
            if isinstance(event, Mapping)
            and str(event.get("event_id") or "").strip()
        )
    added = 0
    for raw in list(getattr(src, "proof_lineage_events", []) or []):
        if not isinstance(raw, Mapping):
            continue
        event = dict(raw)
        event_id = str(event.get("event_id") or "").strip()
        details = event.get("details")
        if not isinstance(details, Mapping):
            continue
        try:
            envelope = ProofLineageEnvelope.from_record(event.get("proof_lineage"))
        except (TypeError, ValueError):
            continue
        event_type = str(event.get("event_type") or "").strip()
        expected_event_id = lineage_event_identity(
            event_type=event_type,
            envelope=envelope,
            phase=str(event.get("phase") or "").strip(),
            verdict=str(event.get("verdict") or "").strip(),
            evidence_hash=str(event.get("evidence_hash") or "").strip(),
            occurrence_key=dst._lineage_event_occurrence_key(event_type, details),
        )
        if (
            _safe_int(event.get("schema_version")) != 1
            or not event_id
            or event_id != expected_event_id
            or event_id in dst_ids
        ):
            continue
        dst_events.append(copy.deepcopy(event))
        dst_ids.add(event_id)
        added += 1
    return added


def _dossier_tool_metric_is_branch_artifact(key: object) -> bool:
    metric_key = str(key or "")
    return metric_key.startswith(
        (
            "mini_verified_",
            "mini_hollow_",
            "mini_negative_",
            "mini_graph_hollow_",
            "mini_graph_negative_",
        )
    )


def _merge_dossier_tool_metrics(dst: ProofDossier, src: ProofDossier) -> None:
    """Merge sibling telemetry without importing sibling proof artifacts."""

    for key, value in dict(getattr(src, "tool_metrics", {}) or {}).items():
        if _dossier_tool_metric_is_branch_artifact(key):
            continue
        if (
            key in MONOTONIC_LEAN_ATTEMPT_METRICS
            and callable(getattr(src, "_monotonic_tool_metric_sink", None))
        ):
            continue
        dst.tool_metrics[key] = int(dst.tool_metrics.get(key, 0) or 0) + int(
            value or 0
        )


def _merge_dossier_observability(dst: ProofDossier, src: ProofDossier) -> None:
    """Merge non-proof telemetry from another branch."""

    _merge_dossier_tool_metrics(dst, src)
    for record in getattr(src, "parallel_sample_proof_states", []) or []:
        copied_record = copy.deepcopy(record)
        if copied_record not in getattr(dst, "parallel_sample_proof_states", []):
            dst.parallel_sample_proof_states.append(copied_record)
    for record in getattr(src, "parallel_sample_failures", []) or []:
        copied_record = copy.deepcopy(record)
        if copied_record not in getattr(dst, "parallel_sample_failures", []):
            dst.parallel_sample_failures.append(copied_record)
    del dst.parallel_sample_failures[:-16]


_STRUCTURAL_FANIN_NODE_KINDS: Set[str] = {
    "missing_obligation",
    "replan_queue_item",
    "strategy_route",
    "formal_variant",
    "proposed_claim",
    "proof_state_root",
    "proof_state_child_goal",
    "proof_state_decomposition_task",
}

# Routes and replans encode distinct mathematical strategies even when they
# target the same proposition.  Coalescing those would erase alternatives.
# These target-like kinds, in contrast, represent the same open formal work
# when Lean supplied the same receipt-bound identity in the exact environment.
_STRUCTURAL_FANIN_SEMANTIC_COALESCE_KINDS: Set[str] = {
    "missing_obligation",
    "formal_variant",
    "proposed_claim",
    "proof_state_root",
    "proof_state_child_goal",
}


def _mapped_proof_idea_graph_id(
    value: str,
    source_to_target_node_id: Mapping[str, str],
) -> str:
    clean = str(value or "").strip()
    return str(source_to_target_node_id.get(clean, clean) or "").strip()


def _mapped_proof_idea_graph_ids(
    values: Sequence[str],
    source_to_target_node_id: Mapping[str, str],
) -> Tuple[str, ...]:
    return tuple(
        mapped
        for value in values
        if (
            mapped := _mapped_proof_idea_graph_id(
                value,
                source_to_target_node_id,
            )
        )
    )


def _proof_idea_graph_ids(record: ProofIdeaRecord) -> Set[str]:
    """Collect every graph-coordinate field remapped during idea fan-in."""

    values: List[str] = list(record.consumer_ids)
    for intent in record.claim_intents:
        values.extend(
            (
                intent.claim_id,
                intent.obligation_id,
                *intent.obligation_ids,
                *intent.consumer_ids,
                *intent.dependency_claim_ids,
            )
        )
    for resolution in record.claim_resolutions:
        values.extend(
            (
                resolution.claim_id,
                resolution.evidence_id,
                *resolution.node_ids,
            )
        )
    for observation in record.observations:
        values.extend((observation.claim_id, observation.route_id))
    for transition in record.status_history:
        values.extend(
            (transition.claim_id, transition.route_id, transition.evidence_id)
        )
    return {str(value or "").strip() for value in values if str(value or "").strip()}


def _proof_idea_branch_payload_hash(src: ProofDossier) -> str:
    """Fingerprint one branch fragment without trusting run-local object ids."""

    records = []
    for idea_id, record in sorted(
        dict(getattr(src, "proof_ideas", {}) or {}).items(),
        key=lambda item: str(item[0]),
    ):
        if not isinstance(record, ProofIdeaRecord):
            continue
        records.append((str(idea_id or ""), record.to_record()))
    payload = json.dumps(
        records,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    return hashlib.sha256(payload.encode("utf-8", errors="replace")).hexdigest()


def _proof_idea_fanin_branch_id(
    src: ProofDossier,
    *,
    branch_source: str,
    branch_key: str = "",
) -> str:
    source = str(branch_source or "branch-fanin").strip() or "branch-fanin"
    key = str(branch_key or "").strip()
    return stable_identity(
        "proof-idea-fanin-branch",
        str(getattr(src, "theorem_name", "") or ""),
        source,
        key,
        _proof_idea_branch_payload_hash(src),
    )


def _branch_local_observation(
    observation: ProofIdeaObservation,
    *,
    proof_idea_id: str,
    branch_id: str,
) -> ProofIdeaObservation:
    payload = observation.to_record()
    payload.pop("observation_id", None)
    return replace(
        observation,
        observation_id=stable_identity(
            "proof-idea-branch-observation",
            proof_idea_id,
            observation.observation_id,
            branch_id,
            json.dumps(payload, sort_keys=True, ensure_ascii=True),
        ),
        branch_id=branch_id,
    )


def _branch_local_status_transition(
    transition: ProofIdeaStatusTransition,
    *,
    proof_idea_id: str,
    branch_id: str,
) -> ProofIdeaStatusTransition:
    payload = transition.to_record()
    payload.pop("transition_id", None)
    return replace(
        transition,
        transition_id=stable_identity(
            "proof-idea-branch-status",
            proof_idea_id,
            transition.transition_id,
            branch_id,
            json.dumps(payload, sort_keys=True, ensure_ascii=True),
        ),
        branch_id=branch_id,
    )


def _branch_local_claim_resolution(
    resolution: ProofIdeaClaimResolution,
    *,
    proof_idea_id: str,
    branch_id: str,
) -> ProofIdeaClaimResolution:
    """Re-identify a mapped idea-global resolution without forging branch state.

    Claim resolutions intentionally have no branch coordinate: an accepted
    proposition resolves the claim for the whole proof idea.  ``branch_id`` is
    retained as an argument for call compatibility but is not identity input.
    """

    payload = resolution.to_record()
    payload.pop("resolution_id", None)
    return replace(
        resolution,
        resolution_id=stable_identity(
            "proof-idea-fanin-resolution",
            proof_idea_id,
            resolution.resolution_id,
            json.dumps(payload, sort_keys=True, ensure_ascii=True),
        ),
    )


def _mapped_claim_resolution(
    resolution: ProofIdeaClaimResolution,
    source_to_target_node_id: Mapping[str, str],
) -> Optional[ProofIdeaClaimResolution]:
    claim_id = _mapped_proof_idea_graph_id(
        resolution.claim_id,
        source_to_target_node_id,
    )
    evidence_id = _mapped_proof_idea_graph_id(
        resolution.evidence_id,
        source_to_target_node_id,
    )
    if not claim_id or not evidence_id:
        return None
    return replace(
        resolution,
        claim_id=claim_id,
        evidence_id=evidence_id,
        node_ids=_mapped_proof_idea_graph_ids(
            resolution.node_ids,
            source_to_target_node_id,
        ),
    )


def _align_coalesced_claim_intent(
    intent: ProofIdeaClaimIntent,
    existing: ProofIdeaClaimIntent,
) -> Tuple[ProofIdeaClaimIntent, Dict[str, str]]:
    """Make one mapped branch intent merge-safe without discarding variants.

    Exact semantic graph fan-in can map two differently rendered planner claims
    onto one durable work owner.  The destination intent remains the canonical
    singleton view. Alternate renderings and planner descriptions have
    dedicated fields; their arrival is also returned for an auditable note.
    """

    conflicts: Dict[str, str] = {}
    statement_identity = intent.statement_identity
    alternative_statement_identities = set(intent.alternative_statement_identities)
    if existing.statement_identity != intent.statement_identity:
        alternative_statement_identities.add(intent.statement_identity)
        statement_identity = existing.statement_identity

    statement = intent.statement
    alternative_statements = set(intent.alternative_statements)
    if existing.statement and intent.statement and existing.statement != intent.statement:
        alternative_statements.add(intent.statement)
        statement = existing.statement

    alternative_fields = {
        "role": "role_alternatives",
        "sanity_check": "sanity_check_alternatives",
        "counting_classification": "counting_classification_alternatives",
        "obligation_id": "obligation_ids",
    }
    for field_name, alternatives_field in alternative_fields.items():
        source_value = str(getattr(intent, field_name, "") or "")
        known_values = {
            str(value or "")
            for value in (
                getattr(existing, field_name, ""),
                *tuple(getattr(existing, alternatives_field, ()) or ()),
            )
            if str(value or "")
        }
        if known_values and source_value and source_value not in known_values:
            conflicts[field_name] = source_value

    obligation_ids = tuple(
        sorted(
            set(existing.obligation_ids)
            | set(intent.obligation_ids)
        )
    )

    return (
        replace(
            intent,
            statement_identity=statement_identity,
            statement=statement,
            obligation_id="",
            obligation_ids=obligation_ids,
            alternative_statement_identities=tuple(
                alternative_statement_identities
            ),
            alternative_statements=tuple(alternative_statements),
        ),
        conflicts,
    )


def _remap_branch_proof_idea_record(
    dst: ProofDossier,
    record: ProofIdeaRecord,
    *,
    source_to_target_node_id: Mapping[str, str],
    branch_id: str,
    branch_source: str,
) -> ProofIdeaRecord:
    """Rebind a source lifecycle fragment to the graph produced by fan-in.

    Source graph ids cease to be valid when an equivalent node is coalesced or
    an equal-id conflict is remapped.  Rebinding must precede aggregate merge;
    importing first leaves durable claim/status references pointing at nodes
    that never enter the destination graph.
    """

    existing = dict(getattr(dst, "proof_ideas", {}) or {}).get(
        record.proof_idea_id
    )
    existing_observations = {
        item.observation_id: item
        for item in (
            existing.observations if isinstance(existing, ProofIdeaRecord) else ()
        )
    }
    existing_statuses = {
        item.transition_id: item
        for item in (
            existing.status_history if isinstance(existing, ProofIdeaRecord) else ()
        )
    }
    existing_resolutions = {
        item.resolution_id: item
        for item in (
            existing.claim_resolutions
            if isinstance(existing, ProofIdeaRecord)
            else ()
        )
    }
    existing_claim_intents = {
        item.claim_id: item
        for item in (
            existing.claim_intents if isinstance(existing, ProofIdeaRecord) else ()
        )
    }

    claim_intents = list(
        existing.claim_intents if isinstance(existing, ProofIdeaRecord) else ()
    )
    intent_conflicts: List[Tuple[str, Dict[str, str]]] = []
    for intent in record.claim_intents:
        if existing_claim_intents.get(intent.claim_id) == intent:
            continue
        mapped_claim_id = _mapped_proof_idea_graph_id(
            intent.claim_id,
            source_to_target_node_id,
        )
        if not mapped_claim_id:
            # Claim intents require a real destination graph owner. Keeping a
            # structurally valid record with an empty required id is impossible
            # and preserving the source spelling would forge authority.
            continue
        mapped_obligation_ids = _mapped_proof_idea_graph_ids(
            intent.obligation_ids,
            source_to_target_node_id,
        )
        mapped = replace(
            intent,
            claim_id=mapped_claim_id,
            obligation_id="",
            obligation_ids=mapped_obligation_ids,
            consumer_ids=_mapped_proof_idea_graph_ids(
                intent.consumer_ids,
                source_to_target_node_id,
            ),
            dependency_claim_ids=_mapped_proof_idea_graph_ids(
                intent.dependency_claim_ids,
                source_to_target_node_id,
            ),
        )
        existing_intent = existing_claim_intents.get(mapped.claim_id)
        if existing_intent is not None:
            mapped, conflicts = _align_coalesced_claim_intent(
                mapped,
                existing_intent,
            )
            if conflicts:
                intent_conflicts.append((mapped.claim_id, conflicts))
        claim_intents.append(mapped)
    observations = list(
        existing.observations if isinstance(existing, ProofIdeaRecord) else ()
    )
    branchless_event_remapped = False
    for observation in record.observations:
        if existing_observations.get(observation.observation_id) == observation:
            continue
        mapped = replace(
            observation,
            claim_id=_mapped_proof_idea_graph_id(
                observation.claim_id, source_to_target_node_id
            ),
            route_id=_mapped_proof_idea_graph_id(
                observation.route_id, source_to_target_node_id
            ),
        )
        existing_observation = existing_observations.get(mapped.observation_id)
        if existing_observation != mapped:
            original_branch_id = str(mapped.branch_id or "").strip()
            cloned_branch_collision = bool(
                existing_observation is not None
                and original_branch_id
                and str(existing_observation.branch_id or "").strip()
                == original_branch_id
            )
            event_branch_id = (
                branch_id
                if cloned_branch_collision
                else original_branch_id or branch_id
            )
            branchless_event_remapped = bool(
                branchless_event_remapped
                or not original_branch_id
                or cloned_branch_collision
            )
            mapped = _branch_local_observation(
                mapped,
                proof_idea_id=record.proof_idea_id,
                branch_id=event_branch_id,
            )
        observations.append(mapped)
    for claim_id, conflicts in intent_conflicts:
        conflict_payload = json.dumps(
            conflicts,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
        observations.append(
            ProofIdeaObservation.create(
                proof_idea_id=record.proof_idea_id,
                occurrence_key=(
                    f"coalesced-claim-intent:{branch_id}:{claim_id}:"
                    f"{conflict_payload}"
                ),
                kind="note",
                summary=(
                    "Semantic fan-in retained the destination claim intent and "
                    f"recorded branch-local singleton variants: {conflict_payload}"
                ),
                claim_id=claim_id,
                source_trigger=str(branch_source or "branch-fanin"),
                branch_id=branch_id,
            )
        )
    resolutions = list(
        existing.claim_resolutions if isinstance(existing, ProofIdeaRecord) else ()
    )
    for resolution in record.claim_resolutions:
        if existing_resolutions.get(resolution.resolution_id) == resolution:
            continue
        mapped = _mapped_claim_resolution(
            resolution,
            source_to_target_node_id,
        )
        if mapped is None:
            # Certified resolutions require both a destination claim and its
            # destination evidence node. A partial remap is not a certificate.
            continue
        if existing_resolutions.get(mapped.resolution_id) != mapped:
            mapped = _branch_local_claim_resolution(
                mapped,
                proof_idea_id=record.proof_idea_id,
                branch_id=branch_id,
            )
        resolutions.append(mapped)
    statuses = list(
        existing.status_history if isinstance(existing, ProofIdeaRecord) else ()
    )
    for transition in record.status_history:
        if existing_statuses.get(transition.transition_id) == transition:
            continue
        mapped = replace(
            transition,
            claim_id=_mapped_proof_idea_graph_id(
                transition.claim_id, source_to_target_node_id
            ),
            route_id=_mapped_proof_idea_graph_id(
                transition.route_id, source_to_target_node_id
            ),
            evidence_id=_mapped_proof_idea_graph_id(
                transition.evidence_id, source_to_target_node_id
            ),
        )
        existing_status = existing_statuses.get(mapped.transition_id)
        if existing_status != mapped:
            original_branch_id = str(mapped.branch_id or "").strip()
            cloned_branch_collision = bool(
                existing_status is not None
                and original_branch_id
                and str(existing_status.branch_id or "").strip()
                == original_branch_id
            )
            event_branch_id = (
                branch_id
                if cloned_branch_collision
                else original_branch_id or branch_id
            )
            branchless_event_remapped = bool(
                branchless_event_remapped
                or not original_branch_id
                or cloned_branch_collision
            )
            mapped = _branch_local_status_transition(
                mapped,
                proof_idea_id=record.proof_idea_id,
                branch_id=event_branch_id,
            )
        statuses.append(mapped)

    # ``observations``/``status_history`` above are seeded from the DESTINATION
    # record and then extended with mapped source events, so the merged
    # provenance must cover both sides. Taking only the source's provenance
    # dropped every destination branch, and ProofIdeaRecord rejects an event
    # whose branch is not declared ("observations/statuses reference unknown
    # branches"). Union them the same way consumer_ids merges existing + delta.
    existing_branches = tuple(
        existing.branch_provenance if isinstance(existing, ProofIdeaRecord) else ()
    )
    # Drop only entries the destination already declares IDENTICALLY. A same
    # branch_id carrying different ancestry is a genuine provenance conflict:
    # let it reach _merge_keyed_records, which raises, rather than silently
    # resolving destination-wins and discarding the source's parent_branch_id.
    existing_branch_records = set(existing_branches)
    branches = existing_branches + tuple(
        item
        for item in record.branch_provenance
        if item not in existing_branch_records
    )
    if (
        (branchless_event_remapped or intent_conflicts)
        and branch_id not in {item.branch_id for item in branches}
    ):
        branches += (
            ProofIdeaBranchProvenance(
                branch_id=branch_id,
                source=str(branch_source or "branch-fanin"),
            ),
        )
    existing_consumer_ids = tuple(
        existing.consumer_ids if isinstance(existing, ProofIdeaRecord) else ()
    )
    child_consumer_delta = tuple(
        value for value in record.consumer_ids if value not in existing_consumer_ids
    )
    return replace(
        record,
        consumer_ids=existing_consumer_ids
        + _mapped_proof_idea_graph_ids(
            child_consumer_delta,
            source_to_target_node_id,
        ),
        claim_intents=tuple(claim_intents),
        claim_resolutions=tuple(resolutions),
        observations=tuple(observations),
        status_history=tuple(statuses),
        branch_provenance=branches,
    )


def _merge_branch_proof_ideas(
    dst: ProofDossier,
    src: ProofDossier,
    *,
    source_to_target_node_id: Mapping[str, str],
    branch_source: str,
    branch_key: str = "",
    proof_idea_ids: Optional[Set[str]] = None,
) -> int:
    """Merge one branch's descriptive lifecycle after graph-id rebinding."""

    fallback_branch_id = _proof_idea_fanin_branch_id(
        src,
        branch_source=branch_source,
        branch_key=branch_key,
    )
    changed = 0
    for record in dict(getattr(src, "proof_ideas", {}) or {}).values():
        if not isinstance(record, ProofIdeaRecord):
            continue
        if proof_idea_ids is not None and record.proof_idea_id not in proof_idea_ids:
            continue
        source_branch_ids = sorted(
            {
                item.branch_id
                for item in record.branch_provenance
                if str(item.branch_id or "").strip()
            }
        )
        existing = dst.proof_ideas.get(record.proof_idea_id)
        existing_branch_ids = {
            item.branch_id
            for item in (
                existing.branch_provenance
                if isinstance(existing, ProofIdeaRecord)
                else ()
            )
        }
        unique_source_branch_replayed = False
        if (
            len(source_branch_ids) == 1
            and isinstance(existing, ProofIdeaRecord)
        ):
            source_branch_id = source_branch_ids[0]
            existing_observation_ids = {
                item.observation_id for item in existing.observations
            }
            existing_status_ids = {
                item.transition_id for item in existing.status_history
            }
            unique_source_branch_replayed = bool(
                any(
                    _branch_local_observation(
                        replace(
                            observation,
                            claim_id=_mapped_proof_idea_graph_id(
                                observation.claim_id,
                                source_to_target_node_id,
                            ),
                            route_id=_mapped_proof_idea_graph_id(
                                observation.route_id,
                                source_to_target_node_id,
                            ),
                        ),
                        proof_idea_id=record.proof_idea_id,
                        branch_id=source_branch_id,
                    ).observation_id
                    in existing_observation_ids
                    for observation in record.observations
                )
                or any(
                    _branch_local_status_transition(
                        replace(
                            transition,
                            claim_id=_mapped_proof_idea_graph_id(
                                transition.claim_id,
                                source_to_target_node_id,
                            ),
                            route_id=_mapped_proof_idea_graph_id(
                                transition.route_id,
                                source_to_target_node_id,
                            ),
                            evidence_id=_mapped_proof_idea_graph_id(
                                transition.evidence_id,
                                source_to_target_node_id,
                            ),
                        ),
                        proof_idea_id=record.proof_idea_id,
                        branch_id=source_branch_id,
                    ).transition_id
                    in existing_status_ids
                    for transition in record.status_history
                )
            )
        # A unique source branch is the exact owner of branchless child events.
        # Multi-branch aggregates use an explicit fan-in branch only for those
        # branchless events; existing branch-local events keep their branches.
        branch_id = (
            source_branch_ids[0]
            if len(source_branch_ids) == 1
            and (
                source_branch_ids[0] not in existing_branch_ids
                or unique_source_branch_replayed
            )
            else fallback_branch_id
        )
        remapped = _remap_branch_proof_idea_record(
            dst,
            record,
            source_to_target_node_id=source_to_target_node_id,
            branch_id=branch_id,
            branch_source=branch_source,
        )
        before = dst.proof_ideas.get(remapped.proof_idea_id)
        if isinstance(before, ProofIdeaRecord):
            # A losing/child branch contributes alternatives and lifecycle
            # evidence; it must not replace the destination's active claim
            # formulation.  ``ProofIdeaClaimIntent.merged`` intentionally
            # treats its right operand as the newer primary for ordinary
            # same-dossier updates, so pre-merge in the opposite direction at
            # this explicit fan-in boundary to retain destination authority.
            remapped = remapped.merged(before)
        after = dst.upsert_proof_idea(remapped)
        changed += int(before != after)
    return changed


def seed_relevant_proof_ideas_for_child(
    dst: ProofDossier,
    src: ProofDossier,
    *,
    lineage_sources: Sequence[Mapping[str, Any]] = (),
    branch_source: str,
    branch_key: str,
) -> Tuple[Set[str], str]:
    """Seed only the parent strategy that owns one focused child target."""

    selected_envelope = ProofLineageEnvelope()
    selected_idea_ids: Set[str] = set()
    primary_envelopes: List[ProofLineageEnvelope] = []
    for raw in lineage_sources:
        if not isinstance(raw, Mapping):
            continue
        raw_primary = raw.get("primary_consumer_binding")
        if not isinstance(raw_primary, Mapping):
            raw_primary = raw.get("primary_cognition_scope")
        if isinstance(raw_primary, Mapping):
            try:
                primary = ProofLineageEnvelope.from_metadata(raw_primary)
            except (TypeError, ValueError):
                primary = ProofLineageEnvelope()
            if primary.proof_idea_id in getattr(src, "proof_ideas", {}):
                primary_envelopes.append(primary)
        try:
            envelope = ProofLineageEnvelope.from_metadata(raw)
        except (TypeError, ValueError):
            continue
        if envelope.proof_idea_id in getattr(src, "proof_ideas", {}):
            selected_idea_ids.add(envelope.proof_idea_id)
            if not selected_envelope.proof_idea_id:
                selected_envelope = envelope
    primary_idea_ids = {
        envelope.proof_idea_id for envelope in primary_envelopes
    }
    if len(primary_idea_ids) == 1:
        selected_idea_ids = set(primary_idea_ids)
        selected_envelope = next(
            envelope
            for envelope in primary_envelopes
            if envelope.proof_idea_id in selected_idea_ids
        )
    elif len(primary_idea_ids) > 1 or len(selected_idea_ids) > 1:
        return set(), ""
    if not selected_idea_ids:
        return set(), ""

    branch_id = _proof_idea_fanin_branch_id(
        src,
        branch_source=branch_source,
        branch_key=branch_key,
    )
    seeded: Dict[str, ProofIdeaRecord] = {}
    for idea_id in sorted(selected_idea_ids):
        record = src.proof_ideas.get(idea_id)
        if not isinstance(record, ProofIdeaRecord):
            continue
        branches = tuple(record.branch_provenance)
        if branch_id not in {item.branch_id for item in branches}:
            branches += (
                ProofIdeaBranchProvenance(
                    branch_id=branch_id,
                    source=str(branch_source or "child-session"),
                ),
            )
        seeded[idea_id] = replace(record, branch_provenance=branches)
    dst.proof_ideas = copy.deepcopy(seeded)
    if not seeded:
        return set(), ""

    if selected_envelope.proof_idea_id not in seeded:
        selected_envelope = ProofLineageEnvelope(
            proof_idea_id=next(iter(sorted(seeded)))
        )
    root_graph = getattr(dst, "proof_graph", None)
    root = (
        getattr(root_graph, "nodes", {}).get(getattr(root_graph, "root_node_id", ""))
        if root_graph is not None
        else None
    )
    if root is not None:
        metadata = dict(getattr(root, "metadata", {}) or {})
        metadata.update(selected_envelope.merged_metadata(metadata))
        metadata["branch_id"] = branch_id
        root.metadata = metadata
    return set(seeded), branch_id


def selected_child_proof_idea_packet(
    dossier: ProofDossier,
    selected_work: Mapping[str, Any],
    *,
    graph_node: Any = None,
    session: Any = None,
) -> Dict[str, Any]:
    """Bind graph-selected child work to one exact cognition branch.

    Scheduler-produced consumer bindings are authoritative and pass through
    unchanged.  Older graph work may carry lineage only on its owning node;
    upgrade that record only when the node identifies one proof idea and its
    branch is explicit or uniquely determined.  Multiple possible branches
    fail closed instead of exposing sibling attempts to the child.
    """

    packet = copy.deepcopy(dict(selected_work or {}))
    incoming_had_explicit_cognition = selected_work_has_explicit_cognition(packet)
    raw_bindings = [
        dict(item)
        for item in list(packet.get("consumer_bindings") or [])
        if isinstance(item, Mapping)
    ]

    def validated_binding(raw: Mapping[str, Any]) -> Dict[str, Any]:
        binding = dict(raw)
        try:
            binding_lineage = ProofLineageEnvelope.from_metadata(binding)
        except (TypeError, ValueError) as exc:
            raise ValueError("selected child cognition binding is malformed") from exc
        bound_idea = dict(getattr(dossier, "proof_ideas", {}) or {}).get(
            binding_lineage.proof_idea_id
        )
        if not isinstance(bound_idea, ProofIdeaRecord):
            raise ValueError("selected child cognition binding is stale")
        known_branches = {
            str(item.branch_id or "").strip()
            for item in bound_idea.branch_provenance
            if str(item.branch_id or "").strip()
        }
        binding_branch = str(binding.get("branch_id") or "").strip()
        explicitly_global = bool(
            str(binding.get("branch_scope") or "").strip() == "global"
            or binding.get("global_lifecycle_scope") is True
        )
        if not binding_branch and not explicitly_global:
            if len(known_branches) != 1:
                raise ValueError(
                    "graph-selected child cognition has no unique branch binding"
                )
            binding_branch = next(iter(known_branches))
            binding["branch_id"] = binding_branch
        if binding_branch and binding_branch not in known_branches:
            raise ValueError(
                "selected child cognition binding names a stale branch"
            )
        bound_graph_node_id = str(binding.get("graph_node_id") or "").strip()
        selected_graph_node_id = str(
            getattr(graph_node, "node_id", "") or ""
        ).strip()
        if (
            bound_graph_node_id
            and selected_graph_node_id
            and bound_graph_node_id != selected_graph_node_id
        ):
            raise ValueError(
                "selected child cognition binding names a different graph node"
            )
        return binding

    raw_primary = packet.get("primary_consumer_binding")
    if not isinstance(raw_primary, Mapping):
        raw_primary = packet.get("primary_cognition_scope")
    if isinstance(raw_primary, Mapping):
        primary = validated_binding(raw_primary)
        primary_id = str(primary.get("consumer_binding_id") or "").strip()
        if raw_bindings:
            primary_indexes = [
                index
                for index, candidate in enumerate(raw_bindings)
                if (
                    primary_id
                    and str(candidate.get("consumer_binding_id") or "").strip()
                    == primary_id
                )
                or candidate == dict(raw_primary)
            ]
            if len(primary_indexes) != 1:
                raise ValueError(
                    "selected child primary cognition is not a unique consumer"
                )
            raw_bindings[primary_indexes[0]] = primary
            packet["consumer_bindings"] = raw_bindings
        packet["primary_consumer_binding"] = primary
        return packet
    if raw_bindings:
        validated = [validated_binding(item) for item in raw_bindings]
        if len(validated) != 1:
            raise ValueError(
                "selected child cognition has multiple consumers and no primary"
            )
        packet["consumer_bindings"] = validated
        packet["primary_consumer_binding"] = validated[0]
        return packet
    metadata = dict(getattr(graph_node, "metadata", {}) or {})
    try:
        lineage = ProofLineageEnvelope.from_metadata(metadata)
    except (TypeError, ValueError):
        lineage = ProofLineageEnvelope()
    if not lineage.proof_idea_id:
        return packet
    idea = dict(getattr(dossier, "proof_ideas", {}) or {}).get(
        lineage.proof_idea_id
    )
    if not isinstance(idea, ProofIdeaRecord):
        return packet
    branch_id = str(metadata.get("branch_id") or "").strip()
    if not branch_id:
        branch_ids = {
            str(item.branch_id or "").strip()
            for item in idea.branch_provenance
            if str(item.branch_id or "").strip()
        }
        if len(branch_ids) != 1:
            raise ValueError(
                "graph-selected child cognition has no unique branch binding"
            )
        branch_id = next(iter(branch_ids))
    graph_node_id = str(getattr(graph_node, "node_id", "") or "").strip()
    binding = {
        "consumer_binding_id": stable_identity(
            "selected-child-consumer-binding",
            lineage.proof_idea_id,
            lineage.route_id,
            lineage.claim_id,
            branch_id,
            graph_node_id,
        ),
        "proof_lineage": lineage.to_record(),
        "branch_id": branch_id,
        "reason": "exact graph-selected child cognition",
        "graph_node_id": graph_node_id,
    }
    packet["consumer_bindings"] = [binding]
    packet["primary_consumer_binding"] = binding
    execution_scope = dict(packet.get("execution_scope") or {})
    execution_scope.setdefault(
        "target_statement",
        str(
            packet.get("exact_target_statement")
            or packet.get("target_statement")
            or getattr(graph_node, "statement", "")
            or ""
        ),
    )
    execution_scope.setdefault(
        "environment_hash",
        str(getattr(dossier, "current_lean_environment_hash", "") or ""),
    )
    execution_scope.setdefault(
        "graph_revision",
        str(dossier.proof_idea_graph_revision() or ""),
    )
    packet["execution_scope"] = execution_scope
    if (
        not incoming_had_explicit_cognition
        and selected_work_has_explicit_cognition(packet)
    ):
        # Scheduler stamping necessarily precedes this legacy lineage upgrade.
        # The new binding changes scoped graph identity, so preserve the
        # upgrader's compatibility contract by binding the upgraded packet to
        # the current graph once. Explicitly cognition-bound packets return
        # through the branches above and are never restamped here.
        stamper = getattr(session, "_stamp_selected_work_graph_revision", None)
        if callable(stamper):
            try:
                packet = stamper(packet)
            except (TypeError, ValueError, AttributeError) as exc:
                raise ValueError(
                    "selected child cognition could not be bound to the current graph"
                ) from exc
    return packet


def merge_relevant_child_proof_ideas(
    dst: ProofDossier,
    src: ProofDossier,
    *,
    proof_idea_ids: Set[str],
    source_to_target_node_id: Optional[Mapping[str, str]] = None,
    branch_source: str,
    branch_key: str,
) -> int:
    """Fold focused child lifecycle deltas into their parent strategy.

    Child graph ids are authoritative only after they have landed in the
    destination graph.  Explicitly map every unlanded child-owned id to the
    empty sentinel so the ordinary "preserve inherited parent id" fallback
    cannot alias an unrelated parent node with the same spelling.
    """

    if not proof_idea_ids:
        return 0
    supplied_remap = dict(source_to_target_node_id or {})
    src_graph = getattr(src, "proof_graph", None)
    dst_graph = getattr(dst, "proof_graph", None)
    src_nodes = getattr(src_graph, "nodes", {}) or {}
    dst_nodes = getattr(dst_graph, "nodes", {}) or {}
    child_owned_ids = {
        str(node_id or "").strip()
        for node_id in src_nodes
        if str(node_id or "").strip()
    }
    dst_node_ids = {
        str(node_id or "").strip()
        for node_id in dst_nodes
        if str(node_id or "").strip()
    }
    source_records = [
        record
        for idea_id, record in dict(getattr(src, "proof_ideas", {}) or {}).items()
        if idea_id in proof_idea_ids and isinstance(record, ProofIdeaRecord)
    ]
    landed_remap = {
        source_id: target_id
        for raw_source_id, raw_target_id in supplied_remap.items()
        if (source_id := str(raw_source_id or "").strip())
        and (target_id := str(raw_target_id or "").strip()) in dst_node_ids
    }
    changed = 0
    for record in source_records:
        source_reference_ids = _proof_idea_graph_ids(record)
        existing = dict(getattr(dst, "proof_ideas", {}) or {}).get(
            record.proof_idea_id
        )
        inherited_reference_ids = (
            _proof_idea_graph_ids(existing)
            if isinstance(existing, ProofIdeaRecord)
            else set()
        )
        safe_remap = {
            node_id: "" for node_id in child_owned_ids | source_reference_ids
        }
        # Inheritance is scoped to this exact proof idea. A reference from a
        # sibling idea cannot authorize a same-spelled child event here.
        safe_remap.update(
            {
                node_id: node_id
                for node_id in (
                    (source_reference_ids & inherited_reference_ids)
                    - child_owned_ids
                )
            }
        )
        # Successfully landed structural mappings take precedence over
        # inherited spellings when a child-local node collided with a parent.
        safe_remap.update(landed_remap)
        changed += _merge_branch_proof_ideas(
            dst,
            src,
            source_to_target_node_id=safe_remap,
            branch_source=branch_source,
            branch_key=branch_key,
            proof_idea_ids={record.proof_idea_id},
        )
    return changed

def _structural_fanin_node_is_terminal_or_tombstoned(graph: Any, node: Any) -> bool:
    if node is None:
        return True
    status = str(getattr(node, "status", "") or "")
    if status in {"failed", "invalidated", "obsolete", "rejected", "superseded"}:
        return True
    is_tombstone = getattr(graph, "is_superseded_tombstone", None)
    if callable(is_tombstone) and bool(is_tombstone(node)):
        return True
    metadata = getattr(node, "metadata", {}) or {}
    return any(
        bool(metadata.get(flag))
        for flag in (
            "proposal_superseded",
            "proposal_invalidated",
            "route_retired",
            "route_dependency_contradicted",
            "retired_by_repeated_repair_failure",
        )
    )


def _structural_fanin_node_is_live_open(graph: Any, node: Any) -> bool:
    if node is None or str(getattr(node, "status", "") or "") not in {
        "open",
        "blocked",
    }:
        return False
    return not _structural_fanin_node_is_terminal_or_tombstoned(graph, node)


def _structural_fanin_semantic_key(
    graph: Any,
    node: Any,
    *,
    exact_environment_hash: str,
) -> Optional[Tuple[Any, ...]]:
    """Return a receipt-bound key that cannot cross kind/environment borders."""

    kind = str(getattr(node, "kind", "") or "")
    if kind not in _STRUCTURAL_FANIN_SEMANTIC_COALESCE_KINDS:
        return None
    return graph_node_semantic_work_key(
        graph,
        node,
        exact_environment_hash=exact_environment_hash,
        allow_exact_surface_identity=False,
    )


def _merge_parallel_sample_structural_progress(
    dst: ProofDossier,
    src: ProofDossier,
    *,
    sample_index: int = -1,
    remap_conflicts: bool = False,
    branch_provenance: str = "",
) -> Dict[str, int]:
    """Import safe open graph/frontier work from a nonselected sample.

    Parallel samples are isolated branches. Verified helpers already have a
    durable merge path; this function preserves *structural search work* from
    losing failed samples without overwriting the selected branch's graph. Only
    open/blocked non-helper work with non-conflicting node ids is imported.
    """

    _merge_proof_lineage_events(dst, src)

    dst_graph = getattr(dst, "proof_graph", None)
    src_graph = getattr(src, "proof_graph", None)
    if dst_graph is None or src_graph is None:
        _merge_branch_proof_ideas(
            dst,
            src,
            source_to_target_node_id={},
            branch_source=(
                str(branch_provenance or "").strip()
                or f"parallel-sample:{int(sample_index or 0)}"
            ),
            branch_key=str(sample_index),
        )
        return {
            "nodes_imported": 0,
            "nodes_coalesced": 0,
            "edges_imported": 0,
            "branch_frames_imported": 0,
            "conflicts": 0,
        }
    dst_nodes = getattr(dst_graph, "nodes", None)
    if not isinstance(dst_nodes, dict):
        dst_nodes = {}
        setattr(dst_graph, "nodes", dst_nodes)
    src_nodes = getattr(src_graph, "nodes", None)
    if not isinstance(src_nodes, dict):
        src_nodes = {}
    imported_node_ids: Set[str] = set()
    coalesced_source_node_ids: Set[str] = set()
    structural_source_node_ids: Set[str] = set()
    source_to_target_node_id: Dict[str, str] = {}
    conflicts = 0
    dst_environment_hash = str(
        getattr(dst, "current_lean_environment_hash", "") or ""
    ).strip()
    src_environment_hash = str(
        getattr(src, "current_lean_environment_hash", "") or ""
    ).strip()
    exact_environment_hash = (
        dst_environment_hash
        if dst_environment_hash
        and dst_environment_hash == src_environment_hash
        else ""
    )
    semantic_targets: Dict[Tuple[Any, ...], str] = {}
    if exact_environment_hash:
        for target_id in sorted(dst_nodes, key=str):
            target_node = dst_nodes[target_id]
            semantic_key = _structural_fanin_semantic_key(
                dst_graph,
                target_node,
                exact_environment_hash=exact_environment_hash,
            )
            if semantic_key is not None:
                semantic_targets.setdefault(semantic_key, str(target_id or ""))
    for node_id in sorted(src_nodes, key=str):
        node = src_nodes[node_id]
        clean_id = str(node_id or "").strip()
        if not clean_id:
            continue
        node_kind = str(getattr(node, "kind", "") or "")
        eligible_structural_node = bool(
            node_kind in _STRUCTURAL_FANIN_NODE_KINDS
            and _structural_fanin_node_is_live_open(src_graph, node)
        )
        if not eligible_structural_node and clean_id not in dst_nodes:
            continue
        semantic_key = (
            _structural_fanin_semantic_key(
                src_graph,
                node,
                exact_environment_hash=exact_environment_hash,
            )
            if eligible_structural_node
            else None
        )
        semantic_target_id = (
            semantic_targets.get(semantic_key) if semantic_key is not None else None
        )
        if semantic_target_id and semantic_target_id != clean_id:
            source_to_target_node_id[clean_id] = semantic_target_id
            coalesced_source_node_ids.add(clean_id)
            structural_source_node_ids.add(clean_id)
            continue
        if semantic_target_id and clean_id in dst_nodes:
            source_to_target_node_id[clean_id] = clean_id
            structural_source_node_ids.add(clean_id)
            continue
        if clean_id in dst_nodes:
            existing = dst_nodes.get(clean_id)
            existing_is_tombstoned_or_terminal = (
                _structural_fanin_node_is_terminal_or_tombstoned(
                    dst_graph, existing
                )
            )
            conflicting = (
                getattr(existing, "kind", "") != getattr(node, "kind", "")
                or str(getattr(existing, "statement", "") or "")
                != str(getattr(node, "statement", "") or "")
                or (eligible_structural_node and existing_is_tombstoned_or_terminal)
            )
            if conflicting:
                conflicts += 1
                # A live source must never be swallowed by an equal-id durable
                # tombstone. Preserve the tombstone and deterministically
                # remap the live work even for ordinary parallel fan-in.
                force_live_remap = bool(
                    eligible_structural_node
                    and existing_is_tombstoned_or_terminal
                )
                if not remap_conflicts and not force_live_remap:
                    continue
                remap_provenance = str(branch_provenance or "").strip() or (
                    f"parallel-sample:{int(sample_index or 0)}"
                )
                suffix = hashlib.sha256(
                    (
                        f"{clean_id}\n{getattr(node, 'kind', '')}\n"
                        f"{getattr(node, 'statement', '')}\n{remap_provenance}"
                    ).encode("utf-8", errors="replace")
                ).hexdigest()[:12]
                target_id = f"{clean_id}__branch_{suffix}"
                collision_index = 1
                while target_id in dst_nodes:
                    target_id = (
                        f"{clean_id}__branch_{suffix}_{collision_index}"
                    )
                    collision_index += 1
            else:
                source_to_target_node_id[clean_id] = clean_id
                if eligible_structural_node:
                    structural_source_node_ids.add(clean_id)
                continue
        else:
            target_id = clean_id
        if not eligible_structural_node:
            continue
        copied = copy.deepcopy(node)
        metadata = dict(getattr(copied, "metadata", {}) or {})
        metadata["parallel_sample_imported"] = True
        metadata["parallel_sample_index"] = int(sample_index or 0)
        if target_id != clean_id:
            metadata["parallel_sample_original_node_id"] = clean_id
            metadata["persistent_branch_original_node_id"] = clean_id
            metadata["persistent_branch_source"] = str(branch_provenance or "")
        setattr(copied, "metadata", metadata)
        setattr(copied, "node_id", target_id)
        dst_nodes[target_id] = copied
        source_to_target_node_id[clean_id] = target_id
        imported_node_ids.add(target_id)
        structural_source_node_ids.add(clean_id)
        if semantic_key is not None:
            semantic_targets.setdefault(semantic_key, target_id)

    proof_idea_branch_source = str(branch_provenance or "").strip() or (
        f"parallel-sample:{int(sample_index or 0)}"
    )
    _merge_branch_proof_ideas(
        dst,
        src,
        source_to_target_node_id=source_to_target_node_id,
        branch_source=proof_idea_branch_source,
        branch_key=str(sample_index),
    )

    dst_edges = getattr(dst_graph, "edges", None)
    if not isinstance(dst_edges, list):
        dst_edges = []
        setattr(dst_graph, "edges", dst_edges)
    existing_edges = {
        (
            str(getattr(edge, "source", "") or ""),
            str(getattr(edge, "target", "") or ""),
            str(getattr(edge, "kind", "") or ""),
        )
        for edge in list(dst_edges)
    }
    edges_imported = 0
    for edge in list(getattr(src_graph, "edges", []) or []):
        source_raw = str(getattr(edge, "source", "") or "")
        target_raw = str(getattr(edge, "target", "") or "")
        source = source_to_target_node_id.get(source_raw, source_raw)
        target = source_to_target_node_id.get(target_raw, target_raw)
        kind = str(getattr(edge, "kind", "") or "")
        if source not in dst_nodes or target not in dst_nodes:
            continue
        if (
            source_raw not in structural_source_node_ids
            and target_raw not in structural_source_node_ids
        ):
            continue
        if _structural_fanin_node_is_terminal_or_tombstoned(
            dst_graph, dst_nodes.get(source)
        ):
            continue
        if _structural_fanin_node_is_terminal_or_tombstoned(
            dst_graph, dst_nodes.get(target)
        ):
            continue
        key = (source, target, kind)
        if key in existing_edges:
            continue
        copied_edge = copy.deepcopy(edge)
        setattr(copied_edge, "source", source)
        setattr(copied_edge, "target", target)
        dst_edges.append(copied_edge)
        existing_edges.add(key)
        edges_imported += 1

    branch_frames_imported = 0
    dst_frames = getattr(dst_graph, "branch_frames", None)
    if not isinstance(dst_frames, dict):
        dst_frames = {}
        setattr(dst_graph, "branch_frames", dst_frames)
    for frame_id, frame in (getattr(src_graph, "branch_frames", {}) or {}).items():
        clean_frame_id = str(frame_id or "").strip()
        if not clean_frame_id or clean_frame_id in dst_frames:
            continue
        raw_route_id = str(getattr(frame, "route_id", "") or "")
        route_id = source_to_target_node_id.get(raw_route_id, raw_route_id)
        mapped_route = dst_nodes.get(route_id)
        if (
            mapped_route is None
            or str(getattr(mapped_route, "kind", "") or "")
            != "strategy_route"
            or _structural_fanin_node_is_terminal_or_tombstoned(
                dst_graph,
                mapped_route,
            )
        ):
            continue
        copied_frame = copy.deepcopy(frame)
        setattr(copied_frame, "route_id", route_id)
        metadata = dict(getattr(copied_frame, "metadata", {}) or {})
        metadata["parallel_sample_imported"] = True
        metadata["parallel_sample_index"] = int(sample_index or 0)
        setattr(copied_frame, "metadata", metadata)
        dst_frames[clean_frame_id] = copied_frame
        branch_frames_imported += 1

    if edges_imported:
        rebuild_edges = getattr(dst_graph, "_rebuild_edge_index", None)
        if callable(rebuild_edges):
            try:
                rebuild_edges()
            except Exception:
                pass

    if (
        imported_node_ids
        or coalesced_source_node_ids
        or edges_imported
        or branch_frames_imported
        or conflicts
    ):
        increment = getattr(dst, "increment_tool_metric", None)
        if callable(increment):
            increment(
                "mini_parallel_sample_structural_nodes_imported",
                len(imported_node_ids),
            )
            increment(
                "mini_parallel_sample_structural_nodes_coalesced",
                len(coalesced_source_node_ids),
            )
            increment(
                "mini_parallel_sample_structural_edges_imported",
                edges_imported,
            )
            increment(
                "mini_parallel_sample_structural_branch_frames_imported",
                branch_frames_imported,
            )
            increment("mini_parallel_sample_structural_conflicts", conflicts)
    # Structural fan-in invents open targets outside the normal
    # accept/projection hooks. Reconcile immediately so already-certified
    # facts on the destination retire matching imported peers before the
    # next scheduler boundary can re-dispatch them.
    if imported_node_ids:
        reconcile = getattr(dst, "reconcile_verified_facts", None)
        if callable(reconcile):
            reconcile(
                trigger="parallel_structural_fanin",
                projected_node_ids=sorted(imported_node_ids),
            )
    return {
        "nodes_imported": len(imported_node_ids),
        "nodes_coalesced": len(coalesced_source_node_ids),
        "edges_imported": edges_imported,
        "branch_frames_imported": branch_frames_imported,
        "conflicts": conflicts,
    }


_RECURSIVE_CHILD_STRUCTURAL_NODE_KINDS: Set[str] = {
    "missing_obligation",
    "replan_queue_item",
    "formal_variant",
    "proposed_claim",
    "proof_state_decomposition_task",
}
_MAX_RECURSIVE_CHILD_STRUCTURAL_NODES = 64

_RECURSIVE_CHILD_NODE_REFERENCE_FIELDS: Set[str] = {
    "node_id",
    "claim_id",
    "variant_id",
    "replan_id",
    "dependency_id",
    "source_node_id",
    "claim_node_id",
    "obligation_id",
    "resolved_by_obligation_id",
    "parent_node_id",
    "route_id",
    "parent_route_id",
}
_RECURSIVE_CHILD_NODE_REFERENCE_SUFFIXES: Tuple[str, ...] = (
    "_node_id",
    "_route_id",
    "_claim_id",
    "_variant_id",
    "_obligation_id",
    "_replan_id",
    "_dependency_id",
)
_RECURSIVE_CHILD_NODE_REFERENCE_LIST_FIELDS: Set[str] = {
    "node_ids",
    "route_ids",
    "claim_ids",
    "variant_ids",
    "obligation_ids",
    "replan_ids",
    "dependency_ids",
}
_RECURSIVE_CHILD_NODE_REFERENCE_LIST_SUFFIXES: Tuple[str, ...] = (
    "_node_ids",
    "_route_ids",
    "_claim_ids",
    "_variant_ids",
    "_obligation_ids",
    "_replan_ids",
    "_dependency_ids",
)
_MAX_RECURSIVE_CHILD_METADATA_REFERENCES = 128
_MAX_RECURSIVE_CHILD_METADATA_ITEMS = 1024


def _sanitize_recursive_child_metadata_value(
    value: Any,
    source_to_target_node_id: Mapping[str, str],
    *,
    field_name: str = "",
    depth: int = 0,
    item_budget: Optional[List[int]] = None,
    seen_container_ids: Optional[Set[int]] = None,
) -> Any:
    """Recursively remap graph-local ids and drop unmapped authority."""

    if field_name == "consumer_binding_id":
        # This digest binds the original graph coordinates. Any fan-in remap
        # invalidates it; downstream typed binding construction can mint a
        # destination-local identity from the sanitized coordinates.
        return None
    if item_budget is None:
        item_budget = [_MAX_RECURSIVE_CHILD_METADATA_ITEMS]
    if seen_container_ids is None:
        seen_container_ids = set()
    if item_budget[0] <= 0:
        if isinstance(value, Mapping):
            return {}
        if isinstance(value, (list, tuple, set, frozenset)):
            return []
        return None
    item_budget[0] -= 1
    if isinstance(value, (Mapping, list, tuple, set, frozenset)):
        container_id = id(value)
        if container_id in seen_container_ids:
            return {} if isinstance(value, Mapping) else []
        # Keep this id for the whole traversal, not merely the active stack.
        # Shared aliases otherwise recreate the same subtree exponentially.
        seen_container_ids.add(container_id)
    is_reference = field_name in _RECURSIVE_CHILD_NODE_REFERENCE_FIELDS or (
        field_name.endswith(_RECURSIVE_CHILD_NODE_REFERENCE_SUFFIXES)
    )
    is_reference_list = field_name in (
        _RECURSIVE_CHILD_NODE_REFERENCE_LIST_FIELDS
    ) or field_name.endswith(_RECURSIVE_CHILD_NODE_REFERENCE_LIST_SUFFIXES)
    if is_reference_list:
        if not isinstance(value, (list, tuple, set, frozenset)):
            return None
        if isinstance(value, (set, frozenset)):
            # Sorting a hostile wide set defeats the output bound. Preserve a
            # deterministic order only when the entire set itself is bounded;
            # otherwise drop the advisory collection at this trust boundary.
            items = (
                sorted(value, key=lambda item: str(item or ""))
                if len(value) <= _MAX_RECURSIVE_CHILD_METADATA_REFERENCES
                else ()
            )
        else:
            items = islice(value, _MAX_RECURSIVE_CHILD_METADATA_REFERENCES)
        mapped = []
        for raw in items:
            reference = str(raw or "").strip()
            target = str(source_to_target_node_id.get(reference) or "").strip()
            if target:
                mapped.append(target)
        return list(dict.fromkeys(mapped)) or None
    if is_reference:
        reference = str(value or "").strip()
        return source_to_target_node_id.get(reference) or None
    if depth >= 8:
        # Never preserve an opaque container beyond the sanitization bound;
        # doing so would recreate an unchecked nested authority channel.
        if isinstance(value, Mapping):
            return {}
        if isinstance(value, (list, tuple, set, frozenset)):
            return []
        return value
    if isinstance(value, Mapping):
        sanitized: Dict[str, Any] = {}
        for raw_key, raw_value in islice(value.items(), 256):
            if not isinstance(raw_key, str):
                continue
            clean_value = _sanitize_recursive_child_metadata_value(
                raw_value,
                source_to_target_node_id,
                field_name=raw_key,
                depth=depth + 1,
                item_budget=item_budget,
                seen_container_ids=seen_container_ids,
            )
            if clean_value is not None:
                sanitized[raw_key] = clean_value
        return sanitized
    if isinstance(value, (list, tuple, set, frozenset)):
        if isinstance(value, (set, frozenset)):
            items = (
                sorted(value, key=lambda item: str(item or ""))
                if len(value) <= _MAX_RECURSIVE_CHILD_METADATA_REFERENCES
                else ()
            )
        else:
            items = islice(value, _MAX_RECURSIVE_CHILD_METADATA_REFERENCES)
        return [
            clean
            for item in items
            if (
                clean := _sanitize_recursive_child_metadata_value(
                    item,
                    source_to_target_node_id,
                    depth=depth + 1,
                    item_budget=item_budget,
                    seen_container_ids=seen_container_ids,
                )
            )
            is not None
        ]
    return value


def merge_recursive_child_structural_progress(
    dst: ProofDossier,
    src: ProofDossier,
    *,
    parent_obligation_id: str,
    branch_key: str = "",
    node_id_remap_out: Optional[MutableMapping[str, str]] = None,
) -> Dict[str, int]:
    """Import bounded live child work under one selected parent obligation.

    A recursive child's ``root`` names the selected obligation, not the parent
    theorem.  The root is therefore an anchor only: it is mapped explicitly to
    ``parent_obligation_id`` and is never copied.  Strategy routes and branch
    frames remain child-local because their assembly contracts are defined
    against the child's root authority.  Their live claim/variant/obligation
    work is retained without promoting a child route to a parent-root route.

    This is an incremental node/edge fan-in.  It does not clone, checkpoint,
    or snapshot either graph.
    """

    dst_graph = getattr(dst, "proof_graph", None)
    src_graph = getattr(src, "proof_graph", None)
    parent_id = str(parent_obligation_id or "").strip()
    if (
        dst_graph is None
        or src_graph is None
        or parent_id not in getattr(dst_graph, "nodes", {})
    ):
        return {
            "nodes_imported": 0,
            "nodes_coalesced": 0,
            "edges_imported": 0,
            "blockers_attached": 0,
            "conflicts": 0,
        }
    parent_node = dst_graph.nodes.get(parent_id)
    if _structural_fanin_node_is_terminal_or_tombstoned(
        dst_graph, parent_node
    ):
        return {
            "nodes_imported": 0,
            "nodes_coalesced": 0,
            "edges_imported": 0,
            "blockers_attached": 0,
            "conflicts": 0,
        }

    dst_environment_hash = str(
        getattr(dst, "current_lean_environment_hash", "") or ""
    ).strip()
    src_environment_hash = str(
        getattr(src, "current_lean_environment_hash", "") or ""
    ).strip()
    exact_environment_hash = (
        dst_environment_hash
        if dst_environment_hash
        and dst_environment_hash == src_environment_hash
        else ""
    )

    dst_nodes = dst_graph.nodes
    src_nodes = getattr(src_graph, "nodes", {}) or {}
    source_to_target_node_id: Dict[str, str] = {
        str(src_graph.root_node_id): parent_id
    }
    eligible_source_ids = {
        str(node_id or "").strip()
        for node_id, node in src_nodes.items()
        if str(node_id or "").strip() != str(src_graph.root_node_id)
        and str(getattr(node, "kind", "") or "")
        in _RECURSIVE_CHILD_STRUCTURAL_NODE_KINDS
        and _structural_fanin_node_is_live_open(src_graph, node)
        and not (
            str(getattr(node, "kind", "") or "")
            == "proof_state_decomposition_task"
            and str(getattr(node, "status", "") or "") != "open"
        )
    }
    semantic_targets: Dict[Tuple[Any, ...], str] = {}
    if exact_environment_hash:
        for target_id, target_node in dst_nodes.items():
            semantic_key = _structural_fanin_semantic_key(
                dst_graph,
                target_node,
                exact_environment_hash=exact_environment_hash,
            )
            if semantic_key is not None:
                semantic_targets.setdefault(semantic_key, str(target_id))

    conflicts = 0
    coalesced_source_ids: Set[str] = set()
    import_targets: Dict[str, str] = {}
    prior_import_targets: Dict[Tuple[str, str, str], str] = {}
    for target_id, target_node in dst_nodes.items():
        target_metadata = dict(getattr(target_node, "metadata", {}) or {})
        if (
            target_metadata.get("recursive_child_imported") is not True
            or not _structural_fanin_node_is_live_open(
                dst_graph, target_node
            )
            or str(
                target_metadata.get("recursive_parent_obligation_id") or ""
            )
            != parent_id
            or str(
                target_metadata.get("recursive_child_environment_hash") or ""
            )
            != src_environment_hash
        ):
            continue
        original_id = str(
            target_metadata.get("recursive_child_original_node_id") or ""
        ).strip()
        if not original_id:
            continue
        prior_import_targets.setdefault(
            (
                original_id,
                str(getattr(target_node, "kind", "") or ""),
                str(getattr(target_node, "statement", "") or ""),
            ),
            str(target_id),
        )
    provenance = f"{parent_id}:{src_environment_hash}"
    for source_id in sorted(eligible_source_ids):
        node = src_nodes[source_id]
        prior_import_target = prior_import_targets.get(
            (
                source_id,
                str(getattr(node, "kind", "") or ""),
                str(getattr(node, "statement", "") or ""),
            )
        )
        if prior_import_target:
            source_to_target_node_id[source_id] = prior_import_target
            coalesced_source_ids.add(source_id)
            continue
        semantic_key = (
            _structural_fanin_semantic_key(
                src_graph,
                node,
                exact_environment_hash=exact_environment_hash,
            )
            if exact_environment_hash
            else None
        )
        semantic_target = (
            semantic_targets.get(semantic_key)
            if semantic_key is not None
            else None
        )
        if semantic_target:
            source_to_target_node_id[source_id] = semantic_target
            coalesced_source_ids.add(source_id)
            continue
        target_id = source_id
        existing = dst_nodes.get(target_id)
        if existing is not None:
            existing_metadata = dict(getattr(existing, "metadata", {}) or {})
            same_prior_import = bool(
                getattr(existing, "kind", "") == getattr(node, "kind", "")
                and _structural_fanin_node_is_live_open(dst_graph, existing)
                and str(getattr(existing, "statement", "") or "")
                == str(getattr(node, "statement", "") or "")
                and existing_metadata.get("recursive_child_imported") is True
                and str(
                    existing_metadata.get("recursive_parent_obligation_id")
                    or ""
                )
                == parent_id
                and str(
                    existing_metadata.get("recursive_child_environment_hash")
                    or ""
                )
                == src_environment_hash
                and str(
                    existing_metadata.get("recursive_child_original_node_id")
                    or ""
                )
                == source_id
            )
            if same_prior_import:
                source_to_target_node_id[source_id] = target_id
                coalesced_source_ids.add(source_id)
                continue
            conflicts += 1
            suffix = hashlib.sha256(
                (
                    f"{source_id}\n{getattr(node, 'kind', '')}\n"
                    f"{getattr(node, 'statement', '')}\n{provenance}"
                ).encode("utf-8", errors="replace")
            ).hexdigest()[:12]
            target_id = f"{source_id}__recursive_{suffix}"
            collision_index = 1
            while target_id in dst_nodes:
                candidate = dst_nodes[target_id]
                candidate_metadata = dict(
                    getattr(candidate, "metadata", {}) or {}
                )
                if (
                    getattr(candidate, "kind", "") == getattr(node, "kind", "")
                    and _structural_fanin_node_is_live_open(
                        dst_graph, candidate
                    )
                    and str(getattr(candidate, "statement", "") or "")
                    == str(getattr(node, "statement", "") or "")
                    and candidate_metadata.get("recursive_child_imported") is True
                    and str(
                        candidate_metadata.get(
                            "recursive_parent_obligation_id"
                        )
                        or ""
                    )
                    == parent_id
                    and str(
                        candidate_metadata.get(
                            "recursive_child_environment_hash"
                        )
                        or ""
                    )
                    == src_environment_hash
                    and str(
                        candidate_metadata.get(
                            "recursive_child_original_node_id"
                        )
                        or ""
                    )
                    == source_id
                ):
                    break
                target_id = (
                    f"{source_id}__recursive_{suffix}_{collision_index}"
                )
                collision_index += 1
            if target_id in dst_nodes:
                source_to_target_node_id[source_id] = target_id
                coalesced_source_ids.add(source_id)
                continue
        if len(import_targets) >= _MAX_RECURSIVE_CHILD_STRUCTURAL_NODES:
            # The cap limits new allocations, not source inspection.  A later
            # cutpoint recognizes the first page as prior imports and spends
            # its budget on the remaining tail instead of starving it forever.
            continue
        source_to_target_node_id[source_id] = target_id
        import_targets[source_id] = target_id
        if semantic_key is not None:
            semantic_targets.setdefault(semantic_key, target_id)

    imported_node_ids: Set[str] = set()
    for source_id, target_id in import_targets.items():
        source_node = src_nodes[source_id]
        try:
            # ProofGraphNode's only mutable non-metadata fields are lists.
            # Copy those explicitly and sanitize metadata from the source so a
            # hostile wide nested value is never deep-copied before bounds are
            # applied.
            copied = copy.copy(source_node)
            copied.support_names = list(
                islice(getattr(source_node, "support_names", ()) or (), 256)
            )
        except Exception:
            continue
        # Attempts are not imported.  Their graph-local sequential ids could
        # alias unrelated parent attempts and would otherwise grow as orphan
        # per-node references outside the parent's attempt compaction policy.
        copied.attempt_ids = []
        metadata = _sanitize_recursive_child_metadata_value(
            getattr(source_node, "metadata", {}) or {},
            source_to_target_node_id,
        )
        if not isinstance(metadata, dict):
            metadata = {}
        metadata.update(
            {
                "recursive_child_imported": True,
                "recursive_parent_obligation_id": parent_id,
                "recursive_child_original_node_id": source_id,
                "recursive_child_branch_key": str(branch_key or "").strip(),
                # Open structural work may cross a monotone child theory
                # epoch, but it keeps the environment in which its statement
                # was created.  This is provenance only: no proof or helper
                # authority is imported by this path.
                "recursive_child_environment_hash": src_environment_hash,
            }
        )
        copied.node_id = target_id
        if str(getattr(copied, "kind", "") or "").startswith("proof_state_"):
            # A child proof-state record owns process-local ids and verifier
            # authority.  Carrying its nested projection through a graph-id
            # remap can alias and overwrite parent scheduler state on restore.
            # Retain only the graph-native task artifact, minting a fresh local
            # id from the remapped graph id; hydration can then materialize it
            # without inheriting child-local execution records.
            state_node_id = target_id.removeprefix("proof_state:")
            copied.name = state_node_id
            for private_field in (
                "proof_state_node",
                "proof_state_assembly",
                "residual_goal_attestation",
                "residual_goal_source",
                "pending_residual_goal_extraction",
                "verifier_retry_states",
                "dependencies",
                "parent_node_id",
                "child_node_ids",
                "blocked_by_node_ids",
            ):
                metadata.pop(private_field, None)
            metadata["proof_state_node_id"] = state_node_id
        copied.metadata = metadata
        dst_nodes[target_id] = copied
        imported_node_ids.add(target_id)

    edges_before = len(getattr(dst_graph, "edges", []) or [])
    attached_targets = {
        source_to_target_node_id[source_id]
        for source_id in eligible_source_ids
        if source_id in source_to_target_node_id
        and source_to_target_node_id[source_id] != parent_id
        and _structural_fanin_node_is_live_open(
            dst_graph,
            dst_nodes.get(source_to_target_node_id[source_id]),
        )
    }
    for target_id in sorted(attached_targets):
        dst_graph.add_edge(parent_id, target_id, "recursive_child_work")
    for edge in list(getattr(src_graph, "edges", []) or []):
        source_raw = str(getattr(edge, "source", "") or "")
        target_raw = str(getattr(edge, "target", "") or "")
        if (
            source_raw not in source_to_target_node_id
            or target_raw not in source_to_target_node_id
        ):
            continue
        source = source_to_target_node_id[source_raw]
        target = source_to_target_node_id[target_raw]
        if source == target or source not in dst_nodes or target not in dst_nodes:
            continue
        dst_graph.add_edge(source, target, str(getattr(edge, "kind", "") or ""))

    # ``blocked`` is meaningful only together with blockers that survived the
    # authority boundary.  A child-local blocker may be terminal, ineligible,
    # or deferred to a later bounded page; copying the lifecycle without any
    # mapped ``blocked_by`` edge creates permanently invisible work.  Reopen
    # that work now, and re-block it on a later cutpoint if its live blocker is
    # subsequently imported and the edge becomes representable.
    for source_id in sorted(eligible_source_ids):
        source_node = src_nodes[source_id]
        if str(getattr(source_node, "status", "") or "") != "blocked":
            continue
        target_id = source_to_target_node_id.get(source_id)
        target_node = dst_nodes.get(str(target_id or ""))
        target_metadata = dict(getattr(target_node, "metadata", {}) or {})
        if (
            target_node is None
            or target_metadata.get("recursive_child_imported") is not True
            or str(
                target_metadata.get("recursive_parent_obligation_id") or ""
            )
            != parent_id
            or str(
                target_metadata.get("recursive_child_original_node_id") or ""
            )
            != source_id
            or _structural_fanin_node_is_terminal_or_tombstoned(
                dst_graph, target_node
            )
        ):
            continue
        mapped_blockers = dst_graph.outgoing(target_node.node_id, kind="blocked_by")
        if mapped_blockers:
            target_node.status = "blocked"
            target_node.metadata.pop(
                "recursive_child_unmapped_blockers_reopened", None
            )
            continue
        target_node.status = "open"
        target_node.metadata.pop("blocker", None)
        target_node.metadata.pop("blocked_by_node_ids", None)
        target_node.metadata["recursive_child_unmapped_blockers_reopened"] = True

    contract_blockers: Set[str] = set()
    for route in src_nodes.values():
        if (
            str(getattr(route, "kind", "") or "") != "strategy_route"
            or not _structural_fanin_node_is_live_open(src_graph, route)
        ):
            continue
        raw_contract = (getattr(route, "metadata", {}) or {}).get(
            "route_assembly_contract"
        )
        if not isinstance(raw_contract, Mapping):
            continue
        contract = dict(raw_contract)
        if (
            str(contract.get("target_node_id") or "")
            != str(src_graph.root_node_id)
            or str(contract.get("target_statement") or "").strip()
            != str(getattr(src, "root_statement", "") or "").strip()
        ):
            continue
        for source_requirement_id in list(
            contract.get("required_node_ids") or ()
        ):
            mapped = source_to_target_node_id.get(
                str(source_requirement_id or "").strip()
            )
            if (
                mapped
                and mapped != parent_id
                and mapped in dst_nodes
                and _structural_fanin_node_is_live_open(
                    dst_graph, dst_nodes.get(mapped)
                )
            ):
                contract_blockers.add(mapped)
    blockers_attached = 0
    if contract_blockers:
        existing_blockers = {
            str(getattr(edge, "target", "") or "")
            for edge in dst_graph.outgoing(parent_id, kind="blocked_by")
        }
        parent_was_blocked = str(getattr(parent_node, "status", "") or "") == (
            "blocked"
        )
        dst_graph.mark_node_blocked(
            parent_id,
            reason="recursive_child_structural_work",
            blocker_node_ids=sorted(contract_blockers),
        )
        blockers_attached = len(contract_blockers - existing_blockers)
        if not parent_was_blocked and str(
            getattr(parent_node, "status", "") or ""
        ) == "blocked":
            blockers_attached = max(1, blockers_attached)

    edges_imported = max(
        0, len(getattr(dst_graph, "edges", []) or []) - edges_before
    )
    if imported_node_ids:
        reconcile = getattr(dst, "reconcile_verified_facts", None)
        if callable(reconcile):
            try:
                reconcile(
                    trigger="recursive_child_structural_fanin",
                    projected_node_ids=sorted(imported_node_ids),
                )
            except Exception:
                pass
    increment = getattr(dst, "increment_tool_metric", None)
    if callable(increment) and (
        imported_node_ids or edges_imported or conflicts
    ):
        increment(
            "mini_recursive_child_structural_nodes_imported",
            len(imported_node_ids),
        )
        increment(
            "mini_recursive_child_structural_edges_imported",
            edges_imported,
        )
        increment("mini_recursive_child_structural_conflicts", conflicts)
    if node_id_remap_out is not None:
        node_id_remap_out.update(
            {
                source_id: target_id
                for source_id, target_id in source_to_target_node_id.items()
                if target_id in dst_nodes
            }
        )
    return {
        "nodes_imported": len(imported_node_ids),
        "nodes_coalesced": len(coalesced_source_ids),
        "edges_imported": edges_imported,
        "blockers_attached": blockers_attached,
        "conflicts": conflicts,
    }


def _parallel_sample_structural_summary(
    dossier: ProofDossier,
    *,
    max_work_items: int = 12,
    max_nodes: int = 16,
    max_branch_frames: int = 12,
) -> Dict[str, Any]:
    """Return a bounded search-structure snapshot for a parallel sample."""

    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {}
    clone_graph = getattr(graph, "clone", None)
    if callable(clone_graph):
        try:
            graph = clone_graph()
        except Exception:
            try:
                graph = copy.deepcopy(graph)
            except Exception:
                return {}
    else:
        try:
            graph = copy.deepcopy(graph)
        except Exception:
            return {}
    summary: Dict[str, Any] = {}
    graph_summary = getattr(graph, "summary", None)
    if callable(graph_summary):
        try:
            summary["graph_summary"] = dict(graph_summary())
        except Exception:
            summary["graph_summary_error"] = True
    work_frontier = getattr(graph, "work_frontier", None)
    if callable(work_frontier):
        frontier: List[Dict[str, Any]] = []
        try:
            raw_frontier = work_frontier(max_items=max(1, int(max_work_items or 1)))
        except Exception:
            raw_frontier = []
            summary["work_frontier_error"] = True
        for raw in list(raw_frontier or [])[: max(0, int(max_work_items or 0))]:
            if isinstance(raw, dict):
                item = copy.deepcopy(raw)
            else:
                to_record = getattr(raw, "to_record", None)
                if callable(to_record):
                    try:
                        item = copy.deepcopy(to_record())
                    except Exception:
                        item = {}
                else:
                    item = {
                        "work_type": str(getattr(raw, "work_type", "") or ""),
                        "node_id": str(getattr(raw, "node_id", "") or ""),
                        "source": str(getattr(raw, "source", "") or ""),
                    }
            if item:
                frontier.append(item)
        if frontier:
            summary["work_frontier"] = frontier
    nodes: List[Dict[str, Any]] = []
    for node_id, node in list((getattr(graph, "nodes", {}) or {}).items()):
        kind = str(getattr(node, "kind", "") or "")
        status = str(getattr(node, "status", "") or "")
        if kind not in _STRUCTURAL_FANIN_NODE_KINDS:
            continue
        if status not in {"open", "blocked"}:
            continue
        metadata = dict(getattr(node, "metadata", {}) or {})
        metadata_flags = {
            key: copy.deepcopy(metadata[key])
            for key in (
                "source",
                "work_type",
                "target_integrity_adjudication",
                "formalization_required",
                "route_id",
                "route_kind",
                "parallel_sample_imported",
                "parallel_sample_index",
            )
            if key in metadata
        }
        nodes.append(
            {
                "node_id": str(node_id or ""),
                "kind": kind,
                "status": status,
                "statement": str(getattr(node, "statement", "") or "")[:500],
                "metadata": metadata_flags,
            }
        )
        if len(nodes) >= max(0, int(max_nodes or 0)):
            break
    if nodes:
        summary["open_structural_nodes"] = nodes
    frames: List[Dict[str, Any]] = []
    for frame in list((getattr(graph, "branch_frames", {}) or {}).values()):
        try:
            record = asdict(frame)
        except Exception:
            record = {
                "frame_id": str(getattr(frame, "frame_id", "") or ""),
                "route_id": str(getattr(frame, "route_id", "") or ""),
                "status": str(getattr(frame, "status", "") or ""),
            }
        frames.append(copy.deepcopy(record))
        if len(frames) >= max(0, int(max_branch_frames or 0)):
            break
    if frames:
        summary["branch_frames"] = frames
    return summary


def _parallel_sample_proof_state_record(dossier: ProofDossier) -> Dict[str, Any]:
    """Combine proof-state metrics with graph search structure for a sample."""

    record = getattr(dossier, "proof_state_record", None)
    out: Dict[str, Any] = copy.deepcopy(record) if isinstance(record, dict) else {}
    structural_summary = _parallel_sample_structural_summary(dossier)
    if structural_summary:
        out["graph_structural_summary"] = structural_summary
    if _parallel_sample_has_proof_disproof_conflict(dossier):
        out["terminal_authority"] = "proof_disproof_conflict"
    elif _parallel_sample_has_root_disproof(dossier):
        out["terminal_authority"] = "mathematical_disproof"
    elif _parallel_sample_has_finalized_root_proof(dossier):
        out["terminal_authority"] = "finalized_root_proof"
    return out


def _parallel_samples_arg(value: str) -> int:
    """argparse type for ``--parallel-samples``: positive int only."""

    try:
        n = int(value)
    except (TypeError, ValueError):
        raise argparse.ArgumentTypeError(
            f"parallel-samples must be a positive integer, got {value!r}"
        ) from None
    if n < 1:
        raise argparse.ArgumentTypeError(
            f"parallel-samples must be >= 1, got {n}"
        )
    return n


def _parallel_temps_arg(value: str) -> str:
    """argparse type for comma-separated finite floats in [0, 2]."""

    text = str(value or "").strip()
    if not text:
        return ""
    parts = [p.strip() for p in text.split(",") if p.strip()]
    for p in parts:
        try:
            t = float(p)
        except (TypeError, ValueError):
            raise argparse.ArgumentTypeError(
                f"parallel-temps entry must be a finite float, got {p!r}"
            ) from None
        if t != t or t in (float("inf"), float("-inf")):
            raise argparse.ArgumentTypeError(
                f"parallel-temps entry must be finite, got {p!r}"
            )
        if t < 0.0 or t > 2.0:
            raise argparse.ArgumentTypeError(
                f"parallel-temps entry must be in [0.0, 2.0], got {t}"
            )
    return ",".join(parts)


def _stratify_sample_temperatures(
    sample_count: int,
    temperatures: Tuple[float, ...],
) -> List[Optional[float]]:
    """Distribute a fixed set of temperatures across N samples."""

    n = max(1, int(sample_count))
    if not temperatures:
        return [None] * n
    temps = list(temperatures)
    if len(temps) >= n:
        return [float(t) for t in temps[:n]]
    bucket_size = max(1, n // len(temps))
    out: List[Optional[float]] = []
    for t in temps:
        out.extend([float(t)] * bucket_size)
    while len(out) < n:
        out.append(float(temps[-1]))
    return out[:n]
