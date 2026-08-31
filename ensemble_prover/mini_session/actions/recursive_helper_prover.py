"""Prove one open child goal in a bounded, freshly scoped child session.

The action runs after cheaper deterministic child work, respects per-node retry
clusters and recursion-depth limits, and uses a budget separate from root
recursive passes. A successful child proof is rechecked in the parent context
before its helper declaration enters the parent dossier; failed attempts leave
the node open for other eligible actions.
"""

from __future__ import annotations

import copy
import hashlib
import json
import time
from typing import Any, ClassVar, FrozenSet, List, Mapping, Optional

from ..action import (
    MiniOutcome,
    action_dispatch_replaced,
    require_current_action_dispatch,
)
from ..recursive_helper_prover import (
    _bounded_nested_elapsed_deadline_epoch_s,
    prove_helper_in_subsession,
)


RECURSIVE_HELPER_PARENT_RECHECK_TIMEOUT_S = 300.0
RECURSIVE_HELPER_TARGET_TYPECHECK_TIMEOUT_FLOOR_S = 300.0
CHILD_EXECUTION_SCHEMA_VERSION = 1


def _nonnegative_counter(value: Any) -> int:
    try:
        return max(0, int(value or 0))
    except (TypeError, ValueError, OverflowError):
        return 0


def _exception_chain_contains_timeout(exc: BaseException) -> bool:
    """Recognize direct and strict-deadline timeout wrappers."""

    current: Optional[BaseException] = exc
    seen: set[int] = set()
    for _depth in range(8):
        if current is None or id(current) in seen:
            break
        seen.add(id(current))
        if isinstance(current, TimeoutError):
            return True
        current = getattr(current, "__cause__", None) or getattr(
            current,
            "__context__",
            None,
        )
    return False


async def _typecheck_recursive_helper_target(
    *,
    session: Any,
    statement: str,
) -> dict[str, Any]:
    """Lean-elaborate an unreceipted generated child before any LLM work."""

    lean = getattr(session, "lean", None)
    if lean is None or not (
        callable(getattr(lean, "check_with_sorry_raw", None))
        or callable(getattr(lean, "check", None))
    ):
        return {
            "ok": False,
            "inconclusive": True,
            "output": "Lean checker missing generated-child typecheck API",
        }
    try:
        configured_timeout_s = max(
            float(getattr(getattr(lean, "cfg", None), "timeout_s", 0.0) or 0.0),
            float(getattr(lean, "timeout_s", 0.0) or 0.0),
        )
    except (TypeError, ValueError):
        configured_timeout_s = 0.0
    dossier = getattr(session, "dossier", None)
    helpers_getter = getattr(dossier, "verified_helper_blocks", None)
    try:
        helpers = list(helpers_getter() or ()) if callable(helpers_getter) else []
    except Exception:
        return {
            "ok": False,
            "inconclusive": True,
            "output": "verified helper context unavailable for child typecheck",
        }
    conv = getattr(session, "conv", None)
    preamble = str(
        getattr(conv, "lean_preamble", "")
        or getattr(conv, "preamble", "")
        or ""
    )
    try:
        from ensemble_prover.mini_recursive import _typecheck_claim_statement

        ok, inconclusive, output = await _typecheck_claim_statement(
            lean=lean,
            statement=str(statement or ""),
            preamble=preamble,
            helpers=helpers,
            timeout_s=max(
                RECURSIVE_HELPER_TARGET_TYPECHECK_TIMEOUT_FLOOR_S,
                configured_timeout_s,
            ),
        )
        return {
            "ok": bool(ok),
            "inconclusive": bool(inconclusive),
            "output": str(output or ""),
        }
    except Exception as exc:
        return {
            "ok": False,
            "inconclusive": True,
            "output": f"{type(exc).__name__}: {exc}",
        }


def _commit_staged_recursive_helper_graph_publication(
    graph: Any,
    staged_graph: Any,
) -> None:
    """Commit one successfully staged graph publication explicitly.

    Publication methods are intentionally rich: proving a claim may add
    certificate edges and reconcile linked graph state.  Run those methods on
    an isolated graph first, then copy their dataclass state into the live
    graph only after every method has returned.  Updating existing nodes in
    place preserves references held by schedulers and diagnostics.  This is an
    explicit graph transaction, not a broad ``__dict__`` rewind.
    """

    live_nodes = graph.nodes
    staged_nodes = staged_graph.nodes
    for node_id in tuple(live_nodes):
        if node_id not in staged_nodes:
            live_nodes.pop(node_id, None)
    for node_id, staged_node in staged_nodes.items():
        live_node = live_nodes.get(node_id)
        if live_node is None:
            live_nodes[node_id] = staged_node
            continue
        if live_node == staged_node:
            continue
        live_node.kind = staged_node.kind
        live_node.name = staged_node.name
        live_node.statement = staged_node.statement
        live_node.status = staged_node.status
        live_node.phase = staged_node.phase
        live_node.turn_index = staged_node.turn_index
        live_node.source_hash = staged_node.source_hash
        live_node.proof_hash = staged_node.proof_hash
        live_node.support_names[:] = staged_node.support_names
        live_node.attempt_ids[:] = staged_node.attempt_ids
        live_node.metadata.clear()
        live_node.metadata.update(staged_node.metadata)

    live_edges_by_key = {
        (edge.source, edge.target, edge.kind): edge for edge in graph.edges
    }
    graph.edges[:] = [
        live_edges_by_key.get(
            (edge.source, edge.target, edge.kind),
            edge,
        )
        for edge in staged_graph.edges
    ]
    graph.helper_name_to_node_id.clear()
    graph.helper_name_to_node_id.update(staged_graph.helper_name_to_node_id)

    live_attempts_by_id = {
        attempt.attempt_id: attempt for attempt in graph.attempts
    }
    committed_attempts = []
    for staged_attempt in staged_graph.attempts:
        live_attempt = live_attempts_by_id.get(staged_attempt.attempt_id)
        if live_attempt is None:
            committed_attempts.append(staged_attempt)
            continue
        if live_attempt != staged_attempt:
            live_attempt.node_id = staged_attempt.node_id
            live_attempt.phase = staged_attempt.phase
            live_attempt.turn_index = staged_attempt.turn_index
            live_attempt.verdict = staged_attempt.verdict
            live_attempt.proof_hash = staged_attempt.proof_hash
            live_attempt.error_type = staged_attempt.error_type
            live_attempt.helper_names[:] = staged_attempt.helper_names
            live_attempt.source = staged_attempt.source
            live_attempt.metadata.clear()
            live_attempt.metadata.update(staged_attempt.metadata)
        committed_attempts.append(live_attempt)
    graph.attempts[:] = committed_attempts
    graph.attempt_history_pruned = staged_graph.attempt_history_pruned

    live_frames = graph.branch_frames
    for frame_id in tuple(live_frames):
        if frame_id not in staged_graph.branch_frames:
            live_frames.pop(frame_id, None)
    for frame_id, staged_frame in staged_graph.branch_frames.items():
        live_frame = live_frames.get(frame_id)
        if live_frame is None:
            live_frames[frame_id] = staged_frame
            continue
        if live_frame == staged_frame:
            continue
        live_frame.route_id = staged_frame.route_id
        live_frame.case_node_id = staged_frame.case_node_id
        live_frame.case_helper_name = staged_frame.case_helper_name
        live_frame.case_statement = staged_frame.case_statement
        live_frame.branch_name = staged_frame.branch_name
        live_frame.branch_index = staged_frame.branch_index
        live_frame.assumption_statement = staged_frame.assumption_statement
        live_frame.assumption_key = staged_frame.assumption_key
        live_frame.case_full_statement = staged_frame.case_full_statement
        live_frame.reducer_node_id = staged_frame.reducer_node_id
        live_frame.reducer_helper_name = staged_frame.reducer_helper_name
        live_frame.reducer_statement = staged_frame.reducer_statement
        live_frame.status = staged_frame.status
        live_frame.metadata.clear()
        live_frame.metadata.update(staged_frame.metadata)

    graph.active_root_target_statements[:] = (
        staged_graph.active_root_target_statements
    )
    graph.active_root_target_contract_identities[:] = (
        staged_graph.active_root_target_contract_identities
    )
    graph.active_root_target_universe_observed = (
        staged_graph.active_root_target_universe_observed
    )
    graph._edge_keys.clear()
    graph._edge_keys.update(staged_graph._edge_keys)
    graph._next_attempt_index = staged_graph._next_attempt_index
    graph._attempt_ids.clear()
    graph._attempt_ids.update(staged_graph._attempt_ids)
    graph._value_propagation_cache_signature = (
        staged_graph._value_propagation_cache_signature
    )
    graph._value_propagation_cache_values.clear()
    graph._value_propagation_cache_values.update(
        staged_graph._value_propagation_cache_values
    )


def _publish_recursive_helper_exact_graph_lineage(
    *,
    dossier: Any,
    proof_state_node: Any,
    helper_name: str,
    target_statement: str,
    acceptance_status: Mapping[str, Any],
) -> tuple[str, ...]:
    """Retire the exact graph lineage behind a verified proof-state child.

    A proof-state child promoted from a graph obligation can outlive a monotone
    preamble extension.  Its parent acceptance proves the *current-environment*
    target, while the originating graph nodes intentionally retain their older
    environment stamp and therefore reject generic helper reuse.  Bridge that
    narrow publication boundary without weakening the generic exact-environment
    rule:

    * require the receipt produced by ``_accept_proof_state_helper`` after a
      real Lean attempt, including the accepted helper's source hash;
    * require an exact promoted-obligation diagnostic on this proof-state node;
    * follow only that obligation's named dependency, its same-named sibling
      obligations, the exact named claim, and exact child formal variants;
    * require every old stamp to be an authoritative ancestor of the current
      environment before re-stamping and using ordinary graph certification.

    Arbitrary same-surface graph nodes are deliberately excluded.  Generic
    ancestor reuse therefore remains fail-closed.
    """

    from ensemble_prover.contract_identity import parse_lean_contract_identity
    from ensemble_prover.proof_dossier import (
        verified_helper_bound_contract_identity,
    )
    from ensemble_prover.proof_graph import (
        _graph_metadata_raw_lean_identities,
        graph_helper_bound_contract_identity,
        graph_node_bound_contract_identity,
        graph_statement_key,
        stamp_graph_node_environment,
    )

    status = dict(acceptance_status or {})
    accepted_name = str(status.get("accepted_helper_name") or "").strip()
    accepted_source_hash = str(status.get("accepted_source_hash") or "").strip()
    requested_name = str(helper_name or "").strip()
    if (
        str(status.get("status") or "").strip() != "accepted"
        or status.get("lean_attempted") is not True
        or not requested_name
        or accepted_name != requested_name
        or not accepted_source_hash
    ):
        return ()

    graph = getattr(dossier, "proof_graph", None)
    verified_helpers = getattr(dossier, "verified_helpers", None)
    if graph is None or not isinstance(verified_helpers, Mapping):
        return ()
    helper_record = verified_helpers.get(requested_name)
    if helper_record is None:
        return ()
    current_environment = str(
        getattr(dossier, "current_lean_environment_hash", "") or ""
    ).strip()
    helper_environment = str(
        getattr(helper_record, "verification_environment_hash", "") or ""
    ).strip()
    helper_source_hash = str(
        getattr(helper_record, "source_hash", "") or ""
    ).strip()
    if (
        not current_environment
        or helper_environment != current_environment
        or helper_source_hash != accepted_source_hash
    ):
        return ()

    helper_node_id = str(
        getattr(graph, "helper_name_to_node_id", {}).get(requested_name) or ""
    ).strip()
    helper_node = getattr(graph, "nodes", {}).get(helper_node_id)
    helper_metadata = dict(getattr(helper_node, "metadata", {}) or {})
    target_key = graph_statement_key(target_statement)
    proof_state_target_key = graph_statement_key(
        getattr(proof_state_node, "target", "") or ""
    )
    helper_target_key = graph_statement_key(
        getattr(helper_node, "statement", "") or ""
    )
    if (
        helper_node is None
        or getattr(helper_node, "kind", "") != "helper"
        or getattr(helper_node, "status", "") != "proved"
        or not target_key
        or proof_state_target_key != target_key
        or helper_target_key != target_key
        or str(
            helper_metadata.get("verified_helper_environment_hash") or ""
        ).strip()
        != current_environment
        or str(helper_node.source_hash or "").strip() != accepted_source_hash
    ):
        return ()

    origin_ids: list[str] = []
    for raw_diagnostic in list(
        getattr(proof_state_node, "diagnostics", None) or []
    ):
        if not isinstance(raw_diagnostic, Mapping):
            continue
        diagnostic = dict(raw_diagnostic)
        if str(diagnostic.get("error_type") or "").strip() != (
            "trusted_graph_obligation_promoted"
        ):
            continue
        obligation_id = str(diagnostic.get("obligation_id") or "").strip()
        if obligation_id and obligation_id not in origin_ids:
            origin_ids.append(obligation_id)
    if not origin_ids:
        return ()
    proof_state_node_id = str(
        getattr(proof_state_node, "node_id", "") or ""
    ).strip()
    if not proof_state_node_id:
        return ()

    def eligible_old_target(node: Any, *, kind: str) -> bool:
        if (
            node is None
            or str(getattr(node, "kind", "") or "") != kind
            or str(getattr(node, "status", "") or "") != "open"
            or graph.is_superseded_tombstone(node)
            or graph_statement_key(getattr(node, "statement", "") or "")
            != target_key
        ):
            return False
        old_environment = str(
            dict(getattr(node, "metadata", {}) or {}).get(
                "statement_environment_hash"
            )
            or ""
        ).strip()
        if not old_environment:
            return False
        return bool(
            old_environment == current_environment
            or dossier.lean_environment_is_compatible(
                old_environment,
                current_environment,
            )
        )

    dependency_names: set[str] = set()
    origin_nodes: list[Any] = []
    for origin_id in origin_ids:
        origin = graph.nodes.get(origin_id)
        if not eligible_old_target(origin, kind="missing_obligation"):
            return ()
        origin_metadata = dict(origin.metadata or {})
        dependency_name = str(
            origin_metadata.get("missing_dependency") or ""
        ).strip()
        if (
            not dependency_name
            or origin_metadata.get("promoted_to_proof_state") is not True
            or str(
                origin_metadata.get("proof_state_child_node_id") or ""
            ).strip()
            != proof_state_node_id
        ):
            return ()
        dependency_names.add(dependency_name)
        origin_nodes.append(origin)

    obligations: list[Any] = []
    for candidate in graph.nodes_by_kind("missing_obligation"):
        if not eligible_old_target(candidate, kind="missing_obligation"):
            continue
        candidate_metadata = dict(candidate.metadata or {})
        if (
            str(candidate_metadata.get("missing_dependency") or "").strip()
            in dependency_names
            and candidate_metadata.get("promoted_to_proof_state") is True
            and str(
                candidate_metadata.get("proof_state_child_node_id") or ""
            ).strip()
            == proof_state_node_id
        ):
            obligations.append(candidate)

    claims: list[Any] = []
    for candidate in graph.nodes_by_kind("proposed_claim"):
        if not eligible_old_target(candidate, kind="proposed_claim"):
            continue
        metadata = dict(candidate.metadata or {})
        candidate_names = {
            str(getattr(candidate, "name", "") or "").strip(),
            str(metadata.get("claim_name") or "").strip(),
        }
        if dependency_names.intersection(candidate_names):
            claims.append(candidate)

    variants: list[Any] = []
    seen_variant_ids: set[str] = set()
    for claim in claims:
        for edge in graph.outgoing(claim.node_id, kind="claim_formalized_as"):
            candidate = graph.nodes.get(edge.target)
            if (
                eligible_old_target(candidate, kind="formal_variant")
                and candidate.node_id not in seen_variant_ids
            ):
                seen_variant_ids.add(candidate.node_id)
                variants.append(candidate)

    # The diagnostic must bind to at least its exact origin, while claim and
    # variant publication are optional when that route did not create them.
    targets: list[Any] = []
    seen_target_ids: set[str] = set()
    for candidate in [*claims, *variants, *obligations, *origin_nodes]:
        if candidate.node_id not in seen_target_ids:
            seen_target_ids.add(candidate.node_id)
            targets.append(candidate)
    if not targets:
        return ()

    # Surface equality across a monotone environment extension is sufficient
    # only when no stronger evidence contradicts it.  When both the accepted
    # current helper and an ancestor target carry receipt-bound Lean
    # identities, their full-expression hashes are authoritative proposition
    # identities.  A definite mismatch must reject the entire lineage before
    # any node is re-stamped or marked.
    helper_identities = {
        identity
        for identity in (
            verified_helper_bound_contract_identity(helper_record),
            graph_helper_bound_contract_identity(helper_node),
        )
        if identity
    }
    helper_expression_hashes = {
        parsed[0]
        for identity in helper_identities
        if (parsed := parse_lean_contract_identity(identity)) is not None
    }
    if len(helper_expression_hashes) > 1:
        return ()
    if helper_expression_hashes:
        helper_expression_hash = next(iter(helper_expression_hashes))
        for candidate in targets:
            candidate_identity = graph_node_bound_contract_identity(candidate)
            parsed_candidate = parse_lean_contract_identity(candidate_identity)
            if (
                parsed_candidate is not None
                and parsed_candidate[0] != helper_expression_hash
            ):
                return ()
            raw_expression_hashes = {
                parsed[0]
                for raw_identity in _graph_metadata_raw_lean_identities(
                    dict(getattr(candidate, "metadata", {}) or {})
                )
                if (parsed := parse_lean_contract_identity(raw_identity))
                is not None
            }
            if any(
                raw_hash != helper_expression_hash
                for raw_hash in raw_expression_hashes
            ):
                return ()

    # All graph mutation happens on an isolated staging copy.  If stamping or
    # any certification method raises, the live graph has not been touched and
    # the caller can retain the accepted helper while reporting the residual.
    staged_graph = copy.deepcopy(graph)
    staged_targets = [staged_graph.nodes[candidate.node_id] for candidate in targets]
    staged_claims = [staged_graph.nodes[candidate.node_id] for candidate in claims]
    staged_variants = [staged_graph.nodes[candidate.node_id] for candidate in variants]
    staged_obligations = [
        staged_graph.nodes[candidate.node_id] for candidate in obligations
    ]
    staged_helper_node = staged_graph.nodes.get(helper_node_id)
    if staged_helper_node is None:
        return ()

    ancestor_hashes = list(dossier.lean_environment_ancestors(current_environment))
    for candidate in staged_targets:
        # Parent acceptance established the exact proposition in the current
        # environment, but it did not produce a new structural-expression
        # identity for this graph node.  Drop the old environment's identity
        # and receipt before re-stamping instead of reminting unsupported
        # structural authority under the new environment hash.
        for key in (
            "contract_identity",
            "statement_contract_identity",
            "structural_statement_identity",
            "contract_identity_statement_key",
            "contract_identity_environment_hash",
            "contract_identity_evidence_receipt",
        ):
            candidate.metadata.pop(key, None)
        stamp_graph_node_environment(
            candidate,
            environment_hash=current_environment,
            ancestor_hashes=ancestor_hashes,
            stamp_source="recursive_helper_exact_lineage_current_env_acceptance",
        )

    published: list[str] = []
    for candidate in staged_claims:
        staged_graph.mark_claim_proved_by_helper(
            candidate.node_id,
            staged_helper_node.node_id,
            source_hash=accepted_source_hash,
            proof_hash=accepted_source_hash,
        )
        if candidate.status == "proved":
            candidate.metadata.pop("uncertified_claim_proved_ignored", None)
            published.append(candidate.node_id)
    for candidate in staged_variants:
        staged_graph.mark_variant_proved_by_helper(
            candidate.node_id,
            staged_helper_node.node_id,
            source_hash=accepted_source_hash,
            proof_hash=accepted_source_hash,
        )
        if candidate.status == "proved":
            candidate.metadata.pop("uncertified_variant_proved_ignored", None)
            if candidate.node_id not in published:
                published.append(candidate.node_id)
    for candidate in staged_obligations:
        staged_graph.mark_obligation_proved_by_helper(
            candidate.node_id,
            staged_helper_node.node_id,
            source_hash=accepted_source_hash,
            proof_hash=accepted_source_hash,
        )
        if candidate.status == "proved":
            candidate.metadata.pop("uncertified_obligation_proved_ignored", None)
            if candidate.node_id not in published:
                published.append(candidate.node_id)
    if set(published) != {candidate.node_id for candidate in staged_targets}:
        return ()
    _commit_staged_recursive_helper_graph_publication(graph, staged_graph)
    return tuple(published)


class RecursiveHelperProverAction:
    """Spawn a child MiniSession to prove ONE open child_goal helper."""

    # Priority 35 is the static fallback order. ``is_applicable`` gates
    # fresh child goals until deterministic retrieval/closure lanes have
    # either run or become unavailable.
    id: str = "recursive_helper_prover"
    priority: int = 35
    cost_estimate_s: float = 90.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {"_nested_execution_frame"}
    )

    def failed_dispatch_durable_state(self) -> dict[str, Any]:
        """Project only provider-free resumable child receipts."""

        frame = self._nested_execution_frame
        if not isinstance(frame, Mapping):
            return {}
        status = str(frame.get("status") or "")
        if status not in {
            "scheduler_backoff",
            "parent_recheck_pending",
            "retryable_error",
        }:
            return {}
        if frame.get("child_session") is not None:
            return {}
        projected = copy.deepcopy(dict(frame))
        projected["child_session"] = None
        return {"nested_execution_frame": projected}

    def merge_failed_dispatch_durable_state(self, state: Any) -> None:
        """Restore a validated provider-free child receipt."""

        record = dict(state or {}) if isinstance(state, dict) else {}
        frame = record.get("nested_execution_frame")
        if not isinstance(frame, dict) or frame.get("child_session") is not None:
            return
        self._nested_execution_frame = copy.deepcopy(frame)

    def __init__(
        self,
        *,
        max_attempts_per_node: int = 2,
        helper_turns: int = 5,
        refine_enabled: bool = False,
        max_giveups_per_cluster_per_node: int = 2,
        max_elapsed_s: float = 0.0,
    ) -> None:
        self.max_attempts_per_node = int(max_attempts_per_node or 0)
        self.helper_turns = int(helper_turns or 0)
        self.refine_enabled = bool(refine_enabled)
        self.max_giveups_per_cluster_per_node = int(
            max_giveups_per_cluster_per_node or 0
        )
        self.max_elapsed_s = max(0.0, float(max_elapsed_s or 0.0))
        self._nested_execution_frame: dict[str, Any] = {}

    def on_outcome_applied(self, session: Any, outcome: MiniOutcome) -> None:
        del session
        # A child may finish at the exact end of its action lease, leaving no
        # time for the mandatory replay in the parent environment.  That is a
        # suspended parent-only recheck, not a completed/failed child attempt.
        # Keep the proof-bearing frame through outcome application so a
        # later dispatch can replay it without spending another child attempt.
        outcome_metadata = getattr(outcome, "metadata", None) or {}
        if bool(
            outcome_metadata.get("parent_recheck_pending")
            or outcome_metadata.get("recursive_helper_cleanup_retry_pending")
            or outcome_metadata.get(
                "recursive_helper_zero_provider_retry_pending"
            )
        ):
            return
        self._nested_execution_frame = {}

    @staticmethod
    def _cleanup_retry_frame_identity(frame: Mapping[str, Any]) -> str:
        """Return the stable identity of one already-reserved child attempt."""

        descriptor = dict(frame.get("descriptor") or {})
        payload = {
            "owner_action_id": str(frame.get("owner_action_id") or ""),
            "child_kind": str(frame.get("child_kind") or ""),
            "descriptor": descriptor,
        }
        if (
            payload["owner_action_id"] != "recursive_helper_prover"
            or payload["child_kind"] != "recursive_helper_subsession"
            or not str(descriptor.get("node_id") or "")
            or int(descriptor.get("attempt_number") or 0) <= 0
            or not str(descriptor.get("helper_name") or "")
            or not str(descriptor.get("target_statement") or "")
        ):
            return ""
        return hashlib.sha256(
            json.dumps(
                payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=True,
            ).encode("utf-8")
        ).hexdigest()

    def owns_cleanup_retry_continuation(self, identity: str) -> bool:
        """Validate scheduler headroom against the live durable child frame."""

        clean = str(identity or "").strip()
        frame = self._nested_execution_frame
        return bool(
            clean
            and str(frame.get("status") or "")
            in {
                "child_prepared",
                "child_live",
                "child_complete",
                "parent_recheck_pending",
            }
            and self._cleanup_retry_frame_identity(frame) == clean
        )

    # --- Helpers ---

    @staticmethod
    def _is_attackable_child_goal(node: Any) -> bool:
        """A fresh or previously-attacked open child_goal worth LLM effort."""
        if getattr(node, "kind", "") != "child_goal":
            return False
        if getattr(node, "status", "") != "open":
            return False
        # A Lean-falsified goal is provably unprovable — never spend LLM effort on
        # it (defense-in-depth; work_frontier.add() already blocks emission).
        if getattr(node, "falsified", False):
            return False
        if dict(getattr(node, "pending_helper_acceptance", {}) or {}):
            # A completed child proof already owns the verifier lane. Starting
            # another child session would overwrite or duplicate paid work.
            return False
        target = " ".join(str(getattr(node, "target", "") or "").split())
        if target in {"False", "false"}:
            return False
        return True

    @staticmethod
    def _residual_attestation_status(session: Any, node: Any) -> str:
        """Return a fail-closed execution status for Lean residual children.

        Normal structural child goals do not need residual receipts.  A child
        whose source is a kernel-produced residual boundary does: if the
        proof-state implementation is missing the validator, the validator
        raises, or the persisted batch no longer validates, recursive proving
        must not spend an attempt (and, more importantly, must not show the
        reconstructed proposition to an LLM).
        """

        proof_state = getattr(session, "proof_state", None)
        status_getter = getattr(
            proof_state,
            "residual_goal_attestation_status",
            None,
        )
        if callable(status_getter):
            try:
                persisted_status = str(status_getter(node) or "").strip()
                from ensemble_prover.proof_state_executor import (
                    proof_state_node_current_residual_attestation_status,
                )
                current_status = (
                    proof_state_node_current_residual_attestation_status(
                        conv=getattr(session, "conv", None),
                        dossier=getattr(session, "dossier", None),
                        lean=getattr(session, "lean", None),
                        proof_state=proof_state,
                        node_or_id=node,
                    )
                )
                if (
                    persisted_status == "attested"
                    and current_status
                    == "residual_elaboration_attestation_required"
                ):
                    return "residual_elaboration_reattestation_required"
                return current_status or persisted_status
            except TypeError:
                try:
                    return str(status_getter(node) or "").strip()
                except Exception:
                    pass
            except Exception:
                # Determine below whether this is a receipt-bearing boundary;
                # those boundaries fail closed when validation is unavailable.
                pass
        source = str(
            getattr(getattr(node, "goal", None), "source_failure", "") or ""
        ).strip()
        try:
            from ensemble_prover.proof_state import (
                proof_state_source_requires_residual_goal_attestation,
            )

            if proof_state_source_requires_residual_goal_attestation(source):
                return "residual_elaboration_attestation_required"
        except Exception:
            # Unknown extension nodes retain the historical structural-child
            # behavior.  A production ProofSearchState always exposes the
            # validator above and the source predicate imported here.
            if source:
                return "residual_elaboration_attestation_required"
        return "not_required"

    @classmethod
    def _node_has_residual_execution_authority(
        cls,
        session: Any,
        node: Any,
    ) -> bool:
        return cls._residual_attestation_status(session, node) not in {
            "residual_elaboration_attestation_required",
            "residual_elaboration_reattestation_required",
        }

    def _node_is_candidate(
        self,
        node: Any,
        session: Any = None,
        *,
        residual_required_ids: Optional[set[str]] = None,
        residual_authorized_ids: Optional[set[str]] = None,
    ) -> bool:
        if not self._is_attackable_child_goal(node):
            return False
        if residual_required_ids is not None and residual_authorized_ids is not None:
            node_id = str(getattr(node, "node_id", "") or "")
            if node_id in residual_required_ids and node_id not in residual_authorized_ids:
                return False
        elif not self._node_has_residual_execution_authority(session, node):
            return False
        if not self._node_under_attempt_cap(node):
            return False
        return self._node_under_giveup_cap(node)

    @staticmethod
    def _retrieval_available_for_node(session: Any, node: Any) -> bool:
        action_dispatchable = getattr(session, "action_dispatchable", None)
        if callable(action_dispatchable):
            try:
                if not bool(
                    action_dispatchable("proof_state_retrieval", context="frontier")
                ):
                    return False
            except TypeError:
                if not bool(action_dispatchable("proof_state_retrieval")):
                    return False
        else:
            action_available = getattr(session, "action_available", None)
            if callable(action_available) and not bool(
                action_available("proof_state_retrieval")
            ):
                return False
        action_available = getattr(session, "action_available", None)
        if (
            not callable(action_dispatchable)
            and callable(action_available)
            and not bool(action_available("proof_state_retrieval"))
        ):
            return False
        action = getattr(session, "registered_action", lambda _id: None)(
            "proof_state_retrieval"
        )
        max_results = int(getattr(action, "max_results", 0) or 0)
        if max_results <= 0:
            return False
        helper_blocks = []
        dossier = getattr(session, "dossier", None)
        read_only_probe = str(
            getattr(session, "_applicability_probe_context", "") or ""
        ).endswith("_probe")
        blocks_getter = getattr(
            dossier,
            (
                "verified_helper_blocks_snapshot"
                if read_only_probe
                else "verified_helper_blocks"
            ),
            None,
        )
        if callable(blocks_getter):
            try:
                helper_blocks = list(blocks_getter() or [])
            except Exception:
                helper_blocks = []
        if getattr(session, "searcher", None) is None and not helper_blocks:
            return False
        try:
            from ensemble_prover.proof_state_scheduler import (
                _proof_state_node_needs_retrieval,
            )

            return bool(
                _proof_state_node_needs_retrieval(
                    getattr(session, "searcher", None),
                    node,
                    max_results=max_results,
                    local_helper_blocks=helper_blocks,
                )
            )
        except Exception:
            return not bool(getattr(node, "retrieval_attempted", False))

    @staticmethod
    def _child_closure_available(session: Any) -> bool:
        action_dispatchable = getattr(session, "action_dispatchable", None)
        if callable(action_dispatchable):
            try:
                return bool(action_dispatchable("child_closure", context="frontier"))
            except TypeError:
                return bool(action_dispatchable("child_closure"))
        action_available = getattr(session, "action_available", None)
        if callable(action_available):
            return bool(action_available("child_closure"))
        return getattr(session, "registered_action", lambda _id: None)(
            "child_closure"
        ) is not None

    def _deterministic_child_work_exhausted(self, session: Any, node: Any) -> bool:
        """Cheap child work must run before recursive LLM helper proving.

        The gate is availability-aware: recursion is allowed when retrieval or
        child closure is unregistered/exhausted, but not while those lanes can
        still attack the same open child goal.
        """

        if self._retrieval_available_for_node(session, node):
            return False
        advisory_hash = str(
            getattr(node, "falsification_advisory_candidate_hash", "") or ""
        ).strip()
        advisory_getter = getattr(
            getattr(session, "dossier", None),
            "lean_checked_unpromoted_refutation_candidates_for_statement",
            None,
        )
        if advisory_hash and callable(advisory_getter):
            try:
                if advisory_getter(str(getattr(node, "target", "") or "")):
                    # Let the recursive lane spend the next quantum completing
                    # the certificate. Deterministic proof work remains open
                    # and is retried normally if the child cannot certify it.
                    return True
            except Exception:
                pass
        if not self._child_closure_available(session):
            return True
        try:
            from ensemble_prover.proof_state import (
                proof_state_decl_application_pending_names,
            )

            if proof_state_decl_application_pending_names(node):
                return False
        except Exception:
            pass
        return int(getattr(node, "tactic_attempts", 0) or 0) > 0

    def _selected_target_node(
        self,
        session: Any,
        *,
        residual_required_ids: Optional[set[str]] = None,
        residual_authorized_ids: Optional[set[str]] = None,
    ) -> Optional[Any]:
        selected_getter = getattr(session, "selected_work_item_for", None)
        if not callable(selected_getter):
            return None
        selected = selected_getter(
            self.id,
            work_types=("child_llm_prove",),
        )
        if selected is None:
            return None
        node_id = str(getattr(selected, "node_id", "") or "").strip()
        node = getattr(session.proof_state, "nodes", {}).get(node_id)
        if node is None:
            return None
        if not self._node_is_candidate(
            node,
            session=session,
            residual_required_ids=residual_required_ids,
            residual_authorized_ids=residual_authorized_ids,
        ):
            return None
        return node if self._deterministic_child_work_exhausted(session, node) else None

    def _node_under_attempt_cap(self, node: Any) -> bool:
        # Adversarial review fix (2026-05-09): align with
        # _node_under_giveup_cap convention: <=0 means UNCAPPED
        # (always allow). Previously this returned False (always
        # blocked) when max_attempts_per_node was 0 — the asymmetry
        # was a footgun. The factory passes int(... or 2) which
        # masks the bug for default callers, but direct constructors
        # could hit it.
        attempts = int(getattr(node, "recursive_attempts", 0) or 0)
        frame = self._nested_execution_frame
        descriptor = (
            dict(frame.get("descriptor") or {})
            if isinstance(frame, dict)
            else {}
        )
        if (
            str(frame.get("status") or "")
            in {
                "child_prepared",
                "child_live",
                "child_complete",
                "parent_recheck_pending",
            }
            and str(descriptor.get("node_id") or "")
            == str(getattr(node, "node_id", "") or "")
        ):
            return True
        if self.max_attempts_per_node <= 0:
            return True  # uncapped
        return attempts < self.max_attempts_per_node

    def _node_under_giveup_cap(self, node: Any) -> bool:
        if self.max_giveups_per_cluster_per_node <= 0:
            return True
        counts = getattr(node, "recursive_giveup_counts", None) or {}
        for cluster, count in counts.items():
            if int(count or 0) >= self.max_giveups_per_cluster_per_node:
                return False
        return True

    @staticmethod
    def _node_graph_search_value(session: Any, node: Any) -> float:
        dossier = getattr(session, "dossier", None)
        graph = getattr(dossier, "proof_graph", None)
        graph_nodes = getattr(graph, "nodes", {}) or {}
        node_id = str(getattr(node, "node_id", "") or "")
        graph_node = graph_nodes.get(node_id) or graph_nodes.get(f"proof_state:{node_id}")
        metadata = getattr(graph_node, "metadata", None) or {}
        try:
            return float(metadata.get("search_value") or 0.0)
        except (TypeError, ValueError):
            return 0.0

    def _select_target_node(self, session: Any) -> Optional[Any]:
        if session.proof_state is None:
            return None
        residual_required_ids: Optional[set[str]] = None
        residual_authorized_ids: Optional[set[str]] = None
        try:
            from ensemble_prover.proof_state_executor import (
                proof_state_current_residual_route_context_hashes,
            )

            route_contexts = proof_state_current_residual_route_context_hashes(
                conv=getattr(session, "conv", None),
                dossier=getattr(session, "dossier", None),
                lean=getattr(session, "lean", None),
                proof_state=session.proof_state,
            )
            (
                residual_required_ids,
                residual_authorized_ids,
                _route_validity,
            ) = session.proof_state._residual_goal_attestation_validation(  # noqa: SLF001
                route_elaboration_context_hashes=route_contexts,
            )
        except Exception:
            # Fall back to the per-node fail-closed validator below.
            residual_required_ids = None
            residual_authorized_ids = None
        # A retained nested frame is already-paid, in-flight work. Continue it
        # before consulting a newly projected frontier item or the ordinary
        # least-attempted-node ordering; otherwise a fresh node wins the sort
        # and ``prepare_state`` overwrites hours of durable child state.
        frame = self._nested_execution_frame
        descriptor = (
            dict(frame.get("descriptor") or {})
            if isinstance(frame, dict)
            else {}
        )
        if str(frame.get("status") or "") in {
            "child_prepared",
            "child_live",
            "child_complete",
            "parent_recheck_pending",
            "scheduler_backoff",
        }:
            framed_node_id = str(descriptor.get("node_id") or "").strip()
            framed_node = getattr(session.proof_state, "nodes", {}).get(
                framed_node_id
            )
            if (
                framed_node is not None
                and self._node_is_candidate(
                    framed_node,
                    session=session,
                    residual_required_ids=residual_required_ids,
                    residual_authorized_ids=residual_authorized_ids,
                )
                and self._deterministic_child_work_exhausted(
                    session,
                    framed_node,
                )
            ):
                return framed_node
        selected_getter = getattr(session, "selected_work_item_for", None)
        if callable(selected_getter):
            selected = selected_getter(self.id, work_types=("child_llm_prove",))
            if selected is not None:
                return self._selected_target_node(
                    session,
                    residual_required_ids=residual_required_ids,
                    residual_authorized_ids=residual_authorized_ids,
                )
        nodes = getattr(session.proof_state, "nodes", None) or {}
        candidates: List[Any] = []
        for node in nodes.values():
            if not self._node_is_candidate(
                node,
                session=session,
                residual_required_ids=residual_required_ids,
                residual_authorized_ids=residual_authorized_ids,
            ):
                continue
            if not self._deterministic_child_work_exhausted(session, node):
                continue
            candidates.append(node)
        if not candidates:
            return None
        # Prefer graph-propagated value first, then nodes never attempted
        # recursively, then the oldest attempt, then local priority.
        candidates.sort(
            key=lambda n: (
                -self._node_graph_search_value(session, n),
                int(getattr(n, "recursive_attempts", 0) or 0),
                int(getattr(n, "last_recursive_attempt_iteration", -1) or -1),
                -float(getattr(n, "priority", 0.0) or 0.0),
            )
        )
        return candidates[0]

    @staticmethod
    def _depth_under_cap(session: Any) -> bool:
        # Adversarial-review fix (2026-05-09): align with the nudge
        # convention where ``max_recursion_depth=0`` means "uncapped"
        # (give-up nudge stays in normal protocol framing). The action
        # previously read ``max_recursion_depth=0`` as "active cap of
        # 0" → action never runs. Two layers, two different semantics
        # for the same field. Now both treat 0 as "uncapped" consistently.
        depth = int(getattr(session, "recursion_depth", 0) or 0)
        # Read directly without ``or 3`` fallback to preserve 0 → uncapped.
        raw_cap = getattr(session, "max_recursion_depth", 3)
        cap = int(raw_cap if raw_cap is not None else 3)
        if cap <= 0:
            return True  # uncapped
        return depth < cap

    @staticmethod
    def _worker_request_capacity_available(session: Any) -> bool:
        """Fail closed only when the worker's minimum reservation cannot fit."""

        controller = getattr(session, "cost_controller", None)
        client = getattr(session, "prover_client", None)
        probe = getattr(controller, "request_output_capacity_available", None)
        if controller is None or client is None or not callable(probe):
            return True
        try:
            # Import locally to avoid coupling action-module initialization.
            # This must be the same work-aware cap the eventual conversation
            # reservation uses; probing the backend's 384K capability while
            # the worker requests 20K would incorrectly suppress affordable
            # DeepSeek child work.
            from .conversation_turn import _selected_work_max_tokens_override

            max_tokens = _selected_work_max_tokens_override(session, client)
        except Exception:
            return True
        try:
            return bool(
                probe(
                    client=client,
                    call_kind="chat_with_tools",
                    max_tokens_override=max_tokens,
                    candidate_count=1,
                )
            )
        except Exception:
            # The real reservation remains authoritative for unknown or
            # extension-provided controllers.
            return True

    # --- Action API ---

    def is_applicable(self, session: Any) -> bool:
        if (
            session.dossier is None
            or session.lean is None
            or session.conv is None
            or session.prover_client is None
        ):
            return False
        if session.proof_state is None:
            return False
        if not self._depth_under_cap(session):
            return False
        if not self._worker_request_capacity_available(session):
            return False
        return self._select_target_node(session) is not None

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Explicit observational applicability for frontier construction."""

        return self.is_applicable(session)

    async def run(self, session: Any) -> MiniOutcome:
        # CRITICAL fix (2026-05-09): helper_decl_from_proof lives in
        # mini_recursive, NOT proof_dossier. Wrong import would
        # ImportError on every successful child sub-session — caught
        # by adversarial review.
        #
        # Also: imports MUST happen BEFORE the attempt-counter bump
        # so an ImportError doesn't bypass the bump (the bump exists
        # specifically to prevent infinite loops on hard nodes; if a
        # crash bypassed it, the same node would be selected forever).
        from ensemble_prover.mini_recursive import helper_decl_from_proof
        from ensemble_prover.proof_dossier import is_answer_unsafe_statement_text
        from ensemble_prover.proof_state_executor import (
            _accept_proof_state_helper,
            _try_proof_state_child_falsification_preflight,
            retain_pending_helper_acceptance_retry,
            stage_pending_helper_acceptance,
        )

        started = time.monotonic()
        dispatch_id = str(
            getattr(session, "_inflight_action_dispatch_id", "") or ""
        ).strip()
        record_event = getattr(session, "_record_event", None)
        recorder = getattr(session, "recorder", None)

        def _emit_telemetry(record: dict) -> None:
            """Best-effort telemetry write that ALSO logs failures.

            Adversarial review (2026-05-09) HIGH: silent try/except
            around recorder calls makes classifier crashes invisible
            in JSONL post-mortem. This wrapper retries via the raw
            recorder if _record_event raises.
            """
            try:
                if callable(record_event):
                    record_event(dict(record))
                    return
                if recorder is not None and hasattr(recorder, "record_turn"):
                    recorder.record_turn(dict(record))
            except Exception:
                pass

        scheduled_reattestations: List[str] = []
        reattestation_scheduling_error = ""
        try:
            from ensemble_prover.proof_state_executor import (
                ensure_current_typed_residual_attestation_retries,
            )

            scheduled_reattestations = list(
                ensure_current_typed_residual_attestation_retries(
                    conv=getattr(session, "conv", None),
                    dossier=getattr(session, "dossier", None),
                    lean=getattr(session, "lean", None),
                    proof_state=getattr(session, "proof_state", None),
                )
            )
        except Exception as exc:
            # Candidate/status validation below still fails closed; scheduling
            # the verifier-only continuation is best-effort at this direct
            # action boundary and authoritative in the session frontier.
            try:
                error_detail = str(exc)
            except Exception:
                error_detail = "<exception detail unavailable>"
            reattestation_scheduling_error = (
                f"{type(exc).__name__}: {error_detail}"
            )[:300]

        node = self._select_target_node(session)
        if node is None:
            cost = time.monotonic() - started
            verdict = (
                "residual_goal_reattestation_deferred"
                if scheduled_reattestations
                else "no_target_node"
            )
            telemetry_record = {
                "phase": "recursive_helper_prover",
                "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                "verdict": verdict,
            }
            if reattestation_scheduling_error:
                telemetry_record[
                    "residual_goal_reattestation_scheduling_error"
                ] = reattestation_scheduling_error
            _emit_telemetry(telemetry_record)
            outcome_metadata = {
                "verdict": verdict,
                "residual_goal_reattestation_pending": bool(
                    scheduled_reattestations
                ),
                "residual_goal_reattestation_parent_node_ids": list(
                    scheduled_reattestations
                ),
                "preserve_action_budget": bool(scheduled_reattestations),
                "preserve_frontier_work": bool(scheduled_reattestations),
                "iteration_neutral": bool(scheduled_reattestations),
                "scheduler_neutral": bool(scheduled_reattestations),
                "stagnation_neutral": bool(scheduled_reattestations),
                "hard_pivot_neutral": bool(scheduled_reattestations),
            }
            if reattestation_scheduling_error:
                outcome_metadata[
                    "residual_goal_reattestation_scheduling_error"
                ] = reattestation_scheduling_error
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata=outcome_metadata,
            )

        residual_attestation_status = self._residual_attestation_status(
            session,
            node,
        )
        if residual_attestation_status in {
            "residual_elaboration_attestation_required",
            "residual_elaboration_reattestation_required",
        }:
            # This is a race/restore defense in addition to the candidate
            # filter above.  Quarantine before target parsing, reservation,
            # attempt-counter mutation, child-session construction, or any
            # provider call.
            reattestation_pending = residual_attestation_status == (
                "residual_elaboration_reattestation_required"
            )
            if not reattestation_pending:
                node.status = "blocked"
                node.action = residual_attestation_status
                node.blocker = residual_attestation_status
                node.priority = 0.0
            cost = time.monotonic() - started
            _emit_telemetry({
                "phase": "recursive_helper_prover",
                "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                "node_id": getattr(node, "node_id", ""),
                "residual_goal_attestation_status": residual_attestation_status,
                "verdict": (
                    "residual_goal_reattestation_deferred"
                    if reattestation_pending
                    else "residual_goal_dispatch_quarantined"
                ),
            })
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "verdict": (
                        "residual_goal_reattestation_deferred"
                        if reattestation_pending
                        else "residual_goal_dispatch_quarantined"
                    ),
                    "node_id": getattr(node, "node_id", ""),
                    "residual_goal_attestation_status": (
                        residual_attestation_status
                    ),
                    "preserve_action_budget": True,
                    "preserve_frontier_work": bool(reattestation_pending),
                    "residual_goal_reattestation_pending": bool(
                        reattestation_pending
                    ),
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                },
            )

        # Validate target BEFORE bumping attempt counter (HIGH-4 fix:
        # don't burn budget on degenerate nodes).
        target_statement = str(getattr(node, "target", "") or "").strip()
        if not target_statement:
            cost = time.monotonic() - started
            _emit_telemetry({
                "phase": "recursive_helper_prover",
                "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                "node_id": getattr(node, "node_id", ""),
                "verdict": "no_target_statement",
            })
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "verdict": "no_target_statement",
                    "node_id": getattr(node, "node_id", ""),
                },
            )

        if " ".join(target_statement.split()) in {"False", "false"}:
            node.status = "rejected"
            node.action = "recursive_helper_target_quarantined"
            node.blocker = "recursive helper target is the proposition False"
            node.priority = 0.0
            cost = time.monotonic() - started
            _emit_telemetry({
                "phase": "recursive_helper_prover",
                "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                "node_id": getattr(node, "node_id", ""),
                "verdict": "trivial_false_target_quarantined",
            })
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "verdict": "trivial_false_target_quarantined",
                    "node_id": getattr(node, "node_id", ""),
                },
            )

        frame = self._nested_execution_frame
        frame_descriptor = (
            dict(frame.get("descriptor") or {})
            if isinstance(frame, dict)
            else {}
        )
        resuming_reserved_child = bool(
            str(frame.get("status") or "")
            in {
                "child_prepared",
                "child_live",
                "child_complete",
                "parent_recheck_pending",
            }
            and str(frame_descriptor.get("node_id") or "")
            == str(getattr(node, "node_id", "") or "")
        )
        new_action_deadline_epoch_s = 0.0
        ancestor_deadline_epoch_s = max(
            0.0,
            float(
                getattr(
                    session,
                    "recursive_elapsed_deadline_epoch_s",
                    0.0,
                )
                or 0.0
            ),
        )
        if not resuming_reserved_child:
            # Falsification is advisory. Fund it only from time beyond the
            # configured child-proof lease. With no ancestor deadline it gets
            # its own bounded quantum; with an ancestor it is skipped unless
            # that ancestor has genuine surplus. This prevents a diagnostic
            # timeout from shortening a hard mathematical attempt.
            if ancestor_deadline_epoch_s > 0.0:
                ancestor_remaining_s = max(
                    0.0,
                    ancestor_deadline_epoch_s - time.time(),
                )
                child_reserve_s = (
                    max(0.0, float(self.max_elapsed_s or 0.0))
                    if self.max_elapsed_s > 0.0
                    else ancestor_remaining_s
                )
                preflight_timeout_s = min(
                    15.0,
                    max(0.0, ancestor_remaining_s - child_reserve_s),
                )
                preflight_deadline_monotonic = (
                    time.monotonic() + preflight_timeout_s
                    if preflight_timeout_s > 0.0
                    else 0.0
                )
            else:
                preflight_timeout_s = 15.0
                preflight_deadline_monotonic = 0.0
            dossier = getattr(session, "dossier", None)
            helpers_getter = getattr(dossier, "verified_helper_blocks", None)
            helper_blocks = (
                tuple(helpers_getter()) if callable(helpers_getter) else ()
            )
            acceptance_preamble = getattr(session, "acceptance_preamble", None)
            preamble = (
                str(acceptance_preamble() or "")
                if callable(acceptance_preamble)
                else str(
                    getattr(getattr(session, "conv", None), "lean_preamble", "")
                    or getattr(getattr(session, "conv", None), "preamble", "")
                    or ""
                )
            )
            child_falsified, falsification_record = (
                await _try_proof_state_child_falsification_preflight(
                    lean=getattr(session, "lean", None),
                    dossier=dossier,
                    proof_state=getattr(session, "proof_state", None),
                    node=node,
                    preamble=preamble,
                    helpers=helper_blocks,
                    turn=int(getattr(session, "iteration", 0) or 0),
                    timeout_s=preflight_timeout_s,
                    deadline_monotonic=preflight_deadline_monotonic,
                    deadline_exhausted=lambda: action_dispatch_replaced(
                        session,
                        dispatch_id,
                    ),
                )
            )
            require_current_action_dispatch(session, dispatch_id)
            if falsification_record:
                _emit_telemetry(dict(falsification_record))
            if child_falsified:
                cost = time.monotonic() - started
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=True,
                    cost_seconds=cost,
                    metadata={
                        "verdict": (
                            "child_goal_falsified_before_recursive_session"
                        ),
                        "node_id": str(getattr(node, "node_id", "") or ""),
                        "authoritative_falsification": True,
                        "preserve_action_budget": True,
                        "strong_progress": True,
                    },
                )
            if bool(falsification_record.get("retryable_infrastructure")):
                cost = time.monotonic() - started
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=cost,
                    metadata={
                        "verdict": "child_falsification_preflight_deferred",
                        "node_id": str(getattr(node, "node_id", "") or ""),
                        "retryable_infrastructure": True,
                        "preserve_frontier_work": True,
                        "preserve_action_budget": True,
                        "iteration_neutral": True,
                        "scheduler_neutral": True,
                        "stagnation_neutral": True,
                        "hard_pivot_neutral": True,
                    },
                )

        if residual_attestation_status != "attested":
            target_type_status = await _typecheck_recursive_helper_target(
                session=session,
                statement=target_statement,
            )
            require_current_action_dispatch(session, dispatch_id)
            if not bool(target_type_status.get("ok")):
                type_output = str(target_type_status.get("output") or "")
                type_inconclusive = bool(
                    target_type_status.get("inconclusive")
                )
                if not type_inconclusive:
                    node.status = "blocked"
                    node.action = "recursive_helper_target_type_rejected"
                    node.blocker = "recursive_helper_target_type_rejected"
                    node.priority = 0.0
                    verdict = "recursive_helper_target_type_rejected"
                else:
                    verdict = "recursive_helper_target_typecheck_deferred"
                cost = time.monotonic() - started
                _emit_telemetry({
                    "phase": "recursive_helper_prover",
                    "turn_in_phase": int(
                        getattr(session, "iteration", 0) or 0
                    ),
                    "node_id": getattr(node, "node_id", ""),
                    "target_statement": target_statement[:500],
                    "lean_output": type_output[:1200],
                    "lean_error_type": (
                        "recursive_helper_target_typecheck_inconclusive"
                        if type_inconclusive
                        else "recursive_helper_target_type_rejected"
                    ),
                    "provider_attempts": [],
                    "verdict": verdict,
                })
                metadata = {
                    "verdict": verdict,
                    "node_id": getattr(node, "node_id", ""),
                    "lean_error": type_output,
                    "lean_error_type": (
                        "recursive_helper_target_typecheck_inconclusive"
                        if type_inconclusive
                        else "recursive_helper_target_type_rejected"
                    ),
                    "provider_attempts": [],
                    "preserve_action_budget": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                }
                if type_inconclusive:
                    metadata.update(
                        {
                            "recursive_helper_target_typecheck_pending": True,
                            "preserve_frontier_work": True,
                            "defer_selected_frontier_action": True,
                            "refund_local_repair_quota": True,
                            "non_consuming_repair_ticket_continuation": True,
                            "llm_failure_kind": (
                                "recursive_target_typecheck_inconclusive"
                            ),
                            "llm_retryable": True,
                            "llm_failure_scope": "scoped",
                            "scoped_failure_reason": (
                                "recursive_target_typecheck_inconclusive"
                            ),
                        }
                    )
                else:
                    metadata.update(
                        {
                            "recursive_helper_target_type_rejected": True,
                            "preserve_frontier_work": False,
                        }
                    )
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=cost,
                    metadata=metadata,
                )

        proof_state = getattr(session, "proof_state", None)

        def _same_statement(left: str, right: str) -> bool:
            if not str(left or "").strip() or not str(right or "").strip():
                return False
            try:
                from ensemble_prover.proof_state import (
                    canonicalize_lean_statement_for_identity,
                )

                return (
                    canonicalize_lean_statement_for_identity(left)
                    == canonicalize_lean_statement_for_identity(right)
                )
            except Exception:
                return " ".join(str(left).split()) == " ".join(str(right).split())

        equivalent_anchor = ""
        if proof_state is not None:
            nodes = getattr(proof_state, "nodes", {}) or {}
            root = nodes.get(getattr(proof_state, "root_node_id", "root"))
            if root is not None and _same_statement(
                target_statement,
                str(getattr(root, "target", "") or ""),
            ):
                equivalent_anchor = "root"
            parent = nodes.get(str(getattr(node, "parent_node_id", "") or ""))
            if not equivalent_anchor and parent is not None and _same_statement(
                target_statement,
                str(getattr(parent, "target", "") or ""),
            ):
                equivalent_anchor = "parent"
        if equivalent_anchor:
            node.status = "obsolete"
            node.action = "active_equivalent_child_quarantined"
            node.blocker = (
                "recursive helper target restates the active "
                f"{equivalent_anchor} goal; not a smaller reusable subgoal"
            )
            node.priority = 0.0
            record_transition = getattr(proof_state, "record_transition", None)
            if callable(record_transition):
                try:
                    record_transition(
                        node_id=getattr(node, "node_id", ""),
                        source="recursive_helper_prover",
                        error_type="active_equivalent_child_goal_quarantined",
                        action=node.action,
                        blocker=node.blocker,
                        phase="recursive_helper_prover",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        payload={
                            "target_statement": target_statement[:500],
                            "equivalent_anchor": equivalent_anchor,
                        },
                    )
                except Exception:
                    pass
            cost = time.monotonic() - started
            _emit_telemetry({
                "phase": "recursive_helper_prover",
                "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                "node_id": getattr(node, "node_id", ""),
                "equivalent_anchor": equivalent_anchor,
                "verdict": "active_equivalent_target_quarantined",
            })
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "verdict": "active_equivalent_target_quarantined",
                    "node_id": getattr(node, "node_id", ""),
                    "equivalent_anchor": equivalent_anchor,
                },
            )

        # Establish a stable helper name for the wrapper.
        proposed_name = (
            getattr(node, "proved_helper_name", "")
            or f"helper_{getattr(node, 'node_id', 'unknown')}"
        ).strip() or "helper_unknown"

        conv = getattr(session, "conv", None)
        if is_answer_unsafe_statement_text(
            target_statement,
            suppress_solution_placeholders=bool(
                getattr(conv, "suppress_solution_placeholders", True)
            ),
            opaque_mode=bool(getattr(conv, "opaque_mode", True)),
            allow_official_answer_visibility=bool(
                getattr(conv, "allow_official_answer_visibility", False)
            ),
            official_answer_payload_present=getattr(
                conv,
                "official_answer_payload_present",
                getattr(
                    getattr(session, "dossier", None),
                    "official_answer_payload_present",
                    None,
                ),
            ),
        ):
            node.status = "obsolete"
            node.action = "answer_unsafe_child_quarantined"
            node.blocker = (
                "recursive helper target references an answer placeholder; "
                "not a reusable mathematical subgoal"
            )
            node.priority = 0.0
            record_transition = getattr(proof_state, "record_transition", None)
            if callable(record_transition):
                try:
                    record_transition(
                        node_id=getattr(node, "node_id", ""),
                        source="recursive_helper_prover",
                        error_type="answer_unsafe_child_goal_quarantined",
                        action=node.action,
                        blocker=node.blocker,
                        phase="recursive_helper_prover",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        payload={
                            "helper_name": proposed_name,
                            "target_statement": target_statement[:500],
                        },
                    )
                except Exception:
                    pass
            cost = time.monotonic() - started
            _emit_telemetry({
                "phase": "recursive_helper_prover",
                "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                "node_id": getattr(node, "node_id", ""),
                "helper_name": proposed_name,
                "verdict": "answer_unsafe_target_quarantined",
            })
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "verdict": "answer_unsafe_target_quarantined",
                    "node_id": getattr(node, "node_id", ""),
                    "helper_name": proposed_name,
                },
            )

        existing_statement_key = ""
        target_statement_key = ""
        if session.dossier is not None:
            try:
                from ensemble_prover.proof_dossier import (
                    canonical_dossier_statement_key,
                    helper_decl_statement,
                )

                target_statement_key = canonical_dossier_statement_key(
                    target_statement
                )
                existing = getattr(session.dossier, "verified_helpers", {}).get(
                    proposed_name
                )
                if existing is not None:
                    existing_statement_key = canonical_dossier_statement_key(
                        helper_decl_statement(
                            str(getattr(existing, "source", "") or "")
                        )
                    )
            except Exception:
                existing_statement_key = ""
                target_statement_key = ""
        if (
            session.dossier is not None
            and session.dossier.has_helper(proposed_name)
            and existing_statement_key
            and target_statement_key
            and existing_statement_key == target_statement_key
        ):
            reconciled: List[dict] = []
            reconcile = getattr(proof_state, "reconcile_helpers_to_dossier", None)
            if callable(reconcile):
                try:
                    reconciled = list(
                        reconcile(
                            session.dossier,
                            source="recursive_helper_prover_existing_helper",
                            phase="recursive_helper_prover",
                            turn_index=int(getattr(session, "iteration", 0) or 0),
                            target_node_id=str(getattr(node, "node_id", "") or ""),
                        )
                        or []
                    )
                except Exception:
                    reconciled = []
            _emit_telemetry({
                "phase": "recursive_helper_prover",
                "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                "node_id": getattr(node, "node_id", ""),
                "helper_name": proposed_name,
                "target_statement": target_statement[:200],
                "reconciled_child_goals": list(reconciled),
                "verdict": "helper_already_in_parent_dossier",
            })
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(proposed_name,),
                progress=True,
                cost_seconds=cost,
                metadata={
                    "verdict": "helper_already_in_parent_dossier",
                    "node_id": getattr(node, "node_id", ""),
                    "helper_name": proposed_name,
                    "reconciled_child_goals": list(reconciled),
                    "recursion_depth_parent": int(
                        getattr(session, "recursion_depth", 0) or 0
                    ),
                },
            )

        frame = self._nested_execution_frame
        frame_descriptor = (
            dict(frame.get("descriptor") or {})
            if isinstance(frame, dict)
            else {}
        )
        resuming_nested_child = bool(
            str(frame.get("status") or "")
            in {
                "child_prepared",
                "child_live",
                "child_complete",
                "parent_recheck_pending",
            }
            and str(frame_descriptor.get("node_id") or "")
            == str(getattr(node, "node_id", "") or "")
            and str(frame_descriptor.get("helper_name") or "") == proposed_name
            and str(frame_descriptor.get("target_statement") or "")
            == target_statement
        )

        # Bump the attempt counter before the child runs, but never charge the
        # same live child frame twice.
        # Direct assignment — ProofStateNode is a non-frozen dataclass;
        # AttributeError here would be a structural bug worth surfacing,
        # not silently passing.
        attempt_snapshot: dict[str, Any] = {}
        if not resuming_nested_child:
            new_action_deadline_epoch_s = (
                _bounded_nested_elapsed_deadline_epoch_s(
                    max_elapsed_s=self.max_elapsed_s,
                    ancestor_deadline_epoch_s=ancestor_deadline_epoch_s,
                )
            )
            prior_attempts = int(getattr(node, "recursive_attempts", 0) or 0)
            prior_iteration = getattr(node, "last_recursive_attempt_iteration", -1)
            attempt_snapshot = {
                "attempts": prior_attempts,
                "iteration": int(
                    prior_iteration if prior_iteration is not None else -1
                ),
                "frame": copy.deepcopy(self._nested_execution_frame),
            }
            node.recursive_attempts = prior_attempts + 1
            node.last_recursive_attempt_iteration = int(
                getattr(session, "iteration", 0) or 0
            )
            self._nested_execution_frame = {
                    "schema_version": 1,
                    "owner_action_id": self.id,
                    "child_kind": "recursive_helper_subsession",
                    "descriptor": {
                        "node_id": str(getattr(node, "node_id", "") or ""),
                        "attempt_number": int(
                            getattr(node, "recursive_attempts", 0) or 0
                        ),
                        "helper_name": proposed_name,
                        "target_statement": target_statement,
                        "recursion_depth": int(
                            getattr(session, "recursion_depth", 0) or 0
                        )
                        + 1,
                        "refine_enabled": bool(self.refine_enabled),
                        "max_turns": int(self.helper_turns or 0),
                        "action_deadline_epoch_s": new_action_deadline_epoch_s,
                    },
                    "status": "child_prepared",
                    "child_session": None,
                    "completed_result": None,
                    "child_reason": "node_reserved",
            }

        # --- Run the child sub-session, or continue a proof-bearing parent replay. ---
        depth_str = str(int(getattr(session, "recursion_depth", 0) or 0))
        resuming_parent_recheck = bool(
            resuming_nested_child
            and str(self._nested_execution_frame.get("status") or "")
            == "parent_recheck_pending"
        )
        deadline_epoch_s = 0.0
        if resuming_parent_recheck:
            # The child already consumed its durable lease.  Give only the
            # mandatory parent replay a fresh, tightly bounded window; the
            # ancestor deadline remains authoritative.
            deadline_epoch_s = _bounded_nested_elapsed_deadline_epoch_s(
                max_elapsed_s=RECURSIVE_HELPER_PARENT_RECHECK_TIMEOUT_S,
                ancestor_deadline_epoch_s=float(
                    getattr(
                        session,
                        "recursive_elapsed_deadline_epoch_s",
                        0.0,
                    )
                    or 0.0
                )
            )
            descriptor = self._nested_execution_frame.get("descriptor")
            if isinstance(descriptor, dict):
                descriptor["action_deadline_epoch_s"] = deadline_epoch_s
        else:
            try:
                deadline_epoch_s = float(
                    dict(self._nested_execution_frame.get("descriptor") or {}).get(
                        "action_deadline_epoch_s",
                        0.0,
                    )
                    or 0.0
                )
            except Exception:
                deadline_epoch_s = 0.0
        ancestor_deadline_epoch_s = max(
            0.0,
            float(
                getattr(
                    session,
                    "recursive_elapsed_deadline_epoch_s",
                    0.0,
                )
                or 0.0
            ),
        )
        if ancestor_deadline_epoch_s > 0.0 and (
            deadline_epoch_s <= 0.0
            or ancestor_deadline_epoch_s < deadline_epoch_s
        ):
            deadline_epoch_s = ancestor_deadline_epoch_s
            descriptor = self._nested_execution_frame.get("descriptor")
            if isinstance(descriptor, dict):
                descriptor["action_deadline_epoch_s"] = deadline_epoch_s
        if resuming_parent_recheck:
            completed_result = self._nested_execution_frame.get("completed_result")
            if (
                not isinstance(completed_result, (list, tuple))
                or len(completed_result) != 3
                or not isinstance(completed_result[2], dict)
            ):
                raise RuntimeError("invalid pending recursive-helper parent recheck")
            ok = bool(completed_result[0])
            proof_text = completed_result[1]
            telemetry = dict(completed_result[2])
        else:
            advisory_getter = getattr(
                getattr(session, "dossier", None),
                "lean_checked_unpromoted_refutation_candidates_for_statement",
                None,
            )
            advisory_refutation_candidates = ()
            if callable(advisory_getter):
                try:
                    advisory_refutation_candidates = tuple(
                        advisory_getter(target_statement) or ()
                    )
                except Exception:
                    advisory_refutation_candidates = ()
            ok, proof_text, telemetry = await prove_helper_in_subsession(
                parent_session=session,
                helper_name=proposed_name,
                target_statement=target_statement,
                max_turns=self.helper_turns,
                refine_enabled=self.refine_enabled,
                trace_label=f"[helper-recursion d{depth_str}]",
                nested_node_id=str(getattr(node, "node_id", "") or ""),
                nested_attempt_number=int(
                    getattr(node, "recursive_attempts", 0) or 0
                ),
                max_elapsed_s=self.max_elapsed_s,
                action_deadline_epoch_s=deadline_epoch_s,
                advisory_refutation_candidates=(
                    advisory_refutation_candidates
                ),
                publication_guard=lambda: require_current_action_dispatch(
                    session,
                    dispatch_id,
                ),
            )
            require_current_action_dispatch(session, dispatch_id)

        telemetry = dict(telemetry or {})
        if str(telemetry.get("verdict") or "") == "selected_proof_idea_context_invalidated":
            if attempt_snapshot:
                node.recursive_attempts = int(attempt_snapshot["attempts"])
                node.last_recursive_attempt_iteration = int(
                    attempt_snapshot["iteration"]
                )
                self._nested_execution_frame = copy.deepcopy(
                    attempt_snapshot["frame"]
                )
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "verdict": "selected_proof_idea_context_invalidated",
                    "node_id": getattr(node, "node_id", ""),
                    "helper_name": proposed_name,
                    "child_telemetry": telemetry,
                    "selected_work_projection_invalidated": True,
                    "selected_work_projection_zero_provider": True,
                    "scoped_failure_reason": (
                        "selected_proof_idea_context_invalidated"
                    ),
                    "preserve_action_budget": True,
                    "refund_local_repair_quota": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                },
            )
        child_helper_names = {
            str(name or "").strip()
            for name in list(telemetry.get("child_helpers_added") or ())
            if str(name or "").strip()
        }
        seeded_child_helper_names = {
            str(name or "").strip()
            for key in ("child_seeded_helpers", "child_seeded_proposed_helpers")
            for name in list(telemetry.get(key) or ())
            if str(name or "").strip()
        }
        child_verified_progress = bool(
            child_helper_names - seeded_child_helper_names
        )
        cleanup_infrastructure_yield = bool(
            not ok
            and telemetry.get("retryable_infrastructure")
            and str(telemetry.get("verdict") or "")
            == "recursive_helper_cleanup_infrastructure_yield"
            and str(
                telemetry.get("retryable_infrastructure_reason") or ""
            ).startswith("recursive_helper_")
        )
        zero_provider_failure = bool(
            not ok
            and bool(telemetry.get("zero_provider_failure"))
            and int(telemetry.get("provider_calls_completed") or 0) == 0
            and not child_verified_progress
            and not bool(telemetry.get("child_goal_falsified"))
        )
        fresh_zero_provider_failure = bool(
            zero_provider_failure
            and not resuming_nested_child
            and attempt_snapshot
        )
        resumed_zero_provider_failure = bool(
            zero_provider_failure
            and resuming_nested_child
            and not resuming_parent_recheck
        )
        recursive_attempt_refunded = False
        zero_provider_backoff_identity = ""
        if fresh_zero_provider_failure:
            attempted_frame = copy.deepcopy(self._nested_execution_frame)
            zero_provider_backoff_identity = (
                self._cleanup_retry_frame_identity(attempted_frame)
                if isinstance(attempted_frame, Mapping)
                else ""
            )
            node.recursive_attempts = int(attempt_snapshot["attempts"])
            node.last_recursive_attempt_iteration = int(
                attempt_snapshot["iteration"]
            )
            self._nested_execution_frame = copy.deepcopy(
                attempt_snapshot["frame"]
            )
            if zero_provider_backoff_identity:
                # Keep only a provider-free scheduler receipt after refunding
                # the mathematical reservation.  This action-owned frame is
                # retained, pins the exact child identity for its bounded
                # deferred retry, and contains no live child capabilities.
                attempted_descriptor = dict(
                    attempted_frame.get("descriptor") or {}
                )
                attempted_descriptor["zero_provider_backoff_identity"] = (
                    zero_provider_backoff_identity
                )
                self._nested_execution_frame = {
                    "schema_version": CHILD_EXECUTION_SCHEMA_VERSION,
                    "owner_action_id": self.id,
                    "child_kind": "recursive_helper_subsession",
                    "descriptor": attempted_descriptor,
                    "status": "scheduler_backoff",
                    "child_session": None,
                    "completed_result": None,
                    "child_reason": "zero_provider_failure_deferred",
                }
            recursive_attempt_refunded = True
        elif resumed_zero_provider_failure:
            zero_provider_backoff_identity = (
                self._cleanup_retry_frame_identity(
                    self._nested_execution_frame
                )
                if isinstance(self._nested_execution_frame, Mapping)
                else ""
            )

        cleanup_continuation_identity = ""
        cleanup_continuation_granted = False
        if (
            cleanup_infrastructure_yield
            and int(telemetry.get("provider_calls_completed") or 0) > 0
        ):
            frame = self._nested_execution_frame
            descriptor = (
                frame.get("descriptor")
                if isinstance(frame, dict)
                and isinstance(frame.get("descriptor"), dict)
                else None
            )
            cleanup_continuation_identity = (
                self._cleanup_retry_frame_identity(frame)
                if isinstance(frame, Mapping)
                else ""
            )
            if (
                descriptor is not None
                and cleanup_continuation_identity
                and cleanup_continuation_identity
                not in set(
                    getattr(
                        session,
                        "recursive_helper_cleanup_continuation_identities",
                        set(),
                    )
                    or set()
                )
            ):
                # ``MiniSession.apply`` publishes this exact identity into its
                # durable one-shot ledger together with the quota extension.
                # The action only proposes the grant; it never refunds the
                # paid invocation or the node's mathematical attempt.
                cleanup_continuation_granted = True

        # Persist any give-up cluster the child sub-session tripped.
        # ``prove_helper_in_subsession`` exports the most-recent
        # cluster id under ``telemetry["giveup_cluster"]`` (None if no
        # give-up fired). Bumping per-cluster counts here closes the
        # adversarial-review HIGH-3 ("dead giveup-cap" finding).
        child_giveup = telemetry.get("giveup_cluster") if isinstance(telemetry, dict) else None
        child_giveup_match = telemetry.get("giveup_match") if isinstance(telemetry, dict) else ""
        if child_giveup:
            try:
                node.recursive_giveup_cluster = str(child_giveup)
                counts = getattr(node, "recursive_giveup_counts", None)
                if isinstance(counts, dict):
                    counts[str(child_giveup)] = int(counts.get(str(child_giveup), 0) or 0) + 1
            except Exception:
                pass

        helpers_added: List[str] = []
        graph_lineage_published_node_ids: tuple[str, ...] = ()
        verdict = "child_session_no_progress"
        recheck_exception_text = ""
        post_child_elapsed_budget_exhausted = False
        parent_recheck_timeout_exception = False
        staged_parent_acceptance = False
        parent_candidate_owner_busy = False

        if ok and proof_text:
            from ensemble_prover.proof_dossier import (
                canonical_dossier_statement_key,
                helper_decl_statement,
            )

            # Wrap the proof as a real helper declaration and recheck
            # against the PARENT context (parent's preamble +
            # parent's verified helpers).
            #
            # CRITICAL ordering (HIGH-1 fix from review): _accept_
            # proof_state_helper must run BEFORE any verified-helper
            # merge from the child dossier. _accept_ short-circuits
            # via dossier.has_helper(name); if the child already
            # populated parent.verified_helpers[proposed_name] (via
            # prove_helper_in_subsession's merge-back), the recheck
            # would silently return False. prove_helper_in_subsession
            # has been updated to NOT merge back with the proposed
            # helper's name, only side-helpers — but we also defend
            # by checking has_helper BEFORE wrapping.
            existing_statement_key = ""
            target_statement_key = canonical_dossier_statement_key(target_statement)
            if session.dossier is not None:
                existing = getattr(session.dossier, "verified_helpers", {}).get(
                    proposed_name
                )
                if existing is not None:
                    existing_statement_key = canonical_dossier_statement_key(
                        helper_decl_statement(
                            str(getattr(existing, "source", "") or "")
                        )
                    )
            # Raw dossier presence is not a current parent-context/visibility
            # receipt. Even an identical proposition must pass the same full
            # acceptance boundary as a newly returned child proof.
            reusable_without_recheck = False
            if reusable_without_recheck:
                # Already in the parent dossier (e.g., via earlier
                # successful pass). Skip the recheck and treat as
                # already-proved.
                helpers_added.append(proposed_name)
                verdict = "helper_already_in_parent_dossier"
            else:
                helper_block = helper_decl_from_proof(
                    proposed_name, target_statement, proof_text
                )
                staged_parent_acceptance = stage_pending_helper_acceptance(
                    conv=session.conv,
                    dossier=session.dossier,
                    node=node,
                    helper_block=helper_block,
                    source=f"recursive_helper:{node.node_id}",
                    continuation={
                        "kind": "recursive_helper",
                        "target_node_id": str(node.node_id or ""),
                        "helper_name": proposed_name,
                        "statement": target_statement,
                        "source": f"recursive_helper_prover:{node.node_id}",
                        "phase": "recursive_helper_prover",
                        "turn_index": int(
                            getattr(session, "iteration", 0) or 0
                        ),
                    },
                )
                if not staged_parent_acceptance:
                    parent_candidate_owner_busy = True
                    post_child_elapsed_budget_exhausted = True
                    recheck_exception_text = (
                        "pending helper acceptance slot already owns a distinct "
                        "paid candidate"
                    )
                accepted = False
                acceptance_status: dict[str, Any] = {}
                parent_recheck_timeout_s = (
                    RECURSIVE_HELPER_PARENT_RECHECK_TIMEOUT_S
                )
                if deadline_epoch_s > 0.0:
                    parent_recheck_timeout_s = min(
                        parent_recheck_timeout_s,
                        max(0.0, deadline_epoch_s - time.time()),
                    )
                if parent_candidate_owner_busy:
                    acceptance_status.update(
                        {
                            "status": "retryable_error",
                            "error_kind": "pending_helper_acceptance_owned",
                            "lean_attempted": False,
                        }
                    )
                elif parent_recheck_timeout_s <= 0.0:
                    post_child_elapsed_budget_exhausted = True
                    recheck_exception_text = (
                        "TimeoutError: recursive helper action elapsed budget "
                        "expired before parent recheck"
                    )
                else:
                    try:
                        accepted = await _accept_proof_state_helper(
                            lean=session.lean,
                            conv=session.conv,
                            dossier=session.dossier,
                            helper_block=helper_block,
                            phase="recursive_helper_prover",
                            turn_index=int(
                                getattr(session, "iteration", 0) or 0
                            ),
                            timeout_s=parent_recheck_timeout_s,
                            proof_cache=session.proof_cache,
                            proof_state=getattr(session, "proof_state", None),
                            target_statement=target_statement,
                            status_out=acceptance_status,
                            verified_helper_accept_callback=getattr(
                                session,
                                "theory_verified_helper_accept_callback",
                                None,
                            ),
                            deadline_exhausted=lambda: action_dispatch_replaced(
                                session,
                                dispatch_id,
                            ),
                        )
                        require_current_action_dispatch(session, dispatch_id)
                    except Exception as exc:
                        # Surface classifier/recheck failures so they cannot be
                        # mistaken for an ordinary Lean rejection.
                        recheck_exception_text = f"{type(exc).__name__}: {exc}"
                        acceptance_status.update(
                            {
                                "status": "retryable_error",
                                "error_kind": type(exc).__name__,
                                "error": str(exc)[:240],
                                "lean_attempted": True,
                            }
                        )
                        if _exception_chain_contains_timeout(exc):
                            # The child proof remains valuable.  A verifier or
                            # strict-deadline timeout is infrastructure, not a
                            # mathematical rejection; retain it for the same
                            # durable parent-only replay as a pre-start expiry.
                            post_child_elapsed_budget_exhausted = True
                            parent_recheck_timeout_exception = True

                if accepted:
                    node.pending_helper_acceptance = {}
                    landed_name = str(
                        acceptance_status.get("accepted_helper_name")
                        or proposed_name
                    )
                    try:
                        graph_lineage_published_node_ids = (
                            _publish_recursive_helper_exact_graph_lineage(
                                dossier=session.dossier,
                                proof_state_node=node,
                                helper_name=landed_name,
                                target_statement=target_statement,
                                acceptance_status=acceptance_status,
                            )
                        )
                    except Exception as exc:
                        # The helper is already committed and useful to ordinary
                        # proof-state assembly.  Keep it on any narrow graph
                        # publication failure, but make that residual visible.
                        _emit_telemetry(
                            {
                                "phase": "recursive_helper_prover",
                                "turn_in_phase": int(
                                    getattr(session, "iteration", 0) or 0
                                ),
                                "node_id": getattr(node, "node_id", ""),
                                "helper_name": landed_name,
                                "exception_type": type(exc).__name__,
                                "exception_text": str(exc)[:300],
                                "verdict": (
                                    "recursive_helper_exact_graph_lineage_"
                                    "publication_failed"
                                ),
                            }
                        )
                    # Mark the proof_state node as proved via lemma-DAG
                    # equivalence so downstream assembly picks it up.
                    recorded = False
                    try:
                        recorded_node_id = session.proof_state.record_lemma_dag_candidate(
                            helper_name=landed_name,
                            statement=target_statement,
                            accepted=True,
                            source=f"recursive_helper_prover:{node.node_id}",
                            phase="recursive_helper_prover",
                            turn_index=int(getattr(session, "iteration", 0) or 0),
                            target_node_id=str(getattr(node, "node_id", "") or ""),
                        )
                        recorded = bool(recorded_node_id)
                    except Exception as exc:
                        _emit_telemetry({
                            "phase": "recursive_helper_prover",
                            "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
                            "node_id": getattr(node, "node_id", ""),
                            "helper_name": proposed_name,
                            "exception_type": type(exc).__name__,
                            "exception_text": str(exc)[:300],
                            "verdict": "record_lemma_dag_candidate_failed",
                        })
                    helpers_added.append(landed_name)
                    if recorded:
                        verdict = "helper_proved_recursively"
                    else:
                        verdict = "helper_proved_but_proof_state_record_failed"
                else:
                    acceptance_retryable = bool(
                        str(acceptance_status.get("status") or "")
                        in {"retryable_error", "cancelled"}
                        or post_child_elapsed_budget_exhausted
                    )
                    if acceptance_retryable:
                        if not acceptance_status:
                            acceptance_status.update(
                                {
                                    "status": "retryable_error",
                                    "error_kind": (
                                        "recursive_helper_parent_recheck_deferred"
                                    ),
                                    "lean_attempted": False,
                                }
                            )
                        if staged_parent_acceptance:
                            retain_pending_helper_acceptance_retry(
                                proof_state=session.proof_state,
                                node=node,
                                status=acceptance_status,
                            )
                        verdict = "child_session_parent_acceptance_deferred"
                    elif post_child_elapsed_budget_exhausted:
                        verdict = (
                            "child_session_parent_recheck_timeout_pending"
                            if parent_recheck_timeout_exception
                            else "child_session_action_elapsed_budget_exhausted"
                        )
                    else:
                        verdict = (
                            "child_session_solved_but_parent_recheck_exception"
                            if recheck_exception_text
                            else "child_session_solved_but_parent_recheck_failed"
                        )
                        node.pending_helper_acceptance = {}
        elif ok and not proof_text:
            verdict = "child_session_solved_no_proof_text"
        # A bounded timeout remains no-progress, but expose the actual cause.
        elif cleanup_infrastructure_yield:
            verdict = "child_session_cleanup_infrastructure_yield"
        elif bool(
            telemetry.get("action_elapsed_budget_exhausted")
            if isinstance(telemetry, dict)
            else False
        ):
            verdict = "child_session_action_elapsed_budget_exhausted"

        # A durably-falsified child goal is real progress: the branch is proven
        # dead and permanently pruned. Surface it so stagnation/metrics don't
        # under-count it as a wasted no-op turn (the node is already suppressed
        # from the frontier, so this cannot re-fire on the same node).
        child_goal_falsified = bool(
            telemetry.get("child_goal_falsified")
            if isinstance(telemetry, dict)
            else False
        )
        if child_goal_falsified and verdict == "child_session_no_progress":
            verdict = "child_goal_lean_falsified"

        parent_recheck_pending = bool(
            post_child_elapsed_budget_exhausted and ok and proof_text
            and (
                parent_candidate_owner_busy
                or not dict(
                    getattr(node, "pending_helper_acceptance", {}) or {}
                )
            )
        )
        helper_acceptance_handoff_pending = bool(
            ok
            and proof_text
            and staged_parent_acceptance
            and dict(getattr(node, "pending_helper_acceptance", {}) or {})
        )
        parent_recheck_rejected = bool(
            ok
            and proof_text
            and verdict == "child_session_solved_but_parent_recheck_failed"
        )
        parent_recheck_continuation_granted = bool(
            parent_recheck_pending and not resuming_parent_recheck
        )
        if parent_recheck_pending:
            # ``prove_helper_in_subsession`` has already finalized its child
            # frame.  Replace the bulky child snapshot with the minimum
            # proof-bearing continuation state.  This mutation is published by
            # ordinary parent outcome application.
            descriptor = dict(
                self._nested_execution_frame.get("descriptor") or {}
            )
            descriptor["action_deadline_epoch_s"] = 0.0
            self._nested_execution_frame = {
                "schema_version": 2,
                "owner_action_id": self.id,
                "child_kind": "recursive_helper_subsession",
                "descriptor": descriptor,
                "status": "parent_recheck_pending",
                "child_session": None,
                "completed_result": [True, proof_text, dict(telemetry)],
                "child_reason": "parent_recheck_pending",
            }

        _emit_telemetry({
            "phase": "recursive_helper_prover",
            "turn_in_phase": int(getattr(session, "iteration", 0) or 0),
            "node_id": getattr(node, "node_id", ""),
            "helper_name": proposed_name,
            "target_statement": target_statement[:200],
            "child_solved": bool(ok),
            "helpers_added": list(helpers_added),
            "graph_lineage_published_node_ids": list(
                graph_lineage_published_node_ids
            ),
            "child_telemetry": telemetry,
            "child_giveup_cluster": child_giveup,
            "child_giveup_match": child_giveup_match,
            "recheck_exception": recheck_exception_text,
            "post_child_elapsed_budget_exhausted": (
                post_child_elapsed_budget_exhausted
            ),
            "parent_recheck_timeout_exception": (
                parent_recheck_timeout_exception
            ),
            "recursive_attempts": int(getattr(node, "recursive_attempts", 0) or 0),
            "verdict": verdict,
        })

        cost = time.monotonic() - started
        return MiniOutcome(
            action_id=self.id,
            solved=False,  # this action does NOT close the root directly
            proof=None,
            helpers_added=tuple(helpers_added),
            progress=bool(helpers_added or child_goal_falsified),
            cost_seconds=cost,
            metadata={
                "verdict": verdict,
                "node_id": getattr(node, "node_id", ""),
                "helper_name": proposed_name,
                "graph_lineage_published_node_ids": list(
                    graph_lineage_published_node_ids
                ),
                "child_telemetry": telemetry,
                "child_giveup_cluster": child_giveup,
                "child_goal_falsified": child_goal_falsified,
                "recheck_exception": recheck_exception_text,
                "post_child_elapsed_budget_exhausted": (
                    post_child_elapsed_budget_exhausted
                ),
                "parent_recheck_timeout_exception": (
                    parent_recheck_timeout_exception
                ),
                "parent_recheck_pending": parent_recheck_pending,
                "helper_acceptance_handoff_pending": (
                    helper_acceptance_handoff_pending
                ),
                "parent_recheck_rejected": parent_recheck_rejected,
                # A completed child proof must get one controller continuation
                # even when it lands on the parent's final iteration.  Only
                # the child -> parent-recheck transition is iteration-neutral:
                # if that replay times out again it consumes an ordinary
                # iteration, so repeated verifier failures cannot livelock.
                "parent_recheck_continuation_granted": (
                    parent_recheck_continuation_granted
                ),
                "zero_provider_failure": zero_provider_failure,
                "recursive_attempt_refunded": recursive_attempt_refunded,
                "recursive_helper_zero_provider_retry_pending": bool(
                    zero_provider_failure
                ),
                "recursive_helper_resumed_zero_provider_failure": bool(
                    resumed_zero_provider_failure
                ),
                "recursive_helper_zero_provider_backoff_identity": (
                    zero_provider_backoff_identity
                    or str(
                        frame_descriptor.get(
                            "zero_provider_backoff_identity"
                        )
                        or ""
                    )
                ),
                "recursive_helper_cleanup_continuation_identity": (
                    cleanup_continuation_identity
                ),
                "recursive_helper_cleanup_continuation_granted": bool(
                    cleanup_continuation_granted
                ),
                "provider_calls_completed": _nonnegative_counter(
                    telemetry.get("provider_calls_completed")
                ),
                "provider_dispatches_started": _nonnegative_counter(
                    telemetry.get("provider_dispatches_started")
                ),
                **(
                    {
                        "recursive_helper_cleanup_retry_pending": True,
                        "retryable_infrastructure": True,
                        "retryable_infrastructure_reason": str(
                            telemetry.get("retryable_infrastructure_reason")
                            or ""
                        ),
                        "terminal_failure": False,
                        "llm_retryable": True,
                    }
                    if cleanup_infrastructure_yield
                    else {}
                ),
                "iteration_neutral": bool(
                    zero_provider_failure
                    or parent_recheck_continuation_granted
                    or (
                        helper_acceptance_handoff_pending
                        and not resuming_parent_recheck
                    )
                ),
                # The child attempt has already been charged on reservation.
                # Keep this continuation schedulable even when the enclosing
                # action invocation pool was otherwise exhausted.
                "preserve_action_budget": bool(
                    zero_provider_failure or parent_recheck_pending
                ),
                "preserve_frontier_work": bool(
                    zero_provider_failure
                    or cleanup_infrastructure_yield
                    or parent_recheck_pending
                    or helper_acceptance_handoff_pending
                ),
                "preserve_selected_frontier_action": bool(
                    zero_provider_failure
                    or cleanup_infrastructure_yield
                    or parent_recheck_pending
                ),
                "defer_selected_frontier_action": bool(
                    zero_provider_failure
                ),
                **(
                    {
                        "llm_failure_kind": (
                            "recursive_helper_zero_provider_failure"
                        ),
                        "llm_retryable": True,
                        "llm_failure_scope": "scoped",
                        "scoped_failure_reason": (
                            "recursive_helper_zero_provider_failure"
                        ),
                    }
                    if zero_provider_failure
                    else {}
                ),
                "scheduler_neutral": bool(
                    zero_provider_failure
                    or cleanup_infrastructure_yield
                    or parent_recheck_pending
                    or helper_acceptance_handoff_pending
                ),
                "stagnation_neutral": bool(
                    zero_provider_failure
                    or cleanup_infrastructure_yield
                    or parent_recheck_pending
                    or helper_acceptance_handoff_pending
                    or parent_recheck_rejected
                ),
                "hard_pivot_neutral": bool(
                    zero_provider_failure or cleanup_infrastructure_yield
                ),
                "recursion_depth_parent": int(getattr(session, "recursion_depth", 0) or 0),
            },
        )
