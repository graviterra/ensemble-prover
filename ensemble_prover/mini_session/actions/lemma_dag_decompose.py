"""Materialize typed lemma-DAG candidates as proof-graph obligations.

Candidates come from the latest conversation-turn extraction. Lean-verified
helpers become durable proved nodes; well-formed unresolved statements remain
open for bounded closure. A failed speculative decomposition rolls its proof
state checkpoint back while retaining independently verified dossier evidence.
"""

from __future__ import annotations

import time
from typing import Any, ClassVar, FrozenSet, Sequence

from ...proof_dossier import helper_decl_name, strong_progress_for_accepted_helpers
from ...mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ...root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ..action import MiniOutcome
from ..graph_sync import sync_proof_state_to_graph


def _resync_graph_from_dossier(dossier: Any) -> None:
    """Re-materialize graph helper nodes for surviving verified_helpers.

    Defect found by adversarial review (2026-05-08): rollback restores
    proof_graph to its pre-checkpoint state, but verified_helpers are
    durable wins and survive rollback. ``dossier.record_verified_helper``
    writes to BOTH stores synchronously, so after rollback the dossier
    knows about helpers the rolled-back graph has forgotten.

    Re-running the dossier's existing ``_sync_legacy_helpers_to_graph``
    re-creates graph nodes for every surviving verified helper.

    M7 fix (2026-05-08): ``_sync_legacy_helpers_to_graph`` REWRITES
    ``dossier.verified_helpers`` to drop entries it considers unsafe
    (empty source, answer-unsafe, or name mismatch). On a rollback path
    that should be purely additive to the graph, that drop can lose
    durable verified helpers if any have been seeded directly (test
    fixtures, snapshot rehydration). Snapshot the helper dict before
    the resync and restore any keys that vanished.
    """

    if dossier is None:
        return
    sync = getattr(dossier, "_sync_legacy_helpers_to_graph", None)
    if not callable(sync):
        return
    snapshot = None
    try:
        helpers = getattr(dossier, "verified_helpers", None)
        if isinstance(helpers, dict):
            snapshot = dict(helpers)
    except Exception:
        snapshot = None
    try:
        sync()
    except Exception:
        # Best-effort. The dossier still owns the durable helper
        # records; only graph-walk queries are affected if this
        # fails, and they degrade gracefully (helper appears as
        # "not proven" in the graph but the dossier still has it).
        pass
    if snapshot is None:
        return
    try:
        current = getattr(dossier, "verified_helpers", None)
        if not isinstance(current, dict):
            return
        # Restore any helper key that the resync filter dropped. We
        # never overwrite an existing entry (the resync may have
        # legitimately replaced a helper with a corrected version).
        for name, record in snapshot.items():
            if name not in current:
                current[name] = record
    except Exception:
        pass


class LemmaDagDecomposeAction:
    id: str = "lemma_dag_decompose"
    priority: int = 55
    cost_estimate_s: float = 30.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})

    def __init__(
        self,
        *,
        timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        helpers_override: Sequence[str] = (),
        backtracking_enabled: bool = True,
        max_parent_stub_goals: int = 8,
        root_tactic_max_candidates: int = 32,
    ) -> None:
        self.timeout_s = float(timeout_s or 0.0)
        self._helpers_override = tuple(helpers_override)
        self.backtracking_enabled = bool(backtracking_enabled)
        self.max_parent_stub_goals = max(0, int(max_parent_stub_goals or 0))
        self.root_tactic_max_candidates = max(
            0,
            int(root_tactic_max_candidates or 0),
        )


    def _helpers_for(self, session: Any) -> Sequence[str]:
        if self._helpers_override:
            return self._helpers_override
        extraction = getattr(session, "last_turn_extraction", None)
        if extraction is None:
            return ()
        return tuple(getattr(extraction, "lemma_dag_candidates", ()) or ())

    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0:
            return False
        conv = getattr(session, "conv", None)
        if conv is not None and not bool(
            getattr(conv, "allow_helper_decomposition", True)
        ):
            return False
        metadata = getattr(session, "last_action_outcome_metadata", {}) or {}
        if metadata.get("giveup_cluster"):
            return False
        if session.dossier is None or session.proof_state is None or session.lean is None:
            return False
        if not self._helpers_for(session):
            return False
        selected_getter = getattr(session, "selected_work_item_for", None)
        if callable(selected_getter):
            selected = selected_getter(
                self.id,
                work_types=("lemma_dag_decomposition",),
            )
            if selected is not None:
                node_id = str(getattr(selected, "node_id", "") or "").strip()
                node = getattr(session.proof_state, "nodes", {}).get(node_id)
                return bool(
                    node is not None
                    and getattr(node, "kind", "") == "decomposition_task"
                    and getattr(node, "status", "") == "open"
                )
        ps = session.proof_state
        has_open = getattr(ps, "has_open_decomposition_task", None)
        if callable(has_open) and not has_open():
            # D2 gate-side fix (2026-05-09): if any helper is a
            # sorry-stub (LLM's decomposition request), this action
            # IS applicable — it will open the task itself in run().
            from ensemble_prover.proof_state_executor import (
                _is_sorry_stub_body,
                _lemma_dag_parent_stub_candidate_sources,
            )
            for h in self._helpers_for(session):
                if _is_sorry_stub_body(h):
                    return True
            if _lemma_dag_parent_stub_candidate_sources(
                ps,
                self._helpers_for(session),
            ):
                return True
            return False
        return True

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.proof_state_executor import _try_proof_state_lemma_dag_helpers

        started = time.monotonic()
        helpers = list(self._helpers_for(session))
        selected_ids = ()
        selected_getter = getattr(session, "selected_work_item_node_ids", None)
        if callable(selected_getter):
            selected_ids = selected_getter(
                self.id,
                work_types=("lemma_dag_decomposition",),
            )

        # Gap 3: open a checkpoint so a "no helpers accepted" outcome can
        # roll back the speculative open child_goal nodes / failed_attempts
        # bumps / next_index advances that would otherwise pollute the
        # graph permanently. Verified helpers (dossier.verified_helpers)
        # are NOT snapshotted — they survive rollback as durable wins.
        checkpoint_id: str = ""
        ps = session.proof_state
        backtracking_supported = (
            self.backtracking_enabled
            and ps is not None
            and callable(getattr(ps, "checkpoint", None))
            and callable(getattr(ps, "rollback", None))
            and callable(getattr(ps, "commit", None))
        )
        if backtracking_supported:
            try:
                checkpoint_id = ps.checkpoint(
                    dossier=session.dossier,
                    label=f"lemma_dag_decompose:turn={int(getattr(session, 'iteration', 0))}",
                )
            except Exception:
                checkpoint_id = ""

        rolled_back = False
        accepted: list = []
        success = False
        new_child_node_ids: list[str] = []
        # Phase 2 (2026-05-09): commit when any child_goal nodes were
        # added by this attempt, even if zero helpers were Lean-verified.
        # The user-mandated rollback contract is:
        #   - Commit when >=1 well-formed child_goal node was added
        #     (durable evidence of "the LLM thinks this is needed").
        #   - Roll back only when the call raised an exception OR no
        #     child_goal nodes were added at all (purely speculative).
        # Snapshot child_goal node IDs before the call so we can detect
        # the diff after.
        child_goal_ids_before = (
            {nid for nid, n in (ps.nodes or {}).items() if getattr(n, "kind", "") == "child_goal"}
            if ps is not None
            else set()
        )
        decomposition_child_links_before = (
            {
                str(nid): tuple(str(cid) for cid in getattr(n, "child_node_ids", ()) or ())
                for nid, n in (ps.nodes or {}).items()
                if getattr(n, "kind", "") == "decomposition_task"
            }
            if ps is not None
            else {}
        )
        assembly_groups_before = (
            {
                str(nid): tuple(
                    str(getattr(group, "assembly_id", "") or "")
                    for group in getattr(n, "assembly_attempt_groups", ()) or ()
                    if str(getattr(group, "assembly_id", "") or "").strip()
                )
                for nid, n in (ps.nodes or {}).items()
            }
            if ps is not None
            else {}
        )
        pending_residual_extractions_before = (
            {
                str(node_id): dict(
                    getattr(node, "pending_residual_goal_extraction", {}) or {}
                )
                for node_id, node in (ps.nodes or {}).items()
                if dict(
                    getattr(node, "pending_residual_goal_extraction", {}) or {}
                )
            }
            if ps is not None
            else {}
        )
        decomposition_child_links_added: list[str] = []
        assembly_groups_added: list[str] = []
        pending_residual_extraction_node_ids: list[str] = []
        # Guard against asyncio.CancelledError (BaseException subclass in
        # Python 3.8+) leaking the open checkpoint. Use try/finally so the
        # checkpoint resolves regardless of how the await exits, and a
        # bare BaseException catch around the rollback attempt so a
        # cancelled task still re-raises correctly.
        try:
            accepted = await _try_proof_state_lemma_dag_helpers(
                conv=session.conv,
                lean=session.lean,
                dossier=session.dossier,
                proof_state=session.proof_state,
                helpers=helpers,
                recorder=session.recorder,
                trace_prefix=session.trace_prefix,
                turn=int(getattr(session, "iteration", 0)),
                timeout_s=self.timeout_s,
                proof_cache=session.proof_cache,
                target_task_id=selected_ids[0] if selected_ids else "",
                max_parent_stub_goals=self.max_parent_stub_goals,
            )
            success = True
        finally:
            try:
                child_goal_ids_after = (
                    {nid for nid, n in (ps.nodes or {}).items() if getattr(n, "kind", "") == "child_goal"}
                    if ps is not None
                    else set()
                )
                new_child_node_ids = sorted(child_goal_ids_after - child_goal_ids_before)
            except Exception:
                new_child_node_ids = []
            try:
                decomposition_child_links_after = (
                    {
                        str(nid): tuple(
                            str(cid)
                            for cid in getattr(n, "child_node_ids", ()) or ()
                        )
                        for nid, n in (ps.nodes or {}).items()
                        if getattr(n, "kind", "") == "decomposition_task"
                    }
                    if ps is not None
                    else {}
                )
                linked: set[str] = set()
                for node_id, after_children in decomposition_child_links_after.items():
                    before_children = set(
                        decomposition_child_links_before.get(node_id, ())
                    )
                    for child_id in after_children:
                        if child_id and child_id not in before_children:
                            linked.add(child_id)
                decomposition_child_links_added = sorted(linked)
            except Exception:
                decomposition_child_links_added = []
            try:
                assembly_groups_after = (
                    {
                        str(nid): tuple(
                            str(getattr(group, "assembly_id", "") or "")
                            for group in getattr(n, "assembly_attempt_groups", ()) or ()
                            if str(getattr(group, "assembly_id", "") or "").strip()
                        )
                        for nid, n in (ps.nodes or {}).items()
                    }
                    if ps is not None
                    else {}
                )
                added_groups: list[str] = []
                for node_id, after_groups in assembly_groups_after.items():
                    before_groups = set(assembly_groups_before.get(node_id, ()))
                    for assembly_id in after_groups:
                        if assembly_id and assembly_id not in before_groups:
                            added_groups.append(f"{node_id}:{assembly_id}")
                assembly_groups_added = sorted(added_groups)
            except Exception:
                assembly_groups_added = []
            try:
                pending_residual_extractions_after = {
                    str(node_id): dict(
                        getattr(node, "pending_residual_goal_extraction", {}) or {}
                    )
                    for node_id, node in (ps.nodes or {}).items()
                    if dict(
                        getattr(node, "pending_residual_goal_extraction", {}) or {}
                    )
                }
                pending_residual_extraction_node_ids = sorted(
                    node_id
                    for node_id, pending in (
                        pending_residual_extractions_after.items()
                    )
                    if pending_residual_extractions_before.get(node_id) != pending
                )
            except Exception:
                pending_residual_extraction_node_ids = []
            if checkpoint_id:
                try:
                    new_child_nodes_added = bool(new_child_node_ids)
                    task_child_links_added = bool(decomposition_child_links_added)
                    assembly_contracts_added = bool(assembly_groups_added)
                    pending_residual_extraction_added = bool(
                        pending_residual_extraction_node_ids
                    )
                    # Commit when helpers verified, new child_goal
                    # nodes were added, or existing child_goal nodes
                    # were newly attached to the active task. The
                    # latter preserves duplicate decomposition
                    # evidence across rollback.
                    if success and (
                        accepted
                        or new_child_nodes_added
                        or task_child_links_added
                        or assembly_contracts_added
                        or pending_residual_extraction_added
                    ):
                        ps.commit(checkpoint_id)
                    else:
                        ps.rollback(checkpoint_id)
                        rolled_back = True
                        # When the dossier was supplied to checkpoint(), the
                        # proof_graph rolled back too — but verified helpers
                        # are durable. Re-materialize their graph nodes so
                        # the dossier and graph stay consistent.
                        _resync_graph_from_dossier(session.dossier)
                        # B2 fix (2026-05-11): the prior step re-syncs
                        # ``dossier.proof_graph`` from durable helpers but
                        # does NOT re-sync ``proof_state.nodes``. Without
                        # this step a child_goal whose target matches a
                        # surviving helper stays at ``status="open"``,
                        # making the assembly fixpoint unable to consume
                        # the helper. ``reconcile_helpers_to_dossier``
                        # closes the three-way drift by re-promoting any
                        # matching open child_goal back to ``"proved"``.
                        try:
                            reconciler = getattr(
                                ps, "reconcile_helpers_to_dossier", None
                            )
                            if callable(reconciler):
                                # F5 fix (2026-05-11): pass the session's
                                # absolute turn index so reconcile-driven
                                # transitions don't all get timestamped 0.
                                reconciler(
                                    session.dossier,
                                    turn_index=int(
                                        getattr(session, "iteration", 0) or 0
                                    ),
                                )
                        except Exception:
                            # Best-effort; the dossier still owns the
                            # durable record so the next refresh will
                            # eventually pick it up.
                            pass
                except Exception:
                    # Telemetry-only failure; never mask the underlying
                    # exception (if any). On exception the action body
                    # is about to re-raise as Python unwinds the
                    # try/finally.
                    pass

        if success and not rolled_back and ps is not None:
            sync_proof_state_to_graph(
                ps,
                session.dossier,
                session=session,
                phase="lemma_dag_decompose",
                turn_index=int(getattr(session, "iteration", 0) or 0),
            )

        cost = time.monotonic() - started
        unverified_decomposition_created = bool(
            new_child_node_ids or decomposition_child_links_added
        )
        assembly_contracts_added = bool(assembly_groups_added)
        pending_only_continuation = bool(
            pending_residual_extraction_node_ids
            and not accepted
            and not new_child_node_ids
            and not decomposition_child_links_added
            and not assembly_groups_added
        )
        solved = False
        proof = None
        root_helpers: list[str] = []
        if success and accepted and not rolled_back:
            try:
                from ensemble_prover.proof_state_executor import (
                    _try_proof_state_root_exact_frontier,
                    _try_proof_state_root_tactic_assembly,
                )

                root_ok, root_proof, root_helpers, root_records = (
                    await _try_proof_state_root_exact_frontier(
                        conv=session.conv,
                        lean=session.lean,
                        dossier=session.dossier,
                        proof_state=session.proof_state,
                        turn=int(getattr(session, "iteration", 0) or 0),
                        timeout_s=self.timeout_s,
                    )
                )
                solved = bool(root_ok and root_proof)
                proof = root_proof if solved else None
                if root_records and getattr(session, "recorder", None) is not None:
                    for record in root_records:
                        session.recorder.record_turn(record)
                if root_records:
                    try:
                        sync = getattr(session.proof_state, "sync_to_graph", None)
                        if callable(sync):
                            sync(
                                session.dossier,
                                phase="lemma_dag_decompose_root_exact",
                                turn_index=int(getattr(session, "iteration", 0) or 0),
                            )
                    except Exception:
                        pass
                elif self.root_tactic_max_candidates > 0:
                    tactic_ok, tactic_proof, tactic_helpers, tactic_records = (
                        await _try_proof_state_root_tactic_assembly(
                            conv=session.conv,
                            lean=session.lean,
                            dossier=session.dossier,
                            proof_state=session.proof_state,
                            turn=int(getattr(session, "iteration", 0) or 0),
                            timeout_s=self.timeout_s,
                            max_candidates=self.root_tactic_max_candidates,
                            allow_deferred_retry=True,
                        )
                    )
                    root_helpers.extend(tactic_helpers or ())
                    if (
                        tactic_records
                        and getattr(session, "recorder", None) is not None
                    ):
                        for record in tactic_records:
                            session.recorder.record_turn(record)
                    solved = bool(tactic_ok and tactic_proof)
                    proof = tactic_proof if solved else None
                    if tactic_records:
                        try:
                            sync = getattr(session.proof_state, "sync_to_graph", None)
                            if callable(sync):
                                sync(
                                    session.dossier,
                                    phase="lemma_dag_decompose_root_tactic",
                                    turn_index=int(
                                        getattr(session, "iteration", 0) or 0
                                    ),
                                )
                        except Exception:
                            pass
            except Exception:
                solved = False
                proof = None
                root_helpers = []
        replay_helpers = (
            tuple(session.dossier.verified_helper_blocks())
            if solved and proof and getattr(session, "dossier", None) is not None
            else ()
        )
        helper_names = tuple(
            name
            for block in replay_helpers
            for name in [helper_decl_name(block)]
            if name
        )
        return MiniOutcome(
            action_id=self.id,
            solved=solved,
            proof=proof,
            helpers_added=tuple(accepted or ()) + tuple(root_helpers or ()),
            # Creating unverified work is useful graph evidence and remains
            # durable, but it is not verified progress. Let the session's proof
            # state signature notice the new work without resetting progress as
            # strongly as an accepted helper would.
            # Recording the exact parent stub + context for verifier-only
            # typed extraction is durable forward progress. Treating that
            # handoff as ordinary no-progress lets stagnation/recovery logic
            # suppress the newly committed continuation before it dispatches.
            progress=bool(accepted or pending_residual_extraction_node_ids),
            cost_seconds=cost,
            root_candidate=(
                RootFinalizationCandidate(
                    proof=proof or "",
                    replay_helpers=replay_helpers,
                    helper_names=helper_names,
                    phase="lemma_dag_decompose",
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    source_action_id=self.id,
                    target_statement=str(
                        getattr(session.dossier, "root_statement", "")
                        or getattr(getattr(session, "conv", None), "goal_statement", "")
                        or ""
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=proof or "",
                        phase="lemma_dag_decompose",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        target_statement=str(
                            getattr(session.dossier, "root_statement", "")
                            or getattr(
                                getattr(session, "conv", None),
                                "goal_statement",
                                "",
                            )
                            or ""
                        ),
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        source=self.id,
                    ),
                    metadata={"root_finalization_already_applied": True},
                )
                if solved and proof
                else None
            ),
            metadata={
                "candidate_count": len(helpers),
                "accepted_count": len(accepted or ()),
                "replay_helpers": list(replay_helpers),
                "helper_names": list(helper_names),
                "root_finalization_already_applied": bool(solved and proof),
                "strong_progress": strong_progress_for_accepted_helpers(
                    session.dossier, accepted or ()
                ),
                "unverified_decomposition_created": unverified_decomposition_created,
                "new_child_nodes_added": bool(new_child_node_ids),
                "new_child_node_ids": list(new_child_node_ids),
                "decomposition_child_links_added": bool(
                    decomposition_child_links_added
                ),
                "decomposition_linked_child_node_ids": list(
                    decomposition_child_links_added
                ),
                "assembly_contracts_added": assembly_contracts_added,
                "assembly_group_ids_added": list(assembly_groups_added),
                "pending_residual_goal_extraction_added": bool(
                    pending_residual_extraction_node_ids
                ),
                "pending_residual_goal_extraction_node_ids": list(
                    pending_residual_extraction_node_ids
                ),
                "pending_residual_goal_extraction_preserved": bool(
                    pending_residual_extraction_node_ids
                ),
                # The paid parent stub has only handed off to deterministic
                # typed verification. Preserve one final-iteration slot for
                # that verifier-only continuation; the replay itself consumes
                # a normal iteration if it remains unavailable.
                "iteration_neutral": bool(
                    pending_only_continuation
                ),
                "scheduler_neutral": bool(
                    pending_only_continuation
                ),
                "stagnation_neutral": bool(
                    pending_only_continuation
                ),
                "hard_pivot_neutral": bool(
                    pending_only_continuation
                ),
                "non_consuming_repair_ticket_continuation": bool(
                    pending_only_continuation
                ),
                "target_node_ids": list(selected_ids),
                "selected_work_item": dict(getattr(session, "selected_work_item_record", {}) or {}),
                "checkpoint_id": checkpoint_id,
                "rolled_back": rolled_back,
            },
        )
