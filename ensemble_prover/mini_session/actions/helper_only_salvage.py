"""Salvage and assemble helpers from a turn that produced no root proof.

The action decomposes helper candidates, attempts child closure, verifies
helpers independently, assembles accepted helpers into open graph nodes, and
tries deterministic root closure. It is applicable only when the latest typed
turn extraction contains helpers but no main proof.
"""

from __future__ import annotations

import hashlib
import json
import time
from typing import Any, ClassVar, FrozenSet, List, Optional, Tuple

from ...proof_dossier import strong_progress_for_accepted_helpers
from ...mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ...proof_state_cache import store_verified_helper_for_dossier
from ...root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ...tactic_attempt_telemetry import dossier_lean_attempt_observer
from ..action import MiniOutcome
from ..graph_sync import sync_proof_state_to_graph
from ..tactic_source_suppression import tactic_source_suppression_records


class HelperOnlySalvageAction:
    id: str = "helper_only_salvage"
    priority: int = 60
    cost_estimate_s: float = 10.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state", "conv"})
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {"_fired_for_extraction_key"}
    )

    def __init__(
        self,
        *,
        timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        max_nodes: int = 3,
        run_assembly_after_salvage: bool = True,
        max_candidates: int = 32,
        max_decl_applications: int = 6,
        batch_parallelism: int = 1,
    ) -> None:
        self.timeout_s = float(timeout_s or 0.0)
        self.max_nodes = int(max_nodes or 0)
        self.run_assembly_after_salvage = bool(run_assembly_after_salvage)
        self.max_candidates = int(max_candidates or 0)
        self.max_decl_applications = int(max_decl_applications or 0)
        self.batch_parallelism = int(batch_parallelism or 1)
        self._fired_for_extraction_key: str = ""

    @staticmethod
    def _extraction_key(extraction: Any) -> str:
        if extraction is None:
            return ""
        payload = {
            "helpers": list(getattr(extraction, "helpers", ()) or ()),
            "proof": getattr(extraction, "proof", None),
            "lemma_dag_candidates": list(
                getattr(extraction, "lemma_dag_candidates", ()) or ()
            ),
            "chunks": list(getattr(extraction, "chunks", ()) or ()),
        }
        return hashlib.sha256(
            json.dumps(payload, sort_keys=True, default=str).encode("utf-8")
        ).hexdigest()



    def _last_extraction(self, session: Any) -> Optional[Any]:
        return getattr(session, "last_turn_extraction", None)

    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0:
            return False
        if session.dossier is None or session.lean is None or session.conv is None:
            return False
        if not bool(getattr(session.conv, "allow_helper_decomposition", True)):
            return False
        metadata = getattr(session, "last_action_outcome_metadata", {}) or {}
        if isinstance(metadata, dict) and metadata.get("giveup_cluster"):
            return False
        extraction = self._last_extraction(session)
        if extraction is None:
            return False
        # Helpers without a main proof.
        if getattr(extraction, "proof", None) is not None:
            return False
        helpers = list(getattr(extraction, "helpers", ()) or ())
        if not helpers:
            return False
        # Don't re-fire on the same extraction.
        if self._extraction_key(extraction) == self._fired_for_extraction_key:
            return False
        return True

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.helper_salvage import HelperSalvager
        from ensemble_prover.mini_root_tactic import (
            root_tactic_success_contract_status,
            try_close_root_with_active_lift,
        )
        from ensemble_prover.proof_dossier import helper_decl_name
        from ensemble_prover.proof_state_executor import (
            _proof_state_acceptance_preamble,
            _proof_state_check_preamble,
            _try_proof_state_child_closures,
            _try_proof_state_lemma_dag_helpers,
            _try_proof_state_salvaged_helper_assembly,
            ensure_decomposition_task_open_for_sorry_stubs,
        )

        started = time.monotonic()
        extraction = self._last_extraction(session)
        helpers = list(getattr(extraction, "helpers", ()) or ())
        self._fired_for_extraction_key = self._extraction_key(extraction)

        conv = session.conv
        lean = session.lean
        dossier = session.dossier
        proof_state = session.proof_state
        proof_cache = session.proof_cache

        accepted: List[str] = []
        lemma_dag_helpers: List[str] = []
        lemma_dag_child_node_ids: List[str] = []
        lemma_dag_linked_child_node_ids: List[str] = []
        proof_state_helpers: List[str] = []
        rejected_or_skipped: Tuple[List[str], List[str]] = ([], [])
        solved = False
        proof: Optional[str] = None
        solved_via: str = ""
        root_candidate: Optional[RootFinalizationCandidate] = None
        absolute_turn = int(getattr(session, "iteration", 0))
        defer_fresh_children_to_llm = False
        root_target_statement = str(
            getattr(dossier, "root_statement", "")
            or getattr(conv, "goal_statement", "")
            or ""
        )

        try:
            from ensemble_prover.mini_prover import (
                _bank_helpers_as_proposed,
                _format_root_equivalent_helper_feedback,
                _root_equivalent_sorry_stub_helper_names_from_blocks,
            )

            root_equivalent_names = _root_equivalent_sorry_stub_helper_names_from_blocks(
                helpers,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
            )
        except Exception:
            root_equivalent_names = []
        if root_equivalent_names:
            bankable_sources = [
                src
                for src in helpers
                if isinstance(src, str)
                and (helper_decl_name(src) or "") not in set(root_equivalent_names)
            ]
            banked_proposed_helpers = _bank_helpers_as_proposed(
                dossier,
                bankable_sources,
                phase="helper_only_salvage",
                turn_index=absolute_turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=bool(
                    getattr(conv, "allow_helper_decomposition", True)
                ),
            )
            record = {
                "phase": "helper_only_salvage",
                "turn_in_phase": absolute_turn,
                "rejection_reason": "root_equivalent_helper_stub",
                "rejection_match": ", ".join(root_equivalent_names),
                "banked_proposed_helpers": list(banked_proposed_helpers),
                "verdict": "proof_policy_rejected",
            }
            recorder = getattr(session, "_record_event", None)
            if callable(recorder):
                recorder(record)
            try:
                conv.append_user(
                    _format_root_equivalent_helper_feedback(root_equivalent_names)
                )
            except Exception:
                pass
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "rejection_reason": "root_equivalent_helper_stub",
                    "rejection_match": ", ".join(root_equivalent_names),
                },
            )

        # ---- Pathway (1) + (2): lemma-DAG decomposition + child closure ----
        # Defensive probe so test stubs (SimpleNamespace) without
        # ``has_open_decomposition_task`` fall through to the salvage
        # path. Real proof_state implementations have the method.
        # D2 gate-side fix (2026-05-09): open ad-hoc decomposition_task
        # when sorry-stubs are present so the lemma-DAG path proceeds.
        if (
            helpers
            and proof_state is not None
            and dossier is not None
            and callable(getattr(proof_state, "has_open_decomposition_task", None))
            and not proof_state.has_open_decomposition_task()
        ):
            ensure_decomposition_task_open_for_sorry_stubs(
                proof_state,
                helpers,
                source=f"sorry_stub_helpers_volunteered:helper_only_salvage:turn={absolute_turn}",
            )
        has_decomp = (
            callable(getattr(proof_state, "has_open_decomposition_task", None))
            and proof_state.has_open_decomposition_task()
        )
        if (
            helpers
            and proof_state is not None
            and dossier is not None
            and has_decomp
        ):
            child_goal_ids_before = {
                nid
                for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
                if getattr(node, "kind", "") == "child_goal"
            }
            decomposition_links_before = {
                str(nid): set(str(cid) for cid in getattr(node, "child_node_ids", ()) or ())
                for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
                if getattr(node, "kind", "") == "decomposition_task"
            }
            try:
                lemma_dag_helpers = await _try_proof_state_lemma_dag_helpers(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    helpers=helpers,
                    recorder=session.recorder,
                    trace_prefix=session.trace_prefix,
                    turn=absolute_turn,
                    timeout_s=self.timeout_s,
                    proof_cache=proof_cache,
                )
            except Exception:
                lemma_dag_helpers = []
            child_goal_ids_after = {
                nid
                for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
                if getattr(node, "kind", "") == "child_goal"
            }
            new_child_node_ids = sorted(child_goal_ids_after - child_goal_ids_before)
            lemma_dag_linked_child_node_ids = sorted(
                {
                    str(cid)
                    for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
                    if getattr(node, "kind", "") == "decomposition_task"
                    for cid in getattr(node, "child_node_ids", ()) or ()
                    if str(cid) in child_goal_ids_before
                    and str(cid) not in decomposition_links_before.get(str(nid), set())
                }
            )
            lemma_dag_child_node_ids = sorted(
                set(new_child_node_ids) | set(lemma_dag_linked_child_node_ids)
            )
            sync_proof_state_to_graph(
                proof_state,
                dossier,
                session=session,
                phase="proof_state_lemma_dag_decomposition",
                turn_index=absolute_turn,
            )
            action_available = getattr(session, "action_available", None)
            registered_action = getattr(session, "registered_action", None)
            recursive_action = (
                registered_action("recursive_helper_prover")
                if callable(registered_action)
                else None
            )
            recursive_helper_active = (
                bool(action_available("recursive_helper_prover"))
                if callable(action_available)
                else False
            )
            # Fresh lemma-DAG children are a scheduler boundary.  If the
            # recursive helper action is registered, has budget, and is
            # immediately applicable, defer child handling to the next
            # scheduler turn instead of consuming brand-new decomposition work
            # inline in the salvage action.
            if recursive_action is None:
                recursive_helper_active = False
            elif recursive_helper_active:
                is_applicable = getattr(recursive_action, "is_applicable", None)
                try:
                    recursive_helper_active = bool(
                        is_applicable(session) if callable(is_applicable) else False
                    )
                except Exception:
                    recursive_helper_active = False
                if recursive_helper_active and lemma_dag_child_node_ids:
                    node_is_candidate = getattr(recursive_action, "_node_is_candidate", None)
                    nodes = getattr(proof_state, "nodes", {}) or {}
                    if callable(node_is_candidate):
                        recursive_helper_active = any(
                            node_is_candidate(nodes.get(child_id))
                            for child_id in lemma_dag_child_node_ids
                            if nodes.get(child_id) is not None
                        )
            defer_fresh_children_to_llm = bool(
                lemma_dag_child_node_ids and recursive_helper_active
            )
            if defer_fresh_children_to_llm:
                recorder = getattr(session, "_record_event", None)
                if callable(recorder):
                    recorder({
                        "phase": "proof_state_lemma_dag_child_routing",
                        "turn_in_phase": absolute_turn,
                        "new_child_node_ids": list(lemma_dag_child_node_ids),
                        "linked_child_node_ids": list(lemma_dag_linked_child_node_ids),
                        "verdict": "deferred_to_recursive_helper_prover",
                    })
            if (
                (lemma_dag_helpers or lemma_dag_child_node_ids)
                and self.run_assembly_after_salvage
                and not defer_fresh_children_to_llm
            ):
                try:
                    state_ok, state_proof, ps_helpers = await _try_proof_state_child_closures(
                        conv=conv,
                        lean=lean,
                        dossier=dossier,
                        proof_state=proof_state,
                        recorder=session.recorder,
                        trace_prefix=session.trace_prefix,
                        turn=absolute_turn,
                        timeout_s=self.timeout_s,
                        max_candidates=self.max_candidates,
                        max_nodes=self.max_nodes,
                        max_decl_applications=self.max_decl_applications,
                        batch_parallelism=self.batch_parallelism,
                        proof_cache=proof_cache,
                        target_node_ids=(
                            tuple(lemma_dag_child_node_ids)
                            if lemma_dag_child_node_ids
                            else None
                        ),
                    )
                except Exception:
                    state_ok, state_proof, ps_helpers = False, None, []
                proof_state_helpers.extend(ps_helpers or ())
                sync_proof_state_to_graph(
                    proof_state,
                    dossier,
                    session=session,
                    phase="proof_state_lemma_dag_root_check",
                    turn_index=absolute_turn,
                )
                if state_ok and state_proof:
                    solved = True
                    proof = state_proof
                    solved_via = "lemma_dag_helper"
                    replay_helpers = tuple(dossier.verified_helper_blocks())
                    helper_names = tuple(
                        name
                        for block in replay_helpers
                        for name in [helper_decl_name(block)]
                        if name
                    )
                    root_candidate = RootFinalizationCandidate(
                        proof=state_proof,
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        phase="lemma_dag_helper",
                        turn_index=absolute_turn,
                        source_action_id=self.id,
                        target_statement=root_target_statement,
                        verification_certificate=root_verification_certificate(
                            accepted=True,
                            proof=state_proof,
                            phase="lemma_dag_helper",
                            turn_index=absolute_turn,
                            target_statement=root_target_statement,
                            replay_helpers=replay_helpers,
                            helper_names=helper_names,
                            source=self.id,
                        ),
                        metadata={"root_finalization_already_applied": True},
                    )

        # ---- Pathway (3): HelperSalvager.salvage ----
        if not solved and helpers:
            from ensemble_prover.helper_salvage import collect_open_child_targets

            salvager = HelperSalvager(
                lean,
                preamble=_proof_state_check_preamble(conv),
                answer_safe_preamble=str(getattr(conv, "preamble", "") or ""),
                timeout_s=self.timeout_s,
                relevance_gate_root_statement=str(
                    getattr(dossier, "root_statement", "") or ""
                ),
                relevance_gate_open_targets=collect_open_child_targets(proof_state),
                verified_helper_accept_callback=getattr(
                    session,
                    "theory_verified_helper_accept_callback",
                    None,
                ),
            )
            salvage_result = await salvager.salvage(
                helpers,
                dossier=dossier,
                phase=getattr(conv, "role", "prove"),
                turn_index=absolute_turn,
            )
            invalidated_helpers = [
                *list(getattr(salvage_result, "replaced", []) or []),
                *list(getattr(salvage_result, "evicted", []) or []),
            ]
            if invalidated_helpers and proof_state is not None:
                try:
                    proof_state.reconcile_with_dossier(dossier)
                    proof_state.invalidate_assembly_contracts_for_helpers(
                        invalidated_helpers,
                        phase=getattr(conv, "role", "prove"),
                        turn_index=absolute_turn,
                        conservative=True,
                    )
                except Exception:
                    pass
            accepted = list(salvage_result.accepted)
            rejected_or_skipped = (
                list(salvage_result.rejected),
                list(salvage_result.skipped),
            )

            # Cache successfully salvaged helpers.
            if accepted and proof_cache is not None:
                for helper_name in accepted:
                    helper_record = dossier.verified_helpers.get(helper_name) if dossier is not None else None
                    if helper_record is not None:
                        try:
                            store_verified_helper_for_dossier(
                                proof_cache,
                                helper_record.source,
                                preamble=_proof_state_check_preamble(conv),
                                dossier=dossier,
                                phase=f"{getattr(conv, 'role', 'prove')}:helper_only_salvage",
                            )
                        except Exception:
                            pass

            # ---- Pathway (4): salvaged-helper assembly ----
            if (
                accepted
                and self.run_assembly_after_salvage
                and proof_state is not None
            ):
                try:
                    ok, state_proof, ps_helpers = await _try_proof_state_salvaged_helper_assembly(
                        conv=conv,
                        lean=lean,
                        dossier=dossier,
                        proof_state=proof_state,
                        helper_names=accepted,
                        recorder=session.recorder,
                        trace_prefix=session.trace_prefix,
                        turn=absolute_turn,
                        timeout_s=self.timeout_s,
                        max_nodes=self.max_nodes,
                        proof_cache=proof_cache,
                        phase="helper_only_salvage",
                    )
                except Exception:
                    ok, state_proof, ps_helpers = False, None, []
                proof_state_helpers.extend(ps_helpers or ())
                sync_proof_state_to_graph(
                    proof_state,
                    dossier,
                    session=session,
                    phase="helper_only_salvage_proof_state_assembly",
                    turn_index=absolute_turn,
                )
                if ok and state_proof:
                    solved = True
                    proof = state_proof
                    solved_via = "helper_only_salvage_assembly"
                    replay_helpers = tuple(dossier.verified_helper_blocks())
                    helper_names = tuple(
                        name
                        for block in replay_helpers
                        for name in [helper_decl_name(block)]
                        if name
                    )
                    root_candidate = RootFinalizationCandidate(
                        proof=state_proof,
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        phase="helper_only_salvage_assembly",
                        turn_index=absolute_turn,
                        source_action_id=self.id,
                        target_statement=root_target_statement,
                        verification_certificate=root_verification_certificate(
                            accepted=True,
                            proof=state_proof,
                            phase="helper_only_salvage_assembly",
                            turn_index=absolute_turn,
                            target_statement=root_target_statement,
                            replay_helpers=replay_helpers,
                            helper_names=helper_names,
                            source=self.id,
                        ),
                        metadata={"root_finalization_already_applied": True},
                    )

            # ---- Pathway (5): post-salvage child-closure ----
            if (
                not solved
                and accepted
                and proof_state is not None
                and not defer_fresh_children_to_llm
            ):
                try:
                    state_ok, state_proof, ps_helpers = await _try_proof_state_child_closures(
                        conv=conv,
                        lean=lean,
                        dossier=dossier,
                        proof_state=proof_state,
                        recorder=session.recorder,
                        trace_prefix=session.trace_prefix,
                        turn=absolute_turn,
                        timeout_s=self.timeout_s,
                        max_candidates=self.max_candidates,
                        max_nodes=self.max_nodes,
                        max_decl_applications=self.max_decl_applications,
                        batch_parallelism=self.batch_parallelism,
                        proof_cache=proof_cache,
                    )
                except Exception:
                    state_ok, state_proof, ps_helpers = False, None, []
                proof_state_helpers.extend(ps_helpers or ())
                sync_proof_state_to_graph(
                    proof_state,
                    dossier,
                    session=session,
                    phase="helper_only_salvage_root_check",
                    turn_index=absolute_turn,
                )
                if state_ok and state_proof:
                    solved = True
                    proof = state_proof
                    solved_via = "helper_only_salvage_child_closure"
                    replay_helpers = tuple(dossier.verified_helper_blocks())
                    helper_names = tuple(
                        name
                        for block in replay_helpers
                        for name in [helper_decl_name(block)]
                        if name
                    )
                    root_candidate = RootFinalizationCandidate(
                        proof=state_proof,
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        phase="helper_only_salvage_child_closure",
                        turn_index=absolute_turn,
                        source_action_id=self.id,
                        target_statement=root_target_statement,
                        verification_certificate=root_verification_certificate(
                            accepted=True,
                            proof=state_proof,
                            phase="helper_only_salvage_child_closure",
                            turn_index=absolute_turn,
                            target_statement=root_target_statement,
                            replay_helpers=replay_helpers,
                            helper_names=helper_names,
                            source=self.id,
                        ),
                        metadata={"root_finalization_already_applied": True},
                    )

            # ---- Pathway (6): root-tactic close ----
            if not solved and accepted and self.max_candidates > 0 and dossier is not None:
                try:
                    helper_blocks = dossier.verified_helper_blocks()
                    root_tactic = await try_close_root_with_active_lift(
                        lean=lean,
                        goal_statement=conv.goal_statement,
                        preamble=_proof_state_acceptance_preamble(conv),
                        helpers=helper_blocks,
                        active_root_targets=tuple(
                            item
                            for item in list(getattr(dossier, "active_root_targets", []) or ())
                            if isinstance(item, dict)
                        ),
                        active_root_frame_helper_blocks=dossier.verified_helper_blocks(),
                        timeout_s=self.timeout_s,
                        max_candidates=max(1, self.max_candidates),
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
                            getattr(dossier, "official_answer_payload_present", None),
                        ),
                        tactic_source_suppression_records=tactic_source_suppression_records(
                            session
                        ),
                        tactic_source_suppression_helper_blocks=helper_blocks,
                        attempt_observer=dossier_lean_attempt_observer(
                            dossier,
                            "salvage_root_tactic",
                        ),
                    )
                except Exception:
                    root_tactic = None
                if root_tactic is not None and root_tactic.ok and root_tactic.proof:
                    success_attempt = next(
                        (
                            attempt
                            for attempt in getattr(root_tactic, "attempts", []) or []
                            if isinstance(attempt, dict) and attempt.get("ok")
                        ),
                        None,
                    )
                    contract_status = root_tactic_success_contract_status(
                        dossier,
                        proof=root_tactic.proof,
                        helper_blocks=dossier.verified_helper_blocks(),
                        success_attempt=success_attempt,
                        phase="helper_only_salvage_root_tactic",
                        turn_index=absolute_turn,
                        target_statement=root_target_statement,
                    )
                    replay_helpers = dossier.verified_helper_blocks()
                    helper_names = [
                        helper_decl_name(b) or ""
                        for b in replay_helpers
                        if helper_decl_name(b)
                    ]
                    if not bool(contract_status.get("ready")):
                        try:
                            dossier.record_attempt(
                                phase="helper_only_salvage_root_tactic",
                                turn_index=absolute_turn,
                                proof=root_tactic.proof,
                                helper_names=helper_names,
                                verdict="root_route_contract_not_ready",
                                metadata={
                                    "route_assembly_contract_status": contract_status,
                                },
                            )
                        except Exception:
                            pass
                        root_tactic = None
                if root_tactic is not None and root_tactic.ok and root_tactic.proof:
                    solved = True
                    proof = root_tactic.proof
                    solved_via = "helper_only_salvage_root_tactic"
                    route_helper_names = tuple(
                        str(name or "").strip()
                        for name in list(contract_status.get("helper_names") or [])
                        if str(name or "").strip()
                    )
                    if not route_helper_names:
                        route_helper_names = tuple(helper_names)
                    route_replay_helpers = tuple(
                        block
                        for block in replay_helpers
                        if (helper_decl_name(block) or "") in set(route_helper_names)
                    )
                    if not route_replay_helpers:
                        route_replay_helpers = tuple(replay_helpers)
                    root_candidate = RootFinalizationCandidate(
                        proof=root_tactic.proof,
                        replay_helpers=tuple(route_replay_helpers),
                        helper_names=tuple(route_helper_names),
                        phase="helper_only_salvage_root_tactic",
                        turn_index=absolute_turn,
                        source_action_id=self.id,
                        route_id=str(
                            contract_status.get("route_id")
                            or contract_status.get("created_route_id")
                            or ""
                        ),
                        dependency_node_ids=tuple(
                            str(node_id or "").strip()
                            for node_id in list(
                                contract_status.get("dependency_node_ids")
                                or contract_status.get("required_node_ids")
                                or []
                            )
                            if str(node_id or "").strip()
                        ),
                        target_statement=root_target_statement,
                        # A helper-free close (root_tactic_no_helper_dependencies)
                        # has no route to bind; requiring one would reject a
                        # Lean-accepted proof.  Match try_root_tactic_close.
                        require_route_contract=(
                            str(contract_status.get("verdict") or "")
                            != "root_tactic_no_helper_dependencies"
                        ),
                        verification_certificate=root_verification_certificate(
                            accepted=True,
                            proof=root_tactic.proof,
                            phase="helper_only_salvage_root_tactic",
                            turn_index=absolute_turn,
                            target_statement=root_target_statement,
                            replay_helpers=tuple(route_replay_helpers),
                            helper_names=tuple(route_helper_names),
                            output=str(
                                (success_attempt or {}).get("output")
                                or (success_attempt or {}).get("stdout")
                                or ""
                            ),
                            source=self.id,
                        ),
                        metadata={
                            "route_assembly_contract_status": dict(contract_status)
                        },
                    )

        cost = time.monotonic() - started
        raw_helpers_added = [*lemma_dag_helpers, *accepted, *proof_state_helpers]
        visible_helpers_added = (
            dossier.visible_accepted_helper_names(raw_helpers_added)
            if hasattr(dossier, "visible_accepted_helper_names")
            else list(raw_helpers_added)
        )
        parent_helper_progress = strong_progress_for_accepted_helpers(
            dossier,
            raw_helpers_added,
        )
        return MiniOutcome(
            action_id=self.id,
            solved=solved,
            proof=proof,
            helpers_added=tuple(visible_helpers_added),
            progress=bool(
                solved
                or visible_helpers_added
                or parent_helper_progress
            ),
            cost_seconds=cost,
            root_candidate=root_candidate,
            metadata={
                "lemma_dag_accepted": list(lemma_dag_helpers),
                "visible_helpers_added_count": len(visible_helpers_added),
                "lemma_dag_recorded_child_count": len(lemma_dag_child_node_ids),
                "new_child_node_ids": list(lemma_dag_child_node_ids),
                "linked_child_node_ids": list(lemma_dag_linked_child_node_ids),
                "strong_progress": (
                    bool(solved)
                    or parent_helper_progress
                ),
                "unverified_decomposition_created": bool(lemma_dag_child_node_ids),
                "deferred_fresh_children_to_recursive_helper": bool(
                    defer_fresh_children_to_llm
                ),
                "salvage_accepted": list(accepted),
                "salvage_rejected": rejected_or_skipped[0],
                "salvage_skipped": rejected_or_skipped[1],
                "proof_state_helpers": list(proof_state_helpers),
                "solved_via": solved_via,
                "replay_helpers": list(getattr(root_candidate, "replay_helpers", ()) or ()),
                "helper_names": list(getattr(root_candidate, "helper_names", ()) or ()),
                "root_finalization_already_applied": bool(
                    getattr(root_candidate, "metadata", {}).get(
                        "root_finalization_already_applied"
                    )
                    if root_candidate is not None
                    else False
                ),
            },
        )
