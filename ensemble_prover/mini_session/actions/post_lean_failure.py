"""PostLeanFailureAction — direct replay wrapper for the post-failure cascade.

Wraps the post-failure cascade orchestrator (``run_post_failure_cascade``
from mini_session.turn.post_failure). Normal mini sessions do not register this
as a scheduler action: ``ConversationTurnAction`` owns rejected-turn handling
inline and charges the ``post_lean_failure`` budget bucket directly. This class
remains importable for focused replay/unit tests.

The session's ``ConversationTurnAction.run`` populates
``session.last_lean_verdict`` and ``session.last_turn_extraction`` after
each pipeline pass. PostLeanFailureAction reads those, runs the
cascade, and stores the result on ``session.last_post_failure_result``
for downstream observers.

The class still reads ``session.last_lean_verdict`` and
``session.last_turn_extraction`` when invoked directly, but production
registration intentionally has a single owner to avoid stale verdict replays.
"""

from __future__ import annotations

import hashlib
import json
import time
from typing import Any, ClassVar, FrozenSet, List, Optional

from ...proof_dossier import helper_decl_name, strong_progress_for_accepted_helpers
from ...root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ..action import MiniOutcome


class PostLeanFailureAction:
    id: str = "post_lean_failure"
    priority: int = 25
    cost_estimate_s: float = 30.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"conv", "dossier", "proof_state"})
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {"_fired_for_verdict_key"}
    )

    def __init__(
        self,
        *,
        timeout_s: float = 30.0,
        max_nodes: int = 3,
        max_candidates: int = 32,
        max_decl_applications: int = 6,
        batch_parallelism: int = 1,
        repair_retrieval_top_k: int = 6,
        raw_feedback: bool = False,
    ) -> None:
        self.timeout_s = float(timeout_s or 0.0)
        self.max_nodes = int(max_nodes or 0)
        self.max_candidates = int(max_candidates or 0)
        self.max_decl_applications = int(max_decl_applications or 0)
        self.batch_parallelism = int(batch_parallelism or 1)
        self.repair_retrieval_top_k = int(repair_retrieval_top_k or 0)
        self.raw_feedback = bool(raw_feedback)
        self._fired_for_verdict_key: str = ""

    @staticmethod
    def _verdict_key(verdict: Any) -> str:
        if verdict is None:
            return ""
        payload = {
            key: getattr(verdict, key, None)
            for key in (
                "accepted",
                "error_type",
                "output",
                "feedback",
                "proof",
                "elapsed_s",
            )
        }
        return hashlib.sha256(
            json.dumps(payload, sort_keys=True, default=str).encode("utf-8")
        ).hexdigest()



    def _last_verdict(self, session: Any) -> Optional[Any]:
        return getattr(session, "last_lean_verdict", None)

    def _last_extraction(self, session: Any) -> Optional[Any]:
        return getattr(session, "last_turn_extraction", None)

    def is_applicable(self, session: Any) -> bool:
        if session.dossier is None or session.lean is None or session.conv is None:
            return False
        verdict = self._last_verdict(session)
        if verdict is None or getattr(verdict, "accepted", True):
            return False
        if self._verdict_key(verdict) == self._fired_for_verdict_key:
            return False
        return True

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.helper_salvage import merge_context_helpers
        from ensemble_prover.mini_prover import _drop_last_assistant_if_content
        from ensemble_prover.mini_session.turn import run_post_failure_cascade

        started = time.monotonic()
        verdict = self._last_verdict(session)
        extraction = self._last_extraction(session)
        self._fired_for_verdict_key = self._verdict_key(verdict)

        helpers: List[str] = list(getattr(extraction, "helpers", ()) or ())
        proof = getattr(extraction, "proof", "") or ""
        lemma_dag = list(getattr(extraction, "lemma_dag_candidates", ()) or ())
        context_helpers = (
            session.dossier.verified_helper_blocks() if session.dossier is not None else []
        )
        check_lemmas = merge_context_helpers(context_helpers, helpers)
        action_available = getattr(session, "action_available", None)
        raw_depth_cap = getattr(session, "max_recursion_depth", 3)
        depth_cap = int(raw_depth_cap if raw_depth_cap is not None else 3)
        recursion_depth = int(getattr(session, "recursion_depth", 0) or 0)
        depth_allows_recursive_helper = depth_cap <= 0 or recursion_depth < depth_cap
        defer_rejected_helper_children_to_llm = (
            bool(action_available("recursive_helper_prover"))
            if callable(action_available)
            else False
        )
        defer_rejected_helper_children_to_llm = bool(
            defer_rejected_helper_children_to_llm
            and depth_allows_recursive_helper
            and session.dossier is not None
            and session.lean is not None
            and session.conv is not None
            and getattr(session, "prover_client", None) is not None
            and session.proof_state is not None
        )
        phase_turn = int(getattr(session, "iteration", 0) or 0)
        max_turns = max(
            1,
            int(
                getattr(session.conv, "turn_budget", 0)
                or getattr(session, "max_iterations", 0)
                or phase_turn
                or 1
            ),
        )
        selected_work_item = dict(
            getattr(session, "selected_work_item_record", {}) or {}
        )
        selected_work_type = str(selected_work_item.get("work_type") or "").strip()
        graph_native_target: dict[str, str] = {}
        try:
            from ensemble_prover.mini_session.actions.conversation_turn import (
                _selected_graph_native_proof_target,
            )

            graph_native_target = dict(_selected_graph_native_proof_target(session))
        except Exception:
            graph_native_target = {}
        graph_native_target_statement = str(
            graph_native_target.get("statement") or ""
        ).strip()
        if graph_native_target_statement:
            selected_work_item.setdefault(
                "target_statement",
                graph_native_target_statement,
            )
            selected_work_item.setdefault(
                "graph_native_goal_statement",
                graph_native_target_statement,
            )
        graph_native_failure_context = bool(
            selected_work_type
            in {
                "formalize_claim",
                "formalize_missing_obligation",
                "prove_claim_variant",
                "mine_missing_obligation",
                "route_replan",
                "target_integrity_adjudication",
                "materialize_replay_source",
            }
            or selected_work_item.get("formalization_required")
            or selected_work_item.get("materialization_required")
            or selected_work_item.get("formalization_statement_pending")
        )
        selected_target_statement = str(
            selected_work_item.get("target_statement")
            or graph_native_target_statement
            or ""
        ).strip()
        target_statement = str(
            selected_target_statement
            or (
                ""
                if graph_native_failure_context
                else (
                    getattr(session.conv, "goal_statement", "")
                    or getattr(session.dossier, "root_statement", "")
                    or ""
                )
            )
        ).strip()
        conv_turn_absolute = getattr(session, "_conversation_turn_count", None)
        repair_retrieval_enabled = bool(
            getattr(session, "searcher", None) is not None
            and (not graph_native_failure_context or selected_target_statement)
        )

        cascade = await run_post_failure_cascade(
            conv=session.conv,
            lean=session.lean,
            dossier=session.dossier,
            proof_state=session.proof_state,
            proof=proof,
            helpers=helpers,
            lemma_dag_candidate_helpers=lemma_dag,
            check_lemmas=check_lemmas,
            context_helpers=context_helpers,
            feedback_result=getattr(verdict, "feedback_result", None),
            feedback_source=getattr(verdict, "feedback_source", "primary_check"),
            proof_cache=session.proof_cache,
            searcher=session.searcher,
            repair_retrieval_enabled=repair_retrieval_enabled,
            repair_retrieval_top_k=self.repair_retrieval_top_k,
            proof_state_child_tactics_enabled=True,
            proof_state_child_tactic_timeout_s=self.timeout_s,
            proof_state_child_tactic_max_candidates=self.max_candidates,
            proof_state_child_goal_limit=self.max_nodes,
            proof_state_decl_application_limit=self.max_decl_applications,
            proof_state_batch_parallelism=self.batch_parallelism,
            raw_feedback=self.raw_feedback,
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=phase_turn,
            max_turns=max_turns,
            role=getattr(session.conv, "role", "prove"),
            # Code review fix (2026-05-09): plumb llm_output + opaque_mode
            # so the give-up gate fires on this subaction path too. Without
            # this, the M4 subaction dispatch silently skips the
            # decomposition redirect.
            llm_output=str(getattr(session, "last_llm_content", "") or ""),
            opaque_mode=bool(getattr(session.conv, "opaque_mode", True)),
            allow_official_answer_visibility=bool(
                getattr(session.conv, "allow_official_answer_visibility", False)
            ),
            official_answer_payload_present=getattr(
                session.conv,
                "official_answer_payload_present",
                getattr(session.dossier, "official_answer_payload_present", None),
            ),
            allow_helper_decomposition=bool(
                getattr(session.conv, "allow_helper_decomposition", True)
            ),
            # Phase 2 (2026-05-09): plumb recursion depth for depth-aware nudge.
            recursion_depth=int(getattr(session, "recursion_depth", 0) or 0),
            max_recursion_depth=int(
                getattr(session, "max_recursion_depth", 3)
                if getattr(session, "max_recursion_depth", 3) is not None
                else 3
            ),
            defer_fresh_helper_children_to_llm=defer_rejected_helper_children_to_llm,
            proof_state_failure_context_enabled=not graph_native_failure_context,
            repair_goal_statement=target_statement,
            selected_work_item=selected_work_item,
            target_statement=target_statement,
            event_context={
                "session_scope": str(getattr(session, "scope", "") or ""),
                "conv_turn_absolute": conv_turn_absolute,
                "conv_turn_index_absolute": conv_turn_absolute,
            },
        )
        # Stash the result for observers (e.g., downstream tests, M5+
        # validation harness reads this).
        session.last_post_failure_result = cascade

        # Append cascade feedback to conv if we did not solve.
        if not cascade.solved and cascade.feedback_text:
            try:
                if cascade.giveup_cluster or cascade.target_integrity_signals:
                    _drop_last_assistant_if_content(
                        session.conv,
                        str(getattr(session, "last_llm_content", "") or ""),
                    )
                session.conv.append_user(cascade.feedback_text)
            except Exception:
                pass

        repair_ticket = None
        if (
            not cascade.solved
            and proof
            and not cascade.target_integrity_bypass_local_repair
        ):
            try:
                from ensemble_prover.mini_session.actions.conversation_turn import (
                    _lean_failure_wall_signature,
                    _repair_ticket_from_lean_rejection,
                )

                failure_signature = _lean_failure_wall_signature(
                    cascade.failure_analysis
                )
                lean_output = str(
                    getattr(getattr(verdict, "feedback_result", None), "output", "")
                    or ""
                )
                repair_ticket = _repair_ticket_from_lean_rejection(
                    session=session,
                    action_id=self.id,
                    proof=proof,
                    check_lemmas=check_lemmas,
                    lean_output=lean_output,
                    feedback_text=cascade.feedback_text,
                    feedback_source=str(
                        getattr(verdict, "feedback_source", "primary_check")
                    ),
                    error_type=str(cascade.failure_analysis.get("error_type") or ""),
                    failure_signature=failure_signature,
                    turn_index=phase_turn,
                    metadata={
                        "feedback_mode": cascade.feedback_mode,
                        "failure_analysis": dict(cascade.failure_analysis or {}),
                    },
                )
            except Exception:
                repair_ticket = None

        cost = time.monotonic() - started
        target_integrity_adjudication_available = bool(
            cascade.target_integrity_obligation_node_ids
            or cascade.target_integrity_replan_node_ids
        )
        target_integrity_adjudication_created = bool(
            cascade.target_integrity_adjudication_materialized
        )
        raw_helpers_added = list(cascade.salvaged_helper_names) + list(
            cascade.rejected_helper_triage_accepted
        )
        visible_helpers_added = (
            session.dossier.visible_accepted_helper_names(raw_helpers_added)
            if hasattr(session.dossier, "visible_accepted_helper_names")
            else list(raw_helpers_added)
        )
        visible_proof_state_helpers = (
            session.dossier.visible_accepted_helper_names(cascade.proof_state_helpers)
            if hasattr(session.dossier, "visible_accepted_helper_names")
            else list(cascade.proof_state_helpers or ())
        )
        raw_parent_progress_helpers = raw_helpers_added + list(
            cascade.proof_state_helpers or ()
        )
        parent_helper_progress = strong_progress_for_accepted_helpers(
            session.dossier,
            raw_parent_progress_helpers,
        )
        target_integrity_progress_suppressed = bool(
            target_integrity_adjudication_created
            and not cascade.solved
            and not visible_helpers_added
            and not visible_proof_state_helpers
            and not parent_helper_progress
        )
        if target_integrity_progress_suppressed:
            increment = getattr(session, "_increment_dossier_metric", None)
            if callable(increment):
                try:
                    increment(
                        "mini_session_target_integrity_adjudication_progress_suppressed",
                        1,
                    )
                except Exception:
                    pass
        root_candidate = None
        if cascade.solved and cascade.proof:
            helper_names = tuple(
                name
                for block in check_lemmas
                for name in [helper_decl_name(block)]
                if name
            )
            root_candidate = RootFinalizationCandidate(
                proof=cascade.proof,
                replay_helpers=tuple(check_lemmas),
                helper_names=helper_names,
                phase=cascade.solved_via or self.id,
                turn_index=phase_turn,
                source_action_id=self.id,
                target_statement=str(
                    getattr(session.conv, "goal_statement", "")
                    or getattr(session.dossier, "root_statement", "")
                    or ""
                ),
                verification_certificate=root_verification_certificate(
                    accepted=True,
                    proof=cascade.proof,
                    phase=cascade.solved_via or self.id,
                    turn_index=phase_turn,
                    target_statement=str(
                        getattr(session.conv, "goal_statement", "")
                        or getattr(session.dossier, "root_statement", "")
                        or ""
                    ),
                    replay_helpers=tuple(check_lemmas),
                    helper_names=helper_names,
                    source=self.id,
                ),
                metadata={"root_finalization_already_applied": True},
            )
        return MiniOutcome(
            action_id=self.id,
            solved=bool(cascade.solved),
            proof=cascade.proof if cascade.solved else None,
            helpers_added=tuple(visible_helpers_added),
            progress=bool(
                cascade.solved
                or visible_helpers_added
                or visible_proof_state_helpers
                or parent_helper_progress
            ),
            cost_seconds=cost,
            repair_ticket=repair_ticket,
            root_candidate=root_candidate,
            metadata={
                "salvaged_helper_count": len(cascade.salvaged_helper_names),
                "proof_state_helper_count": len(cascade.proof_state_helpers),
                "rejected_helper_triage_accepted_count": len(
                    cascade.rejected_helper_triage_accepted
                ),
                "visible_helpers_added_count": len(visible_helpers_added),
                "visible_proof_state_helper_count": len(visible_proof_state_helpers),
                "rejected_helper_child_node_count": len(
                    cascade.rejected_helper_child_node_ids
                ),
                "rejected_helper_linked_child_node_count": len(
                    getattr(cascade, "rejected_helper_linked_child_node_ids", [])
                ),
                "strong_progress": (
                    bool(cascade.solved)
                    or parent_helper_progress
                ),
                "unverified_decomposition_created": bool(
                    cascade.rejected_helper_child_node_ids
                ),
                "deferred_rejected_helper_children_to_recursive_helper": bool(
                    cascade.deferred_rejected_helper_children_to_recursive_helper
                ),
                "feedback_mode": cascade.feedback_mode,
                "giveup_cluster": cascade.giveup_cluster,
                "giveup_match": cascade.giveup_match,
                "target_integrity_signals": list(cascade.target_integrity_signals),
                "target_integrity_bypass_local_repair": bool(
                    cascade.target_integrity_bypass_local_repair
                ),
                "target_integrity_disable_proof_state_repair": bool(
                    cascade.target_integrity_disable_proof_state_repair
                ),
                "target_integrity_obligation_node_ids": list(
                    cascade.target_integrity_obligation_node_ids
                ),
                "target_integrity_replan_node_ids": list(
                    cascade.target_integrity_replan_node_ids
                ),
                "target_integrity_adjudication_available": (
                    target_integrity_adjudication_available
                ),
                "target_integrity_adjudication_created": (
                    target_integrity_adjudication_created
                ),
                "target_integrity_adjudication_progress_suppressed": (
                    target_integrity_progress_suppressed
                ),
                "repair_ticket_id": (
                    repair_ticket.ticket_id if repair_ticket is not None else ""
                ),
            },
        )
