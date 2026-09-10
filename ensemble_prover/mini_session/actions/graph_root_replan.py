"""Explicit root planning after a bounded sequence of failed proof tools."""

from __future__ import annotations

import copy
import re
from collections.abc import Mapping
from typing import Any

from ...mini_falsification.model import content_hash
from ...proof_dossier import canonical_dossier_statement_key
from ..action import MiniOutcome
from ..planner_jobs import PlannerJobLaunch
from .recursive_controller import RecursiveControllerAction


class GraphRootReplanAction(RecursiveControllerAction):
    """Use the graph pass pool while keeping the flat proof turn suspended."""

    id = "graph_root_replan"
    _STALL_TOOL_ATTEMPTS = 3
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS = (
        RecursiveControllerAction.FAILED_DISPATCH_ROLLBACK_STATE_FIELDS
        | frozenset({"_active_replan_identity"})
    )
    _SETTINGS = (
        "config", "run_conversation_fn", "max_tool_calls_per_turn",
        "lean_check_tool_enabled", "try_lean_tool_enabled",
        "compute_examples_tool_enabled", "apply_decl_to_goal_tool_enabled",
        "raw_feedback", "repair_retrieval_enabled", "repair_retrieval_top_k",
        "proof_state_child_tactics_enabled", "proof_state_child_tactic_timeout_s",
        "proof_state_child_tactic_max_candidates", "root_tactic_timeout_s",
        "root_tactic_max_candidates", "proof_state_child_goal_limit",
        "proof_state_decl_application_limit", "proof_state_batch_parallelism",
    )

    def __init__(self, *, source_action: Any) -> None:
        super().__init__(
            action_id=self.id,
            priority=21,
            phase_label="[root replanning after proof-tool stall]",
            budget_attr="graph_recursive_decompose_remaining",
            **{name: getattr(source_action, name) for name in self._SETTINGS},
        )
        self._pending_replan_request: dict[str, Any] = {}
        self._served_replan_requests: list[str] = []
        self._active_replan_identity = ""

    @staticmethod
    def _context_identity(session: Any) -> str:
        return content_hash((
            str(session.problem.statement_type or ""),
            str(session.acceptance_preamble() or ""),
            tuple(session._durable_formal_progress_evidence()),
        ))

    def observe_proof_outcome(
        self, session: Any, outcome: MiniOutcome, *, formal_progress: bool,
        sustained_helper_progress: bool = False,
    ) -> None:
        if (
            self._pending_replan_request
            and not self._active_replan_identity
            and not self.selected_replan_work(session)
        ):
            self._pending_replan_request = {}
        if (
            (formal_progress and not sustained_helper_progress)
            or outcome.solved or outcome.exception is not None
        ):
            return
        if not outcome.action_id.startswith("conversation_turn"):
            return
        record = dict(session.selected_work_item_record or {})
        if record and session.selected_work_item_action_id != outcome.action_id:
            return
        if record and record.get("work_type") not in {"root_repair", "assemble_route"}:
            return
        root = str(session.problem.statement_type or "").strip()
        target = str(
            record.get("exact_target_statement") or record.get("target_statement")
            or getattr(session.conv, "goal_statement", "") or ""
        ).strip()
        if not root or canonical_dossier_statement_key(target) != canonical_dossier_statement_key(root):
            return
        metadata = outcome.metadata
        if (
            session._persistent_infrastructure_defer(metadata)
            or metadata.get("paid_tool_infrastructure_disposition")
            or int(metadata.get("provider_calls_completed", 0) or 0) <= 0
            or (
                not sustained_helper_progress
                and int(metadata.get("semantic_diagnostic_best_phase", -1)) < 0
            )
        ):
            return
        attempts = int(metadata.get("proof_tool_attempts", 0) or 0)
        stalled = int(metadata.get("consecutive_no_formal_progress", 0) or 0)
        if not sustained_helper_progress and (
            stalled < self._STALL_TOOL_ATTEMPTS or attempts < self._STALL_TOOL_ATTEMPTS
        ):
            return
        context = self._context_identity(session)
        identity = content_hash(
            (
                context, "sustained_helper_progress",
                session.helper_only_progress_identity,
                int(session.helper_only_provider_quanta),
            )
            if sustained_helper_progress else (
                context, outcome.action_id,
                int(metadata.get("conv_turn_index_absolute", 0) or 0),
                attempts // self._STALL_TOOL_ATTEMPTS,
            )
        )
        if identity in self._served_replan_requests or self._pending_replan_request:
            return
        self._pending_replan_request = {
            "node_id": str(session.dossier.proof_graph.root_node_id),
            "work_type": "root_replan",
            "source": "root_replan",
            "target_statement": root,
            "exact_target_statement": root,
            "context_identity": context,
            "root_environment_identity": content_hash((root, session.acceptance_preamble())),
            "request_identity": identity,
            "owner_action_id": outcome.action_id,
            "stalled_tool_attempts": stalled,
            "diagnostic_kind": str(metadata.get("semantic_diagnostic_best_error_kind") or ""),
            "sustained_helper_progress": sustained_helper_progress,
            "helper_only_progress_identity": (
                session.helper_only_progress_identity if sustained_helper_progress else ""
            ),
        }
        session._record_event({
            "phase": "session_root_replanning",
            "iteration": session.iteration,
            "verdict": "root_replan_requested",
            "selected_work_item": copy.deepcopy(self._pending_replan_request),
        })

    def selected_replan_work(self, session: Any) -> dict[str, Any]:
        request = self._pending_replan_request
        if not request:
            return {}
        if request.get("target_statement") != str(session.problem.statement_type or "").strip():
            return {}
        if request.get("root_environment_identity") != content_hash((
            str(session.problem.statement_type or "").strip(), session.acceptance_preamble(),
        )):
            return {}
        active = self._active_replan_identity == request.get("request_identity")
        if not active and request.get("sustained_helper_progress"):
            # This is a request to replan the unchanged obligation *after*
            # earned work drains. Additional checked helpers enrich that
            # planning context; only parent progress or a changed root can
            # discharge the sustained-progress intervention itself.
            if (
                request.get("helper_only_progress_identity")
                != session._helper_only_root_identity()
                or int(session.max_helper_only_provider_quanta or 0) <= 0
                or int(session.helper_only_provider_quanta or 0)
                < int(session.max_helper_only_provider_quanta)
            ):
                return {}
            selected = copy.deepcopy(request)
            selected["context_identity"] = self._context_identity(session)
            return selected
        if not active and request.get("context_identity") != self._context_identity(session):
            return {}
        return copy.deepcopy(request)

    def is_applicable(self, session: Any) -> bool:
        request = self.selected_replan_work(session)
        active = bool(self._active_replan_identity) and (
            self._active_replan_identity == request.get("request_identity")
        )
        return bool(
            request
            and not (
                request.get("sustained_helper_progress")
                # Once active, an owned ready result must publish even if
                # more child debt arrived while its provider was running.
                and not active
                and session._helper_only_progress_has_funded_continuation()
            )
            and getattr(session.conv, "allow_helper_decomposition", True)
            and (
                self._active_replan_identity
                or not session.repair_policy_narrowing_required
            )
            and super().is_applicable(session)
        )

    async def run(self, session: Any) -> MiniOutcome:
        if not self.is_applicable(session):
            return MiniOutcome(action_id=self.id, solved=False, proof=None, metadata={
                "verdict": "root_replan_not_serviceable", "scheduler_neutral": True,
                "preserve_action_budget": True, "iteration_neutral": True,
                "root_replan_invalidated": bool(
                    self._pending_replan_request and not self.selected_replan_work(session)
                ),
            })
        self._active_replan_identity = str(self._pending_replan_request["request_identity"])
        return await super().run(session)

    def has_owned_active_continuation(self, session: Any) -> bool:
        """Keep paid planner work live without trusting an orphaned marker."""

        if not self._active_replan_identity or not self.selected_replan_work(session):
            return False
        budget = session.budgets.get(self.id)
        dispatch_funded = budget is None or not budget.exhausted()
        driver = self._recursive_driver_state
        identity = driver.get("planner_job_identity")
        broker_status = "missing"
        owned_launch = False
        if driver.get("phase") == "planner_job_pending" and isinstance(identity, Mapping):
            job_id = str(identity.get("job_id") or "").strip()
            fingerprint = str(identity.get("request_fingerprint") or "").strip()
            if job_id and fingerprint:
                launch = self._pending_planner_job_launch
                owned_launch = isinstance(launch, PlannerJobLaunch) and (
                    launch.identity.job_id == job_id
                    and launch.identity.request_fingerprint == fingerprint
                )
                broker = session.planner_job_broker(create=False)
                if broker is not None:
                    broker_status = broker.status(job_id, fingerprint)
        # The scheduler publishes owned ready broker receipts independently
        # of the ordinary action budget, but run() must still accept the work.
        if (dispatch_funded or broker_status == "ready") and session._safe_is_applicable(
            self, context="sustained_helper_progress_active",
        ):
            return True
        if owned_launch or broker_status == "pending":
            return True
        wait = self._planner_equivalent_wait
        return bool(
            wait
            and wait["frontier_signature"] == self._session_progress_signature(session)
            and self._can_wait_for_equivalent_planner(
                session, wait["job_id"], wait["request_fingerprint"],
            )
        )

    def on_outcome_applied(self, session: Any, outcome: MiniOutcome) -> None:
        invalidated = bool(outcome.metadata.get("root_replan_invalidated"))
        if outcome.metadata.get("verdict") == "root_replan_not_serviceable" and not invalidated:
            # A pending provider or temporarily empty pool retains its already
            # authorized request and reservation. A changed root retires them.
            return
        super().on_outcome_applied(session, outcome)
        if not invalidated and (
            outcome.metadata.get("planner_job_pending")
            or outcome.metadata.get("recursive_pass_quantum_yield")
            or outcome.metadata.get("llm_retryable")
            or outcome.metadata.get("preserve_action_budget")
        ):
            return
        identity = str(self._pending_replan_request.get("request_identity") or "")
        if (
            identity and not invalidated and outcome.exception is None
            and int(outcome.metadata.get("passes_used", 0) or 0) > 0
            and session._helper_only_progress_intervention_due()
        ):
            session._reset_helper_only_progress_window()
        if identity:
            self._served_replan_requests = [*self._served_replan_requests, identity][-256:]
        self._pending_replan_request = {}
        self._active_replan_identity = ""

    def scheduler_runtime_state(self) -> dict[str, Any]:
        return {
            **super().scheduler_runtime_state(),
            "root_replan_request": copy.deepcopy(self._pending_replan_request),
            "served_root_replans": list(self._served_replan_requests),
            "active_root_replan": self._active_replan_identity,
        }

    def apply_scheduler_runtime_state(self, state: Any) -> None:
        record = dict(state or {})
        pending = record.get("root_replan_request", {})
        served = record.get("served_root_replans", [])
        active = record.get("active_root_replan", "")
        if not isinstance(pending, dict) or not isinstance(served, list) or len(served) > 256:
            raise ValueError("invalid root replanning runtime state")
        if any(not isinstance(item, str) or len(item) != 64 for item in served):
            raise ValueError("invalid root replanning request history")
        if not isinstance(active, str) or (active and active != pending.get("request_identity")):
            raise ValueError("invalid active root replanning request")
        # Legacy requests omit this optional pair. New intervention intent
        # must not silently change meaning through truthiness or coercion.
        if "sustained_helper_progress" in pending or "helper_only_progress_identity" in pending:
            sustained = pending.get("sustained_helper_progress")
            helper_identity = pending.get("helper_only_progress_identity")
            if type(sustained) is not bool or not isinstance(helper_identity, str):
                raise ValueError("invalid sustained helper replanning request")
            if (sustained and re.fullmatch(r"[0-9a-f]{64}", helper_identity) is None) or (
                not sustained and helper_identity
            ):
                raise ValueError("invalid sustained helper replanning identity")
        super().apply_scheduler_runtime_state(record)
        self._pending_replan_request = copy.deepcopy(pending)
        self._served_replan_requests = list(served)
        self._active_replan_identity = active
