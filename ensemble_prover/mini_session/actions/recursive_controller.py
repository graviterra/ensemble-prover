"""Dispatch bounded recursive decomposition through the session scheduler.

Each recursive attempt receives subgoal-scoped proof state. Normal recursive
work consumes ``recursive_pass_budget_remaining``; adaptive fallback uses the
separate ``adaptive_recursive_pass_budget_remaining`` pool so prepass work
cannot consume its last-resort allowance.
"""

from __future__ import annotations

import asyncio
import copy
from dataclasses import asdict, replace
import time
from typing import Any, Callable, ClassVar, FrozenSet, Optional
import weakref

from ensemble_prover.proof_dossier import (
    helper_decl_name,
    strong_progress_for_accepted_helpers,
    verified_helper_is_premise_projection,
)
from ensemble_prover.helper_quality import verified_helper_admission_quality
from ensemble_prover.llm_error_policy import (
    is_terminal_llm_failure_reason,
    llm_failure_scope,
    projected_scoped_llm_failure_is_retryable,
)
from ensemble_prover.llm_usage import llm_usage_context_metadata
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ensemble_prover.mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ensemble_prover.mini_recursive_identity import (
    mini_recursive_operational_action_spec_paths,
)
from ensemble_prover.mini_recursive_outcome import (
    is_resumable_mini_recursive_yield,
)
from ensemble_prover.mini_session.planner_jobs import (
    PlannerJobLaunch,
    PlannerJobYield,
)

from ..action import MiniOutcome
from ..state_codec import StateSnapshotCompatibilityError, StateSnapshotError


def _verified_helper_names(dossier: Any) -> tuple[str, ...]:
    """Return durable verified-helper names in dossier insertion order."""

    helpers = getattr(dossier, "verified_helpers", None)
    if not isinstance(helpers, dict):
        return ()
    names: list[str] = []
    for name in helpers.keys():
        text = str(name or "").strip()
        if text:
            visible = getattr(dossier, "is_verified_helper_context_visible", None)
            if callable(visible) and not bool(visible(text)):
                continue
            names.append(text)
    return tuple(names)


class RecursiveControllerAction:
    id: str = "recursive_controller"
    priority: int = 20
    cost_estimate_s: float = 300.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier"})
    REPLAY_OPERATIONAL_SPEC_PATHS: ClassVar[FrozenSet[str]] = (
        mini_recursive_operational_action_spec_paths()
    )
    # The normal controller and the adaptive fallback have independent pass
    # cursors, but they depend on the same planner transport.  Scheduler
    # deferral therefore has to cover the family, not merely the action id
    # that happened to observe the transport failure.
    MODEL_CALL_DEFER_FAMILY: ClassVar[str] = "recursive_planner"
    FAILED_DISPATCH_DURABLE_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "_recursive_driver_state",
            "_recursive_root_tactic_context_keys_seen",
        }
    )
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "_recursive_driver_state",
            "_recursive_root_tactic_context_keys_seen",
            "_pending_planner_job_launch",
            "_planner_job_receipt_identities",
        }
    )

    def scheduler_runtime_state(self) -> dict[str, Any]:
        """Return versioned provider-free cursor state for exact replay."""

        return {
            "schema_version": 1,
            "recursive_driver_state": copy.deepcopy(self._recursive_driver_state),
            "recursive_root_tactic_context_keys_seen": sorted(
                self._recursive_root_tactic_context_keys_seen
            ),
            "recursive_fixed_point_environment_signature": str(
                self._recursive_fixed_point_environment_signature or ""
            ),
            "recursive_fixed_point_reason": str(
                self._recursive_fixed_point_reason or ""
            ),
        }

    def apply_scheduler_runtime_state(self, state: Any) -> None:
        """Restore a cursor emitted by :meth:`scheduler_runtime_state`."""

        record = dict(state or {}) if isinstance(state, dict) else {}
        if int(record.get("schema_version", 0) or 0) != 1:
            raise StateSnapshotCompatibilityError(
                "recursive controller runtime-state schema is unsupported"
            )
        driver_state = record.get("recursive_driver_state")
        if not isinstance(driver_state, dict):
            raise StateSnapshotCompatibilityError(
                "recursive controller driver cursor is malformed"
            )
        self._recursive_driver_state = copy.deepcopy(driver_state)
        self._recursive_root_tactic_context_keys_seen = {
            str(item or "")
            for item in list(
                record.get("recursive_root_tactic_context_keys_seen") or []
            )
            if str(item or "")
        }
        self._recursive_fixed_point_environment_signature = str(
            record.get("recursive_fixed_point_environment_signature") or ""
        )
        self._recursive_fixed_point_reason = str(
            record.get("recursive_fixed_point_reason") or ""
        )

    def __init__(
        self,
        *,
        action_id: str = "recursive_controller",
        priority: int = 20,
        phase_label: str = "[mini-recursive]",
        config: Any = None,
        run_conversation_fn: Optional[Callable[..., Any]] = None,
        max_tool_calls_per_turn: int = 10,
        lean_check_tool_enabled: bool = True,
        try_lean_tool_enabled: bool = False,
        compute_examples_tool_enabled: bool = False,
        apply_decl_to_goal_tool_enabled: bool = False,
        raw_feedback: bool = False,
        repair_retrieval_enabled: bool = True,
        repair_retrieval_top_k: int = 6,
        proof_state_child_tactics_enabled: bool = True,
        proof_state_child_tactic_timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        proof_state_child_tactic_max_candidates: int = 32,
        root_tactic_timeout_s: float = 40.0,
        root_tactic_max_candidates: int = 64,
        proof_state_child_goal_limit: int = 3,
        proof_state_decl_application_limit: int = 6,
        proof_state_batch_parallelism: int = 1,
        budget_attr: str = "recursive_pass_budget_remaining",
    ) -> None:
        self.id = str(action_id or "recursive_controller")
        self.priority = int(priority)
        self.phase_label = str(phase_label or "[mini-recursive]")
        self.config = config
        self.run_conversation_fn = run_conversation_fn
        self.max_tool_calls_per_turn = int(max_tool_calls_per_turn or 0)
        self.lean_check_tool_enabled = bool(lean_check_tool_enabled)
        self.try_lean_tool_enabled = bool(try_lean_tool_enabled)
        self.compute_examples_tool_enabled = bool(compute_examples_tool_enabled)
        self.apply_decl_to_goal_tool_enabled = bool(apply_decl_to_goal_tool_enabled)
        self.raw_feedback = bool(raw_feedback)
        self.repair_retrieval_enabled = bool(repair_retrieval_enabled)
        self.repair_retrieval_top_k = int(repair_retrieval_top_k or 0)
        self.proof_state_child_tactics_enabled = bool(proof_state_child_tactics_enabled)
        self.proof_state_child_tactic_timeout_s = float(
            proof_state_child_tactic_timeout_s or 0.0
        )
        self.proof_state_child_tactic_max_candidates = int(
            proof_state_child_tactic_max_candidates or 0
        )
        self.root_tactic_timeout_s = float(root_tactic_timeout_s or 0.0)
        self.root_tactic_max_candidates = int(root_tactic_max_candidates or 0)
        self.proof_state_child_goal_limit = int(proof_state_child_goal_limit or 0)
        self.proof_state_decl_application_limit = int(
            proof_state_decl_application_limit or 0
        )
        self.proof_state_batch_parallelism = int(proof_state_batch_parallelism or 1)
        self.budget_attr = str(budget_attr or "recursive_pass_budget_remaining")
        self._nested_execution_frame: dict[str, Any] = {}
        self._recursive_driver_state: dict[str, Any] = {}
        self._recursive_root_tactic_context_keys_seen: set[str] = set()
        self._recursive_fixed_point_environment_signature = ""
        self._recursive_fixed_point_reason = ""
        self._pending_planner_job_launch: Optional[PlannerJobLaunch] = None
        self._planner_job_receipt_identities: dict[
            tuple[str, str], Any
        ] = {}

    @staticmethod
    def _session_progress_signature(session: Any) -> str:
        signature = getattr(session, "_recursive_planner_frontier_signature", None)
        if not callable(signature):
            # Compatibility for lightweight third-party/test sessions.  Real
            # MiniSession instances use the planner-specific identity so
            # graph-only churn cannot reopen a paid recursive fixed point.
            signature = getattr(session, "_durable_search_progress_signature", None)
        if not callable(signature):
            return ""
        try:
            return str(signature() or "")
        except Exception:
            return ""

    def on_outcome_applied(self, session: Any, outcome: MiniOutcome) -> None:
        # ``run`` normally retires its allocation before returning an
        # outcome.  A run-governor deadline can instead cancel ``run`` and
        # synthesize a terminal outcome from the restored durable cutpoint.
        # In that path the reservation deliberately survives cancellation,
        # but it is no longer resumable once the synthesized outcome is
        # accepted.  Retire it in the common publication hook so a terminal
        # quiescent checkpoint cannot retain a phantom pass allocation.
        planner_pending = bool(outcome.metadata.get("planner_job_pending"))
        pending_identity_record = outcome.metadata.get("planner_job_identity")
        pending_key = (
            str(pending_identity_record.get("job_id") or ""),
            str(pending_identity_record.get("request_fingerprint") or ""),
        ) if isinstance(pending_identity_record, dict) else ("", "")
        broker_getter = getattr(session, "planner_job_broker", None)
        broker = broker_getter(create=False) if callable(broker_getter) else None
        retained: dict[tuple[str, str], Any] = {}
        for key, identity in self._planner_job_receipt_identities.items():
            if planner_pending and key == pending_key:
                retained[key] = identity
                continue
            if broker is not None:
                broker.acknowledge(identity)
        self._planner_job_receipt_identities = retained
        if planner_pending:
            # The pass has reached provider I/O but has not completed.  Its
            # allocation and compact driver cursor remain authoritative until
            # the scheduler-owned raw receipt is consumed or invalidated.
            return
        self._clear_inflight_reservation(session)
        self._nested_execution_frame = {}
        fixed_point_reason = str(
            outcome.metadata.get("recursive_fixed_point_reason") or ""
        ).strip()
        if fixed_point_reason:
            # ``run`` captures this while runtime capabilities are still
            # admitted.  Settlement revokes the action-facing checkpoint
            # facade before this publication hook, so recomputing here would
            # turn a valid fixed point into an infrastructure rollback.
            fixed_point_signature = str(
                outcome.metadata.get(
                    "recursive_fixed_point_environment_signature"
                )
                or ""
            ).strip()
            if not fixed_point_signature:
                fixed_point_signature = str(
                    self._recursive_driver_state.get(
                        "outer_recursive_planner_signature"
                    )
                    or ""
                ).strip()
            if not fixed_point_signature:
                fixed_point_signature = self._session_progress_signature(session)
            if (
                callable(
                    getattr(
                        session,
                        "_recursive_planner_frontier_signature",
                        None,
                    )
                )
                and not fixed_point_signature
            ):
                raise StateSnapshotError(
                    "recursive fixed point cannot be published without a "
                    "planner-frontier identity"
                )
            self._recursive_fixed_point_environment_signature = (
                fixed_point_signature
            )
            self._recursive_fixed_point_reason = fixed_point_reason
        if not bool(outcome.metadata.get("recursive_pass_quantum_yield")):
            terminal_result = self._recursive_driver_state.get("terminal_result")
            terminal_failure_reason = (
                str(dict(terminal_result).get("failure_reason") or "").strip()
                if isinstance(terminal_result, dict)
                else ""
            )
            if (
                str(self._recursive_driver_state.get("phase") or "")
                == "terminal_committed"
                and terminal_failure_reason == "recursive_passes_exhausted"
            ):
                # A configured pass limit is an allocation boundary, not a
                # mathematical fixed point.  The session may explicitly grant
                # this action another pass later (notably the one-pass adaptive
                # fallback lane).  Retain the completed frontier as a
                # pass-committed cursor so that durable tactic deduplication,
                # planner-degeneracy streaks, and failed-claim memory survive
                # that new allocation.  Clearing here made every recovered
                # allocation enter as pass 1 and replay the same root tactic
                # portfolio plus the same paid planner failure indefinitely.
                next_pass = max(
                    1,
                    int(self._recursive_driver_state.get("pass_index", 1) or 1),
                )
                self._recursive_driver_state["phase"] = "pass_committed"
                self._recursive_driver_state["passes"] = max(
                    next_pass,
                    int(self._recursive_driver_state.get("passes", 1) or 1),
                )
                self._recursive_driver_state["terminal_result"] = None
                self._recursive_driver_state.pop(
                    "outer_recursive_planner_signature", None
                )
            else:
                self._recursive_driver_state = {}

    def _driver_has_committed_pass(self) -> bool:
        return str(self._recursive_driver_state.get("phase") or "") in {
            "pass_committed",
            "terminal_committed",
        }

    def _terminal_receipt_pending_publication(self, session: Any = None) -> bool:
        current_signature = (
            self._session_progress_signature(session) if session is not None else ""
        )
        return bool(
            str(self._recursive_driver_state.get("phase") or "")
            == "terminal_committed"
            and isinstance(self._recursive_driver_state.get("terminal_result"), dict)
            and current_signature
            and str(
                self._recursive_driver_state.get(
                    "outer_recursive_planner_signature"
                )
                or ""
            )
            == current_signature
        )

    def _recover_inflight_reservation(self, session: Any) -> int:
        """Re-credit a recursive allocation checkpointed before completion."""

        reservations = getattr(session, "recursive_inflight_reservations", None)
        if not isinstance(reservations, dict):
            return 0
        record = reservations.get(self.id)
        if not isinstance(record, dict):
            return 0
        try:
            pool_attr = str(record.get("pool_attr") or "").strip()
            reserved = max(0, int(record.get("reserved_passes", 0) or 0))
            persisted_extension_grants = max(
                0,
                int(
                    self._recursive_driver_state.get(
                        "pass_extension_grants",
                        0,
                    )
                    or 0
                ),
            )
            credited_extension_grants = max(
                0,
                int(record.get("credited_extension_grants", 0) or 0),
            )
            authorized_ceiling = max(
                0,
                int(
                    self._recursive_driver_state.get(
                        "controller_authorized_pass_ceiling",
                        0,
                    )
                    or 0
                ),
            )
            pass_index = max(
                1,
                int(self._recursive_driver_state.get("pass_index", 1) or 1),
            )
        except (TypeError, ValueError) as exc:
            raise StateSnapshotCompatibilityError(
                "recursive reservation has malformed pass-credit provenance"
            ) from exc
        if pool_attr != self.budget_attr or reserved <= 0:
            reservations.pop(self.id, None)
            return 0
        # The driver publishes its state to this action before asking the
        # session coordinator to persist it.  Cancellation can therefore
        # leave both an inflight reservation and a fully committed pass
        # receipt.  That reservation has already been consumed: re-crediting
        # it would make the completed pass free and allow one extra pass after
        # resume.  Earlier phases remain unfinished work and must be
        # re-credited before the exact mid-pass frontier is resumed.
        pass_already_committed = self._driver_has_committed_pass()
        max_authorized_extensions = max(0, authorized_ceiling - pass_index)
        if (
            credited_extension_grants > persisted_extension_grants
            or (
                authorized_ceiling > 0
                and persisted_extension_grants > max_authorized_extensions
            )
        ):
            raise StateSnapshotCompatibilityError(
                "recursive reservation pass-credit provenance is inconsistent"
            )
        outstanding_extension_credit = max(
            0,
            persisted_extension_grants - credited_extension_grants,
        )
        if outstanding_extension_credit:
            current = int(getattr(session, pool_attr, 0) or 0)
            setattr(
                session,
                pool_attr,
                current + outstanding_extension_credit,
            )
        reservations.pop(self.id, None)
        if pass_already_committed:
            recorder = getattr(session, "_record_event", None)
            if callable(recorder):
                recorder(
                    {
                        "phase": "recursive_inflight_reservation",
                        "action_id": self.id,
                        "pool_attr": pool_attr,
                        "reserved_passes_consumed": reserved,
                        "verdict": "committed_recursive_allocation_recovered",
                    }
                )
            return outstanding_extension_credit
        current = int(getattr(session, pool_attr, 0) or 0)
        setattr(session, pool_attr, current + reserved)
        recorder = getattr(session, "_record_event", None)
        if callable(recorder):
            recorder(
                {
                    "phase": "recursive_inflight_reservation",
                    "action_id": self.id,
                    "pool_attr": pool_attr,
                    "reserved_passes_recredited": reserved,
                    "verdict": "unfinished_recursive_allocation_recovered",
                }
            )
        return reserved + outstanding_extension_credit

    def _inflight_reserved_passes(self, session: Any) -> int:
        """Return a valid pending allocation without consuming it.

        ``is_applicable`` is invoked from speculative scheduler probes whose
        surrounding state may be restored afterwards.  Reservation recovery
        therefore belongs exclusively to ``run``; consuming it here can pop
        the durable record while the credited pool value is rolled back.
        """

        reservations = getattr(session, "recursive_inflight_reservations", None)
        if not isinstance(reservations, dict):
            return 0
        record = reservations.get(self.id)
        if not isinstance(record, dict):
            return 0
        if str(record.get("pool_attr") or "").strip() != self.budget_attr:
            return 0
        if self._driver_has_committed_pass():
            return 0
        return max(0, int(record.get("reserved_passes", 0) or 0))

    def _reserve_inflight(self, session: Any, reserved_passes: int) -> None:
        reservations = getattr(session, "recursive_inflight_reservations", None)
        if not isinstance(reservations, dict):
            reservations = {}
            session.recursive_inflight_reservations = reservations
        reservations[self.id] = {
            "pool_attr": self.budget_attr,
            "reserved_passes": max(0, int(reserved_passes or 0)),
            "credited_extension_grants": max(
                0,
                int(
                    self._recursive_driver_state.get(
                        "pass_extension_grants",
                        0,
                    )
                    or 0
                ),
            ),
        }

    def _clear_inflight_reservation(self, session: Any) -> None:
        reservations = getattr(session, "recursive_inflight_reservations", None)
        if isinstance(reservations, dict):
            reservations.pop(self.id, None)

    def is_applicable(self, session: Any) -> bool:
        if session.dossier is None or session.lean is None or session.prover_client is None:
            return False
        if self._pending_planner_job_launch is not None:
            return False
        pending_identity = self._recursive_driver_state.get("planner_job_identity")
        if (
            str(self._recursive_driver_state.get("phase") or "")
            == "planner_job_pending"
            and isinstance(pending_identity, dict)
        ):
            broker_getter = getattr(session, "planner_job_broker", None)
            broker = broker_getter(create=False) if callable(broker_getter) else None
            if broker is not None:
                status = broker.status(
                    str(pending_identity.get("job_id") or ""),
                    str(pending_identity.get("request_fingerprint") or ""),
                )
                if status == "pending":
                    return False
        if self._recursive_fixed_point_environment_signature:
            current_signature = self._session_progress_signature(session)
            if (
                not current_signature
                or current_signature
                == self._recursive_fixed_point_environment_signature
            ):
                return False
        available_passes = int(getattr(session, self.budget_attr, 0) or 0)
        available_passes += self._inflight_reserved_passes(session)
        # Replaying a committed terminal receipt performs no mathematical or
        # provider work.  It must remain dispatchable after the pass that made
        # it consumed the final budget unit, otherwise the durable outcome is
        # stranded before ``on_outcome_applied`` can publish its fixed point.
        if available_passes <= 0 and not self._terminal_receipt_pending_publication(
            session
        ):
            return False
        if self.run_conversation_fn is None:
            return False
        return True

    def take_pending_planner_job_launch(self) -> Optional[PlannerJobLaunch]:
        """Transfer one prepared provider job to the session after commit."""

        launch = self._pending_planner_job_launch
        self._pending_planner_job_launch = None
        return launch

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Explicitly expose the action's documented probe-pure predicate."""

        return self.is_applicable(session)

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.mini_recursive import run_mini_recursive_attempt
        from ensemble_prover.mini_prover import Conversation

        started = time.monotonic()
        if self._recursive_fixed_point_environment_signature:
            current_signature = self._session_progress_signature(session)
            if current_signature != self._recursive_fixed_point_environment_signature:
                # ``is_applicable`` is probe-pure; publish reopening only once
                # the action is actually dispatched over the changed frontier.
                self._recursive_fixed_point_environment_signature = ""
                self._recursive_fixed_point_reason = ""
        stale_terminal_receipt = bool(
            str(self._recursive_driver_state.get("phase") or "")
            == "terminal_committed"
            and not self._terminal_receipt_pending_publication(session)
        )
        # Consume the already-paid committed reservation before discarding a
        # stale/legacy terminal receipt.  Clearing first would misclassify it as
        # unfinished and mint a replacement pass during recovery.
        self._recover_inflight_reservation(session)
        if stale_terminal_receipt:
            recorder = getattr(session, "_record_event", None)
            if callable(recorder):
                recorder(
                    {
                        "phase": "mini_recursive_terminal_receipt",
                        "action_id": self.id,
                        "verdict": "stale_terminal_receipt_rejected",
                    }
                )
            self._recursive_driver_state = {}

        # A persistent MiniSession gives the recursive driver one pass quantum
        # per action invocation. The driver's exact pass frontier is then
        # checkpointed and resumed, allowing formal-state search, retrieval,
        # and assembly to interleave. Without a coordinator there is nowhere
        # durable to keep that frontier, so preserve the legacy complete-run
        # behavior for standalone/tests rather than yielding lossy state.
        cfg = self.config
        remaining_before = max(
            0,
            int(getattr(session, self.budget_attr, 0) or 0),
        )
        configured_passes = 1
        if cfg is not None and hasattr(cfg, "passes"):
            try:
                configured_passes = max(1, int(getattr(cfg, "passes", 1) or 1))
            except Exception:
                configured_passes = 1
        quantized_persistent_run = callable(
            getattr(session, "_record_pre_select_snapshot", None)
        )
        prior_driver_passes_started = max(
            0,
            int(
                dict(self._recursive_driver_state.get("stats") or {}).get(
                    "passes_started",
                    0,
                )
                or 0
            ),
        )
        prior_driver_extension_grants = max(
            0,
            int(
                self._recursive_driver_state.get("pass_extension_grants", 0)
                or 0
            ),
        )
        reserved_passes = min(
            1 if quantized_persistent_run else configured_passes,
            remaining_before,
        )
        terminal_receipt_replay = self._terminal_receipt_pending_publication(session)
        if reserved_passes <= 0 and not terminal_receipt_replay:
            reserved_passes = 1
        continuation_state_for_attempt: Optional[dict[str, Any]] = None
        driver_pass_ceiling = max(1, reserved_passes)
        if cfg is not None and hasattr(cfg, "passes"):
            try:
                if self._recursive_driver_state:
                    resume_next_pass = max(
                        1,
                        int(
                            self._recursive_driver_state.get("pass_index", 1)
                            or 1
                        ),
                    )
                    persisted_pass_ceiling = max(
                        resume_next_pass,
                        int(
                            self._recursive_driver_state.get(
                                "passes",
                                resume_next_pass,
                            )
                            or resume_next_pass
                        ),
                    )
                    proven_pass_ceiling = max(
                        0,
                        int(
                            self._recursive_driver_state.get(
                                "controller_authorized_pass_ceiling",
                                0,
                            )
                            or 0
                        ),
                    )
                    if proven_pass_ceiling:
                        driver_pass_ceiling = max(
                            resume_next_pass,
                            proven_pass_ceiling,
                        )
                    else:
                        # Legacy frames have no provenance distinguishing an
                        # earned continuation from the old static configured
                        # ceiling.  Admit only what all three authorities
                        # agree on: stored cursor, current allocation, config.
                        driver_pass_ceiling = max(
                            resume_next_pass,
                            min(
                                persisted_pass_ceiling,
                                configured_passes,
                                resume_next_pass
                                + max(1, remaining_before)
                                - 1,
                            ),
                        )
                    continuation_state_for_attempt = copy.deepcopy(
                        self._recursive_driver_state
                    )
                    continuation_state_for_attempt["passes"] = driver_pass_ceiling
                    continuation_state_for_attempt[
                        "controller_authorized_pass_ceiling"
                    ] = driver_pass_ceiling
                else:
                    driver_pass_ceiling = (
                        min(
                            configured_passes,
                            max(1, remaining_before),
                        )
                        if quantized_persistent_run
                        else min(
                            configured_passes,
                            max(1, remaining_before),
                        )
                    )
                cfg = replace(
                    cfg,
                    passes=driver_pass_ceiling,
                    pass_quantum=(reserved_passes if quantized_persistent_run else 0),
                )
            except Exception as exc:
                raise StateSnapshotError(
                    "recursive pass allocation could not be derived from "
                    "its durable controller provenance"
                ) from exc

        # Treat the shared recursive pass budget as an allocation, not as
        # post-hoc stats. If the driver raises or reports only one started
        # pass from a multi-pass allocation, later fallback actions must not
        # spend the remainder as independent p1 attempts.
        remaining_after_reserve = max(0, remaining_before - reserved_passes)
        if reserved_passes > 0:
            self._reserve_inflight(session, reserved_passes)
        setattr(session, self.budget_attr, remaining_after_reserve)

        problem_text = str(getattr(session.problem, "docstring", "") or "")
        helpers_before = set(_verified_helper_names(session.dossier))
        recursive_helper_action = None
        registered_action = getattr(session, "registered_action", None)
        if callable(registered_action):
            recursive_helper_action = registered_action("recursive_helper_prover")
        action_available = getattr(session, "action_available", None)
        recursive_helper_enabled = bool(
            recursive_helper_action is not None
            and (
                action_available("recursive_helper_prover")
                if callable(action_available)
                else True
            )
        )
        raw_recursive_helper_max_depth = getattr(session, "max_recursion_depth", 3)
        recursive_helper_max_depth = int(
            raw_recursive_helper_max_depth
            if raw_recursive_helper_max_depth is not None
            else 3
        )

        async def checkpoint_recursive_driver(
            reason: str,
            state: Optional[dict[str, Any]] = None,
        ) -> None:
            prior_driver_state: dict[str, Any] = {}
            prior_root_tactic_context_keys: set[str] = set()

            def prepare_driver_state() -> None:
                nonlocal prior_driver_state
                nonlocal prior_root_tactic_context_keys
                prior_driver_state = copy.deepcopy(self._recursive_driver_state)
                prior_root_tactic_context_keys = set(
                    self._recursive_root_tactic_context_keys_seen
                )
                if state is None:
                    return
                published_state = copy.deepcopy(dict(state))
                extension_grants = max(
                    prior_driver_extension_grants,
                    int(published_state.get("pass_extension_grants", 0) or 0),
                )
                published_state["controller_authorized_pass_ceiling"] = (
                    driver_pass_ceiling
                    + max(
                        0,
                        extension_grants - prior_driver_extension_grants,
                    )
                )
                self._recursive_root_tactic_context_keys_seen.update(
                    str(item or "")
                    for item in list(
                        published_state.get(
                            "root_tactic_attempted_context_keys",
                            [],
                        )
                        or []
                    )
                    if str(item or "")
                )
                if str(published_state.get("phase") or "") == "terminal_committed":
                    # The recursive driver's route hash scopes Lean/provider
                    # facts inside one attempt, but it cannot see the outer
                    # checkpoint identity or branch-merged planner inputs. Bind
                    # the terminal decision to that complete frontier before
                    # atomically publishing it with the session checkpoint.
                    published_state["outer_recursive_planner_signature"] = (
                        self._session_progress_signature(session)
                    )
                self._recursive_driver_state = published_state

            def rollback_driver_state(exc: BaseException) -> None:
                # A completed pass remains consumed in the live process when
                # cancellation interrupts its checkpoint. Ordinary nondurable
                # failures still restore the prior receipt for exact replay.
                cancellation_after_commit = isinstance(
                    exc,
                    asyncio.CancelledError,
                ) and self._driver_has_committed_pass()
                if not cancellation_after_commit:
                    self._recursive_driver_state = prior_driver_state
                    self._recursive_root_tactic_context_keys_seen = (
                        prior_root_tactic_context_keys
                    )

            del reason, rollback_driver_state
            prepare_driver_state()
            persist_cutpoint = getattr(
                session,
                "_record_pre_select_snapshot",
                None,
            )
            if callable(persist_cutpoint):
                persist_cutpoint()

        attempt_coro = run_mini_recursive_attempt(
            theorem_name=session.problem.theorem_name,
            root_statement=session.problem.statement_type,
            problem_text=problem_text,
            lean_signature=str(getattr(session.conv, "lean_signature", "") or ""),
            prover_client=session.prover_client,
            refiner_client=session.refiner_client,
            planner_escalation_client=getattr(
                session, "planner_escalation_client", None
            ),
            lean=session.lean,
            llm_preamble=str(getattr(session.conv, "preamble", "") or ""),
            lean_preamble=str(getattr(session.conv, "lean_preamble", "") or ""),
            attempt_dossier=session.dossier,
            conversation_cls=Conversation,
            run_conversation_fn=self.run_conversation_fn,
            max_tool_calls_per_turn=self.max_tool_calls_per_turn,
            lean_check_tool_enabled=self.lean_check_tool_enabled,
            try_lean_tool_enabled=self.try_lean_tool_enabled,
            compute_examples_tool_enabled=self.compute_examples_tool_enabled,
            apply_decl_to_goal_tool_enabled=self.apply_decl_to_goal_tool_enabled,
            raw_feedback=self.raw_feedback,
            repair_retrieval_enabled=self.repair_retrieval_enabled,
            repair_retrieval_top_k=self.repair_retrieval_top_k,
            proof_state_child_tactics_enabled=self.proof_state_child_tactics_enabled,
            proof_state_child_tactic_timeout_s=self.proof_state_child_tactic_timeout_s,
            proof_state_child_tactic_max_candidates=self.proof_state_child_tactic_max_candidates,
            root_tactic_timeout_s=self.root_tactic_timeout_s,
            root_tactic_max_candidates=self.root_tactic_max_candidates,
            proof_state_child_goal_limit=self.proof_state_child_goal_limit,
            proof_state_decl_application_limit=self.proof_state_decl_application_limit,
            proof_state_batch_parallelism=self.proof_state_batch_parallelism,
            recorder=session.recorder,
            searcher=session.searcher,
            proof_cache=getattr(session, "proof_cache", None),
            cache_owner_theorem_name=str(
                getattr(session.dossier, "cache_owner_theorem_name", "")
                or getattr(session.problem, "theorem_name", "")
                or ""
            ),
            cost_controller=getattr(session, "cost_controller", None),
            trace_prefix=session.trace_prefix,
            branch_label=self.phase_label,
            opaque_mode=bool(getattr(session.conv, "opaque_mode", True)),
            allow_official_answer_visibility=bool(
                getattr(session.conv, "allow_official_answer_visibility", False)
            ),
            official_answer_payload_present=getattr(
                session.conv,
                "official_answer_payload_present",
                getattr(session.dossier, "official_answer_payload_present", None),
            ),
            adaptive_fallback=(
                self.budget_attr == "adaptive_recursive_pass_budget_remaining"
            ),
            budget_kind=(
                "adaptive_recursive_fallback"
                if self.budget_attr == "adaptive_recursive_pass_budget_remaining"
                else "recursive_prepass"
            ),
            config=cfg,
            strict_progress_accounting=bool(
                getattr(session, "strict_progress_accounting", False)
            ),
            soft_progress_streak_cap=int(
                getattr(session, "max_soft_progress_streak", 4) or 0
            ),
            recursive_helper_prover_enabled=recursive_helper_enabled,
            recursive_helper_max_depth=recursive_helper_max_depth,
            recursive_helper_max_attempts_per_node=int(
                getattr(recursive_helper_action, "max_attempts_per_node", 2)
                if getattr(recursive_helper_action, "max_attempts_per_node", 2)
                is not None
                else 2
            ),
            recursive_helper_turns=int(
                getattr(recursive_helper_action, "helper_turns", 5) or 5
            ),
            recursive_helper_refine=bool(
                getattr(recursive_helper_action, "refine_enabled", False)
            ),
            recursive_helper_budget=0,
            recursion_depth=int(getattr(session, "recursion_depth", 0) or 0),
            progress_callback=checkpoint_recursive_driver,
            verified_helper_accept_callback=getattr(
                session,
                "theory_verified_helper_accept_callback",
                None,
            ),
            continuation_state=(
                continuation_state_for_attempt
                if continuation_state_for_attempt is not None
                else (
                    copy.deepcopy(self._recursive_driver_state)
                    if self._recursive_driver_state
                    else None
                )
            ),
            prior_root_tactic_context_keys=tuple(
                sorted(self._recursive_root_tactic_context_keys_seen)
            ),
            planner_job_broker=(
                session.planner_job_broker()
                if callable(getattr(session, "planner_job_broker", None))
                and (
                    not callable(
                        getattr(session, "owns_planner_split_scheduler", None)
                    )
                    or session.owns_planner_split_scheduler()
                )
                else None
            ),
            planner_frontier_signature=self._session_progress_signature(session),
            planner_owner_lane_id=self.id,
        )
        try:
            result = await attempt_coro
        except PlannerJobYield as pending:
            identity_record = asdict(pending.launch.identity)
            self._planner_job_receipt_identities[
                (
                    pending.launch.identity.job_id,
                    pending.launch.identity.request_fingerprint,
                )
            ] = pending.launch.identity
            prior_phase = str(self._recursive_driver_state.get("phase") or "")
            self._recursive_driver_state.update(
                {
                    "phase": "planner_job_pending",
                    "planner_job_prior_phase": prior_phase,
                    "planner_job_identity": identity_record,
                    "outer_recursive_planner_signature": (
                        self._session_progress_signature(session)
                    ),
                }
            )
            session_ref = weakref.ref(session)

            def reconcile_provider_exposure(count: int) -> None:
                live_session = session_ref()
                if live_session is None:
                    return
                accrue = getattr(live_session, "_accrue_provider_exposure", None)
                if callable(accrue) and int(count or 0) > 0:
                    accrue({"provider_dispatches_started": int(count or 0)})

            self._pending_planner_job_launch = replace(
                pending.launch,
                usage_context=llm_usage_context_metadata(),
                reconcile_provider_exposure=reconcile_provider_exposure,
            )
            persist_cutpoint = getattr(session, "_record_pre_select_snapshot", None)
            if callable(persist_cutpoint):
                persist_cutpoint()
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=max(0.0, time.monotonic() - started),
                metadata={
                    "planner_job_pending": True,
                    "planner_job_identity": identity_record,
                    "preserve_action_budget": True,
                    "preserve_frontier_work": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "recursive_pass_quantum_yield": True,
                },
            )
        except asyncio.CancelledError:
            # Cancellation is a pause/interruption, not a completed
            # allocation.  Preserve the live reservation so an in-process
            # resume has the same recovery semantics as a process restart.
            raise
        except Exception:
            self._clear_inflight_reservation(session)
            raise
        except BaseException:
            self._clear_inflight_reservation(session)
            raise
        else:
            self._clear_inflight_reservation(session)

        if bool(getattr(result, "resumed_from_terminal_receipt", False)):
            # The pass represented by the terminal receipt was charged before
            # that receipt became durable.  This invocation reserved a pass
            # only because action outcome publication happens outside the
            # recursive driver.  Re-credit that speculative reservation; no
            # mathematical or provider work was replayed.
            setattr(
                session,
                self.budget_attr,
                max(0, int(getattr(session, self.budget_attr, 0) or 0))
                + reserved_passes,
            )

        passes_used = int(getattr(getattr(result, "stats", None), "passes_started", 0) or 0)
        failure_reason = str(
            getattr(result, "failure_reason", "") or ""
        ).strip()
        identity_pending_yielded = bool(
            failure_reason == "recursive_contract_identity_pending_yield"
        )
        identity_service_blocked = bool(
            failure_reason
            == "recursive_contract_identity_service_unavailable"
        )
        identity_infrastructure_unknown = bool(
            failure_reason
            == "recursive_contract_identity_infrastructure_unknown"
        )
        # The driver publishes this once it has already yielded on identity
        # exhaustion for this pass and re-entry changed nothing.  It stays a
        # SCOPED failure — the identity service is infrastructure, not a
        # mathematical verdict — but it must not be re-credited as a quantum
        # yield, or the pass is never charged and the loop is unbounded.
        identity_service_exhausted = bool(
            failure_reason
            == "recursive_contract_identity_service_exhausted"
        )
        quantum_yielded = is_resumable_mini_recursive_yield(failure_reason)
        identity_prepass_deferred = bool(
            identity_pending_yielded
            or identity_service_blocked
            or identity_infrastructure_unknown
        )
        if identity_prepass_deferred:
            # These yields happen before a mathematical pass is admitted.
            # Return this invocation's reservation, but never exceed the
            # controller pool observed at admission.  Identity exhaustion is
            # intentionally excluded: it is the bounded terminal retry for
            # this pass and must remain charged.
            setattr(
                session,
                self.budget_attr,
                min(
                    remaining_before,
                    max(0, int(getattr(session, self.budget_attr, 0) or 0))
                    + reserved_passes,
                ),
            )
        # The real quantized driver consumes one pass before yielding. Keep
        # accounting robust for terminal results and compatible driver
        # implementations that complete multiple passes without a quantum
        # result: charge their observed invocation delta instead of leaving
        # phantom passes in the session pool. Cumulative resumed stats are
        # offset by the durable pre-invocation checkpoint value.
        invocation_passes_used = max(0, passes_used - prior_driver_passes_started)
        if not quantum_yielded and invocation_passes_used > reserved_passes:
            additional_used = min(
                max(0, invocation_passes_used - reserved_passes),
                max(0, int(getattr(session, self.budget_attr, 0) or 0)),
            )
            if additional_used > 0:
                setattr(
                    session,
                    self.budget_attr,
                    max(
                        0,
                        int(getattr(session, self.budget_attr, 0) or 0)
                        - additional_used,
                    ),
                )
        if quantum_yielded and self._recursive_driver_state:
            extension_grants = max(
                prior_driver_extension_grants,
                int(
                    self._recursive_driver_state.get("pass_extension_grants", 0)
                    or 0
                ),
            )
            newly_earned_extensions = max(
                0,
                extension_grants - prior_driver_extension_grants,
            )
            if newly_earned_extensions:
                setattr(
                    session,
                    self.budget_attr,
                    max(
                        0,
                        int(getattr(session, self.budget_attr, 0) or 0),
                    )
                    + newly_earned_extensions,
                )
                reservations = getattr(
                    session,
                    "recursive_inflight_reservations",
                    None,
                )
                reservation = (
                    reservations.get(self.id)
                    if isinstance(reservations, dict)
                    else None
                )
                if isinstance(reservation, dict):
                    reservation["credited_extension_grants"] = (
                        extension_grants
                    )
        helpers_added = tuple(
            name
            for name in _verified_helper_names(session.dossier)
            if name not in helpers_before
        )
        premise_projection_helpers_added = tuple(
            name
            for name in helpers_added
            if verified_helper_is_premise_projection(
                getattr(session.dossier, "verified_helpers", {}).get(name, name)
            )
        )
        nonprogress_helpers_added = tuple(
            name
            for name in helpers_added
            if (
                name in premise_projection_helpers_added
                or not verified_helper_admission_quality(
                    getattr(session.dossier, "verified_helpers", {}).get(
                        name, name
                    )
                ).generic_novelty
            )
        )
        substantive_helpers_added = tuple(
            name
            for name in helpers_added
            if name not in nonprogress_helpers_added
        )
        solved = bool(getattr(result, "ok", False))
        disproved = bool(getattr(result, "disproved", False))
        fixed_point_reasons = {
            "recursive_planner_empty_fixed_point",
            "recursive_helper_only_fixed_point",
            "recursive_progress_fixed_point",
            "recursive_planner_transport_empty_fixed_point",
        }
        fixed_point_reason = (
            failure_reason if failure_reason in fixed_point_reasons else ""
        )
        fixed_point_signature = ""
        if fixed_point_reason:
            fixed_point_signature = str(
                self._recursive_driver_state.get(
                    "outer_recursive_planner_signature",
                    "",
                )
                or self._session_progress_signature(session)
                or ""
            ).strip()
            if (
                callable(
                    getattr(
                        session,
                        "_recursive_planner_frontier_signature",
                        None,
                    )
                )
                and not fixed_point_signature
            ):
                raise StateSnapshotError(
                    "recursive fixed point cannot be returned without a "
                    "planner-frontier identity"
                )
        terminal_failure = bool(
            disproved or is_terminal_llm_failure_reason(failure_reason)
        )
        stats = getattr(result, "stats", None)
        nested_scoped_failure_reason = ""
        nested_scoped_failure_kind = ""
        nested_scoped_failure_metadata: dict[str, Any] = {}
        durable_plan_record = self._recursive_driver_state.get("plan") or {}
        pass_outcome_kind = str(
            self._recursive_driver_state.get("pass_outcome_kind") or ""
        ).strip()
        current_quantum_ended_in_scoped_planner_failure = bool(
            quantum_yielded
            and isinstance(durable_plan_record, dict)
            and (
                pass_outcome_kind == "planner_scoped_failure"
                or (
                    not pass_outcome_kind
                    and str(durable_plan_record.get("strategy") or "").strip()
                    == "planner scoped failure deferred"
                )
            )
        )
        if stats is not None:
            try:
                planner_failure_count = int(
                    getattr(stats, "planner_scoped_failures", 0) or 0
                )
            except Exception:
                planner_failure_count = 0
            candidate_reason = str(
                getattr(stats, "last_planner_failure_reason", "") or ""
            ).strip()
            current_attempt_ended_in_scoped_planner_failure = bool(
                current_quantum_ended_in_scoped_planner_failure
                or (
                    llm_failure_scope(failure_reason) == "scoped"
                    and candidate_reason == failure_reason
                )
            )
            if (
                current_attempt_ended_in_scoped_planner_failure
                and planner_failure_count > 0
                and llm_failure_scope(candidate_reason) == "scoped"
            ):
                nested_scoped_failure_reason = candidate_reason
                nested_scoped_failure_kind = str(
                    getattr(stats, "last_planner_failure_kind", "") or ""
                ).strip()
                raw_failure_metadata = getattr(
                    stats,
                    "last_planner_failure_metadata",
                    {},
                )
                if isinstance(raw_failure_metadata, dict):
                    nested_scoped_failure_metadata = dict(raw_failure_metadata)
        failure_scope = (
            "scoped"
            if (
                identity_service_blocked
                or identity_service_exhausted
                or identity_infrastructure_unknown
                or nested_scoped_failure_reason
            )
            else llm_failure_scope(failure_reason)
        )
        scoped_failure_reason = (
            nested_scoped_failure_reason or failure_reason
            if failure_scope == "scoped"
            else ""
        )
        nested_scoped_failure_retryable = (
            projected_scoped_llm_failure_is_retryable(
                reason=nested_scoped_failure_reason,
                kind=nested_scoped_failure_kind,
                metadata=nested_scoped_failure_metadata,
            )
        )
        nested_zero_provider_failure = bool(
            nested_scoped_failure_retryable
            and nested_scoped_failure_metadata.get("zero_provider_failure")
            and int(
                nested_scoped_failure_metadata.get(
                    "provider_calls_completed",
                    0,
                )
                or 0
            )
            == 0
        )
        if nested_zero_provider_failure and reserved_passes > 0:
            # A provider-free planner outage consumed no mathematical pass.
            # Reopen exactly this controller allocation; the ordinary action
            # budget is preserved centrally from the same zero-provider
            # receipt, while a paid/partially-completed pass remains charged.
            setattr(session, self.budget_attr, remaining_before)
        # Keep premise projections in ``helpers_added`` so their valid Lean
        # declarations remain observable and reusable inside this run.  They
        # must not claim even soft/material progress, however: otherwise a
        # ladder of ``P -> P`` helpers releases reserved fallbacks and delays
        # stagnation despite leaving the mathematical frontier unchanged.
        material_progress = bool(solved or substantive_helpers_added)
        strong_progress = bool(
            solved
            or strong_progress_for_accepted_helpers(session.dossier, helpers_added)
        )
        replay_helpers = (
            tuple(session.dossier.verified_helper_blocks())
            if solved and getattr(result, "proof", None) and session.dossier is not None
            else ()
        )
        helper_names = tuple(
            name
            for block in replay_helpers
            for name in [helper_decl_name(block)]
            if name
        )

        cost = time.monotonic() - started
        return MiniOutcome(
            action_id=self.id,
            solved=solved,
            proof=getattr(result, "proof", None) if solved else None,
            helpers_added=helpers_added,
            progress=material_progress,
            cost_seconds=cost,
            root_candidate=(
                RootFinalizationCandidate(
                    proof=str(getattr(result, "proof", "") or ""),
                    replay_helpers=replay_helpers,
                    helper_names=helper_names,
                    phase="mini_recursive_root_tactic",
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    source_action_id=self.id,
                    target_statement=str(
                        getattr(session.dossier, "root_statement", "")
                        or getattr(getattr(session, "problem", None), "statement_type", "")
                        or ""
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=str(getattr(result, "proof", "") or ""),
                        phase="mini_recursive_root_tactic",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        target_statement=str(
                            getattr(session.dossier, "root_statement", "")
                            or getattr(
                                getattr(session, "problem", None),
                                "statement_type",
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
                if solved and getattr(result, "proof", None)
                else None
            ),
            metadata={
                "passes_used": passes_used,
                "passes_reserved": reserved_passes,
                "recursive_pass_quantum_yield": quantum_yielded,
                "recursive_contract_identity_pending_yield": (
                    identity_pending_yielded
                ),
                "recursive_contract_identity_service_unavailable": (
                    identity_service_blocked
                ),
                "recursive_contract_identity_infrastructure_unknown": (
                    identity_infrastructure_unknown
                ),
                "recursive_driver_next_pass_index": int(
                    self._recursive_driver_state.get("pass_index", 0) or 0
                )
                if quantum_yielded
                else 0,
                "recursive_material_progress": material_progress,
                "strong_progress": strong_progress,
                "recursive_helpers_added": list(helpers_added),
                "recursive_helpers_added_count": len(helpers_added),
                "recursive_substantive_helpers_added": list(
                    substantive_helpers_added
                ),
                "recursive_premise_projection_helpers_added": list(
                    premise_projection_helpers_added
                ),
                "recursive_budget_attr": self.budget_attr,
                "adaptive_fallback": (
                    self.budget_attr == "adaptive_recursive_pass_budget_remaining"
                ),
                "budget_kind": (
                    "adaptive_recursive_fallback"
                    if self.budget_attr == "adaptive_recursive_pass_budget_remaining"
                    else "recursive_prepass"
                ),
                "recursive_budget_remaining": int(
                    getattr(session, self.budget_attr, 0) or 0
                ),
                "recursive_fixed_point_reason": (
                    fixed_point_reason
                ),
                "recursive_fixed_point_environment_signature": (
                    fixed_point_signature
                ),
                "recursive_failure_reason": failure_reason,
                "replay_helpers": list(replay_helpers),
                "helper_names": list(helper_names),
                "root_finalization_already_applied": bool(
                    solved and getattr(result, "proof", None)
                ),
                "terminal_failure": terminal_failure,
                "terminal_failure_reason": (
                    "root_disproved_by_audited_lean_certificate"
                    if disproved
                    else failure_reason if terminal_failure else ""
                ),
                "terminal_failure_kind": (
                    "mathematical_disproof" if disproved else ""
                ),
                "disproved": disproved,
                **nested_scoped_failure_metadata,
                "scoped_failure_reason": scoped_failure_reason,
                "llm_failure_scope": failure_scope,
                "llm_failure_kind": nested_scoped_failure_kind,
                # The nested call has already exhausted its in-call retry
                # policy.  A typed transient remains retryable only as a
                # later scheduler quantum, after other proof families run.
                "llm_retryable": nested_scoped_failure_retryable,
                "recursive_zero_provider_budget_refunded": (
                    nested_zero_provider_failure
                ),
                "model_call_defer_family": self.MODEL_CALL_DEFER_FAMILY,
                "preserve_frontier_work": bool(
                    quantum_yielded or terminal_failure or scoped_failure_reason
                ),
                "defer_selected_frontier_action": bool(
                    scoped_failure_reason or fixed_point_reason
                ),
            },
        )
