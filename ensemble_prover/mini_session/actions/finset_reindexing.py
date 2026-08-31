"""First-class finite indexed sum/product reindexing action."""

from __future__ import annotations

import asyncio
import time
from typing import Any, ClassVar, FrozenSet

from ensemble_prover.mini_finset_reindexer import (
    detect_finset_reindexing_profile,
    finset_reindexing_scripts,
)
from ensemble_prover.mini_tactic_closer import (
    TacticPatternCache,
    is_transient_tactic_close_failure,
    try_close_with_tactics,
)
from ensemble_prover.proof_dossier import helper_decl_name, text_hash
from ensemble_prover.proof_state_executor import (
    _extract_and_spawn_typed_residual_goals,
    _proof_state_residual_lemmas,
    _proof_state_residual_preamble,
)
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ensemble_prover.tactic_attempt_telemetry import (
    dossier_lean_attempt_observer,
    tactic_attempt_telemetry_fields,
)

from ..action import MiniOutcome
from ..tactic_source_suppression import tactic_source_context_key


class FinsetReindexingAction:
    """Try bounded finite-sum/product reindexing before model turns."""

    id: str = "finset_reindexing"
    priority: int = 10
    cost_estimate_s: float = 12.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset(
        {"dossier", "proof_state", "session_state"}
    )

    def __init__(
        self,
        *,
        phase: str = "finset_reindexing_prepass",
        timeout_s: float = 12.0,
        max_candidates: int = 18,
        max_infrastructure_retries: int = 1,
    ) -> None:
        self.phase = str(phase or "finset_reindexing_prepass")
        self.timeout_s = float(timeout_s or 0.0)
        self.max_candidates = int(max_candidates or 0)
        self.max_infrastructure_retries = max(
            0,
            int(max_infrastructure_retries or 0),
        )
        self._attempted_context_keys: set[str] = set()
        self._infrastructure_failure_counts: dict[str, int] = {}
        self._infrastructure_retry_after_epoch_s: dict[str, float] = {}
        self._pattern_cache = TacticPatternCache()



    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0 or self.max_candidates <= 0:
            return False
        if session.dossier is None or session.lean is None:
            return False
        goal = self._goal_statement(session)
        if not goal:
            return False
        profile = detect_finset_reindexing_profile(goal)
        if not profile.should_attempt:
            return False
        proof_state = getattr(session, "proof_state", None)
        root_id = str(getattr(proof_state, "root_node_id", "") or "root")
        root = getattr(proof_state, "nodes", {}).get(root_id)
        if root is not None and getattr(
            root, "pending_residual_goal_extraction", {}
        ):
            return False
        helper_blocks = self._helper_blocks(session)
        helper_names = self._helper_names(helper_blocks)
        context_key = self._context_key(
            session,
            goal,
            helper_names=helper_names,
            helper_blocks=helper_blocks,
        )
        if context_key in self._attempted_context_keys:
            return False
        exhausted = getattr(session, "static_action_context_exhausted", None)
        if callable(exhausted) and exhausted(self.id, context_key):
            return False
        if time.time() < float(
            self._infrastructure_retry_after_epoch_s.get(context_key, 0.0)
            or 0.0
        ):
            return False
        return True

    async def run(self, session: Any) -> MiniOutcome:
        started = time.monotonic()
        goal = self._goal_statement(session)
        profile = detect_finset_reindexing_profile(goal)
        helper_blocks = self._helper_blocks(session)
        helper_names = self._helper_names(helper_blocks)
        residual_preamble = _proof_state_residual_preamble(
            getattr(session, "conv", None)
        )
        residual_helpers = tuple(
            _proof_state_residual_lemmas(
                getattr(session, "conv", None),
                helper_blocks,
            )
        )
        context_key = self._context_key(
            session,
            goal,
            helper_names=helper_names,
            helper_blocks=helper_blocks,
        )
        infrastructure_attempt, admitted = self._claim_shared_attempt(
            session,
            context_key,
        )
        if not admitted:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "phase": self.phase,
                    "finset_reindexing_context_consumed": True,
                    "infrastructure_failure_count": infrastructure_attempt,
                    "infrastructure_retry_granted": False,
                    "infrastructure_retry_exhausted": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "preserve_action_budget": True,
                    "verdict": "finset_reindexing_shared_attempt_exhausted",
                },
            )
        self._increment_metric(session, "mini_session_finset_reindexing_applicable")
        self._increment_metric(session, "mini_session_finset_reindexing_attempts")
        if profile.finite_sum_count > 0:
            self._increment_metric(
                session,
                "mini_session_finset_reindexing_sum_goals_attempted",
            )
        if profile.finite_product_count > 0:
            self._increment_metric(
                session,
                "mini_session_finset_reindexing_product_goals_attempted",
            )
        if profile.has_filter:
            self._increment_metric(
                session,
                "mini_session_finset_reindexing_filter_rewrites_attempted",
            )
        if profile.has_antidiagonal:
            self._increment_metric(
                session,
                "mini_session_finset_reindexing_antidiagonal_rewrites_attempted",
            )

        needs_intro = goal.lstrip().startswith(("∀", "forall")) or "→" in goal or "->" in goal
        script_count = len(finset_reindexing_scripts(profile, needs_intro=needs_intro))
        base_attempt_observer = dossier_lean_attempt_observer(
            getattr(session, "dossier", None),
            "finset_reindexing_tactic",
        )
        dispatch_committed = False

        def attempt_observer(event: str, attempt: Any) -> None:
            nonlocal dispatch_committed
            base_attempt_observer(event, attempt)
            if event == "dispatched" and not dispatch_committed:
                self._commit_shared_attempt(session, context_key)
                dispatch_committed = True

        try:
            result = await try_close_with_tactics(
                session.lean,
                goal,
                residual_preamble,
                residual_helpers,
                timeout_s=self.timeout_s,
                max_candidates=self.max_candidates,
                pattern_cache=self._pattern_cache,
                pattern_context={
                    "scope": self.id,
                    "phase": self.phase,
                    "mode": "finite_bigop_reindexing",
                    "finset_reindexing_context_key": context_key,
                    "finset_reindexing_finite_sum_count": str(
                        profile.finite_sum_count
                    ),
                    "finset_reindexing_finite_product_count": str(
                        profile.finite_product_count
                    ),
                },
                source_prefixes=("finset_reindexing",),
                suppress_solution_placeholders=bool(
                    getattr(session.conv, "suppress_solution_placeholders", True)
                )
                if getattr(session, "conv", None) is not None
                else True,
                opaque_mode=bool(getattr(session.conv, "opaque_mode", True))
                if getattr(session, "conv", None) is not None
                else True,
                allow_official_answer_visibility=bool(
                    getattr(session.conv, "allow_official_answer_visibility", False)
                )
                if getattr(session, "conv", None) is not None
                else False,
                official_answer_payload_present=getattr(
                    session.conv,
                    "official_answer_payload_present",
                    getattr(
                        getattr(session, "dossier", None),
                        "official_answer_payload_present",
                        None,
                    ),
                )
                if getattr(session, "conv", None) is not None
                else getattr(
                    getattr(session, "dossier", None),
                    "official_answer_payload_present",
                    None,
                ),
                attempt_observer=attempt_observer,
            )
            if not dispatch_committed:
                self._commit_shared_attempt(session, context_key)
                dispatch_committed = True
        except asyncio.CancelledError:
            if not dispatch_committed:
                self._release_shared_attempt(session, context_key)
            raise
        except Exception as exc:
            if not dispatch_committed:
                self._commit_shared_attempt(session, context_key)
                dispatch_committed = True
            cost = time.monotonic() - started
            (
                retry_after_epoch_s,
                infrastructure_retry_granted,
                infrastructure_failure_count,
            ) = self._defer_infrastructure_retry(
                session,
                context_key,
                attempt_number=infrastructure_attempt,
            )
            infrastructure_retry_exhausted = not infrastructure_retry_granted
            if infrastructure_retry_exhausted:
                self._attempted_context_keys.add(context_key)
                self._consume_shared_context(session, context_key)
            self._increment_metric(session, "mini_session_finset_reindexing_failed")
            self._record_event(
                session,
                {
                    "phase": self.phase,
                    "action_id": self.id,
                    "context_key_hash": text_hash(context_key),
                    **profile.metadata(),
                    "finset_reindexing_script_count": script_count,
                    "exception_type": type(exc).__name__,
                    "exception_message": str(exc),
                    "retry_after_epoch_s": retry_after_epoch_s,
                    "infrastructure_failure_count": infrastructure_failure_count,
                    "infrastructure_retry_granted": infrastructure_retry_granted,
                    "infrastructure_retry_exhausted": (
                        infrastructure_retry_exhausted
                    ),
                    "verdict": "finset_reindexing_exception",
                },
            )
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=cost,
                metadata={
                    "phase": self.phase,
                    "exception_type": type(exc).__name__,
                    "exception_message": str(exc),
                    "verdict": "finset_reindexing_infrastructure_failure",
                    "infrastructure_failure": True,
                    "infrastructure_failure_count": infrastructure_failure_count,
                    "infrastructure_retry_granted": infrastructure_retry_granted,
                    "infrastructure_retry_exhausted": (
                        infrastructure_retry_exhausted
                    ),
                    "finset_reindexing_context_consumed": (
                        infrastructure_retry_exhausted
                    ),
                    "preserve_action_budget": infrastructure_retry_granted,
                    "preserve_frontier_work": infrastructure_retry_granted,
                    "scheduler_neutral": infrastructure_retry_granted,
                    "stagnation_neutral": infrastructure_retry_granted,
                    "hard_pivot_neutral": infrastructure_retry_granted,
                    "iteration_neutral": infrastructure_retry_granted,
                    "retry_after_epoch_s": retry_after_epoch_s,
                    **profile.metadata(),
                },
            )

        attempts = list(getattr(result, "attempts", []) or [])
        diagnostic_goal_count = sum(
            len(list(attempt.get("remaining_goals") or ()))
            for attempt in attempts
            if isinstance(attempt, dict)
            and str(attempt.get("source") or "").startswith("finset_reindexing")
            and bool(attempt.get("partial_stub_validated", False))
        )
        if bool(getattr(result, "ok", False)):
            spawned_goal_nodes = ()
            typed_goal_count = 0
            receipt_status = "residual_attestation_not_requested"
        else:
            spawned_goal_nodes, typed_goal_count, receipt_status = (
                await self._spawn_reindexing_goals(
                    session,
                    attempts,
                    preamble=residual_preamble,
                    helper_blocks=residual_helpers,
                )
            )
        root_node = getattr(
            getattr(session, "proof_state", None),
            "nodes",
            {},
        ).get(
            str(
                getattr(
                    getattr(session, "proof_state", None),
                    "root_node_id",
                    "root",
                )
                or "root"
            )
        )
        residual_retry_pending = bool(
            root_node is not None
            and dict(
                getattr(root_node, "pending_residual_goal_extraction", {}) or {}
            ).get("source", "").startswith("finset_reindexing")
        )
        validation_status = self._receipt_status_metadata(
            receipt_status,
            typed_goal_count=typed_goal_count,
        )
        if diagnostic_goal_count:
            self._increment_metric(
                session,
                "mini_session_finset_reindexing_side_conditions_exposed",
                diagnostic_goal_count,
            )
        if spawned_goal_nodes:
            self._increment_metric(
                session,
                "mini_session_finset_reindexing_side_conditions_materialized",
                len(spawned_goal_nodes),
            )
        ok = bool(getattr(result, "ok", False))
        transient_failure = is_transient_tactic_close_failure(result)
        if transient_failure:
            (
                retry_after_epoch_s,
                infrastructure_retry_granted,
                infrastructure_failure_count,
            ) = self._defer_infrastructure_retry(
                session,
                context_key,
                attempt_number=infrastructure_attempt,
            )
        else:
            retry_after_epoch_s = 0.0
            infrastructure_retry_granted = False
            infrastructure_failure_count = 0
            self._infrastructure_failure_counts.pop(context_key, None)
            self._infrastructure_retry_after_epoch_s.pop(context_key, None)
        infrastructure_retry_exhausted = bool(
            transient_failure and not infrastructure_retry_granted
        )
        context_consumed = bool(
            not ok
            and (
                infrastructure_retry_exhausted
                or (
                    attempts
                    and (
                        spawned_goal_nodes
                        or (
                            not diagnostic_goal_count
                            and not infrastructure_retry_granted
                        )
                        or (
                            diagnostic_goal_count
                            and bool(validation_status.get("complete", False))
                            and not infrastructure_retry_granted
                        )
                    )
                )
            )
        )
        if context_consumed:
            self._attempted_context_keys.add(context_key)
            self._consume_shared_context(session, context_key)
        if ok:
            self._increment_metric(session, "mini_session_finset_reindexing_solved")
        else:
            self._increment_metric(session, "mini_session_finset_reindexing_failed")
        proof = str(getattr(result, "proof", "") or "")
        root_candidate = (
            RootFinalizationCandidate(
                proof=proof,
                replay_helpers=tuple(helper_blocks),
                helper_names=tuple(helper_names),
                phase=self.phase,
                turn_index=int(getattr(session, "iteration", 0) or 0),
                source_action_id=self.id,
                target_statement=goal,
                verification_certificate=root_verification_certificate(
                    accepted=True,
                    proof=proof,
                    phase=self.phase,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    target_statement=goal,
                    replay_helpers=helper_blocks,
                    helper_names=helper_names,
                    source=self.id,
                ),
            )
            if ok and proof
            else None
        )
        cost = time.monotonic() - started
        event = {
            "phase": self.phase,
            "action_id": self.id,
            "context_key_hash": text_hash(context_key),
            **profile.metadata(),
            "finset_reindexing_script_count": script_count,
            "finset_reindexing_side_condition_goal_count": diagnostic_goal_count,
            "finset_reindexing_typed_side_condition_goal_count": typed_goal_count,
            "finset_reindexing_residual_attestation_status": receipt_status,
            "finset_reindexing_side_condition_node_ids": list(spawned_goal_nodes),
            "tactic_candidate_count": int(getattr(result, "candidate_count", 0) or 0),
            **tactic_attempt_telemetry_fields(attempts),
            "tactic_attempts": attempts[:8],
            "tactic_elapsed_s": float(getattr(result, "elapsed_s", 0.0) or 0.0),
            "tactic_exit_reason": str(getattr(result, "exit_reason", "") or ""),
            "tactic_transient_failure": bool(transient_failure),
            "retry_after_epoch_s": retry_after_epoch_s,
            "infrastructure_failure_count": infrastructure_failure_count,
            "infrastructure_retry_granted": infrastructure_retry_granted,
            "infrastructure_retry_exhausted": infrastructure_retry_exhausted,
            "finset_reindexing_validation": dict(validation_status),
            "finset_reindexing_context_consumed": bool(context_consumed),
            "verdict": "finset_reindexing_solved" if ok else "finset_reindexing_failed",
        }
        self._record_event(session, event)
        return MiniOutcome(
            action_id=self.id,
            solved=ok,
            proof=proof if ok else None,
            helpers_added=(),
            progress=bool(ok or spawned_goal_nodes or residual_retry_pending),
            cost_seconds=cost,
            root_candidate=root_candidate,
            metadata={
                "phase": self.phase,
                "lean_verdict": "tactic_solved" if ok else "tactic_rejected",
                "lean_error_type": self._last_error_type(attempts),
                "tactic_transient_failure": bool(transient_failure),
                "retry_after_epoch_s": retry_after_epoch_s,
                "infrastructure_failure_count": infrastructure_failure_count,
                "infrastructure_retry_granted": infrastructure_retry_granted,
                "infrastructure_retry_exhausted": infrastructure_retry_exhausted,
                "finset_reindexing_validation": dict(validation_status),
                "finset_reindexing_context_consumed": bool(context_consumed),
                "finset_reindexing_script_count": script_count,
                "finset_reindexing_side_condition_goal_count": (
                    diagnostic_goal_count
                ),
                "finset_reindexing_typed_side_condition_goal_count": typed_goal_count,
                "finset_reindexing_residual_attestation_status": receipt_status,
                "finset_reindexing_side_condition_node_ids": list(spawned_goal_nodes),
                "schedulable_decomposition_created": bool(
                    spawned_goal_nodes or residual_retry_pending
                ),
                "pending_residual_goal_extraction_added": residual_retry_pending,
                "preserve_action_budget": bool(
                    residual_retry_pending or infrastructure_retry_granted
                ),
                "iteration_neutral": bool(
                    residual_retry_pending or infrastructure_retry_granted
                ),
                "scheduler_neutral": bool(
                    residual_retry_pending or infrastructure_retry_granted
                ),
                "strong_progress": bool(ok),
                "stagnation_neutral": bool(
                    not ok and not infrastructure_retry_exhausted
                ),
                "hard_pivot_neutral": bool(
                    not ok and not infrastructure_retry_exhausted
                ),
                **profile.metadata(),
            },
        )

    def _defer_infrastructure_retry(
        self,
        session: Any,
        context_key: str,
        *,
        attempt_number: int,
    ) -> tuple[float, bool, int]:
        """Grant a bounded transient retry and return its durable receipt."""

        del session
        failure_count = max(1, int(attempt_number or 1))
        exhausted = failure_count > self.max_infrastructure_retries
        self._infrastructure_failure_counts[context_key] = failure_count
        retry_granted = not exhausted
        if not retry_granted:
            self._infrastructure_retry_after_epoch_s.pop(context_key, None)
            return 0.0, False, failure_count
        delay_s = min(1.0, 0.05 * (2 ** min(5, failure_count - 1)))
        retry_after_epoch_s = time.time() + delay_s
        self._infrastructure_retry_after_epoch_s[context_key] = (
            retry_after_epoch_s
        )
        return retry_after_epoch_s, True, failure_count

    def next_eligible_at(self, session: Any) -> float:
        """Expose the durable retry wake time to MiniSession's wait lane."""

        if self.timeout_s <= 0.0 or self.max_candidates <= 0:
            return 0.0
        goal = self._goal_statement(session)
        if not goal:
            return 0.0
        helper_blocks = self._helper_blocks(session)
        context_key = self._context_key(
            session,
            goal,
            helper_names=self._helper_names(helper_blocks),
            helper_blocks=helper_blocks,
        )
        return max(
            0.0,
            float(
                self._infrastructure_retry_after_epoch_s.get(
                    context_key,
                    0.0,
                )
                or 0.0
            ),
        )

    @staticmethod
    def _goal_statement(session: Any) -> str:
        conv = getattr(session, "conv", None)
        if conv is not None:
            goal = str(getattr(conv, "goal_statement", "") or "").strip()
            if goal:
                return goal
        problem = getattr(session, "problem", None)
        return str(getattr(problem, "statement_type", "") or "").strip()

    @staticmethod
    def _helper_blocks(session: Any) -> tuple[str, ...]:
        dossier = getattr(session, "dossier", None)
        if dossier is None:
            return ()
        getter = getattr(dossier, "verified_helper_blocks", None)
        if not callable(getter):
            return ()
        try:
            return tuple(str(item or "") for item in list(getter() or ()) if str(item or "").strip())
        except Exception:
            return ()

    @staticmethod
    def _helper_names(helper_blocks: tuple[str, ...]) -> tuple[str, ...]:
        return tuple(
            name
            for block in helper_blocks
            for name in [helper_decl_name(block)]
            if name
        )

    def _context_key(
        self,
        session: Any,
        goal: str,
        *,
        helper_names: tuple[str, ...] | None = None,
        helper_blocks: tuple[str, ...] | None = None,
    ) -> str:
        del helper_names
        blocks = helper_blocks if helper_blocks is not None else self._helper_blocks(session)
        base_key = tactic_source_context_key(
            source_prefix=self.id,
            goal_statement=goal,
            helper_blocks=blocks,
        )
        generation_identity = getattr(
            session,
            "lean_capability_generation_identity",
            lambda: getattr(session, "lean", None),
        )()
        generation_id = generation_identity
        conv = getattr(session, "conv", None)
        preamble = _proof_state_residual_preamble(conv)
        needs_intro = goal.lstrip().startswith(("∀", "forall")) or "→" in goal or "->" in goal
        scripts = finset_reindexing_scripts(
            detect_finset_reindexing_profile(goal),
            needs_intro=needs_intro,
        )
        dossier = getattr(session, "dossier", None)
        policy = (
            f"{self.phase}|timeout={self.timeout_s:g}|"
            f"candidates={self.max_candidates}|"
            f"infra_retries={self.max_infrastructure_retries}|"
            f"opaque={bool(getattr(conv, 'opaque_mode', True))}|"
            f"allow_answer={bool(getattr(conv, 'allow_official_answer_visibility', False))}|"
            f"suppress_placeholders={bool(getattr(conv, 'suppress_solution_placeholders', True))}|"
            f"answer_payload={getattr(conv, 'official_answer_payload_present', getattr(dossier, 'official_answer_payload_present', None))}|"
            f"scripts={text_hash(chr(10).join(map(repr, scripts)))}|v=3"
        )
        return "|".join(
            (
                base_key,
                f"preamble={text_hash(str(preamble or ''))}",
                f"policy={text_hash(policy)}",
                f"lean_generation={generation_id}",
            )
        )

    def _consume_shared_context(self, session: Any, context_key: str) -> None:
        consume = getattr(session, "consume_static_action_context", None)
        if callable(consume):
            consume(self.id, context_key)

    def _commit_shared_attempt(self, session: Any, context_key: str) -> None:
        commit = getattr(session, "mark_static_action_attempt_dispatched", None)
        if callable(commit):
            commit(self.id, context_key)

    def _release_shared_attempt(self, session: Any, context_key: str) -> None:
        release = getattr(session, "release_static_action_attempt", None)
        if callable(release):
            release(self.id, context_key)

    def _claim_shared_attempt(
        self,
        session: Any,
        context_key: str,
    ) -> tuple[int, bool]:
        claim = getattr(session, "claim_static_action_attempt", None)
        if not callable(claim):
            return 1, True
        return claim(
            self.id,
            context_key,
            max_attempts=self.max_infrastructure_retries + 1,
        )

    @staticmethod
    def _last_error_type(attempts: list[Any]) -> str:
        for attempt in reversed(attempts):
            if not isinstance(attempt, dict):
                continue
            error_type = str(attempt.get("error_type") or "").strip()
            if error_type:
                return error_type
        return ""

    @classmethod
    async def _spawn_reindexing_goals(
        cls,
        session: Any,
        attempts: list[Any],
        *,
        preamble: str,
        helper_blocks: tuple[str, ...],
    ) -> tuple[tuple[str, ...], int, str]:
        candidates: list[tuple[str, str]] = []
        for attempt in list(attempts or ()):
            if not isinstance(attempt, dict):
                continue
            attempt_source = str(attempt.get("source") or "").strip()
            if not attempt_source.startswith("finset_reindexing"):
                continue
            if not bool(attempt.get("partial_stub_validated", False)):
                continue
            proof = str(
                attempt.get("partial_proof_stub")
                or attempt.get("proof_stub")
                or ""
            ).strip()
            if not proof:
                continue
            candidate = (proof, f"finset_reindexing:{attempt_source}")
            if candidate not in candidates:
                candidates.append(candidate)
        if not candidates:
            return (), 0, "residual_attestation_not_requested"
        proof_state = getattr(session, "proof_state", None)
        lean = getattr(session, "lean", None)
        if proof_state is None or lean is None:
            return (), 0, "residual_attestation_infrastructure_deferred"
        parent_node_id = str(getattr(proof_state, "root_node_id", "") or "root")
        parent = getattr(proof_state, "nodes", {}).get(parent_node_id)
        if parent is None:
            return (), 0, "residual_attestation_infrastructure_deferred"
        deadline_monotonic = cls._run_governor_deadline(session)
        last_status = "residual_attestation_lean_rejected"
        for parent_stub, source in candidates:
            checkpoint_id = cls._checkpoint_residual_spawn(
                session,
                label="finset_reindexing_typed_residual_spawn",
            )
            try:
                spawned, goal_count, status = (
                    await _extract_and_spawn_typed_residual_goals(
                        lean=lean,
                        proof_state=proof_state,
                        parent_node=parent,
                        parent_proof_stub=parent_stub,
                        source=source,
                        preamble=str(preamble or ""),
                        lemmas=helper_blocks,
                        timeout_s=0.0,
                        max_goals=256,
                        deadline_monotonic=deadline_monotonic,
                        origin_metadata={
                            "kind": "finset_reindexing",
                            "phase": cls.id,
                            "source": source,
                        },
                        action_metadata={"action_id": cls.id},
                    )
                )
            except BaseException:
                cls._rollback_residual_spawn(proof_state, checkpoint_id)
                raise
            last_status = status
            if status.endswith("_deferred"):
                cls._commit_residual_spawn(proof_state, checkpoint_id)
                return (), goal_count, status
            if status != "residual_attestation_admitted" or not spawned:
                cls._commit_residual_spawn(proof_state, checkpoint_id)
                continue
            try:
                parent = getattr(proof_state, "nodes", {}).get(parent_node_id)
                if parent is not None:
                    parent.action = "assemble_from_children"
                    parent.blocker = (
                        "Finset reindexing exposed "
                        f"{goal_count} typed side condition(s)"
                    )
                    parent.priority = proof_state._priority(parent)
                sync = getattr(proof_state, "sync_to_graph", None)
                dossier = getattr(session, "dossier", None)
                if callable(sync) and dossier is not None:
                    sync(
                        dossier,
                        phase="finset_reindexing_side_conditions",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        refresh_target_node_ids=spawned,
                    )
            except Exception:
                cls._rollback_residual_spawn(proof_state, checkpoint_id)
                restored_parent = getattr(proof_state, "nodes", {}).get(
                    parent_node_id
                )
                if restored_parent is not None:
                    await _extract_and_spawn_typed_residual_goals(
                        lean=lean,
                        proof_state=proof_state,
                        parent_node=restored_parent,
                        parent_proof_stub=parent_stub,
                        source=source,
                        preamble=str(preamble or ""),
                        lemmas=helper_blocks,
                        timeout_s=0.0,
                        max_goals=256,
                        deadline_monotonic=time.monotonic(),
                        origin_metadata={
                            "kind": "finset_reindexing",
                            "phase": cls.id,
                            "source": source,
                        },
                        action_metadata={"action_id": cls.id},
                    )
                return (), goal_count, "residual_attestation_admission_deferred"
            cls._commit_residual_spawn(proof_state, checkpoint_id)
            return tuple(spawned), goal_count, status
        return (), 0, last_status

    @staticmethod
    def _checkpoint_residual_spawn(session: Any, *, label: str) -> str:
        proof_state = getattr(session, "proof_state", None)
        checkpoint = getattr(proof_state, "checkpoint", None)
        if not callable(checkpoint):
            return ""
        try:
            return str(
                checkpoint(dossier=getattr(session, "dossier", None), label=label)
                or ""
            )
        except TypeError:
            try:
                return str(checkpoint(label=label) or "")
            except Exception:
                return ""
        except Exception:
            return ""

    @staticmethod
    def _commit_residual_spawn(proof_state: Any, checkpoint_id: str) -> None:
        commit = getattr(proof_state, "commit", None)
        if checkpoint_id and callable(commit):
            try:
                commit(checkpoint_id)
            except Exception:
                pass

    @staticmethod
    def _rollback_residual_spawn(proof_state: Any, checkpoint_id: str) -> None:
        rollback = getattr(proof_state, "rollback", None)
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass

    @staticmethod
    def _run_governor_deadline(session: Any) -> float:
        remaining = getattr(session, "_run_governor_remaining_s", None)
        if not callable(remaining):
            return 0.0
        try:
            seconds = remaining()
            return (
                time.monotonic() + max(0.0, float(seconds))
                if seconds is not None
                else 0.0
            )
        except (TypeError, ValueError):
            return 0.0

    @staticmethod
    def _receipt_status_metadata(
        status: str,
        *,
        typed_goal_count: int,
    ) -> dict[str, Any]:
        deferred = str(status or "").endswith("_deferred")
        admitted = status == "residual_attestation_admitted"
        rejected = bool(
            status
            and not deferred
            and not admitted
            and status != "residual_attestation_not_requested"
        )
        return {
            "attempted_groups": int(status != "residual_attestation_not_requested"),
            "validated_groups": int(admitted),
            "rejected_groups": int(rejected),
            "failed_groups": int(deferred),
            "timed_out": "timeout" in str(status or ""),
            "complete": not deferred,
            "last_reason": str(status or ""),
            "typed_goal_count": int(typed_goal_count or 0),
        }

    @staticmethod
    def _increment_metric(session: Any, key: str, amount: int = 1) -> None:
        dossier = getattr(session, "dossier", None)
        increment = getattr(dossier, "increment_tool_metric", None)
        if callable(increment):
            try:
                increment(key, int(amount or 1))
            except Exception:
                pass

    @staticmethod
    def _record_event(session: Any, record: dict[str, Any]) -> None:
        event = getattr(session, "_record_event", None)
        if callable(event):
            try:
                event(dict(record))
                return
            except Exception:
                pass
        recorder = getattr(session, "recorder", None)
        if recorder is not None and hasattr(recorder, "record_turn"):
            try:
                recorder.record_turn(dict(record))
                return
            except Exception:
                pass


__all__ = ["FinsetReindexingAction"]
