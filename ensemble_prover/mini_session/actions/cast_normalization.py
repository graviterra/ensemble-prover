"""First-class guarded cast/subtraction normalization action."""

from __future__ import annotations

import asyncio
import time
from typing import Any, ClassVar, FrozenSet

from ensemble_prover.mini_cast_normalizer import (
    cast_normalization_context_key,
    cast_normalization_scripts,
    cast_side_condition_goal_count,
    detect_cast_normalization_profile,
)
from ensemble_prover.mini_tactic_closer import (
    TacticPatternCache,
    is_transient_tactic_close_failure,
    is_transient_tactic_exception,
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


class CastNormalizationAction:
    """Try guarded Nat-cast rewrites before spending LLM turns."""

    id: str = "cast_normalization"
    priority: int = 9
    cost_estimate_s: float = 12.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})

    def __init__(
        self,
        *,
        phase: str = "cast_normalization_prepass",
        timeout_s: float = 12.0,
        max_candidates: int = 16,
        max_transient_attempts: int = 3,
    ) -> None:
        self.phase = str(phase or "cast_normalization_prepass")
        self.timeout_s = float(timeout_s or 0.0)
        self.max_candidates = int(max_candidates or 0)
        self.max_transient_attempts = max(1, int(max_transient_attempts or 1))
        self._attempted_context_keys: set[str] = set()
        self._transient_cooldowns: dict[str, int] = {}
        self._pattern_cache = TacticPatternCache()



    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0 or self.max_candidates <= 0:
            return False
        if session.dossier is None or session.lean is None:
            return False
        goal = self._goal_statement(session)
        if not goal:
            return False
        profile = detect_cast_normalization_profile(goal)
        if not profile.should_attempt:
            return False
        proof_state = getattr(session, "proof_state", None)
        root_id = str(getattr(proof_state, "root_node_id", "") or "root")
        root = getattr(proof_state, "nodes", {}).get(root_id)
        if root is not None and getattr(
            root, "pending_residual_goal_extraction", {}
        ):
            return False
        context_key = self._context_key(session, goal)
        if context_key in self._attempted_context_keys:
            return False
        exhausted = getattr(session, "static_action_context_exhausted", None)
        if callable(exhausted) and exhausted(self.id, context_key):
            return False
        cooldown_until = self._transient_cooldowns.get(context_key)
        if cooldown_until is not None:
            current_iteration = int(getattr(session, "iteration", 0) or 0)
            if current_iteration <= cooldown_until:
                return False
            self._transient_cooldowns.pop(context_key, None)
        return True

    async def run(self, session: Any) -> MiniOutcome:
        started = time.monotonic()
        goal = self._goal_statement(session)
        profile = detect_cast_normalization_profile(goal)
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
        transient_attempts, admitted = self._claim_shared_attempt(
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
                    "cast_normalization_context_consumed": True,
                    "cast_normalization_transient_attempts": transient_attempts,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "preserve_action_budget": True,
                    "verdict": "cast_normalization_shared_attempt_exhausted",
                },
            )
        self._increment_metric(session, "mini_session_cast_normalization_applicable")
        self._increment_metric(session, "mini_session_cast_normalization_attempts")
        if profile.nat_subtraction_count > 0:
            self._increment_metric(
                session,
                "mini_session_cast_normalization_nat_sub_guards_attempted",
            )
        if profile.nat_choose_count > 0:
            self._increment_metric(
                session,
                "mini_session_cast_normalization_choose_rewrites_attempted",
            )

        needs_intro = goal.lstrip().startswith(("∀", "forall")) or "→" in goal or "->" in goal
        script_count = len(cast_normalization_scripts(profile, needs_intro=needs_intro))
        base_attempt_observer = dossier_lean_attempt_observer(
            getattr(session, "dossier", None),
            "cast_normalization_tactic",
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
                    "mode": "guarded_nat_cast",
                    "cast_normalization_context_key": context_key,
                    "cast_normalization_nat_subtraction_count": str(
                        profile.nat_subtraction_count
                    ),
                    "cast_normalization_nat_choose_count": str(
                        profile.nat_choose_count
                    ),
                },
                source_prefixes=("cast_normalization",),
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
            transient_exception = is_transient_tactic_exception(exc)
            cooldown_until, competing_action_available = (
                self._transient_cooldown_until(session)
                if transient_exception
                else (int(getattr(session, "iteration", 0) or 0), False)
            )
            if transient_exception:
                self._transient_cooldowns[context_key] = cooldown_until
                shared_exhausted = (
                    transient_attempts >= self.max_transient_attempts
                )
                if shared_exhausted:
                    self._attempted_context_keys.add(context_key)
            else:
                shared_exhausted = True
            if shared_exhausted:
                self._consume_shared_context(session, context_key)
            self._increment_metric(session, "mini_session_cast_normalization_failed")
            self._record_event(
                session,
                {
                    "phase": self.phase,
                    "action_id": self.id,
                    "context_key_hash": text_hash(context_key),
                    **profile.metadata(),
                    "cast_normalization_script_count": script_count,
                    "exception_type": type(exc).__name__,
                    "exception_message": str(exc),
                    "tactic_transient_failure": transient_exception,
                    "cast_normalization_context_consumed": shared_exhausted,
                    "cast_normalization_transient_attempts": transient_attempts,
                    "cast_normalization_competing_action_available": bool(
                        competing_action_available
                    ),
                    "cast_normalization_deferred_until_iteration": (
                        cooldown_until if transient_exception else None
                    ),
                    "verdict": "cast_normalization_exception",
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
                    "lean_verdict": (
                        "tactic_transient_exception"
                        if transient_exception
                        else "tactic_exception"
                    ),
                    "exception_type": type(exc).__name__,
                    "exception_message": str(exc),
                    "tactic_transient_failure": transient_exception,
                    "cast_normalization_context_consumed": shared_exhausted,
                    "cast_normalization_transient_attempts": transient_attempts,
                    "cast_normalization_competing_action_available": bool(
                        competing_action_available
                    ),
                    "cast_normalization_deferred_until_iteration": (
                        cooldown_until if transient_exception else None
                    ),
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    **profile.metadata(),
                },
                exception=None if transient_exception else exc,
            )

        attempts = list(getattr(result, "attempts", []) or [])
        side_goal_count = cast_side_condition_goal_count(attempts)
        if bool(getattr(result, "ok", False)):
            spawned_side_condition_nodes = ()
            typed_side_goal_count = 0
            residual_attestation_status = "residual_attestation_not_requested"
        else:
            (
                spawned_side_condition_nodes,
                typed_side_goal_count,
                residual_attestation_status,
            ) = await self._spawn_side_condition_goals(
                session,
                attempts,
                preamble=residual_preamble,
                helper_blocks=residual_helpers,
            )
        if side_goal_count > 0:
            self._increment_metric(
                session,
                "mini_session_cast_normalization_side_conditions_exposed",
                side_goal_count,
            )
        if spawned_side_condition_nodes:
            self._increment_metric(
                session,
                "mini_session_cast_normalization_side_conditions_materialized",
                len(spawned_side_condition_nodes),
        )
        ok = bool(getattr(result, "ok", False))
        transient_failure = is_transient_tactic_close_failure(result)
        aggregate_error_type = self._aggregate_error_type(result, attempts)
        residual_attestation_deferred = residual_attestation_status.endswith(
            "_deferred"
        )
        residual_retry_pending = bool(
            residual_attestation_deferred
            and self._root_has_pending_residual_extraction(
                session,
                source_prefix="cast_normalization",
            )
        )
        cooldown_until = int(getattr(session, "iteration", 0) or 0)
        cooldown_competing_action_available = False
        if transient_failure:
            cooldown_until, cooldown_competing_action_available = (
                self._transient_cooldown_until(session)
            )
        context_consumed = bool(
            not ok
            and (
                spawned_side_condition_nodes
                or (
                    not transient_failure
                    and not residual_attestation_deferred
                )
            )
        )
        if transient_failure and not context_consumed:
            context_consumed = bool(
                transient_attempts >= self.max_transient_attempts
            )
        if context_consumed:
            self._attempted_context_keys.add(context_key)
            self._consume_shared_context(session, context_key)
        elif transient_failure:
            self._transient_cooldowns[context_key] = cooldown_until
        if ok:
            self._increment_metric(session, "mini_session_cast_normalization_solved")
        else:
            self._increment_metric(session, "mini_session_cast_normalization_failed")
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
            "cast_normalization_script_count": script_count,
            "cast_normalization_side_condition_goal_count": side_goal_count,
            "cast_normalization_typed_side_condition_goal_count": (
                typed_side_goal_count
            ),
            "cast_normalization_residual_attestation_status": (
                residual_attestation_status
            ),
            "cast_normalization_side_condition_node_ids": list(
                spawned_side_condition_nodes
            ),
            "tactic_candidate_count": int(getattr(result, "candidate_count", 0) or 0),
            **tactic_attempt_telemetry_fields(attempts),
            "tactic_attempts": attempts[:8],
            "tactic_elapsed_s": float(getattr(result, "elapsed_s", 0.0) or 0.0),
            "tactic_exit_reason": str(getattr(result, "exit_reason", "") or ""),
            "tactic_transient_failure": bool(transient_failure),
            "cast_normalization_context_consumed": bool(context_consumed),
            "cast_normalization_transient_attempts": transient_attempts,
            "cast_normalization_competing_action_available": bool(
                cooldown_competing_action_available
            ),
            "cast_normalization_deferred_until_iteration": (
                cooldown_until if transient_failure and not context_consumed else None
            ),
            "verdict": "cast_normalization_solved" if ok else "cast_normalization_failed",
        }
        self._record_event(session, event)
        return MiniOutcome(
            action_id=self.id,
            solved=ok,
            proof=proof if ok else None,
            helpers_added=(),
            progress=bool(
                ok or spawned_side_condition_nodes or residual_retry_pending
            ),
            cost_seconds=cost,
            root_candidate=root_candidate,
            metadata={
                "phase": self.phase,
                "lean_verdict": "tactic_solved" if ok else "tactic_rejected",
                "lean_error_type": aggregate_error_type,
                "tactic_transient_failure": bool(transient_failure),
                "cast_normalization_context_consumed": bool(context_consumed),
                "cast_normalization_transient_attempts": transient_attempts,
                "cast_normalization_competing_action_available": bool(
                    cooldown_competing_action_available
                ),
                "cast_normalization_deferred_until_iteration": (
                    cooldown_until
                    if transient_failure and not context_consumed
                    else None
                ),
                "cast_normalization_script_count": script_count,
                "cast_normalization_side_condition_goal_count": side_goal_count,
                "cast_normalization_typed_side_condition_goal_count": (
                    typed_side_goal_count
                ),
                "cast_normalization_residual_attestation_status": (
                    residual_attestation_status
                ),
                "cast_normalization_side_condition_node_ids": list(
                    spawned_side_condition_nodes
                ),
                "schedulable_decomposition_created": bool(
                    spawned_side_condition_nodes or residual_retry_pending
                ),
                "pending_residual_goal_extraction_added": residual_retry_pending,
                "preserve_action_budget": residual_retry_pending,
                "iteration_neutral": residual_retry_pending,
                "scheduler_neutral": residual_retry_pending,
                "strong_progress": bool(ok),
                "stagnation_neutral": not ok,
                "hard_pivot_neutral": not ok,
                **profile.metadata(),
            },
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
        blocks = helper_blocks if helper_blocks is not None else self._helper_blocks(session)
        names = helper_names if helper_names is not None else self._helper_names(blocks)
        block_by_name = {
            name: block
            for block in blocks
            for name in [helper_decl_name(block)]
            if name
        }
        helper_fingerprints = tuple(
            f"{name}:{text_hash(block_by_name.get(name, ''))}"
            for name in names
            if str(name or "").strip()
        )
        base_key = cast_normalization_context_key(goal, helper_fingerprints)
        generation_identity = getattr(
            session,
            "lean_capability_generation_identity",
            lambda: getattr(session, "lean", None),
        )()
        generation_id = generation_identity
        conv = getattr(session, "conv", None)
        preamble = _proof_state_residual_preamble(conv)
        needs_intro = goal.lstrip().startswith(("∀", "forall")) or "→" in goal or "->" in goal
        scripts = cast_normalization_scripts(
            detect_cast_normalization_profile(goal),
            needs_intro=needs_intro,
        )
        dossier = getattr(session, "dossier", None)
        policy = (
            f"{self.phase}|timeout={self.timeout_s:g}|"
            f"candidates={self.max_candidates}|"
            f"transient_attempts={self.max_transient_attempts}|"
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
            max_attempts=self.max_transient_attempts,
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
    def _aggregate_error_type(cls, result: Any, attempts: list[Any]) -> str:
        """Describe an interrupted portfolio without blaming its last tactic."""

        exit_reason = str(
            getattr(result, "exit_reason", "") or ""
        ).strip().lower()
        try:
            candidate_count = max(
                0,
                int(getattr(result, "candidate_count", 0) or 0),
            )
        except (TypeError, ValueError, OverflowError):
            candidate_count = 0
        if exit_reason == "timeout" and (
            candidate_count <= 0 or len(attempts) < candidate_count
        ):
            return "tactic_portfolio_timeout"
        if is_transient_tactic_close_failure(result):
            return "tactic_portfolio_infrastructure_failure"
        return cls._last_error_type(attempts)

    def _transient_cooldown_until(self, session: Any) -> tuple[int, bool]:
        current_iteration = int(getattr(session, "iteration", 0) or 0)
        competing_action_available = self._has_competing_applicable_action(session)
        return current_iteration + (1 if competing_action_available else 0), bool(
            competing_action_available
        )

    def release_transient_no_applicable_cooldown(self, session: Any) -> bool:
        """Release one funded retry when the anticipated competitor vanished.

        The action yields one scheduler iteration after a transient Lean
        failure only when another action appears applicable.  Applicability is
        necessarily a probe: graph/route gates can make that competitor
        unserviceable by the next select.  At a genuine no-applicable boundary
        the session may remove this action-local delay without granting any
        new tactic budget; the existing invocation budget remains the bound.
        """

        goal = self._goal_statement(session)
        if not goal:
            return False
        context_key = self._context_key(session, goal)
        cooldown_until = self._transient_cooldowns.get(context_key)
        if cooldown_until is None:
            return False
        current_iteration = int(getattr(session, "iteration", 0) or 0)
        if current_iteration > int(cooldown_until):
            self._transient_cooldowns.pop(context_key, None)
            return False
        budget = getattr(session, "budgets", {}).get(self.id)
        exhausted = getattr(budget, "exhausted", None)
        if callable(exhausted):
            try:
                if bool(exhausted()):
                    return False
            except Exception:
                return False
        self._transient_cooldowns.pop(context_key, None)
        return True

    def _has_competing_applicable_action(self, session: Any) -> bool:
        actions = list(getattr(session, "actions", ()) or ())
        if not actions:
            return False
        budgets = getattr(session, "budgets", {}) or {}
        dispatchable = getattr(session, "action_dispatchable", None)
        safe_is_applicable = getattr(session, "_safe_is_applicable", None)
        effective_static_defer = getattr(
            session,
            "_model_call_deferred_static_action_effective",
            None,
        )
        raw_static_defers = {
            str(item or "").strip()
            for item in list(
                getattr(session, "model_call_deferred_static_action_ids", set())
                or set()
            )
            if str(item or "").strip()
        }
        for action in actions:
            if action is self:
                continue
            action_id = str(getattr(action, "id", "") or "").strip()
            if not action_id:
                continue
            try:
                deferred = (
                    bool(effective_static_defer(action_id))
                    if callable(effective_static_defer)
                    else action_id in raw_static_defers
                )
            except Exception:
                deferred = action_id in raw_static_defers
            if deferred:
                continue
            budget = budgets.get(action_id) if isinstance(budgets, dict) else None
            if budget is not None and callable(getattr(budget, "exhausted", None)):
                try:
                    if bool(budget.exhausted()):
                        continue
                except Exception:
                    continue
            if callable(dispatchable):
                try:
                    if not bool(
                        dispatchable(
                            action_id,
                            context="cast_normalization_transient_cooldown",
                        )
                    ):
                        continue
                except Exception:
                    continue
            if callable(safe_is_applicable):
                if safe_is_applicable(
                    action,
                    context="cast_normalization_transient_cooldown",
                ):
                    return True
                continue
            try:
                if bool(action.is_applicable(session)):
                    return True
            except Exception:
                continue
        return False

    @classmethod
    async def _spawn_side_condition_goals(
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
            if not attempt_source.startswith("cast_normalization"):
                continue
            if not bool(attempt.get("partial_stub_validated", False)):
                continue
            attempt_proof = str(attempt.get("partial_proof_stub") or "").strip()
            if not attempt_proof:
                continue
            candidate = (
                attempt_proof,
                f"cast_normalization:{attempt_source}",
            )
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
                label="cast_normalization_typed_residual_spawn",
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
                            "kind": "cast_normalization",
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
                cls._finish_typed_residual_spawn(
                    session,
                    parent_node_id=parent_node_id,
                    spawned=tuple(spawned),
                    goal_count=goal_count,
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
                            "kind": "cast_normalization",
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
    def _root_has_pending_residual_extraction(
        session: Any,
        *,
        source_prefix: str,
    ) -> bool:
        proof_state = getattr(session, "proof_state", None)
        root_id = str(getattr(proof_state, "root_node_id", "") or "root")
        root = getattr(proof_state, "nodes", {}).get(root_id)
        pending = dict(
            getattr(root, "pending_residual_goal_extraction", {}) or {}
        )
        return str(pending.get("source") or "").startswith(source_prefix)

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
    def _finish_typed_residual_spawn(
        session: Any,
        *,
        parent_node_id: str,
        spawned: tuple[str, ...],
        goal_count: int,
    ) -> None:
        proof_state = getattr(session, "proof_state", None)
        if proof_state is None:
            return
        parent = getattr(proof_state, "nodes", {}).get(parent_node_id)
        if parent is not None:
            parent.action = "assemble_from_children"
            parent.blocker = (
                f"cast normalization exposed {goal_count} typed side condition(s)"
            )
            parent.priority = proof_state._priority(parent)
        sync = getattr(proof_state, "sync_to_graph", None)
        dossier = getattr(session, "dossier", None)
        if callable(sync) and dossier is not None:
            sync(
                dossier,
                phase="cast_normalization_side_conditions",
                turn_index=int(getattr(session, "iteration", 0) or 0),
                refresh_target_node_ids=spawned,
            )

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


__all__ = ["CastNormalizationAction"]
