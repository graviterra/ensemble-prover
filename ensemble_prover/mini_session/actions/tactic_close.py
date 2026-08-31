"""Expose bounded deterministic root tactic closure as a session action.

The action calls the shared root-closing primitive, preserves its attempt
telemetry, and packages any verification evidence as a typed ``MiniOutcome``.
``MiniSession.apply`` owns cross-cutting action-outcome accounting.
"""

from __future__ import annotations

import time
from typing import Any, ClassVar, FrozenSet, Mapping

from ensemble_prover.mini_tactic_closer import TacticPatternCache
from ensemble_prover.proof_dossier import helper_decl_name
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ..action import MiniOutcome
from ..tactic_source_suppression import (
    excluded_tactic_source_prefixes_for_context,
    tactic_source_suppression_records,
)


class RootTacticCloseAction:
    """Run the deterministic root closer once with the configured budget."""

    id: str = "tactic_close"
    priority: int = 10
    cost_estimate_s: float = 40.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})

    def __init__(
        self,
        *,
        phase: str = "root_tactic_prepass",
        timeout_s: float = 40.0,
        max_candidates: int = 64,
    ) -> None:
        self.phase = str(phase or "root_tactic_prepass")
        self.timeout_s = float(timeout_s or 0.0)
        self.max_candidates = int(max_candidates or 0)
        self._attempted_context_keys: set[str] = set()
        self._deferred_context_key_set: set[str] = set()
        self._continued_context_key_set: set[str] = set()
        self._pattern_cache = TacticPatternCache()



    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0 or self.max_candidates <= 0:
            return False
        if session.dossier is None or session.lean is None:
            return False
        key = self._context_key(session)
        proof_state = getattr(session, "proof_state", None)
        if key and key in self._attempted_context_keys_for(proof_state):
            return False
        if key and key in self._deferred_context_keys_for(proof_state):
            if key not in self._continued_context_keys_for(proof_state):
                return True
            try:
                proof_state.root_tactic_deferred_skips += 1
            except Exception:
                pass
            return False
        if key and self._deferred_context_keys_for(proof_state):
            self._mark_context_reenabled(proof_state, key)
        return True

    async def run(self, session: Any) -> MiniOutcome:
        # Lazy import keeps mini_prover.py decoupled from mini_session at
        # module load time. M2 will make mini_prover.prove_problem invoke
        # this action; both directions of the import are exercised then.
        from ensemble_prover.mini_prover import _try_root_tactic_close

        context_key = self._context_key(session)
        proof_state = getattr(session, "proof_state", None)
        retry_after_defer = bool(
            context_key and context_key in self._deferred_context_keys_for(proof_state)
        )
        if retry_after_defer:
            try:
                proof_state.root_tactic_transient_retries += 1
            except Exception:
                pass
        elif context_key and self._deferred_context_keys_for(proof_state):
            self._mark_context_reenabled(proof_state, context_key)
        started = time.monotonic()
        helper_blocks = self._helper_blocks(session)
        theorem_name, goal_statement = self._active_root_identity(session)
        excluded_source_prefixes = excluded_tactic_source_prefixes_for_context(
            session,
            goal_statement=goal_statement,
            helper_blocks=helper_blocks,
        )
        try:
            ok, proof = await _try_root_tactic_close(
                phase=self.phase,
                theorem_name=theorem_name,
                goal_statement=goal_statement,
                preamble=session.acceptance_preamble() if hasattr(session, "acceptance_preamble") else _fallback_preamble(session),
                lean=session.lean,
                dossier=session.dossier,
                recorder=session.recorder,
                trace_prefix=session.trace_prefix,
                timeout_s=self.timeout_s,
                max_candidates=self.max_candidates,
                pattern_cache=self._pattern_cache,
                pattern_context={
                    "scope": self.id,
                    "phase": self.phase,
                    "root_tactic_context_key": context_key,
                    "tactic_timeout_s": str(
                        round(max(0.0, float(self.timeout_s or 0.0)), 3)
                    ),
                    "max_candidates": str(max(0, int(self.max_candidates or 0))),
                },
                finalize_root=False,
                excluded_source_prefixes=excluded_source_prefixes,
                tactic_source_suppression_records=tactic_source_suppression_records(
                    session
                ),
                tactic_source_suppression_helper_blocks=helper_blocks,
            )
        except Exception as exc:
            if context_key and retry_after_defer:
                self._mark_context_continued(proof_state, context_key)
                self._continued_context_key_set.add(context_key)
                self._mark_context_attempted(proof_state, context_key)
                self._attempted_context_keys.add(context_key)
                try:
                    proof_state.root_tactic_terminal_after_continuation += 1
                except Exception:
                    pass
            elif context_key:
                self._mark_context_deferred(proof_state, context_key)
                self._deferred_context_key_set.add(context_key)
            self._sync_proof_state(session)
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "phase": self.phase,
                    "root_tactic_context_key": context_key,
                    "root_tactic_context_preserved": True,
                    "root_tactic_context_deferred": bool(
                        context_key and not retry_after_defer
                    ),
                    "root_tactic_context_retry_after_defer": bool(retry_after_defer),
                    "verdict": "tactic_exception",
                    "exception_type": type(exc).__name__,
                    "exception_message": str(exc),
                },
            )
        if retry_after_defer and context_key:
            self._mark_context_continued(proof_state, context_key)
            self._continued_context_key_set.add(context_key)
        transient_failure = self._last_root_tactic_transient_failure(
            session,
        )
        deferrable_timeout = self._last_root_tactic_deferrable_timeout(session)
        if context_key and not transient_failure:
            self._mark_context_attempted(proof_state, context_key)
            self._attempted_context_keys.add(context_key)
            if retry_after_defer:
                try:
                    proof_state.root_tactic_terminal_after_continuation += 1
                except Exception:
                    pass
        elif context_key and retry_after_defer:
            self._mark_context_attempted(proof_state, context_key)
            self._attempted_context_keys.add(context_key)
            try:
                proof_state.root_tactic_terminal_after_continuation += 1
            except Exception:
                pass
        elif context_key and transient_failure and not deferrable_timeout:
            self._mark_context_attempted(proof_state, context_key)
            self._attempted_context_keys.add(context_key)
        deferred = bool(
            context_key
            and transient_failure
            and deferrable_timeout
            and not retry_after_defer
        )
        if deferred:
            self._mark_context_deferred(proof_state, context_key)
            self._deferred_context_key_set.add(context_key)
        self._sync_proof_state(session)
        all_helper_blocks = (
            tuple(session.dossier.verified_helper_blocks())
            if ok and proof and getattr(session, "dossier", None) is not None
            else ()
        )
        contract_status = {}
        helper_blocks = all_helper_blocks
        helper_names = tuple(
            name for block in helper_blocks for name in [helper_decl_name(block)] if name
        )
        if ok and proof and getattr(session, "dossier", None) is not None:
            from ensemble_prover.mini_root_tactic import (
                root_tactic_success_contract_status,
            )
            from ensemble_prover.proof_dossier import active_root_target_statement

            # _try_root_tactic_close already recorded the route WITH the active
            # target (stamping active_root_exact_helper).  Re-creating the
            # contract here without that statement would clobber the marker and
            # wrongly make an active-root-only helper route assemblable, so carry
            # the active target through a minimal success_attempt.
            active_target_text = str(
                active_root_target_statement(session.dossier) or ""
            ).strip()
            contract_success_attempt = (
                {"active_root_target_statement": active_target_text}
                if active_target_text
                else None
            )
            contract_status = root_tactic_success_contract_status(
                session.dossier,
                proof=proof,
                helper_blocks=all_helper_blocks,
                success_attempt=contract_success_attempt,
                phase=self.phase,
                turn_index=int(getattr(session, "iteration", 0) or 0),
                target_statement=str(
                    getattr(session.dossier, "root_statement", "")
                    or getattr(getattr(session, "problem", None), "statement_type", "")
                    or ""
                ),
            )
            route_helper_names = tuple(
                str(name or "").strip()
                for name in list(contract_status.get("helper_names") or [])
                if str(name or "").strip()
            )
            if route_helper_names:
                helper_blocks = tuple(
                    block
                    for block in all_helper_blocks
                    if helper_decl_name(block) in set(route_helper_names)
                )
                helper_names = route_helper_names
            else:
                helper_blocks = ()
                helper_names = ()
        cost = time.monotonic() - started
        return MiniOutcome(
            action_id=self.id,
            solved=bool(ok),
            proof=proof if ok else None,
            helpers_added=(),
            progress=bool(ok),
            cost_seconds=cost,
            root_candidate=(
                RootFinalizationCandidate(
                    proof=proof or "",
                    replay_helpers=helper_blocks,
                    helper_names=helper_names,
                    phase=self.phase,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
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
                    target_statement=str(
                        getattr(session.dossier, "root_statement", "")
                        or getattr(getattr(session, "problem", None), "statement_type", "")
                        or ""
                    ),
                    require_route_contract=bool(
                        contract_status.get("route_id")
                        or contract_status.get("created_route_id")
                        or helper_names
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=proof or "",
                        phase=self.phase,
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
                        replay_helpers=helper_blocks,
                        helper_names=helper_names,
                        source=self.id,
                    ),
                    metadata={"route_assembly_contract_status": dict(contract_status)},
                )
                if ok and proof
                else None
            ),
            metadata={
                "phase": self.phase,
                "root_tactic_context_key": context_key,
                "root_tactic_context_preserved": bool(transient_failure),
                "root_tactic_context_deferred": bool(deferred),
                "root_tactic_context_retry_after_defer": bool(retry_after_defer),
                "replay_helpers": list(helper_blocks),
                "helper_names": list(helper_names),
                "route_assembly_contract_status": dict(contract_status),
            },
        )

    def _sync_proof_state(self, session: Any) -> None:
        proof_state = getattr(session, "proof_state", None)
        sync = getattr(proof_state, "sync_to_graph", None)
        if not callable(sync):
            return
        try:
            sync(
                session.dossier,
                phase=self.phase,
                turn_index=int(getattr(session, "iteration", 0) or 0),
            )
        except Exception:
            pass

    @staticmethod
    def _helper_blocks(session: Any) -> tuple[str, ...]:
        dossier = getattr(session, "dossier", None)
        if dossier is None:
            return ()
        getter = getattr(dossier, "verified_helper_blocks", None)
        if not callable(getter):
            return ()
        try:
            return tuple(
                str(item or "")
                for item in list(getter() or ())
                if str(item or "").strip()
            )
        except Exception:
            return ()

    def _context_key(
        self,
        session: Any,
        *,
        refresh_quality: bool = True,
    ) -> str:
        from ensemble_prover.proof_state_executor import _root_tactic_context_key

        dossier = getattr(session, "dossier", None)
        if dossier is None:
            return ""
        try:
            getter = getattr(
                dossier,
                (
                    "verified_helper_blocks"
                    if refresh_quality
                    else "verified_helper_blocks_snapshot"
                ),
                None,
            )
            helper_blocks = list(getter() or ()) if callable(getter) else []
        except Exception:
            helper_blocks = []
        preamble = (
            session.acceptance_preamble()
            if hasattr(session, "acceptance_preamble")
            else _fallback_preamble(session)
        )
        _theorem_name, goal_statement = self._active_root_identity(session)
        return _root_tactic_context_key(
            goal_statement=goal_statement,
            preamble=preamble,
            helpers=helper_blocks,
            timeout_s=self.timeout_s,
            max_candidates=self.max_candidates,
            active_root_targets=tuple(
                item
                for item in list(getattr(dossier, "active_root_targets", []) or ())
                if isinstance(item, Mapping)
            ),
        )

    def frontier_context_key_probe(self, session: Any) -> str:
        """Observational context identity for scheduler ranking."""

        return self._context_key(session, refresh_quality=False)

    @staticmethod
    def _active_root_identity(session: Any) -> tuple[str, str]:
        """Return the scoped session root, never a parent provenance problem."""

        dossier = getattr(session, "dossier", None)
        proof_state = getattr(session, "proof_state", None)
        problem = getattr(session, "problem", None)
        theorem_name = str(
            getattr(dossier, "theorem_name", "")
            or getattr(proof_state, "theorem_name", "")
            or getattr(problem, "theorem_name", "")
            or ""
        )
        goal_statement = str(
            getattr(dossier, "root_statement", "")
            or getattr(proof_state, "root_statement", "")
            or getattr(problem, "statement_type", "")
            or ""
        )
        return theorem_name, goal_statement

    @staticmethod
    def _last_root_tactic_transient_failure(session: Any) -> bool:
        dossier = getattr(session, "dossier", None)
        attempts = getattr(dossier, "attempts", None)
        if isinstance(attempts, list) and attempts:
            last_attempt = attempts[-1]
            if str(getattr(last_attempt, "verdict", "") or "") == (
                "tactic_transient_failure"
            ):
                return True
        recorder = getattr(session, "recorder", None)
        records = getattr(recorder, "records", None)
        if not isinstance(records, list) or not records:
            return False
        last = records[-1]
        if not isinstance(last, dict):
            return False
        return bool(
            last.get("root_tactic_context_preserved")
            and str(last.get("verdict") or "") == "tactic_transient_failure"
        )

    @staticmethod
    def _last_root_tactic_deferrable_timeout(session: Any) -> bool:
        record: Any = {}
        recorder = getattr(session, "recorder", None)
        records = getattr(recorder, "records", None)
        if isinstance(records, list) and records and isinstance(records[-1], dict):
            record = records[-1]
        else:
            dossier = getattr(session, "dossier", None)
            attempts = getattr(dossier, "attempts", None)
            if isinstance(attempts, list) and attempts:
                metadata = getattr(attempts[-1], "metadata", None)
                if isinstance(metadata, dict):
                    record = metadata
            if not record:
                graph_attempts = getattr(
                    getattr(dossier, "proof_graph", None),
                    "attempts",
                    None,
                )
                if isinstance(graph_attempts, list) and graph_attempts:
                    metadata = getattr(graph_attempts[-1], "metadata", None)
                    if isinstance(metadata, dict):
                        record = metadata
        if not isinstance(record, dict):
            return False
        try:
            candidate_count = int(record.get("tactic_candidate_count", 0) or 0)
        except (TypeError, ValueError):
            candidate_count = 0
        attempts = list(record.get("tactic_attempts") or [])
        exit_reason = str(record.get("tactic_exit_reason") or "").strip().lower()
        return bool(
            exit_reason == "timeout"
            and candidate_count > 0
            and len(attempts) < candidate_count
        )

    @staticmethod
    def _deferred_context_keys_from_state(proof_state: Any) -> set[str]:
        root = getattr(proof_state, "nodes", {}).get(
            getattr(proof_state, "root_node_id", ""),
        ) if proof_state is not None else None
        return {
            str(item or "").strip()
            for item in list(getattr(root, "root_tactic_deferred_context_keys", []) or [])
            if str(item or "").strip()
        }

    def _deferred_context_keys_for(self, proof_state: Any) -> set[str]:
        return set(self._deferred_context_key_set) | self._deferred_context_keys_from_state(
            proof_state
        )

    @staticmethod
    def _continued_context_keys_from_state(proof_state: Any) -> set[str]:
        root = getattr(proof_state, "nodes", {}).get(
            getattr(proof_state, "root_node_id", ""),
        ) if proof_state is not None else None
        return {
            str(item or "").strip()
            for item in list(getattr(root, "root_tactic_continued_context_keys", []) or [])
            if str(item or "").strip()
        }

    def _continued_context_keys_for(self, proof_state: Any) -> set[str]:
        return set(self._continued_context_key_set) | self._continued_context_keys_from_state(
            proof_state
        )

    @staticmethod
    def _attempted_context_keys_from_state(proof_state: Any) -> set[str]:
        root = getattr(proof_state, "nodes", {}).get(
            getattr(proof_state, "root_node_id", ""),
        ) if proof_state is not None else None
        return {
            str(item or "").strip()
            for item in list(getattr(root, "root_tactic_attempted_context_keys", []) or [])
            if str(item or "").strip()
        }

    def _attempted_context_keys_for(self, proof_state: Any) -> set[str]:
        return set(self._attempted_context_keys) | self._attempted_context_keys_from_state(
            proof_state
        )

    @staticmethod
    def _mark_context_attempted(proof_state: Any, context_key: str) -> None:
        key = str(context_key or "").strip()
        root = getattr(proof_state, "nodes", {}).get(
            getattr(proof_state, "root_node_id", ""),
        ) if proof_state is not None else None
        if root is None or not key:
            return
        attempted = getattr(root, "root_tactic_attempted_context_keys", None)
        if attempted is None:
            return
        if key in attempted:
            return
        attempted.append(key)
        del attempted[:-4096]
        try:
            proof_state.root_tactic_context_attempts += 1
        except Exception:
            pass

    @staticmethod
    def _mark_context_deferred(proof_state: Any, context_key: str) -> None:
        key = str(context_key or "").strip()
        root = getattr(proof_state, "nodes", {}).get(
            getattr(proof_state, "root_node_id", ""),
        ) if proof_state is not None else None
        if root is None or not key:
            return
        if key not in root.root_tactic_deferred_context_keys:
            root.root_tactic_deferred_context_keys.append(key)
            del root.root_tactic_deferred_context_keys[:-4096]
            try:
                proof_state.root_tactic_transient_deferrals += 1
            except Exception:
                pass

    @staticmethod
    def _mark_context_continued(proof_state: Any, context_key: str) -> None:
        key = str(context_key or "").strip()
        root = getattr(proof_state, "nodes", {}).get(
            getattr(proof_state, "root_node_id", ""),
        ) if proof_state is not None else None
        if root is None or not key:
            return
        continued = getattr(root, "root_tactic_continued_context_keys", None)
        if continued is None or key in continued:
            return
        continued.append(key)
        del continued[:-4096]

    def _mark_context_reenabled(self, proof_state: Any, context_key: str) -> None:
        key = str(context_key or "").strip()
        if not key or key in self._deferred_context_key_set:
            return
        root = getattr(proof_state, "nodes", {}).get(
            getattr(proof_state, "root_node_id", ""),
        ) if proof_state is not None else None
        if root is None:
            return
        deferred = {
            str(item or "").strip()
            for item in list(getattr(root, "root_tactic_deferred_context_keys", []) or [])
            if str(item or "").strip()
        }
        if not deferred or key in deferred:
            return
        reenabled = getattr(root, "root_tactic_reenabled_context_keys", None)
        if reenabled is None or key in reenabled:
            return
        reenabled.append(key)
        del reenabled[:-4096]
        try:
            proof_state.root_tactic_reenabled_by_new_evidence += 1
        except Exception:
            pass


def _fallback_preamble(session: Any) -> str:
    conv = getattr(session, "conv", None)
    if conv is None:
        return ""
    from ensemble_prover.proof_state_executor import _proof_state_acceptance_preamble

    return _proof_state_acceptance_preamble(conv)
