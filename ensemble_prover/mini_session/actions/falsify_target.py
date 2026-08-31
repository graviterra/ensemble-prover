"""Session-native falsification of the active formal target."""

from __future__ import annotations

import hashlib
import json
import time
from typing import Any, ClassVar, FrozenSet

from ensemble_prover.mini_falsification import (
    CounterexampleCandidate,
    FalsificationFinding,
    FalsificationOutcome,
    FalsificationPolicy,
    FalsificationReport,
    FalsificationService,
    TargetKind,
)
from ensemble_prover.mini_falsification.certificate import (
    certify_negation_proof_result,
)
from ensemble_prover.mini_falsification.service import (
    build_local_sequent,
    falsification_environment_hash,
)
from ensemble_prover.mini_falsification.veto import (
    cheap_veto_skip_key,
    coverage_is_pending,
    foreground_veto_is_spent,
    helpers_changed_since_veto,
    infra_retry_is_blocked,
    make_falsification_veto_policy,
    record_veto_outcome,
    session_has_recursive_controller,
)
from ensemble_prover.proof_dossier import (
    _statements_share_bound_lean_identity,
    text_hash,
)
from ..action import MiniOutcome
from ..session import _dispatch_capability_identity


class FalsifyTargetAction:
    id = "falsify_target"
    priority = 11
    cost_estimate_s = 30.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "session_state"})
    # The live estimate follows the engine timeout but is scheduler pacing,
    # not mathematical search identity.
    REPLAY_OPERATIONAL_SPEC_PATHS: ClassVar[FrozenSet[str]] = frozenset(
        {"cost_estimate_s"}
    )
    FAILED_DISPATCH_DURABLE_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {"_completed_contexts"}
    )
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {"_pending_replay_attempts"}
    )

    def __init__(
        self,
        *,
        policy: FalsificationPolicy | None = None,
        lane: str = "foreground",
    ) -> None:
        # Keep the full execution policy private so the generic action-spec
        # walker does not accidentally make timeout/batch tuning replay
        # identity.
        self._policy = policy or FalsificationPolicy()
        self._lane = "idle" if str(lane or "") == "idle" else "foreground"
        self._veto_policy = make_falsification_veto_policy(self._policy)
        if self._lane == "idle":
            self.id = "falsify_coverage"
            self.priority = 90
            # Idle depth may use the full engine portfolio, but it must never
            # preempt proving. The estimate is scheduler pacing only.
            self.cost_estimate_s = max(
                60.0,
                2.0 * float(getattr(self.policy, "engine_timeout_s", 90.0) or 90.0),
            )
        else:
            # One cheap veto quantum. Certification leftover is best-effort;
            # unpromoted candidates remain durable and retryable.
            self.cost_estimate_s = max(
                8.0,
                float(self._veto_policy.aggregate_timeout_s) + 1.0,
            )
        self._completed_contexts: set[str] = set()
        # Runtime fairness guard for completed campaigns. Foreground pending
        # coverage is memory, not a job; the idle lane may resume it.
        self._session_dispatches: set[str] = set()
        self._pending_replay_attempts: set[tuple[str, int, str, str]] = set()

    def replay_config(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "semantic_policy_hash": self.policy.policy_hash,
        }

    @property
    def policy(self) -> FalsificationPolicy:
        return self._policy




    def _candidate_targets(
        self,
        session: Any,
    ) -> tuple[tuple[str, TargetKind, tuple[str, ...]], ...]:
        dossier = getattr(session, "dossier", None)
        root = str(getattr(dossier, "root_statement", "") or "").strip()
        selected = dict(getattr(session, "selected_work_item_record", {}) or {})
        selected_statement = str(
            selected.get("target_statement")
            or selected.get("statement")
            or selected.get("obligation_statement")
            or ""
        ).strip()
        raw_hypotheses = selected.get("hypotheses") or selected.get("local_hypotheses") or ()
        hypotheses = tuple(
            str(item).strip() for item in raw_hypotheses if str(item).strip()
        ) if not isinstance(raw_hypotheses, str) else (raw_hypotheses.strip(),)
        targets: list[tuple[str, TargetKind, tuple[str, ...]]] = []
        include_root = bool(root)
        if (
            include_root
            and self._lane == "foreground"
            and session_has_recursive_controller(session)
        ):
            # Recursive already vetoes the root before proving. Independent
            # foreground crawling of the same statement would preempt that
            # work. The idle lane may still resume deeper root coverage.
            include_root = False
        if include_root:
            targets.append((root, TargetKind.ROOT, ()))
        if selected_statement and selected_statement != root:
            targets.append((selected_statement, TargetKind.HELPER, hypotheses))
        for proposed in dict(getattr(dossier, "proposed_helpers", {}) or {}).values():
            statement = str(getattr(proposed, "statement", "") or "").strip()
            if statement:
                targets.append((statement, TargetKind.HELPER, ()))
        for pending in list(
            getattr(dossier, "mini_falsification_pending_certificates", ()) or ()
        ):
            certificate = (
                pending.get("certificate") if isinstance(pending, dict) else None
            )
            if not isinstance(certificate, dict):
                continue
            statement = str(certificate.get("statement") or "").strip()
            try:
                kind = TargetKind(str(pending.get("target_kind") or "helper"))
            except ValueError:
                kind = TargetKind.HELPER
            if statement:
                targets.append((statement, kind, ()))
        deduped: list[tuple[str, TargetKind, tuple[str, ...]]] = []
        seen: set[tuple[str, tuple[str, ...]]] = set()
        for target in targets:
            key = (target[0], target[2])
            if key[0] and key not in seen:
                seen.add(key)
                deduped.append(target)
        return tuple(deduped)

    def _context_key_for(
        self,
        session: Any,
        target: tuple[str, TargetKind, tuple[str, ...]],
    ) -> str:
        statement, kind, hypotheses = target
        dossier = getattr(session, "dossier", None)
        helpers = list(
            dossier.verified_helper_blocks()
            if callable(getattr(dossier, "verified_helper_blocks", None))
            else ()
        )
        cursor_getter = getattr(dossier, "falsification_cursors_for_statement", None)
        cursor_statement = build_local_sequent(statement, hypotheses)
        preamble = str(session.acceptance_preamble() or "")
        environment_hash = falsification_environment_hash(
            preamble=preamble,
            helpers=helpers,
            policy=self.policy,
            lean=getattr(session, "lean", None),
        )
        cursors = (
            cursor_getter(cursor_statement, environment_hash=environment_hash)
            if callable(cursor_getter)
            else {}
        )
        payload = {
            "statement": statement,
            "kind": kind.value,
            "hypotheses": hypotheses,
            "helpers": helpers,
            "preamble": preamble,
            "environment_hash": environment_hash,
            "cursors": cursors,
            "policy": self.policy.policy_hash,
        }
        return hashlib.sha256(
            json.dumps(payload, sort_keys=True, default=str).encode("utf-8")
        ).hexdigest()

    def _target_environment_key(
        self,
        session: Any,
        target: tuple[str, TargetKind, tuple[str, ...]],
    ) -> str:
        statement, kind, hypotheses = target
        dossier = getattr(session, "dossier", None)
        helpers = list(
            dossier.verified_helper_blocks()
            if callable(getattr(dossier, "verified_helper_blocks", None))
            else ()
        )
        preamble = str(session.acceptance_preamble() or "")
        environment_hash = falsification_environment_hash(
            preamble=preamble,
            helpers=helpers,
            policy=self.policy,
            lean=getattr(session, "lean", None),
        )
        return hashlib.sha256(
            json.dumps(
                {
                    "statement": statement,
                    "kind": kind.value,
                    "hypotheses": hypotheses,
                    "helpers": helpers,
                    "preamble": preamble,
                    "environment_hash": environment_hash,
                    "policy": self.policy.policy_hash,
                },
                sort_keys=True,
                default=str,
            ).encode("utf-8")
        ).hexdigest()

    def _skip_key_for(
        self,
        session: Any,
        target: tuple[str, TargetKind, tuple[str, ...]],
    ) -> str:
        statement, _kind, hypotheses = target
        return cheap_veto_skip_key(
            statement=statement,
            hypotheses=hypotheses,
            preamble=str(session.acceptance_preamble() or ""),
            policy=self.policy,
            lean=getattr(session, "lean", None),
        )

    def _pending_target(
        self, session: Any
    ) -> tuple[str, TargetKind, tuple[str, ...]] | None:
        dossier = getattr(session, "dossier", None)
        helpers = list(
            dossier.verified_helper_blocks()
            if callable(getattr(dossier, "verified_helper_blocks", None))
            else ()
        )
        replay_environment_hash = falsification_environment_hash(
            preamble=str(session.acceptance_preamble() or ""),
            helpers=helpers,
            policy=self.policy,
            lean=getattr(session, "lean", None),
        )
        replay_suppressed = getattr(
            dossier, "certificate_replay_is_suppressed", None
        )
        for target in self._candidate_targets(session):
            target_statement = build_local_sequent(target[0], target[2])
            target_environment_key = self._target_environment_key(session, target)
            skip_key = self._skip_key_for(session, target)
            capability = _dispatch_capability_identity(
                getattr(session, "lean", None)
            )
            if infra_retry_is_blocked(
                dossier, skip_key, capability=capability
            ):
                continue
            if any(
                isinstance(item, dict)
                and isinstance(item.get("certificate"), dict)
                and str(item["certificate"].get("statement") or "").strip()
                == target_statement
                and not (
                    callable(replay_suppressed)
                    and replay_suppressed(
                        certificate_hash=str(
                            item["certificate"].get("certificate_hash") or ""
                        ),
                        environment_hash=replay_environment_hash,
                        policy_hash=self.policy.policy_hash,
                    )
                )
                and (
                    target_environment_key,
                    _dispatch_capability_identity(
                        getattr(session, "lean", None)
                    ),
                    str(item["certificate"].get("certificate_hash") or ""),
                    str(item.get("report_hash") or ""),
                )
                not in self._pending_replay_attempts
                for item in getattr(
                    getattr(session, "dossier", None),
                    "mini_falsification_pending_certificates",
                    (),
                )
                or ()
            ):
                # Cached completion state cannot confer authority on a
                # serialized certificate; force its fresh replay first.
                return target
            helper_growth_replay = bool(
                helpers_changed_since_veto(dossier, skip_key, helpers)
                and callable(
                    getattr(
                        dossier,
                        "lean_checked_unpromoted_refutation_candidates_for_statement",
                        None,
                    )
                )
                and dossier.lean_checked_unpromoted_refutation_candidates_for_statement(
                    target_statement
                )
            )
            if helper_growth_replay:
                # New helpers do not reopen ordinary root search, but they
                # may enable certification of an already-found candidate.
                return target
            if self._lane == "foreground":
                if foreground_veto_is_spent(dossier, skip_key):
                    continue
                if (
                    target_environment_key not in self._session_dispatches
                    and self._context_key_for(session, target)
                    not in self._completed_contexts
                ):
                    return target
                continue
            if coverage_is_pending(dossier, skip_key):
                return target
        return None

    def is_applicable(self, session: Any) -> bool:
        if not self.policy.enabled or getattr(session, "lean", None) is None:
            return False
        dossier = getattr(session, "dossier", None)
        if not str(
            getattr(dossier, "current_lean_environment_hash", "") or ""
        ).strip():
            # A certificate can only authorize the exact target inside a bound
            # Lean statement environment. Wait for session initialization
            # instead of running an inevitably unadmittable campaign.
            return False
        if text_hash(str(session.acceptance_preamble() or "")) != str(
            getattr(dossier, "current_lean_environment_hash", "") or ""
        ).strip():
            # A split prompt/checker context is temporarily inadmissible for
            # this authority path.  Do not consume a semantic completion key:
            # rebinding the dossier environment must immediately reopen it.
            return False
        if getattr(dossier, "root_disproof_certificate", None):
            return False
        return self._pending_target(session) is not None

    async def run(self, session: Any) -> MiniOutcome:
        started = time.monotonic()
        target = self._pending_target(session)
        if target is None:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "scheduler_neutral": True,
                    "iteration_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                },
            )
        context_key = self._context_key_for(session, target)
        statement, kind, hypotheses = target
        dossier = session.dossier
        helpers = list(dossier.verified_helper_blocks())
        cursor_getter = getattr(dossier, "falsification_cursors_for_statement", None)
        cursor_statement = build_local_sequent(statement, hypotheses)
        preamble = str(session.acceptance_preamble() or "")
        target_environment_hash = str(
            getattr(dossier, "current_lean_environment_hash", "") or ""
        ).strip()
        if (
            not target_environment_hash
            or text_hash(preamble) != target_environment_hash
        ):
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "scheduler_neutral": True,
                    "iteration_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "verdict": "falsification_target_environment_unbound",
                },
            )
        environment_hash = falsification_environment_hash(
            preamble=preamble,
            helpers=helpers,
            policy=self.policy,
            lean=getattr(session, "lean", None),
        )
        report = None
        pending_replay_failed: dict[str, Any] | None = None
        pending_replay_status = ""
        pending_replay_key: tuple[str, int, str, str] | None = None
        pending_records = list(
            getattr(dossier, "mini_falsification_pending_certificates", ()) or ()
        )
        for pending in pending_records:
            certificate_record = (
                pending.get("certificate") if isinstance(pending, dict) else None
            )
            persisted_statement = str(
                certificate_record.get("statement") or ""
            ).strip() if isinstance(certificate_record, dict) else ""
            if (
                not isinstance(certificate_record, dict)
                or not persisted_statement
                or persisted_statement != cursor_statement
            ):
                continue
            replay_suppressed = getattr(
                dossier, "certificate_replay_is_suppressed", None
            )
            if callable(replay_suppressed) and replay_suppressed(
                certificate_hash=str(
                    certificate_record.get("certificate_hash") or ""
                ),
                environment_hash=environment_hash,
                policy_hash=self.policy.policy_hash,
            ):
                continue
            pending_replay_key = (
                self._target_environment_key(session, target),
                _dispatch_capability_identity(
                    getattr(session, "lean", None)
                ),
                str(certificate_record.get("certificate_hash") or ""),
                str(pending.get("report_hash") or ""),
            )
            self._pending_replay_attempts.add(pending_replay_key)
            root_statement = str(getattr(dossier, "root_statement", "") or "").strip()
            replay_kind = (
                TargetKind.ROOT
                if _statements_share_bound_lean_identity(
                    dossier,
                    persisted_statement,
                    root_statement,
                    str(
                        getattr(dossier, "current_lean_environment_hash", "")
                        or ""
                    ).strip(),
                )
                else kind
            )
            candidate = CounterexampleCandidate(
                engine="persisted_certificate_replay",
                witness_terms=tuple(certificate_record.get("witness_terms") or ()),
                concrete_statement=str(
                    certificate_record.get("concrete_statement") or ""
                ),
                explanation="fresh replay of quarantined persisted certificate",
            )
            certification = await certify_negation_proof_result(
                session.lean,
                # Replay the exact statement whose proof was serialized.  A
                # canonical-equivalent live root controls classification, not
                # the syntax supplied to Lean.
                statement=persisted_statement,
                proof=str(certificate_record.get("proof_code") or ""),
                candidate=candidate,
                preamble=preamble,
                helpers=helpers,
                policy=self.policy,
                environment_hash=environment_hash,
            )
            pending_replay_status = certification.status.value
            if certification.authoritative:
                dossier.mini_falsification_pending_certificates.remove(pending)
                report = FalsificationReport(
                    statement=persisted_statement,
                    target_kind=replay_kind,
                    findings=(
                        FalsificationFinding(
                            engine="persisted_certificate_replay",
                            outcome=FalsificationOutcome.REFUTED,
                            reason="persisted certificate passed fresh Lean replay and axiom audit",
                            candidates=(candidate,),
                            certificate=certification.certificate,
                            checks_run=1,
                        ),
                    ),
                    policy_hash=self.policy.policy_hash,
                    environment_hash=environment_hash,
                )
            elif certification.retryable:
                pending_replay_failed = pending
                report = FalsificationReport(
                    statement=persisted_statement,
                    target_kind=replay_kind,
                    findings=(
                        FalsificationFinding(
                            engine="persisted_certificate_replay",
                            outcome=FalsificationOutcome.TRANSIENT_FAILURE,
                            reason=certification.reason,
                            checks_run=1,
                            error_kind="infrastructure",
                        ),
                    ),
                    policy_hash=self.policy.policy_hash,
                    environment_hash=environment_hash,
                )
            else:
                # A syntactically unsafe, Lean-rejected, or policy-rejected
                # proof is not made retryable by keeping it quarantined.
                record_disposition = getattr(
                    dossier, "record_certificate_replay_disposition", None
                )
                if callable(record_disposition):
                    record_disposition(
                        certificate_hash=str(
                            certificate_record.get("certificate_hash") or ""
                        ),
                        environment_hash=environment_hash,
                        policy_hash=self.policy.policy_hash,
                        reason=certification.reason,
                    )
                dossier.mini_falsification_pending_certificates.remove(pending)
            break
        if report is None:
            skip_key = self._skip_key_for(session, target)
            helper_growth_replay = helpers_changed_since_veto(
                dossier, skip_key, helpers
            )
            search_policy = (
                self.policy
                if self._lane == "idle" or helper_growth_replay
                else self._veto_policy
            )
            search_environment_hash = falsification_environment_hash(
                preamble=preamble,
                helpers=helpers,
                policy=search_policy,
                lean=getattr(session, "lean", None),
            )
            search_cursors = (
                cursor_getter(
                    cursor_statement,
                    environment_hash=search_environment_hash,
                )
                if callable(cursor_getter)
                else {}
            )
            report = await FalsificationService(policy=search_policy).falsify(
                session.lean,
                statement=statement,
                target_kind=kind,
                preamble=preamble,
                helpers=helpers,
                local_hypotheses=hypotheses,
                cursors=search_cursors,
            )
        environment_still_bound = bool(
            str(
                getattr(dossier, "current_lean_environment_hash", "") or ""
            ).strip()
            == target_environment_hash
            and text_hash(preamble) == target_environment_hash
        )
        promoted = bool(
            environment_still_bound and dossier.record_falsification_report(report)
        )
        terminalized_proof_state_aliases: tuple[str, ...] = ()
        if promoted and report.authoritative_refutation is not None:
            try:
                from ensemble_prover.mini_session.child_goal_falsification import (
                    terminalize_exact_proof_state_aliases,
                )

                certificate_record = report.authoritative_refutation.to_record()
                terminalized_proof_state_aliases = (
                    terminalize_exact_proof_state_aliases(
                        parent_session=session,
                        dossier=dossier,
                        statement=report.statement,
                        certificate_hash=str(
                            certificate_record.get("certificate_hash") or ""
                        ),
                        target_environment_hash=str(
                            getattr(
                                dossier,
                                "current_lean_environment_hash",
                                "",
                            )
                            or ""
                        ).strip(),
                        reason=(
                            "freshly replayed Lean negation terminalized exact goal"
                        ),
                    )
                )
            except Exception:
                # Graph invalidation remains authoritative. A later proof-state
                # reconciliation may retry local alias terminalization.
                terminalized_proof_state_aliases = ()
        authority_conflict = bool(
            report.authoritative_refutation is not None and not promoted
        )
        if report.outcome is FalsificationOutcome.TRANSIENT_FAILURE:
            # Infrastructure failures are retryable, not mathematical route
            # exhaustion. Back off and yield so proving can proceed; a
            # capability-generation change wakes the same work immediately.
            if pending_replay_failed is not None and pending_replay_key is not None:
                self._pending_replay_attempts.discard(pending_replay_key)
            record_veto_outcome(
                dossier,
                self._skip_key_for(session, target),
                report,
                helpers=helpers,
                capability=_dispatch_capability_identity(
                    getattr(session, "lean", None)
                ),
            )
        elif not pending_replay_status:
            # Pending coverage is memory. Foreground spends the cheap-veto
            # skip key so this action cannot monopolize priority 11.
            # Certificate replay of one proof is not a completed veto search.
            self._completed_contexts.add(context_key)
            record_veto_outcome(
                dossier,
                self._skip_key_for(session, target),
                report,
                helpers=helpers,
                capability=_dispatch_capability_identity(
                    getattr(session, "lean", None)
                ),
            )
            if self._lane == "idle" and not report.has_pending_coverage:
                self._session_dispatches.add(
                    self._target_environment_key(session, target)
                )
        effective_kind = report.target_kind
        root_disproved = bool(promoted and effective_kind is TargetKind.ROOT)
        metadata = {
            "strong_progress": promoted,
            "scheduler_neutral": not promoted,
            "stagnation_neutral": not promoted,
            "hard_pivot_neutral": not promoted,
            "iteration_neutral": not promoted,
            "preserve_frontier_work": not promoted,
            "target_statement": report.statement,
            "target_kind": effective_kind.value,
            "pending_certificate_replay_status": pending_replay_status,
            "falsification_report": report.to_record(),
            "falsification_coverage_pending": report.has_pending_coverage,
            "falsification_lane": self._lane,
            "authoritative_refutation": promoted,
            "terminalized_proof_state_aliases": list(
                terminalized_proof_state_aliases
            ),
            "disproved": root_disproved,
            "falsification_trust_boundary_conflict": authority_conflict,
        }
        if authority_conflict:
            metadata.update(
                {
                    "terminal_failure": True,
                    "terminal_failure_reason": "falsification_trust_boundary_conflict",
                    "terminal_failure_kind": "proof_disproof_conflict",
                }
            )
        if root_disproved:
            metadata.update(
                {
                    "terminal_failure": True,
                    "terminal_failure_reason": "root_disproved_by_audited_lean_certificate",
                    "terminal_failure_kind": "mathematical_disproof",
                }
            )
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=promoted,
            cost_seconds=time.monotonic() - started,
            metadata=metadata,
        )


class FalsifyCoverageAction(FalsifyTargetAction):
    """Low-priority resumable coverage. Never preempts proving."""

    id = "falsify_coverage"
    priority = 90

    def __init__(self, *, policy: FalsificationPolicy | None = None) -> None:
        super().__init__(policy=policy, lane="idle")
