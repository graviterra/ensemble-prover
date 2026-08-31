"""First-class resumable formal-state search for Mini."""

from __future__ import annotations

import copy
import hashlib
import json
import time
from typing import Any, ClassVar, Dict, FrozenSet, Optional, Tuple

from ensemble_prover.lean_parser import LeanGoalState, canonical_error_type
from ensemble_prover.mini_formal_state_search import (
    FormalStateSearchCheckpoint,
    FormalStateSearchConfig,
    _formal_policy_identity,
    run_goal_conditioned_formal_search,
)
from ensemble_prover.proof_dossier import (
    helper_decl_name,
    selected_work_has_explicit_cognition,
    text_hash,
)
from ensemble_prover.proof_lineage import (
    ProofIdeaObservation,
    ProofLineageEnvelope,
    stable_identity,
)
from ensemble_prover.proof_state import canonicalize_lean_statement_for_identity
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)
from ensemble_prover.tactic_tree import (
    TacticNodeStatus,
    TacticTree,
    tactic_tree_bottlenecks,
)

from ..action import (
    MiniOutcome,
    action_dispatch_replaced,
    require_current_action_dispatch,
)
from ..graph_sync import sync_proof_state_to_graph


class FormalSelectedProofIdeaContextError(RuntimeError):
    """Explicit selected cognition is unresolved and must not be retried cold."""

    mini_selected_proof_idea_context_error = True


class FormalStateSearchAction:
    """Advance one exact Lean-state frontier by one bounded quantum."""

    id: str = "formal_state_search"
    priority: int = 16
    cost_estimate_s: float = 45.0
    BUDGET_SCOPE: ClassVar[str] = "formal_context"
    SELECTED_FRONTIER_PRECHECK: ClassVar[bool] = True
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {"_contexts"}
    )

    def __init__(self, *, config: FormalStateSearchConfig) -> None:
        self.config = config.normalized()
        self._contexts: Dict[str, Dict[str, Any]] = {}
        self._pending_root_context: str = ""
        self._last_context_key: str = ""
        self._yield_iteration: int = -1
        self._next_eligible_at: float = 0.0

    def failed_dispatch_durable_state(self) -> Dict[str, Any]:
        """Project completed context receipts across generation recovery."""

        durable_statuses = {"acceptance_pending", "solved", "terminal"}
        return {
            "contexts": {
                key: copy.deepcopy(record)
                for key, record in self._contexts.items()
                if str(record.get("status") or "") in durable_statuses
            }
        }

    def merge_failed_dispatch_durable_state(self, state: Any) -> None:
        """Merge only completed/provider-free context receipts."""

        record = dict(state or {}) if isinstance(state, dict) else {}
        contexts = record.get("contexts")
        if not isinstance(contexts, dict):
            return
        self._contexts.update(copy.deepcopy(contexts))

    def is_applicable(self, session: Any) -> bool:
        return self._is_applicable(session, mutate=True)

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Observational applicability used only for scheduler quotation."""

        return self._is_applicable(session, mutate=False)

    def _is_applicable(self, session: Any, *, mutate: bool) -> bool:
        if not self.config.enabled:
            return False
        if (
            getattr(session, "lean", None) is None
            or getattr(session, "prover_client", None) is None
            or getattr(session, "dossier", None) is None
            or getattr(session, "proof_state", None) is None
        ):
            return False
        return self._select_context(session, mutate=mutate) is not None

    def next_eligible_at(self, session: Any) -> float:
        # Refresh from live per-request retry records. A zero result means
        # there is no scheduler-timed formal work currently waiting.
        self._select_context(session)
        return max(0.0, float(self._next_eligible_at or 0.0))

    def should_yield_static_dispatch(self, session: Any) -> bool:
        """Ask the scheduler to try one real competitor, with self fallback."""

        return int(getattr(session, "iteration", 0) or 0) == self._yield_iteration

    def frontier_context_hash(self, session: Any, work_item: Any = None) -> str:
        """Stable selected-lane identity for one frozen mathematical context."""

        return self._frontier_context_hash(
            session,
            work_item,
            mutate=True,
        )

    def frontier_context_hash_probe(
        self,
        session: Any,
        work_item: Any = None,
    ) -> str:
        """Read-only variant used while the scheduler merely quotes work."""

        return self._frontier_context_hash(
            session,
            work_item,
            mutate=False,
        )

    def _frontier_context_hash(
        self,
        session: Any,
        work_item: Any = None,
        *,
        mutate: bool,
    ) -> str:
        """Implement normal and observational context identity lookup."""

        key = ""
        if work_item is not None:
            node_id = str(
                getattr(work_item, "node_id", "")
                or (work_item.get("node_id") if isinstance(work_item, dict) else "")
                or ""
            )
            node = getattr(getattr(session, "proof_state", None), "nodes", {}).get(
                node_id
            )
            if node is not None:
                helpers = self._helper_blocks(
                    session,
                    refresh_quality=mutate,
                )
                key = self._context_key_for_node(
                    session, node_id=node_id, node=node, helpers=helpers
                )
        if not key:
            selected = self._select_context(session, mutate=mutate)
            key = str(selected[0] if selected is not None else "")
        if not key:
            return ""
        generation = int(
            dict(self._contexts.get(key) or {}).get("operation_generation", 0) or 0
        )
        return f"{key}:generation={generation}"

    def frontier_dispatch_rank(self, session: Any, work_item: Any) -> int:
        return self.frontier_dispatch_rank_probe(session, work_item)

    def frontier_dispatch_rank_probe(self, session: Any, work_item: Any) -> int:
        """Rotate live typed contexts while prioritizing acceptance receipts."""

        identity = self.frontier_context_hash_probe(session, work_item)
        key = identity.rsplit(":generation=", 1)[0] if identity else ""
        record = dict(self._contexts.get(key) or {})
        helpers = self._helper_blocks(session, refresh_quality=False)
        ordered_keys = [
            self._context_key_for_node(
                session,
                node_id=node_id,
                node=node,
                helpers=helpers,
            )
            for node_id, node, _is_root in self._candidate_nodes(
                session,
                respect_selected=False,
                mutate=False,
            )
        ]
        if key in ordered_keys and self._last_context_key in ordered_keys:
            size = len(ordered_keys)
            distance = (
                ordered_keys.index(key) - ordered_keys.index(self._last_context_key)
            ) % size
            if distance == 0:
                distance = size
        else:
            distance = (
                ordered_keys.index(key) if key in ordered_keys else len(ordered_keys)
            )
        pending_class = (
            0 if str(record.get("status") or "") == "acceptance_pending" else 1
        )
        return pending_class * (len(ordered_keys) + 1) + distance

    def _helper_blocks(
        self,
        session: Any,
        *,
        refresh_quality: bool = True,
    ) -> Tuple[str, ...]:
        dossier = session.dossier
        if refresh_quality:
            blocks = list(dossier.verified_helper_blocks())
        else:
            snapshot = getattr(dossier, "verified_helper_blocks_snapshot", None)
            blocks = list(snapshot() if callable(snapshot) else ())
        blocks.extend(
            str(item or "").strip()
            for item in list(getattr(dossier, "forced_context_helper_blocks", ()) or ())
            if str(item or "").strip()
        )
        return tuple(dict.fromkeys(blocks))

    def _candidate_nodes(
        self,
        session: Any,
        *,
        respect_selected: bool = True,
        mutate: bool = True,
    ) -> list[Tuple[str, Any, bool]]:
        state = session.proof_state
        nodes = getattr(state, "nodes", {}) or {}
        root_id = str(getattr(state, "root_node_id", "") or "")
        selected_getter = getattr(session, "selected_work_item_for", None)
        selected = (
            selected_getter(
                self.id,
                work_types=("formal_state_expand", "root_repair"),
            )
            if respect_selected and callable(selected_getter)
            else None
        )
        if selected is not None:
            selected_work_type = str(
                getattr(selected, "work_type", "")
                or dict(getattr(session, "selected_work_item_record", {}) or {}).get(
                    "work_type"
                )
                or ""
            )
            selected_node_id = str(
                getattr(selected, "node_id", "")
                or dict(getattr(session, "selected_work_item_record", {}) or {}).get(
                    "node_id"
                )
                or ""
            )
            selected_node = nodes.get(selected_node_id)
            selected_target_hash = str(
                getattr(selected, "target_hash", "")
                or dict(getattr(session, "selected_work_item_record", {}) or {}).get(
                    "target_hash"
                )
                or ""
            )
            current_target_hash = (
                text_hash(
                    canonicalize_lean_statement_for_identity(
                        str(getattr(selected_node, "target", "") or "")
                    )
                )
                if selected_node is not None
                else ""
            )
            stored_goal_hash = str(
                getattr(
                    getattr(selected_node, "goal", None),
                    "normalized_statement_hash",
                    "",
                )
                or current_target_hash
            )
            if (
                selected_work_type == "root_repair"
                and selected_node is not None
                and selected_node_id == root_id
                and str(getattr(selected_node, "status", "")) == "open"
                and callable(getattr(session.prover_client, "chat", None))
                and (
                    not selected_target_hash
                    or selected_target_hash == current_target_hash == stored_goal_hash
                )
            ):
                return [(selected_node_id, selected_node, True)]
            if (
                selected_node is not None
                and str(getattr(selected_node, "kind", "")) == "child_goal"
                and str(getattr(selected_node, "status", "")) == "open"
                and int(getattr(selected_node, "tactic_attempts", 0) or 0) > 0
                and (
                    not selected_target_hash
                    or selected_target_hash == current_target_hash == stored_goal_hash
                )
            ):
                return [(selected_node_id, selected_node, False)]
            return []
        candidates: list[Tuple[str, Any, bool]] = []
        root = nodes.get(root_id)
        registered_action = getattr(session, "registered_action", None)
        root_closer = (
            registered_action("tactic_close") if callable(registered_action) else None
        )
        root_cheap_complete = False
        if root_closer is not None:
            try:
                context_probe = getattr(
                    root_closer,
                    "frontier_context_key_probe",
                    None,
                )
                if not mutate and not callable(context_probe):
                    context_key = ""
                elif not mutate:
                    context_key = context_probe(session)
                else:
                    context_key = root_closer._context_key(session)
                attempted = root_closer._attempted_context_keys_for(state)
                deferred_getter = getattr(
                    root_closer,
                    "_deferred_context_keys_for",
                    lambda _state: (),
                )
                deferred = deferred_getter(state)
                root_cheap_complete = bool(
                    context_key
                    and (context_key in attempted or context_key in deferred)
                )
            except Exception:
                root_cheap_complete = False
        if (
            root is not None
            and str(getattr(root, "status", "")) == "open"
            and root_cheap_complete
        ):
            candidates.append((root_id, root, True))
        children = [
            node
            for node in nodes.values()
            if str(getattr(node, "kind", "")) == "child_goal"
            and str(getattr(node, "status", "")) == "open"
            and int(getattr(node, "tactic_attempts", 0) or 0) > 0
        ]
        children.sort(
            key=lambda node: (
                -float(getattr(node, "priority", 0.0) or 0.0),
                str(getattr(node, "node_id", "") or ""),
            )
        )
        candidates.extend((str(node.node_id), node, False) for node in children)
        return candidates

    @staticmethod
    def _target_invalidated(session: Any, target: str) -> bool:
        checker = getattr(session.dossier, "invalidated_statement_reason", None)
        if not callable(checker):
            return False
        try:
            return bool(checker(str(target or "")))
        except Exception:
            return True

    @staticmethod
    def _increment_metric(session: Any, key: str, amount: int = 1) -> None:
        increment = getattr(session.dossier, "increment_tool_metric", None)
        if callable(increment):
            increment(str(key), int(amount))

    def _publish_operation_metrics(
        self,
        session: Any,
        record: Dict[str, Any],
        *,
        stats: Dict[str, Any],
        generation: int,
        candidate_found: bool = False,
    ) -> Dict[str, Any]:
        """Publish cumulative live-search stats exactly once per generation."""

        out = dict(record or {})
        published = {
            str(key): max(0, int(value or 0))
            for key, value in dict(out.get("published_stats") or {}).items()
        }
        for metric_key, stat_name in (
            ("mini_formal_state_search_nodes_created", "nodes_created"),
            ("mini_formal_state_search_nodes_expanded", "nodes_expanded"),
            ("mini_formal_state_search_lean_checks", "lean_checks"),
            ("mini_formal_state_search_backtracks", "backtracks"),
            ("mini_formal_state_search_value_estimates", "value_estimates"),
            ("mini_formal_state_search_diversity_pruned", "diversity_pruned"),
            ("mini_formal_state_search_operation_timeouts", "operation_timeouts"),
            (
                "mini_formal_state_search_infrastructure_failures",
                "infrastructure_failures",
            ),
            (
                "mini_formal_state_search_completion_rejections",
                "completion_rejections",
            ),
        ):
            current = max(0, int(stats.get(stat_name, 0) or 0))
            prior = max(0, int(published.get(stat_name, 0) or 0))
            self._increment_metric(session, metric_key, max(0, current - prior))
            published[stat_name] = max(prior, current)
        if int(out.get("published_invocation_generation", 0) or 0) < generation:
            self._increment_metric(session, "mini_formal_state_search_invocations")
            out["published_invocation_generation"] = generation
        if (
            candidate_found
            and int(out.get("published_candidate_generation", 0) or 0) < generation
        ):
            self._increment_metric(
                session,
                "mini_formal_state_search_candidates_found",
            )
            out["published_candidate_generation"] = generation
        out["published_stats"] = published
        return out

    @staticmethod
    def _quantum_metric_metadata(
        stats: Dict[str, Any],
        *,
        candidate_found: bool,
        bottlenecks: list[Dict[str, Any]],
    ) -> Dict[str, int]:
        """Return per-quantum counters safe to aggregate across session scopes."""

        return {
            "formal_invocations": 1,
            "formal_nodes_created": max(0, int(stats.get("nodes_created", 0) or 0)),
            "formal_nodes_expanded": max(0, int(stats.get("nodes_expanded", 0) or 0)),
            "formal_lean_checks": max(0, int(stats.get("lean_checks", 0) or 0)),
            "formal_backtracks": max(0, int(stats.get("backtracks", 0) or 0)),
            "formal_value_estimates": max(0, int(stats.get("value_estimates", 0) or 0)),
            "formal_diversity_pruned": max(
                0, int(stats.get("diversity_pruned", 0) or 0)
            ),
            "formal_bottleneck_count": len(bottlenecks),
            "formal_root_unlocking_bottleneck_count": sum(
                1 for item in bottlenecks if item.get("root_unlocking_candidate")
            ),
            "formal_operation_timeouts": max(
                0, int(stats.get("operation_timeouts", 0) or 0)
            ),
            "formal_infrastructure_failures": max(
                0, int(stats.get("infrastructure_failures", 0) or 0)
            ),
            "formal_completion_rejections": max(
                0, int(stats.get("completion_rejections", 0) or 0)
            ),
            "formal_candidates_found": int(bool(candidate_found)),
        }

    def _publish_bottleneck_metrics(
        self,
        session: Any,
        node: Any,
        helpers: Tuple[str, ...],
        record: Dict[str, Any],
        raw_bottlenecks: Any,
    ) -> tuple[Dict[str, Any], list[Dict[str, Any]]]:
        from ensemble_prover.proof_state_executor import _formal_state_root_bottlenecks

        formal_bottlenecks = _formal_state_root_bottlenecks(
            session.proof_state,
            node,
            raw_bottlenecks,
            helpers,
        )
        out = dict(record or {})
        seen = set(out.get("bottleneck_keys") or ())
        current = {
            hashlib.sha256(
                json.dumps(
                    item, ensure_ascii=False, sort_keys=True, default=str
                ).encode("utf-8")
            ).hexdigest()
            for item in formal_bottlenecks
        }
        root_unlocking = {
            hashlib.sha256(
                json.dumps(
                    item, ensure_ascii=False, sort_keys=True, default=str
                ).encode("utf-8")
            ).hexdigest()
            for item in formal_bottlenecks
            if item.get("root_unlocking_candidate")
        }
        self._increment_metric(
            session,
            "mini_formal_state_search_bottlenecks",
            len(current - seen),
        )
        self._increment_metric(
            session,
            "mini_formal_state_search_root_unlocking_bottlenecks",
            len(root_unlocking - seen),
        )
        out["bottleneck_keys"] = sorted(seen | current)
        return out, formal_bottlenecks

    @staticmethod
    def _formal_progress_snapshot(
        continuation: FormalStateSearchCheckpoint | None,
    ) -> Dict[str, int]:
        """Return monotone, kernel-facing progress facts for one context.

        Arbitrary new tactic text and tree-node ids are intentionally absent.
        A receipt improves only by reaching a novel exact Lean goal state, a
        strictly smaller residual goal set, better goal-derived structural
        progress, or a strictly later normalized diagnostic phase.
        """

        if continuation is None:
            return {}
        tree = TacticTree.from_execution_record(continuation.beam_state.tree_record)
        executable = [
            node
            for node in tree.nodes.values()
            if node.depth > 0
            and node.status
            in {
                TacticNodeStatus.OPEN,
                TacticNodeStatus.EXPANDED,
                TacticNodeStatus.SOLVED,
            }
        ]
        goal_counts = [len(node.goals) for node in executable]
        progress_milli = [
            int(round(max(0.0, float(node.features.progress_ratio or 0.0)) * 1000))
            for node in executable
        ]
        unique_state_count = len(
            {tree.goal_state_key(node.goals) for node in executable if node.goals}
        )
        diagnostic_phases = {
            "parse_error": 0,
            "unknown_identifier": 1,
            "unknown_universe": 1,
            "type_mismatch": 2,
            "missing_instance": 2,
            "binder_mismatch": 2,
            "binder_arity_mismatch": 2,
            "unification_failed": 2,
            "tactic_failed": 3,
            "simp_no_progress": 3,
            "termination_failed": 3,
            "proposition_falsified": 3,
            "unsolved_goals": 4,
        }
        best_diagnostic_phase = -1
        best_diagnostic_goal_count = -1
        for cached in tree._cache.values():  # noqa: SLF001 - continuation audit
            parsed = cached.parse_result
            kind = str(canonical_error_type(parsed) or "")
            phase = diagnostic_phases.get(kind)
            if phase is None:
                continue
            residual_count = len(list(getattr(parsed, "remaining_goals", ()) or ()))
            if phase > best_diagnostic_phase:
                best_diagnostic_phase = phase
                best_diagnostic_goal_count = residual_count if residual_count else -1
            elif (
                phase == best_diagnostic_phase == diagnostic_phases["unsolved_goals"]
                and residual_count > 0
                and (
                    best_diagnostic_goal_count < 0
                    or residual_count < best_diagnostic_goal_count
                )
            ):
                best_diagnostic_goal_count = residual_count
        return {
            "max_depth": max((node.depth for node in executable), default=0),
            "unique_state_count": unique_state_count,
            "min_goal_count": min(goal_counts, default=-1),
            "best_progress_milli": max(progress_milli, default=0),
            "best_score_milli": int(
                round(max(0.0, float(continuation.beam_state.best_score or 0.0)) * 1000)
            ),
            "best_diagnostic_phase": best_diagnostic_phase,
            "best_diagnostic_goal_count": best_diagnostic_goal_count,
        }

    @staticmethod
    def _formal_residual_snapshot(
        continuation: FormalStateSearchCheckpoint | None,
    ) -> str:
        """Return the best exact Lean diagnostic/residual retained by a beam."""

        if continuation is None:
            return ""
        tree = TacticTree.from_execution_record(continuation.beam_state.tree_record)
        diagnostic_phases = {
            "parse_error": 0,
            "unknown_identifier": 1,
            "unknown_universe": 1,
            "type_mismatch": 2,
            "missing_instance": 2,
            "binder_mismatch": 2,
            "binder_arity_mismatch": 2,
            "unification_failed": 2,
            "tactic_failed": 3,
            "simp_no_progress": 3,
            "termination_failed": 3,
            "proposition_falsified": 3,
            "unsolved_goals": 4,
        }
        candidates = []
        for cached in tree._cache.values():  # noqa: SLF001 - continuation audit
            parsed = cached.parse_result
            residuals = list(getattr(parsed, "remaining_goals", ()) or ())
            raw = str(getattr(parsed, "raw", "") or "").strip()
            if raw:
                exact_output = raw
            elif residuals:
                goal_blocks = []
                for goal in residuals:
                    hypotheses = [
                        str(item or "").strip()
                        for item in list(getattr(goal, "hypotheses", ()) or ())
                        if str(item or "").strip()
                    ]
                    target = str(getattr(goal, "target", "") or "").strip()
                    goal_blocks.append(
                        "\n".join([*hypotheses, f"⊢ {target}" if target else "⊢ ?"])
                    )
                exact_output = "remaining goals:\n" + "\n\n".join(goal_blocks)
            else:
                diagnostics = [
                    str(getattr(item, "message", "") or "").strip()
                    for item in list(getattr(parsed, "diagnostics", ()) or ())
                    if str(getattr(item, "message", "") or "").strip()
                ]
                exact_output = "\n\n".join(diagnostics)
            if not exact_output:
                continue
            phase = diagnostic_phases.get(str(canonical_error_type(parsed) or ""), -1)
            residual_rank = -len(residuals) if residuals else -10_000
            candidates.append((phase, residual_rank, exact_output))
        if not candidates:
            return ""
        return max(candidates, key=lambda item: (item[0], item[1], item[2]))[2]

    def _record_formal_proof_idea_observation(
        self,
        session: Any,
        *,
        context_key: str,
        continuation: FormalStateSearchCheckpoint | None,
        exit_reason: str,
        progress_reasons: Tuple[str, ...],
    ) -> None:
        try:
            lineage = ProofLineageEnvelope.from_metadata(
                getattr(session, "selected_work_item_record", {}) or {}
            )
        except (TypeError, ValueError):
            return
        idea_id = lineage.proof_idea_id
        dossier = getattr(session, "dossier", None)
        ideas = dict(getattr(dossier, "proof_ideas", {}) or {})
        recorder = getattr(dossier, "record_proof_idea_observation", None)
        if not idea_id or idea_id not in ideas or not callable(recorder):
            return
        exact_output = self._formal_residual_snapshot(continuation)
        summary_parts = [f"formal context {context_key}"]
        clean_exit = str(exit_reason or "").strip()
        if clean_exit:
            summary_parts.append(f"exit={clean_exit}")
        if progress_reasons:
            summary_parts.append("progress=" + ", ".join(progress_reasons))
        summary = "; ".join(summary_parts)
        recorder(
            idea_id,
            ProofIdeaObservation(
                observation_id=stable_identity(
                    "proof-idea-formal-state",
                    idea_id,
                    context_key,
                    exact_output,
                    summary,
                ),
                kind="formal_state",
                summary=summary,
                claim_id=lineage.claim_id,
                route_id=lineage.route_id,
                lean_residual_id=(
                    stable_identity(
                        "proof-idea-formal-residual",
                        context_key,
                        exact_output,
                    )
                    if exact_output
                    else ""
                ),
                exact_lean_output=exact_output,
                evidence_hash=text_hash(exact_output or summary),
                branch_id=(
                    ideas[idea_id].branch_provenance[0].branch_id
                    if ideas[idea_id].branch_provenance
                    else ""
                ),
                turn_index=int(getattr(session, "iteration", 0) or 0),
            ),
        )

    @staticmethod
    def _formal_progress_improved(
        prior: Dict[str, Any], current: Dict[str, int]
    ) -> tuple[bool, tuple[str, ...]]:
        if not current:
            return False, ()
        reasons: list[str] = []
        # Prefix depth alone is not mathematical progress: Lean accepts
        # no-ops such as ``skip``. Depth remains cumulative telemetry, but only
        # exact state novelty or goal/feature/diagnostic improvement resets
        # the stall counter.
        if int(current.get("unique_state_count", 0)) > int(
            prior.get("unique_state_count", 0)
        ):
            reasons.append("lean_goal_state_novelty_increased")
        prior_goals = int(prior.get("min_goal_count", -1))
        current_goals = int(current.get("min_goal_count", -1))
        if current_goals >= 0 and (prior_goals < 0 or current_goals < prior_goals):
            reasons.append("residual_goal_count_decreased")
        if int(current.get("best_progress_milli", 0)) > int(
            prior.get("best_progress_milli", 0)
        ):
            reasons.append("structural_progress_increased")
        prior_phase = int(prior.get("best_diagnostic_phase", -1))
        current_phase = int(current.get("best_diagnostic_phase", -1))
        if current_phase > prior_phase:
            reasons.append("lean_diagnostic_phase_advanced")
        elif current_phase == prior_phase == 4:
            prior_diag_goals = int(prior.get("best_diagnostic_goal_count", -1))
            current_diag_goals = int(current.get("best_diagnostic_goal_count", -1))
            if current_diag_goals >= 0 and (
                prior_diag_goals < 0 or current_diag_goals < prior_diag_goals
            ):
                reasons.append("diagnostic_goal_count_decreased")
        return bool(reasons), tuple(reasons)

    @staticmethod
    def _join_formal_progress(
        prior: Dict[str, Any], current: Dict[str, int]
    ) -> Dict[str, int]:
        """Componentwise monotone join of best live progress facts."""

        if not prior:
            return dict(current)
        if not current:
            return {str(key): int(value) for key, value in prior.items()}

        def valid_min(name: str) -> int:
            values = [
                int(source.get(name, -1))
                for source in (prior, current)
                if int(source.get(name, -1)) >= 0
            ]
            return min(values, default=-1)

        prior_phase = int(prior.get("best_diagnostic_phase", -1))
        current_phase = int(current.get("best_diagnostic_phase", -1))
        best_phase = max(prior_phase, current_phase)
        if current_phase > prior_phase:
            best_diag_goals = int(current.get("best_diagnostic_goal_count", -1))
        elif prior_phase > current_phase:
            best_diag_goals = int(prior.get("best_diagnostic_goal_count", -1))
        else:
            best_diag_goals = valid_min("best_diagnostic_goal_count")
        return {
            "max_depth": max(
                int(prior.get("max_depth", 0)),
                int(current.get("max_depth", 0)),
            ),
            "unique_state_count": max(
                int(prior.get("unique_state_count", 0)),
                int(current.get("unique_state_count", 0)),
            ),
            "min_goal_count": valid_min("min_goal_count"),
            "best_progress_milli": max(
                int(prior.get("best_progress_milli", 0)),
                int(current.get("best_progress_milli", 0)),
            ),
            "best_score_milli": max(
                int(prior.get("best_score_milli", 0)),
                int(current.get("best_score_milli", 0)),
            ),
            "best_diagnostic_phase": best_phase,
            "best_diagnostic_goal_count": best_diag_goals,
        }

    @staticmethod
    def _formal_progress_resets_stall(reasons: Tuple[str, ...]) -> bool:
        """Whether progress strictly advances rank rather than only novelty.

        Novel exact states receive the configured bounded exploration window,
        but cannot replenish that window forever. A smaller goal set, improved
        goal-derived structure, or a later diagnostic phase starts a new one.
        """

        return any(reason != "lean_goal_state_novelty_increased" for reason in reasons)

    @staticmethod
    def _provider_retry_delay(
        continuation: FormalStateSearchCheckpoint | None,
        *,
        now: float | None = None,
        policy_identity: str = "",
        beam_width: int = 1,
    ) -> float:
        if continuation is None:
            return 0.0
        retry_records = dict(continuation.policy_retry_records)
        if policy_identity:
            tree = TacticTree.from_execution_record(continuation.beam_state.tree_record)
            owner_ids = list(continuation.beam_state.beam_node_ids)
            if not owner_ids:
                owner_ids = list(continuation.beam_state.recovery_node_ids)
            if not owner_ids:
                owner_ids = list(continuation.beam_state.reserve_node_ids)
            owner_ids = owner_ids[: max(1, int(beam_width or 1))]
            owner_keys: list[str] = []
            for node_id in owner_ids:
                node = tree.nodes.get(str(node_id or ""))
                if node is None or node.status != TacticNodeStatus.OPEN:
                    continue
                payload = {
                    "state": tree.goal_state_key(node.goals),
                    "prefix": [str(item or "") for item in node.tactics_from_root],
                    "policy_identity": str(policy_identity),
                }
                owner_keys.append(
                    hashlib.sha256(
                        json.dumps(
                            payload,
                            sort_keys=True,
                            ensure_ascii=False,
                        ).encode("utf-8")
                    ).hexdigest()
                )
            # Any scheduled owner without a backoff record is executable now.
            if not owner_keys or any(key not in retry_records for key in owner_keys):
                return 0.0
            retry_records = {key: retry_records[key] for key in owner_keys}
        ready_times = [
            max(0.0, float(item.get("next_retry_at", 0.0) or 0.0))
            for item in retry_records.values()
            if not bool(item.get("exhausted", False))
        ]
        current = time.time() if now is None else float(now)
        if not ready_times or any(item <= current for item in ready_times):
            return 0.0
        return max(0.0, min(ready_times) - current)

    @staticmethod
    def _node_integration_hash(node: Any) -> str:
        goal = getattr(node, "goal", None)
        payload = {
            "local_context": [
                str(item or "")
                for item in list(getattr(node, "local_context", ()) or ())
            ],
            "local_argument_terms": sorted(
                (str(name or ""), str(term or ""))
                for name, term in dict(
                    getattr(node, "local_argument_terms", {}) or {}
                ).items()
            ),
            "local_hypotheses": [
                (str(item.get("name") or ""), str(item.get("type") or ""))
                for item in list(getattr(goal, "local_hypotheses", ()) or ())
                if isinstance(item, dict)
            ],
        }
        return hashlib.sha256(
            json.dumps(payload, ensure_ascii=False, sort_keys=True).encode("utf-8")
        ).hexdigest()

    def _context_identity(
        self,
        session: Any,
        *,
        node_id: str,
        target: str,
        helpers: Tuple[str, ...],
        retrieval_hints: Tuple[str, ...],
        local_context: Tuple[str, ...],
        local_argument_terms: Tuple[Tuple[str, str], ...],
        local_hypotheses: Tuple[Tuple[str, str], ...],
    ) -> str:
        _context, cognition_digest = self._formal_policy_cognition_context(
            session,
            project=False,
        )
        legacy_proof_idea_id = ""
        legacy_statement_identity = ""
        if not cognition_digest:
            try:
                selected_lineage = ProofLineageEnvelope.from_metadata(
                    getattr(session, "selected_work_item_record", {}) or {}
                )
            except (TypeError, ValueError):
                selected_lineage = ProofLineageEnvelope()
            legacy_proof_idea_id = selected_lineage.proof_idea_id
            legacy_statement_identity = selected_lineage.statement_identity
        payload = {
            "node_id": node_id,
            "target": target,
            "target_hash": text_hash(target),
            "preamble": session.acceptance_preamble(),
            "helpers": list(helpers),
            "retrieval_hints": list(retrieval_hints),
            # Formal-state continuations are otherwise siloed from
            # the mathematical strategy that owns them. These descriptive
            # coordinates prevent a different idea from inheriting a terminal
            # context while preserving all existing Lean-state inputs.
            "proof_idea_context_digest": cognition_digest,
            # Compatibility for pre-packet continuations/test doubles. New
            # graph-selected work always uses the complete cognition digest.
            "proof_idea_id": legacy_proof_idea_id,
            "statement_identity": legacy_statement_identity,
            # Terminal/live action records are keyed by the same executable
            # provider policy as the nested retry ledger. Swapping a model or
            # a request-shaping policy must create a fresh schedulable context
            # rather than leaving the new route hidden behind an old terminal.
            "formal_policy_identity": _formal_policy_identity(
                getattr(session, "prover_client", None),
                self.config,
            ),
            # ``target`` is the executable closed statement, but these fields
            # are still part of the proof-DAG integration contract.  A local
            # argument remapping must invalidate an in-flight helper even when
            # the normalized proposition itself is unchanged.
            "local_context": list(local_context),
            "local_argument_terms": list(local_argument_terms),
            "local_hypotheses": list(local_hypotheses),
        }
        return hashlib.sha256(
            json.dumps(payload, ensure_ascii=False, sort_keys=True).encode("utf-8")
        ).hexdigest()

    @staticmethod
    def _selected_work_requires_cognition(record: Any) -> bool:
        return selected_work_has_explicit_cognition(record)

    def _formal_policy_cognition_context(
        self,
        session: Any,
        *,
        project: bool,
    ) -> Tuple[str, str]:
        dossier = getattr(session, "dossier", None)
        selected_work = getattr(session, "selected_work_item_record", None)
        resolver = getattr(dossier, "resolve_proof_idea_context", None)
        if not callable(resolver):
            return "", ""
        if project:
            for method_name in (
                "reconcile_proof_attempt_lineage",
                "reconcile_proof_idea_graph_statuses",
            ):
                reconcile = getattr(dossier, method_name, None)
                if callable(reconcile):
                    reconcile()
        resolution = resolver(selected_work, policy="exact_selected")
        digest = str(getattr(resolution, "context_digest", "") or "")
        if str(getattr(resolution, "status", "") or "") != "resolved":
            if self._selected_work_requires_cognition(selected_work):
                if project:
                    raise FormalSelectedProofIdeaContextError(
                        "formal-state selected cognition did not resolve exactly: "
                        f"{getattr(resolution, 'status', 'unbound')}/"
                        f"{getattr(resolution, 'reason', '')}"
                    )
                return "", digest
            return "", ""
        if not project:
            return "", digest
        projector = getattr(dossier, "project_proof_idea_context", None)
        if not callable(projector):
            raise TypeError("resolved formal cognition lacks dossier projector")
        projection = projector(resolution, audience="formal_policy")
        return str(projection.render()), digest

    @staticmethod
    def _retrieval_hints_for_node(session: Any, node: Any) -> Tuple[str, ...]:
        """Join target-local and session premise retrieval without aliases.

        ``ProofStateRetrievalAction`` attaches declaration names to a specific
        node, while ``PremiseRetrievalAction`` publishes target-wide names on
        the session.  Formal search previously consumed only the former, so a
        successful mathematical retrieval prepass was invisible to the tactic
        policy.  Keep both channels explicit and make the joined set part of
        the formal context identity.
        """

        return tuple(
            dict.fromkeys(
                str(item or "").strip()
                for source in (
                    list(getattr(node, "retrieved_decl_names", ()) or ()),
                    list(getattr(session, "last_premise_names", ()) or ()),
                    list(
                        getattr(
                            getattr(session, "conv", None),
                            "known_premise_names",
                            (),
                        )
                        or ()
                    ),
                )
                for item in source
                if str(item or "").strip()
            )
        )

    def _context_key_for_node(
        self,
        session: Any,
        *,
        node_id: str,
        node: Any,
        helpers: Tuple[str, ...],
    ) -> str:
        return self._context_identity(
            session,
            node_id=node_id,
            target=str(getattr(node, "target", "") or ""),
            helpers=helpers,
            retrieval_hints=self._retrieval_hints_for_node(session, node),
            local_context=tuple(
                str(item or "")
                for item in list(getattr(node, "local_context", ()) or ())
            ),
            local_argument_terms=tuple(
                sorted(
                    (str(name or ""), str(term or ""))
                    for name, term in dict(
                        getattr(node, "local_argument_terms", {}) or {}
                    ).items()
                )
            ),
            local_hypotheses=tuple(
                (str(item.get("name") or ""), str(item.get("type") or ""))
                for item in list(
                    getattr(getattr(node, "goal", None), "local_hypotheses", ()) or ()
                )
                if isinstance(item, dict)
            ),
        )

    def _select_context(
        self,
        session: Any,
        *,
        mutate: bool = True,
    ) -> Optional[Tuple[str, str, Any, bool, Tuple[str, ...]]]:
        if mutate:
            self._next_eligible_at = 0.0
        helpers = self._helper_blocks(session, refresh_quality=mutate)
        pending_root_context = self._pending_root_context
        if not pending_root_context:
            # Re-derive the scheduler index from the authoritative current
            # root identity. This also handles multiple historical root
            # candidates without guessing which stale generation should win.
            state = getattr(session, "proof_state", None)
            root_id = str(getattr(state, "root_node_id", "") or "")
            root_node = dict(getattr(state, "nodes", {}) or {}).get(root_id)
            if root_node is not None:
                root_key = self._context_key_for_node(
                    session,
                    node_id=root_id,
                    node=root_node,
                    helpers=helpers,
                )
                root_record = dict(self._contexts.get(root_key) or {})
                if str(
                    root_record.get("status") or ""
                ) == "acceptance_pending" and bool(root_record.get("is_root")):
                    pending_root_context = root_key
                    if mutate:
                        self._pending_root_context = root_key
        if pending_root_context:
            state = getattr(session, "proof_state", None)
            root_id = str(getattr(state, "root_node_id", "") or "")
            root_node = dict(getattr(state, "nodes", {}) or {}).get(root_id)
            pending_record = dict(self._contexts.get(pending_root_context) or {})
            current_target = str(getattr(root_node, "target", "") or "")
            current_context_key = (
                self._context_key_for_node(
                    session,
                    node_id=root_id,
                    node=root_node,
                    helpers=helpers,
                )
                if root_node is not None
                else ""
            )
            continuation_record = pending_record.get("checkpoint")
            continuation_statement = ""
            if continuation_record:
                try:
                    continuation = (
                        FormalStateSearchCheckpoint.from_record_repairing_frontier(
                            dict(continuation_record),
                            beam_width=self.config.beam_width,
                        )
                    )
                    continuation_statement = str(
                        continuation.beam_state.tree_record.get("statement") or ""
                    )
                except (TypeError, ValueError):
                    continuation_statement = ""
            pending_valid = bool(
                root_node is not None
                and str(pending_record.get("status") or "") == "acceptance_pending"
                and bool(pending_record.get("is_root"))
                and str(getattr(root_node, "status", "") or "") == "open"
                and current_context_key == pending_root_context
                and str(pending_record.get("target_hash") or "")
                == text_hash(current_target)
                and str(pending_record.get("integration_hash") or "")
                == self._node_integration_hash(root_node)
                and continuation_statement == current_target
                and not self._target_invalidated(session, current_target)
            )
            if pending_valid:
                return (
                    pending_root_context,
                    root_id,
                    root_node,
                    True,
                    helpers,
                )
            if mutate:
                self._contexts[pending_root_context] = {
                    **pending_record,
                    "status": "terminal",
                    "reason": "acceptance_context_invalidated",
                    "checkpoint": None,
                }
                self._pending_root_context = ""
                self._increment_metric(
                    session,
                    "mini_formal_state_search_acceptance_context_invalidations",
                )
            pending_root_context = ""
        eligible: list[Tuple[str, str, Any, bool, Tuple[str, ...]]] = []
        # A pending accepted root is stronger than ordinary frontier routing.
        # A Lean-solved root must preempt a selected child expansion;
        # otherwise retryable child work can starve root finalization forever.
        candidate_nodes = self._candidate_nodes(
            session,
            respect_selected=not bool(pending_root_context),
            mutate=mutate,
        )
        for node_id, node, is_root in candidate_nodes:
            target = str(getattr(node, "target", "") or "").strip()
            if not target or self._target_invalidated(session, target):
                continue
            key = self._context_identity(
                session,
                node_id=node_id,
                target=target,
                helpers=helpers,
                retrieval_hints=self._retrieval_hints_for_node(session, node),
                local_context=tuple(
                    str(item or "")
                    for item in list(getattr(node, "local_context", ()) or ())
                ),
                local_argument_terms=tuple(
                    sorted(
                        (str(name or ""), str(term or ""))
                        for name, term in dict(
                            getattr(node, "local_argument_terms", {}) or {}
                        ).items()
                    )
                ),
                local_hypotheses=tuple(
                    (str(item.get("name") or ""), str(item.get("type") or ""))
                    for item in list(
                        getattr(getattr(node, "goal", None), "local_hypotheses", ())
                        or ()
                    )
                    if isinstance(item, dict)
                ),
            )
            record = self._contexts.get(key)
            if (
                record is not None
                and str(record.get("status") or "") == "live"
                and record.get("checkpoint")
            ):
                try:
                    context_continuation = (
                        FormalStateSearchCheckpoint.from_record_repairing_frontier(
                            dict(record["checkpoint"]),
                            beam_width=self.config.beam_width,
                        )
                    )
                    retry_delay = self._provider_retry_delay(
                        context_continuation,
                        policy_identity=_formal_policy_identity(
                            getattr(session, "prover_client", None),
                            self.config,
                        ),
                        beam_width=self.config.beam_width,
                    )
                except (TypeError, ValueError):
                    retry_delay = 0.0
                if retry_delay > 0.0:
                    ready_at = time.time() + retry_delay
                    if mutate:
                        self._next_eligible_at = (
                            min(self._next_eligible_at, ready_at)
                            if self._next_eligible_at > 0.0
                            else ready_at
                        )
                    continue
            if record is None or str(record.get("status") or "") in {
                "live",
                "acceptance_pending",
            }:
                eligible.append((key, node_id, node, is_root, helpers))
        if not eligible:
            return None
        if pending_root_context:
            for item in eligible:
                if item[0] == pending_root_context:
                    return item
        keys = [item[0] for item in eligible]
        if self._last_context_key in keys:
            index = (keys.index(self._last_context_key) + 1) % len(eligible)
            return eligible[index]
        return eligible[0]

    async def run(self, session: Any) -> MiniOutcome:
        started = time.monotonic()
        dispatch_id = str(
            getattr(session, "_inflight_action_dispatch_id", "") or ""
        ).strip()
        selected = self._select_context(session)
        if selected is None:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=0.0,
                metadata={"verdict": "no_live_formal_context"},
            )
        key, node_id, node, is_root, helpers = selected
        proof_idea_context, proof_idea_context_digest = (
            self._formal_policy_cognition_context(session, project=True)
        )
        refreshed_key = self._context_key_for_node(
            session,
            node_id=node_id,
            node=node,
            helpers=helpers,
        )
        if refreshed_key != key:
            key = refreshed_key
        self._last_context_key = key
        self._yield_iteration = int(getattr(session, "iteration", 0) or 0) + 1
        target = str(getattr(node, "target", "") or "")
        target_hash = text_hash(target)
        integration_hash = self._node_integration_hash(node)
        record = dict(self._contexts.get(key) or {})
        if str(record.get("status") or "") == "acceptance_pending":
            if bool(record.get("is_root")):
                self._pending_root_context = key
                return self._root_candidate_outcome(
                    session,
                    key=key,
                    target=target,
                    helpers=helpers,
                    record=record,
                    started=started,
                )
            return await self._accept_child_candidate(
                session,
                key=key,
                node_id=node_id,
                node=node,
                record=record,
                started=started,
            )
        continuation = (
            FormalStateSearchCheckpoint.from_record_repairing_frontier(
                dict(record["checkpoint"]),
                beam_width=self.config.beam_width,
            )
            if record.get("checkpoint")
            else None
        )
        generation = max(0, int(record.get("operation_generation", 0) or 0)) + 1
        intent_record = {
            **record,
            "status": "live",
            "node_id": node_id,
            "target_hash": target_hash,
            "integration_hash": integration_hash,
            "checkpoint": (
                continuation.to_record() if continuation is not None else None
            ),
            "operation_generation": generation,
            "operation_status": "live_quantum_started",
        }
        self._contexts[key] = self._publish_operation_metrics(
            session,
            intent_record,
            stats=(
                dict(continuation.beam_state.stats) if continuation is not None else {}
            ),
            generation=generation,
        )

        async def record_live_progress(
            event: str,
            live_continuation: FormalStateSearchCheckpoint,
            payload: Dict[str, Any],
        ) -> None:
            require_current_action_dispatch(session, dispatch_id)
            current = getattr(session.proof_state, "nodes", {}).get(node_id)
            if (
                current is None
                or str(getattr(current, "status", "")) != "open"
                or text_hash(str(getattr(current, "target", "") or "")) != target_hash
                or self._node_integration_hash(current) != integration_hash
            ):
                raise RuntimeError("formal target changed before live progress update")
            progress_record: Dict[str, Any] = {
                **dict(self._contexts.get(key) or {}),
                "status": "live",
                "node_id": node_id,
                "target_hash": target_hash,
                "integration_hash": integration_hash,
                "checkpoint": live_continuation.to_record(),
                "context_hash": live_continuation.context_hash,
                "is_root": bool(is_root),
                "operation_generation": generation,
                "operation_status": f"progress:{event}",
                "operation_event": str(event),
                "operation_payload": dict(payload or {}),
            }
            if event == "candidate_solved" and str(payload.get("proof") or ""):
                progress_record.update(
                    {
                        "status": "acceptance_pending",
                        "proof": str(payload.get("proof") or ""),
                        "tactics": [
                            str(item) for item in list(payload.get("tactics") or ())
                        ],
                    }
                )
            progress_tree = TacticTree.from_execution_record(
                live_continuation.beam_state.tree_record
            )
            progress_record = self._publish_operation_metrics(
                session,
                progress_record,
                stats=dict(live_continuation.beam_state.stats),
                generation=generation,
                candidate_found=event == "candidate_solved",
            )
            progress_record, _ = self._publish_bottleneck_metrics(
                session,
                node,
                helpers,
                progress_record,
                tactic_tree_bottlenecks(progress_tree),
            )
            self._contexts[key] = progress_record
            if event == "candidate_solved" and is_root:
                self._pending_root_context = key

        run = await run_goal_conditioned_formal_search(
            client=session.prover_client,
            lean=session.lean,
            statement=target,
            initial_goals=[LeanGoalState(index=0, hypotheses=[], target=target)],
            preamble=session.acceptance_preamble(),
            helpers=helpers,
            retrieval_hints=self._retrieval_hints_for_node(session, node),
            proof_idea_context=proof_idea_context,
            proof_idea_context_digest=proof_idea_context_digest,
            config=self.config,
            checkpoint=continuation,
            cost_controller=getattr(session, "cost_controller", None),
            role=str(
                getattr(getattr(session, "conv", None), "role", "prove") or "prove"
            ),
            suppress_solution_placeholders=bool(
                getattr(
                    getattr(session, "conv", None),
                    "suppress_solution_placeholders",
                    True,
                )
            ),
            opaque_mode=bool(
                getattr(getattr(session, "conv", None), "opaque_mode", True)
            ),
            allow_official_answer_visibility=bool(
                getattr(
                    getattr(session, "conv", None),
                    "allow_official_answer_visibility",
                    False,
                )
            ),
            official_answer_payload_present=getattr(
                getattr(session, "conv", None),
                "official_answer_payload_present",
                None,
            ),
            progress_callback=record_live_progress,
        )
        require_current_action_dispatch(session, dispatch_id)
        quantum_stats = {
            "nodes_created": run.result.nodes_created,
            "nodes_expanded": run.result.nodes_expanded,
            "lean_checks": run.result.lean_checks,
            "backtracks": run.result.backtracks,
            "value_estimates": run.result.value_estimates,
            "diversity_pruned": run.result.diversity_pruned,
            "operation_timeouts": run.result.operation_timeouts,
            "infrastructure_failures": run.result.infrastructure_failures,
            "completion_rejections": run.result.completion_rejections,
        }
        record = self._publish_operation_metrics(
            session,
            dict(self._contexts.get(key) or record),
            stats=quantum_stats,
            generation=generation,
            candidate_found=bool(run.result.solved),
        )
        record, formal_bottlenecks = self._publish_bottleneck_metrics(
            session,
            node,
            helpers,
            record,
            run.result.bottlenecks,
        )
        quantum_metric_metadata = self._quantum_metric_metadata(
            quantum_stats,
            candidate_found=bool(run.result.solved),
            bottlenecks=formal_bottlenecks,
        )
        self._contexts[key] = record
        current_node = getattr(session.proof_state, "nodes", {}).get(node_id)
        if (
            current_node is None
            or str(getattr(current_node, "status", "")) != "open"
            or text_hash(str(getattr(current_node, "target", "") or "")) != target_hash
            or self._node_integration_hash(current_node) != integration_hash
            or self._target_invalidated(session, target)
        ):
            self._contexts[key] = {
                "status": "terminal",
                "reason": "target_changed_during_quantum",
                "node_id": node_id,
                "target_hash": target_hash,
            }
            if self._pending_root_context == key:
                # ``candidate_solved`` publishes the root acceptance owner.
                # A later target CAS failure invalidates that candidate and
                # must retire the owner in the same live transition.
                self._pending_root_context = ""
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "formal_target_cas_failed",
                    **quantum_metric_metadata,
                },
            )

        if run.result.solved and run.result.proof and run.result.tactics:
            self._record_formal_proof_idea_observation(
                session,
                context_key=key,
                continuation=run.checkpoint,
                exit_reason="solved_candidate",
                progress_reasons=("formal_candidate_solved",),
            )
            solved_record = {
                **record,
                "status": "acceptance_pending",
                "node_id": node_id,
                "target_hash": target_hash,
                "integration_hash": integration_hash,
                "proof": str(run.result.proof),
                "tactics": list(run.result.tactics),
                "checkpoint": (
                    FormalStateSearchCheckpoint(
                        context_hash=run.context_hash,
                        beam_state=run.result.resume_state,
                        value_model_record=dict(run.value_model_record),
                    ).to_record()
                    if run.result.resume_state is not None
                    else None
                ),
                "context_hash": run.context_hash,
                "value_model": dict(run.value_model_record),
                "is_root": bool(is_root),
                "operation_generation": generation,
                "quantum_metric_metadata": quantum_metric_metadata,
            }
            self._contexts[key] = solved_record
            if is_root:
                self._pending_root_context = key
            if is_root:
                return self._root_candidate_outcome(
                    session,
                    key=key,
                    target=target,
                    helpers=helpers,
                    record=solved_record,
                    started=started,
                    nodes_expanded=run.result.nodes_expanded,
                )
            return await self._accept_child_candidate(
                session,
                key=key,
                node_id=node_id,
                node=node,
                record=solved_record,
                started=started,
            )

        live = bool(
            run.checkpoint is not None and run.checkpoint.beam_state.has_live_work()
        )
        prior_progress = dict(record.get("formal_progress") or {})
        current_progress = self._formal_progress_snapshot(run.checkpoint)
        best_progress = self._join_formal_progress(
            prior_progress,
            current_progress,
        )
        progress_improved, progress_reasons = self._formal_progress_improved(
            prior_progress,
            best_progress,
        )
        self._record_formal_proof_idea_observation(
            session,
            context_key=key,
            continuation=run.checkpoint,
            exit_reason=str(run.result.exit_reason or ""),
            progress_reasons=progress_reasons,
        )
        rank_improved = self._formal_progress_resets_stall(progress_reasons)
        provider_retry_pending = bool(
            run.checkpoint is not None
            and any(
                not bool(item.get("exhausted", False))
                for item in run.checkpoint.policy_retry_records.values()
            )
        )
        prior_no_improvement = max(0, int(record.get("no_improvement_quanta", 0) or 0))
        no_improvement_quanta = (
            0
            if rank_improved
            else prior_no_improvement + 1
            if live
            else prior_no_improvement
        )
        configured_no_improvement_limit = max(
            0, int(self.config.max_no_improvement_quanta or 0)
        )
        no_improvement_limit = configured_no_improvement_limit
        stalled = bool(
            live
            and no_improvement_limit > 0
            and no_improvement_quanta >= no_improvement_limit
        )
        if stalled:
            live = False
        # MP-FU-008 zero-yield governor: a lane may keep earning bounded
        # exploration through novelty while never producing a single complete
        # candidate. Rank improvement (fewer/harder residual goals, later
        # diagnostic phase) resets this counter; novelty alone does not.
        # HONEST SEMANTICS (2026-07-30 self-audit): a solved candidate exits
        # through the acceptance path ABOVE and never reaches this block, so
        # every quantum accounted here is definitionally zero-candidate — the
        # governor is therefore a TIGHTER stall window (default 2) that
        # preempts the six-quantum window for any lane whose last quanta were
        # novelty-only, exactly MP-FU-008's "switch instead of paying all six
        # quanta". The candidate term below is defensive future-proofing for
        # a flow where solved quanta ever fall through.
        quantum_candidate_found = bool(run.result.solved)
        prior_zero_yield = max(0, int(record.get("zero_yield_quanta", 0) or 0))
        zero_yield_quanta = (
            0
            if (quantum_candidate_found or rank_improved)
            else prior_zero_yield + 1
            if live or stalled
            else prior_zero_yield
        )
        zero_yield_limit = max(
            0, int(getattr(self.config, "max_zero_yield_quanta", 0) or 0)
        )
        zero_yield_stalled = bool(
            live and zero_yield_limit > 0 and zero_yield_quanta >= zero_yield_limit
        )
        if zero_yield_stalled:
            live = False
            increment = getattr(session.dossier, "increment_tool_metric", None)
            if callable(increment):
                increment("mini_formal_state_search_zero_yield_stalls", 1)
            # Durable failed-route memory (goal-scoped, capped, replayed in
            # the workbench): siblings and restarts see that this exact
            # search regime yielded zero candidates.
            record_scratch = getattr(session.dossier, "record_scratch", None)
            if callable(record_scratch):
                try:
                    record_scratch(
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        tool_call_index=0,
                        ok=False,
                        summary=(
                            "formal_search_zero_yield: "
                            f"{zero_yield_quanta} quanta with zero complete "
                            f"candidates (context={key})"
                        ),
                        code=f"formal_search_zero_yield:{key}",
                        goal_statement=str(
                            getattr(node, "statement", "")
                            or getattr(node, "target", "")
                            or ""
                        ),
                        source_label="formal_search",
                    )
                except Exception:
                    pass
        # A live context owns a bounded continuation. This
        # grants enough scheduler headroom to reach the configured stall
        # decision even near the outer iteration guard; terminalization still
        # prevents semantic/cost reopening at the limit.
        semantic_advance = bool(live)
        outcome_metadata = {
            "verdict": (
                "formal_context_stalled_zero_yield"
                if zero_yield_stalled
                else "formal_context_stalled_no_progress"
                if stalled
                else "formal_quantum_committed"
                if live
                else "formal_context_terminal"
            ),
            "formal_context": key,
            "formal_exit_reason": str(run.result.exit_reason or ""),
            "formal_bottlenecks": list(formal_bottlenecks),
            "semantic_budget_step_consumed": semantic_advance,
            "formal_progress_improved": progress_improved,
            "formal_progress_reasons": list(progress_reasons),
            "formal_rank_improved": rank_improved,
            "formal_no_improvement_quanta": int(no_improvement_quanta),
            "formal_no_improvement_limit": no_improvement_limit,
            "formal_zero_yield_quanta": int(zero_yield_quanta),
            "formal_zero_yield_limit": zero_yield_limit,
            "formal_context_zero_yield_stalled": zero_yield_stalled,
            "formal_provider_retry_pending": provider_retry_pending,
            "formal_context_stalled": bool(stalled or zero_yield_stalled),
            "scheduler_neutral": True,
            "preserve_frontier_work": bool(live),
            "consume_selected_frontier_action": bool(live),
            "formal_quantum_generation": generation,
            **quantum_metric_metadata,
        }
        outcome_cost_seconds = time.monotonic() - started
        self._contexts[key] = {
            **record,
            "status": "live" if live else "terminal",
            "reason": (
                "stalled_zero_candidate_yield"
                if zero_yield_stalled
                else "stalled_no_formal_or_diagnostic_progress"
                if stalled
                else str(run.result.exit_reason or "")
            ),
            "node_id": node_id,
            "target_hash": target_hash,
            "integration_hash": integration_hash,
            "checkpoint": run.checkpoint.to_record()
            if live and run.checkpoint
            else None,
            "context_hash": run.context_hash,
            "is_root": bool(is_root),
            "operation_generation": generation,
            "formal_progress": best_progress or prior_progress,
            "formal_progress_reasons": list(progress_reasons),
            "formal_rank_improved": rank_improved,
            "no_improvement_quanta": int(no_improvement_quanta),
            "no_improvement_limit": no_improvement_limit,
            "configured_no_improvement_limit": configured_no_improvement_limit,
            "zero_yield_quanta": int(zero_yield_quanta),
            "zero_yield_limit": zero_yield_limit,
            "provider_retry_pending": provider_retry_pending,
            "operation_status": "live_quantum_complete",
        }
        session.proof_state.record_transition(
            node_id=node_id,
            source=self.id,
            error_type="formal_state_bottleneck",
            action="resume_formal_state_search" if live else "formal_context_exhausted",
            blocker=(
                "stalled_no_formal_or_diagnostic_progress"
                if stalled
                else str(run.result.exit_reason or "unsolved")
            ),
            phase=self.id,
            turn_index=int(getattr(session, "iteration", 0) or 0),
            payload={
                "context_hash": run.context_hash,
                "bottlenecks": list(formal_bottlenecks),
                "backtracks": int(run.result.backtracks),
            },
        )
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=False,
            cost_seconds=outcome_cost_seconds,
            metadata=outcome_metadata,
        )

    def _root_candidate_outcome(
        self,
        session: Any,
        *,
        key: str,
        target: str,
        helpers: Tuple[str, ...],
        record: Dict[str, Any],
        started: float,
        nodes_expanded: int = 0,
    ) -> MiniOutcome:
        proof = str(record.get("proof") or "")
        helper_names = tuple(
            name for block in helpers for name in [helper_decl_name(block)] if name
        )
        candidate = RootFinalizationCandidate(
            proof=proof,
            replay_helpers=helpers,
            helper_names=helper_names,
            phase="formal_state_search",
            turn_index=int(getattr(session, "iteration", 0) or 0),
            source_action_id=self.id,
            target_statement=target,
            verification_certificate=root_verification_certificate(
                accepted=True,
                proof=proof,
                phase="formal_state_search",
                turn_index=int(getattr(session, "iteration", 0) or 0),
                target_statement=target,
                replay_helpers=helpers,
                helper_names=helper_names,
                source=self.id,
            ),
        )
        return MiniOutcome(
            action_id=self.id,
            solved=True,
            proof=proof,
            progress=False,
            cost_seconds=time.monotonic() - started,
            root_candidate=candidate,
            metadata={
                "formal_context": key,
                "formal_candidate_proof_hash": text_hash(proof),
                "formal_nodes_expanded": int(nodes_expanded or 0),
                "preserve_frontier_work": True,
                "formal_acceptance_preemption": True,
                **dict(record.get("quantum_metric_metadata") or {}),
            },
        )

    async def _accept_child_candidate(
        self,
        session: Any,
        *,
        key: str,
        node_id: str,
        node: Any,
        record: Dict[str, Any],
        started: float,
    ) -> MiniOutcome:
        from ensemble_prover.proof_state_executor import (
            _accept_proof_state_helper,
            _proof_state_helper_block,
        )

        proof = str(record.get("proof") or "")
        dispatch_id = str(
            getattr(session, "_inflight_action_dispatch_id", "") or ""
        ).strip()
        helper_name = (
            f"formal_{hashlib.sha256((key + proof).encode('utf-8')).hexdigest()[:16]}"
        )
        helper_block = _proof_state_helper_block(helper_name, str(node.target), proof)
        status: Dict[str, Any] = {}
        already_accepted = helper_name in {
            name
            for block in tuple(session.dossier.verified_helper_blocks())
            for name in [helper_decl_name(block)]
            if name
        }
        acceptance_dossier = session.dossier
        acceptance_proof_state = session.proof_state
        accepted = already_accepted or await _accept_proof_state_helper(
            lean=session.lean,
            conv=session.conv,
            dossier=acceptance_dossier,
            helper_block=helper_block,
            phase=self.id,
            turn_index=int(getattr(session, "iteration", 0) or 0),
            timeout_s=(
                float(self.config.operation_timeout_s)
                if float(self.config.operation_timeout_s or 0.0) > 0.0
                else float("inf")
            ),
            proof_cache=getattr(session, "proof_cache", None),
            proof_state=acceptance_proof_state,
            status_out=status,
            target_statement=str(node.target),
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
        if accepted:
            solved_context = {
                **record,
                "status": "solved",
                "helper_name": helper_name,
                "checkpoint": None,
            }
            acceptance_dossier.increment_tool_metric("mini_formal_state_search_solved")
            acceptance_proof_state.record_tactic_result(
                node_id=node_id,
                ok=True,
                attempt_count=1,
                exit_reason="solved_by_formal_state_search",
                helper_name=helper_name,
            )
            sync_proof_state_to_graph(
                acceptance_proof_state,
                acceptance_dossier,
                session=session,
                phase=self.id,
                turn_index=int(getattr(session, "iteration", 0) or 0),
                refresh_target_node_ids=(node_id,),
            )
            self._contexts[key] = solved_context
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(helper_name,),
                progress=True,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "formal_search_helper_accepted",
                    "formal_context": key,
                    **dict(record.get("quantum_metric_metadata") or {}),
                },
            )

        error_kind = str(status.get("error_kind") or "").lower()
        retryable = (
            str(status.get("status") or "")
            in {
                "retryable_error",
                "cancelled",
            }
            or "elapsed_budget_exhausted" in error_kind
            or "timeout" in error_kind
            or (error_kind == "deadline_mutation_commit_failed")
        )
        if retryable:
            self._contexts[key] = {**record, "status": "acceptance_pending"}
            live_after_veto = False
        else:
            continuation_record = record.get("checkpoint")
            if continuation_record:
                prior_continuation = (
                    FormalStateSearchCheckpoint.from_record_repairing_frontier(
                        dict(continuation_record),
                        beam_width=self.config.beam_width,
                    )
                )
                state = prior_continuation.beam_state.rejecting_solution(
                    tuple(str(item) for item in record.get("tactics") or ())
                )
                live_after_veto = state.has_live_work()
                self._contexts[key] = {
                    **record,
                    "status": "live" if live_after_veto else "terminal",
                    "checkpoint": (
                        FormalStateSearchCheckpoint(
                            context_hash=prior_continuation.context_hash,
                            beam_state=state,
                            value_model_record=prior_continuation.value_model_record,
                            policy_retry_records=(
                                prior_continuation.policy_retry_records
                            ),
                        ).to_record()
                        if live_after_veto
                        else None
                    ),
                }
            else:
                live_after_veto = False
                self._contexts[key] = {**record, "status": "terminal"}
            self._increment_metric(
                session,
                "mini_formal_state_search_acceptance_vetoes",
            )
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=False,
            cost_seconds=time.monotonic() - started,
            metadata={
                "verdict": (
                    "formal_search_acceptance_retryable_error"
                    if retryable
                    else "formal_search_acceptance_vetoed"
                ),
                "formal_context": key,
                "semantic_budget_step_consumed": not retryable,
                "scheduler_neutral": True,
                # Acceptance is a separate live operation after the exact
                # Lean-state search result. A transient acceptance failure
                # must retry that same typed node/target generation rather
                # than consuming it and falling back to an unscoped action.
                "preserve_frontier_work": retryable or live_after_veto,
                "consume_selected_frontier_action": (not retryable and live_after_veto),
                **dict(record.get("quantum_metric_metadata") or {}),
            },
        )

    def on_outcome_applied(self, session: Any, outcome: MiniOutcome) -> None:
        outcome_metadata = dict(outcome.metadata or {})
        key = self._pending_root_context
        if not key:
            return
        record = dict(self._contexts.get(key) or {})
        if (
            str(outcome.action_id or "") != self.id
            or str(outcome_metadata.get("formal_context") or "") != key
            or str(outcome_metadata.get("formal_candidate_proof_hash") or "")
            != text_hash(str(record.get("proof") or ""))
        ):
            # A pending root candidate may coexist with other typed contexts.
            # Only the exact candidate replay may reconcile its acceptance.
            return
        if bool(getattr(session, "root_finalized", False)):
            self._increment_metric(session, "mini_formal_state_search_solved")
            self._contexts[key] = {**record, "status": "solved", "checkpoint": None}
        else:
            finalization_verdict = str(
                outcome_metadata.get("root_finalization_verdict") or ""
            ).strip()
            lowered_verdict = finalization_verdict.lower()
            retryable_finalization = bool(
                outcome.exception is not None
                or "exception" in lowered_verdict
                or "elapsed_budget_exhausted" in lowered_verdict
                or "timeout" in lowered_verdict
                or "cancel" in lowered_verdict
                or "deadline_mutation_commit_failed" in lowered_verdict
            )
            if retryable_finalization:
                self._increment_metric(
                    session,
                    "mini_formal_state_search_acceptance_retryable_errors",
                )
                self._contexts[key] = {
                    **record,
                    "status": "acceptance_pending",
                    "last_acceptance_retryable_verdict": finalization_verdict,
                }
                # Keep the pending root candidate as the scheduler owner. A
                # retryable finalization must preempt child expansion until it
                # either commits, is semantically vetoed, or is invalidated.
                self._pending_root_context = key
                return
            self._increment_metric(
                session,
                "mini_formal_state_search_acceptance_vetoes",
            )
            continuation_record = record.get("checkpoint")
            if continuation_record:
                prior_continuation = (
                    FormalStateSearchCheckpoint.from_record_repairing_frontier(
                        dict(continuation_record),
                        beam_width=self.config.beam_width,
                    )
                )
                state = prior_continuation.beam_state.rejecting_solution(
                    tuple(str(item) for item in record.get("tactics") or ())
                )
                live_after_veto = state.has_live_work()
                self._contexts[key] = {
                    **record,
                    "status": "live" if live_after_veto else "terminal",
                    "checkpoint": (
                        FormalStateSearchCheckpoint(
                            context_hash=prior_continuation.context_hash,
                            beam_state=state,
                            value_model_record=prior_continuation.value_model_record,
                            policy_retry_records=(
                                prior_continuation.policy_retry_records
                            ),
                        ).to_record()
                        if live_after_veto
                        else None
                    ),
                }
            else:
                self._contexts[key] = {**record, "status": "terminal"}
        self._pending_root_context = ""


__all__ = ["FormalStateSearchAction"]
