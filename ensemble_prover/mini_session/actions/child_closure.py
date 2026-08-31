"""ChildClosureAction — wraps `_try_proof_state_child_closures`.

Runs the deterministic child-closure swarm: walks `proof_state` open child
goals, applies tactics + retrieved declarations, runs assembly fixpoint,
returns ok if root certifies. Consults internal frontiers
(``child_frontier``, ``assembly_frontier``).
"""

from __future__ import annotations

import time
from typing import Any, ClassVar, FrozenSet, Optional

from ensemble_prover.lean_artifact_sanitize import sanitize_lean_artifact_text
from ensemble_prover.mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ensemble_prover.root_finalization import RootFinalizationCandidate

from ..action import MiniOutcome
from ..graph_sync import sync_proof_state_to_graph


class ChildClosureAction:
    id: str = "child_closure"
    priority: int = 65
    cost_estimate_s: float = 60.0
    # Each invocation consumes one durable proof-work identity (one decl,
    # tactic portfolio, acceptance continuation, or residual receipt). New
    # Lean/helper contexts may legitimately reveal more identities later, so
    # aggregate session invocation counts must remain telemetry rather than a
    # lifetime completeness cap.
    BUDGET_SCOPE: ClassVar[str] = "proof_work"
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})
    CHILD_WORK_TYPES: ClassVar[FrozenSet[str]] = frozenset(
        {
            "decl_probe",
            "tactic_swarm",
            "residual_goal_extraction",
            "helper_acceptance",
        }
    )
    FALSIFICATION_PREFLIGHT_RESERVE_S: ClassVar[float] = 15.0
    TYPED_RESIDUAL_RECEIPT_TIMEOUT_FLOOR_S: ClassVar[float] = 300.0
    DEADLINE_ADMISSION_SLACK_S: ClassVar[float] = 1.0
    # One operation, one retry of the same exact timeout context, then one
    # dispatch that can advance to the next frontier identity.
    MINIMUM_SESSION_QUANTA: ClassVar[int] = 3
    # Preserve scheduler interleaving without paying a full session action for
    # every member of a deterministic tactic portfolio. The continuation
    # cursor remains exact, so timeout/defer paths still resume at the first
    # unattempted candidate and no solving candidate is discarded.
    ROOT_TACTIC_PORTFOLIO_MAX_SCHEDULER_QUANTA: ClassVar[int] = 4
    SCHEDULER_BUDGET_SCHEMA_VERSION: ClassVar[int] = 2

    def __init__(
        self,
        *,
        timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        max_candidates: int = 32,
        max_nodes: int = 3,
        max_decl_applications: int = 6,
        batch_parallelism: int = 1,
        formal_search_config: Optional[Any] = None,
    ) -> None:
        self.timeout_s = float(timeout_s or 0.0)
        self.max_candidates = int(max_candidates or 0)
        self.max_nodes = int(max_nodes or 0)
        self.max_decl_applications = int(max_decl_applications or 0)
        self.batch_parallelism = int(batch_parallelism or 1)
        self.formal_search_config = formal_search_config
        # Every selected proving quantum includes the bounded falsification
        # preflight followed by one fully funded Lean operation. Keep explicit
        # slack so the strict enclosing deadline cannot turn an exact grant
        # into a deferred operation while the action is being admitted.
        self.cost_estimate_s = max(
            60.0,
            self.required_dispatch_budget_s("tactic_swarm"),
        )


    def _typed_residual_receipt_budget_s(self, session: Any = None) -> float:
        configured_lean_timeout_s = 0.0
        if session is not None:
            try:
                configured_lean_timeout_s = max(
                    float(
                        getattr(
                            getattr(getattr(session, "lean", None), "cfg", None),
                            "timeout_s",
                            0.0,
                        )
                        or 0.0
                    ),
                    float(
                        getattr(
                            getattr(session, "lean", None),
                            "timeout_s",
                            0.0,
                        )
                        or 0.0
                    ),
                )
            except (TypeError, ValueError):
                configured_lean_timeout_s = 0.0
        operation_timeout_s = max(
            self.TYPED_RESIDUAL_RECEIPT_TIMEOUT_FLOOR_S,
            configured_lean_timeout_s,
        )
        operation_count = 1
        if session is not None:
            proof_state = getattr(session, "proof_state", None)
            try:
                from ensemble_prover.proof_state_executor import (
                    _needs_answer_safe_feedback_check,
                )

                answer_safe_recheck = _needs_answer_safe_feedback_check(
                    getattr(session, "conv", None)
                )
            except Exception:
                # Failing closed here means reserving the possible recheck;
                # it cannot shorten or kill productive work.
                answer_safe_recheck = True
            nodes = getattr(proof_state, "nodes", {}) or {}
            for node_id in self._pending_typed_residual_node_ids(session):
                node = nodes.get(node_id)
                pending = dict(
                    getattr(node, "pending_residual_goal_extraction", {}) or {}
                )
                action_metadata = dict(pending.get("action_metadata") or {})
                if not bool(
                    action_metadata.get(
                        "typed_residual_closed_pending_acceptance"
                    )
                ):
                    continue
                # Normal helper acceptance performs a primary kernel check
                # and, in opaque/answer-safe mode, an independent safe-preamble
                # check. Preserve one further full quantum as well: root work
                # consumes it immediately for exact certification, while a
                # non-root helper must leave enough cumulative budget for the
                # assembly/tactic dispatch that uses the newly proved child.
                required = 2 + int(answer_safe_recheck)
                operation_count = max(operation_count, required)
            if self._pending_helper_acceptance_node_ids(session):
                # These are paid helper candidates awaiting the same primary
                # and optional answer-safe checks. Preserve a subsequent
                # quantum for the assembly/tactic lane that consumes them.
                operation_count = max(
                    operation_count,
                    2 + int(answer_safe_recheck),
                )
        return (
            float(operation_count) * operation_timeout_s
            + self.DEADLINE_ADMISSION_SLACK_S
        )

    def required_dispatch_budget_s(
        self,
        work_type: str = "",
        *,
        session: Any = None,
    ) -> float:
        normalized_work_type = str(work_type or "").strip()
        reserve = (
            max(0.0, float(self.timeout_s))
            + self.FALSIFICATION_PREFLIGHT_RESERVE_S
        )
        if reserve > 0.0:
            reserve += self.DEADLINE_ADMISSION_SLACK_S
        pending_receipt_selected = normalized_work_type == "residual_goal_extraction"
        if (
            not normalized_work_type
            and session is not None
            and self._pending_typed_residual_node_ids(session)
        ):
            # Static/no-applicable recovery has no saved frontier item. Quote
            # the verifier-only operation that actually makes the action
            # applicable, rather than the smaller tactic default.
            pending_receipt_selected = True
        pending_helper_selected = False
        if session is not None:
            pending_helper_ids = set(
                self._pending_helper_acceptance_node_ids(session)
            )
            selected_record = dict(
                getattr(session, "selected_work_item_record", {}) or {}
            )
            selected_node_id = str(
                selected_record.get("node_id") or ""
            ).strip()
            pending_helper_selected = bool(
                pending_helper_ids
                and (
                    not normalized_work_type
                    or selected_node_id in pending_helper_ids
                )
            )
        if pending_receipt_selected or pending_helper_selected:
            reserve = max(
                reserve,
                self._typed_residual_receipt_budget_s(session),
            )
        return reserve

    def minimum_session_budget_s(self) -> float:
        """Fund a bounded retry and a subsequent frontier advance."""

        largest_quantum = max(
            self.required_dispatch_budget_s("decl_probe"),
            self.required_dispatch_budget_s("tactic_swarm"),
        )
        ordinary_minimum = float(self.MINIMUM_SESSION_QUANTA) * largest_quantum
        # A root-shaped zero-goal receipt may require primary helper checking,
        # an independent answer-safe check, and root-exact certification. Keep
        # even finite/custom sessions capable of performing that one durable
        # handoff without depending on optional no-applicable recovery.
        closed_root_minimum = (
            3.0
            * max(
                self.TYPED_RESIDUAL_RECEIPT_TIMEOUT_FLOOR_S,
                max(0.0, float(self.timeout_s or 0.0)),
            )
            + self.DEADLINE_ADMISSION_SLACK_S
        )
        return max(ordinary_minimum, closed_root_minimum)

    def minimum_invocation_budget(self) -> int:
        """Return initial loop sizing; semantic work extends it as needed."""

        return self.MINIMUM_SESSION_QUANTA

    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0 or self.max_nodes <= 0:
            return False
        if session.dossier is None or session.proof_state is None or session.lean is None:
            return False
        remaining_budget_s = self._remaining_action_budget_s(session)
        selected_work_type = ""
        selected = None
        selected_getter = getattr(session, "selected_work_item_for", None)
        selected_bound_to_action = bool(
            str(
                getattr(session, "selected_work_item_action_id", "") or ""
            )
            == self.id
            and getattr(session, "selected_work_item", None) is not None
        )
        if callable(selected_getter):
            selected = selected_getter(
                self.id,
                work_types=(
                    "decl_probe",
                    "tactic_swarm",
                    "residual_goal_extraction",
                    "helper_acceptance",
                ),
            )
            if selected_bound_to_action and selected is None:
                # A bound-but-foreign selection is an authorization failure,
                # not the absence of selected work.  Falling through to the
                # global closeable-work probe previously let a procedural
                # formalization obligation launch unrestricted root assembly.
                return False
            if selected is not None:
                selected_work_type = str(
                    getattr(selected, "work_type", "") or ""
                ).strip()
                exhausted = getattr(
                    session,
                    "proof_work_semantic_attempt_exhausted",
                    None,
                )
                if callable(exhausted) and bool(
                    exhausted(selected, action_id=self.id, touch=False)
                ):
                    return False
        required_budget_s = self.required_dispatch_budget_s(
            selected_work_type,
            session=session,
        )
        if (
            self._pending_typed_residual_node_ids(session)
            and selected_work_type
            not in {"decl_probe", "tactic_swarm", "helper_acceptance"}
        ):
            # A specifically selected tactic/decl lane intentionally bypasses
            # verifier replay so the scheduler can rotate away from a deferred
            # receipt. Do not make that alternate pay the receipt quantum.
            required_budget_s = max(
                required_budget_s,
                self._typed_residual_receipt_budget_s(session),
            )
        if (
            remaining_budget_s is not None
            and remaining_budget_s < required_budget_s
        ):
            # The executor admits only fully funded Lean operations. Do not
            # repeatedly select a frontier lane that cannot fund even one
            # configured operation from its cumulative action budget.
            return False
        if callable(selected_getter):
            selected = selected_getter(
                self.id,
                work_types=(
                    "decl_probe",
                    "tactic_swarm",
                    "residual_goal_extraction",
                    "helper_acceptance",
                ),
            )
            if selected is not None:
                node_id = str(getattr(selected, "node_id", "") or "").strip()
                work_type = str(getattr(selected, "work_type", "") or "").strip()
                node = getattr(session.proof_state, "nodes", {}).get(node_id)
                if work_type == "residual_goal_extraction":
                    pending_status = getattr(
                        session.proof_state,
                        "pending_residual_goal_extraction_status",
                        None,
                    )
                    if node is None or not callable(pending_status):
                        return False
                    try:
                        pending_currentness = str(pending_status(node) or "")
                        current = pending_currentness in {
                            "pending",
                            "rematerialize",
                        }
                        record = dict(
                            getattr(
                                node,
                                "pending_residual_goal_extraction",
                                {},
                            )
                            or {}
                        )
                        retry_key = str(
                            record.get("verifier_retry_key") or ""
                        ).strip()
                        retry_status = getattr(
                            session.proof_state,
                            "verifier_retry_status",
                            None,
                        )
                        if (
                            pending_currentness != "rematerialize"
                            and retry_key
                            and callable(retry_status)
                        ):
                            current = current and str(
                                retry_status(node, retry_key) or ""
                            ) != "cooling"
                        return current
                    except Exception:
                        return False
                if work_type == "helper_acceptance":
                    if node is None or getattr(node, "status", "") != "open":
                        return False
                    record = dict(
                        getattr(node, "pending_helper_acceptance", {}) or {}
                    )
                    if not str(record.get("helper_block") or "").strip():
                        return False
                    retry_key = str(
                        record.get("verifier_retry_key") or ""
                    ).strip()
                    retry_status = getattr(
                        session.proof_state,
                        "verifier_retry_status",
                        None,
                    )
                    if retry_key and callable(retry_status):
                        try:
                            from ensemble_prover.proof_state_executor import (
                                _helper_acceptance_request_hashes,
                            )

                            _request_hash, _context_hash, current_retry_key = (
                                _helper_acceptance_request_hashes(
                                    conv=session.conv,
                                    dossier=session.dossier,
                                    node=node,
                                    helper_block=str(
                                        record.get("helper_block") or ""
                                    ),
                                    source=str(record.get("source") or ""),
                                    context_hash=str(
                                        record.get("caller_context_hash") or ""
                                    ),
                                )
                            )
                            if current_retry_key != retry_key:
                                return True
                            return str(
                                retry_status(node, retry_key) or ""
                            ) != "cooling"
                        except Exception:
                            return True
                    return True
                if (
                    node is None
                    or getattr(node, "kind", "") != "child_goal"
                    or getattr(node, "status", "") != "open"
                ):
                    return False
                if work_type == "decl_probe":
                    from ensemble_prover.proof_state import (
                        proof_state_decl_application_pending_names,
                    )
                    from ensemble_prover.proof_state_executor import (
                        proof_state_decl_application_context_hash,
                    )

                    context_hash = proof_state_decl_application_context_hash(
                        session.conv,
                        session.dossier,
                    )
                    pending_acceptance_source = str(
                        dict(
                            getattr(node, "pending_helper_acceptance", {}) or {}
                        ).get("source")
                        or ""
                    )
                    if (
                        not pending_acceptance_source.startswith(
                            "decl_application:"
                        )
                        and not proof_state_decl_application_pending_names(
                            node,
                            context_hash=context_hash,
                        )
                    ):
                        return False
                if work_type == "tactic_swarm" and self._tactic_context_is_terminal(
                    session,
                    node,
                ):
                    return False
                return True
        return self._has_closeable_work(session)

    def next_eligible_at(self, session: Any) -> float:
        """Earliest durable verifier cooldown owned by this action."""

        proof_state = getattr(session, "proof_state", None)
        nodes = getattr(proof_state, "nodes", {}) or {}
        getter = getattr(proof_state, "verifier_retry_next_eligible_at", None)
        if not callable(getter):
            return 0.0
        wake_times: list[float] = []
        for node in nodes.values():
            if str(getattr(node, "status", "") or "") != "open":
                continue
            residual = dict(
                getattr(node, "pending_residual_goal_extraction", {}) or {}
            )
            helper = dict(getattr(node, "pending_helper_acceptance", {}) or {})
            status_getter = getattr(
                proof_state,
                "pending_residual_goal_extraction_status",
                None,
            )
            if residual and callable(status_getter):
                try:
                    if str(status_getter(node) or "") not in {
                        "pending",
                        "rematerialize",
                    }:
                        residual = {}
                except Exception:
                    pass
            if helper:
                from ensemble_prover.proof_dossier import text_hash

                if (
                    not str(helper.get("helper_block") or "").strip()
                    or str(helper.get("target_hash") or "")
                    != text_hash(str(getattr(node, "target", "") or ""))
                ):
                    helper = {}
            for record in (residual, helper):
                retry_key = str(record.get("verifier_retry_key") or "").strip()
                if not retry_key:
                    continue
                try:
                    ready_at = float(getter(node, retry_key) or 0.0)
                except Exception:
                    continue
                if ready_at > time.time():
                    wake_times.append(ready_at)
        return min(wake_times, default=0.0)

    @staticmethod
    def _pending_typed_residual_node_ids(
        session: Any,
        *,
        include_cooling: bool = False,
    ) -> tuple[str, ...]:
        proof_state = getattr(session, "proof_state", None)
        nodes = getattr(proof_state, "nodes", {}) or {}
        status_getter = getattr(
            proof_state,
            "pending_residual_goal_extraction_status",
            None,
        )
        pending: list[str] = []
        for node_id, node in nodes.items():
            if not dict(
                getattr(node, "pending_residual_goal_extraction", {}) or {}
            ):
                continue
            if callable(status_getter):
                try:
                    if str(status_getter(node) or "") not in {
                        "pending",
                        "rematerialize",
                    }:
                        continue
                except Exception:
                    # A persisted verifier-only request must fail closed into
                    # the generous retry quantum when its status API fails.
                    pass
            record = dict(
                getattr(node, "pending_residual_goal_extraction", {}) or {}
            )
            retry_key = str(record.get("verifier_retry_key") or "").strip()
            retry_status = getattr(proof_state, "verifier_retry_status", None)
            if retry_key and callable(retry_status):
                try:
                    if (
                        not include_cooling
                        and str(retry_status(node, retry_key) or "") == "cooling"
                    ):
                        continue
                except Exception:
                    # Cooldown state is advisory scheduling data. If its probe
                    # fails, retain the verifier route rather than losing work.
                    pass
            pending.append(str(node_id))
        return tuple(pending)

    @staticmethod
    def _pending_helper_acceptance_node_ids(
        session: Any,
        *,
        include_cooling: bool = False,
    ) -> tuple[str, ...]:
        from ensemble_prover.proof_dossier import text_hash

        proof_state = getattr(session, "proof_state", None)
        nodes = getattr(proof_state, "nodes", {}) or {}
        pending: list[str] = []
        for node_id, node in nodes.items():
            record = dict(
                getattr(node, "pending_helper_acceptance", {}) or {}
            )
            if (
                not str(record.get("helper_block") or "").strip()
                or str(record.get("target_hash") or "")
                != text_hash(str(getattr(node, "target", "") or ""))
            ):
                continue
            retry_key = str(record.get("verifier_retry_key") or "").strip()
            retry_status = getattr(proof_state, "verifier_retry_status", None)
            if retry_key and callable(retry_status):
                try:
                    if (
                        not include_cooling
                        and str(retry_status(node, retry_key) or "") == "cooling"
                    ):
                        continue
                except Exception:
                    pass
            pending.append(str(node_id))
        return tuple(pending)

    def _remaining_action_budget_s(self, session: Any) -> Optional[float]:
        budgets = getattr(session, "budgets", {}) or {}
        budget = budgets.get(self.id) if isinstance(budgets, dict) else None
        if budget is None or str(
            getattr(budget, "scope", "session")
        ) not in {"session", "proof_work"}:
            return None
        maximum_s = float(getattr(budget, "max_total_seconds", 0.0) or 0.0)
        if maximum_s <= 0.0:
            return None
        consumed_s = max(
            0.0,
            float(getattr(budget, "total_seconds", 0.0) or 0.0),
        )
        return max(0.0, maximum_s - consumed_s)

    def _has_closeable_work(self, session: Any) -> bool:
        proof_state = getattr(session, "proof_state", None)
        dossier = getattr(session, "dossier", None)
        graph = getattr(dossier, "proof_graph", None)
        if self._has_root_exact_helper_work(session, dossier, proof_state):
            return True
        if self._has_root_tactic_helper_work(session, dossier, proof_state):
            return True
        if self._has_ready_assembly(proof_state, graph):
            return True
        return self._has_unconsumed_child_work(session, proof_state, graph)

    def _has_root_exact_helper_work(
        self,
        session: Any,
        dossier: Any,
        proof_state: Any,
    ) -> bool:
        try:
            from ensemble_prover.proof_state_executor import _root_equivalent_helper_names

            return bool(
                _root_equivalent_helper_names(
                    conv=getattr(session, "conv", None),
                    dossier=dossier,
                    proof_state=proof_state,
                )
            )
        except Exception:
            return False

    def _has_root_tactic_helper_work(
        self,
        session: Any,
        dossier: Any,
        proof_state: Any,
    ) -> bool:
        try:
            from ensemble_prover.proof_state_executor import (
                _has_untried_proof_state_root_tactic_context,
            )

            return bool(
                _has_untried_proof_state_root_tactic_context(
                    conv=getattr(session, "conv", None),
                    dossier=dossier,
                    proof_state=proof_state,
                    timeout_s=self.timeout_s,
                    max_candidates=self.max_candidates,
                    include_deferred=True,
                    touch=False,
                )
            )
        except Exception:
            return False

    def _has_ready_assembly(self, proof_state: Any, graph: Any) -> bool:
        getter = getattr(proof_state, "assembly_frontier", None)
        if not callable(getter):
            return False
        try:
            ready = getter(max_nodes=1, graph=graph)
        except TypeError:
            try:
                ready = getter()
            except Exception:
                return False
        except Exception:
            return False
        return bool(ready)

    def _has_unconsumed_child_work(
        self,
        session: Any,
        proof_state: Any,
        graph: Any,
    ) -> bool:
        getter = getattr(proof_state, "work_frontier", None)
        if not callable(getter):
            return False
        try:
            work_items = getter(
                max_items=max(8, int(self.max_nodes or 0) * 4),
                graph=graph,
            )
        except TypeError:
            try:
                work_items = getter()
            except Exception:
                return False
        except Exception:
            return False
        for item in list(work_items or ()):
            work_type = str(getattr(item, "work_type", "") or "").strip()
            if work_type not in self.CHILD_WORK_TYPES:
                continue
            if self._frontier_work_already_consumed(session, item):
                continue
            exhausted = getattr(
                session,
                "proof_work_semantic_attempt_exhausted",
                None,
            )
            if callable(exhausted) and bool(
                exhausted(item, action_id=self.id, touch=False)
            ):
                continue
            if (
                work_type == "tactic_swarm"
                and self._tactic_context_is_terminal(
                    session,
                    getattr(proof_state, "nodes", {}).get(
                        str(getattr(item, "node_id", "") or "").strip()
                    ),
                )
            ):
                continue
            if self._work_item_targets_open_child(proof_state, item, work_type):
                return True
        return False

    def _tactic_context_is_terminal(self, session: Any, node: Any) -> bool:
        """Observe the executor's exact child-tactic terminal identity.

        The proof-state frontier intentionally remains context-agnostic and can
        therefore advertise a graph-projected tactic item after its complete
        deterministic portfolio has already failed.  Reject that item before
        dispatch using the same semantic key as the executor.  Graph/route
        projection metadata is deliberately absent from this identity; a new
        target, helper set, Lean preamble, tactic budget, or answer-safety
        context produces a new key and reopens the full portfolio.
        """

        if node is None:
            return False
        terminal_keys = set(
            getattr(node, "tactic_terminal_context_keys", []) or []
        )
        if not terminal_keys:
            return False
        try:
            from ensemble_prover.proof_state_executor import (
                _proof_state_child_tactic_terminal_context_key,
            )

            current_key = _proof_state_child_tactic_terminal_context_key(
                conv=getattr(session, "conv", None),
                dossier=getattr(session, "dossier", None),
                proof_state=getattr(session, "proof_state", None),
                node=node,
                timeout_s=self.timeout_s,
                max_candidates=self.max_candidates,
            )
        except Exception:
            # The executor remains authoritative.  A failed observational
            # probe must not suppress potentially useful proof search.
            return False
        return bool(current_key and current_key in terminal_keys)

    @staticmethod
    def _frontier_work_already_consumed(session: Any, item: Any) -> bool:
        consumed = getattr(session, "consumed_frontier_work_keys", None)
        key_getter = getattr(session, "_frontier_work_key", None)
        if consumed is None or not callable(key_getter):
            return False
        try:
            return key_getter(item) in consumed
        except Exception:
            return False

    @staticmethod
    def _work_item_targets_open_child(
        proof_state: Any,
        item: Any,
        work_type: str,
    ) -> bool:
        node_id = str(getattr(item, "node_id", "") or "").strip()
        node = getattr(proof_state, "nodes", {}).get(node_id)
        if node is None:
            return False
        if getattr(node, "kind", "") != "child_goal":
            return False
        if getattr(node, "status", "") != "open":
            return False
        if work_type == "decl_probe":
            from ensemble_prover.proof_state import (
                proof_state_decl_application_pending_names,
            )

            pending_acceptance_source = str(
                dict(getattr(node, "pending_helper_acceptance", {}) or {}).get(
                    "source"
                )
                or ""
            )
            if (
                not pending_acceptance_source.startswith("decl_application:")
                and not proof_state_decl_application_pending_names(node)
            ):
                return False
        return True

    def _already_applied_root_candidate(
        self,
        session: Any,
        proof: Optional[str],
    ) -> Optional[RootFinalizationCandidate]:
        proof_text = str(proof or "").strip()
        if not proof_text:
            return None
        dossier = getattr(session, "dossier", None)
        if dossier is None:
            return None
        artifact_proof_text = sanitize_lean_artifact_text(proof_text)
        final_proof = str(getattr(dossier, "final_proof", "") or "").strip()
        if final_proof not in {proof_text, artifact_proof_text}:
            return None
        return RootFinalizationCandidate(
            proof=proof_text,
            phase="proof_state_child_closure",
            turn_index=int(getattr(session, "iteration", 0)),
            source_action_id=self.id,
            target_statement=str(
                getattr(dossier, "root_statement", "")
                or getattr(getattr(session, "conv", None), "goal_statement", "")
                or ""
            ),
            metadata={"root_finalization_already_applied": True},
        )

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.proof_state_executor import (
            _try_proof_state_child_closures,
            ensure_current_helper_acceptance_retries,
        )

        started = time.monotonic()
        selected_record = dict(
            getattr(session, "selected_work_item_record", {}) or {}
        )
        if (
            str(getattr(session, "selected_work_item_action_id", "") or "")
            == self.id
            and selected_record
            and str(selected_record.get("work_type") or "")
            not in self.CHILD_WORK_TYPES
        ):
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "selected_work_item": selected_record,
                    "selected_work_capability_rejected": True,
                    "preserve_frontier_work": True,
                    "verdict": "selected_work_action_incompatible",
                },
            )
        try:
            ensure_current_helper_acceptance_retries(
                conv=session.conv,
                dossier=session.dossier,
                proof_state=session.proof_state,
            )
        except Exception:
            # Execution still retains exact-currentness checks. Reconciliation
            # is best-effort here, but never runs from scheduler probing.
            pass
        pending_residual_node_ids_at_start = (
            self._pending_typed_residual_node_ids(
                session,
                include_cooling=True,
            )
        )
        pending_helper_node_ids_at_start = (
            self._pending_helper_acceptance_node_ids(
                session,
                include_cooling=True,
            )
        )
        remaining_budget_s = self._remaining_action_budget_s(session)
        action_deadline_monotonic = (
            started + remaining_budget_s
            if remaining_budget_s is not None and remaining_budget_s > 0.0
            else 0.0
        )
        selected_ids = ()
        selected_work_types = ()
        selected_ids_getter = getattr(session, "selected_work_item_node_ids", None)
        selected_types_getter = getattr(session, "selected_work_item_work_types", None)
        if callable(selected_ids_getter):
            selected_ids = selected_ids_getter(
                self.id,
                work_types=(
                    "decl_probe",
                    "tactic_swarm",
                    "residual_goal_extraction",
                    "helper_acceptance",
                ),
            )
        if callable(selected_types_getter):
            selected_work_types = selected_types_getter(
                self.id,
                work_types=(
                    "decl_probe",
                    "tactic_swarm",
                    "residual_goal_extraction",
                    "helper_acceptance",
                ),
            )
        # Split the complete deterministic portfolio into a small, bounded
        # number of scheduler quanta. The exact portfolio and next offset are
        # persisted on the root proof-state node, so neither interleaving nor
        # an operation deadline can remove later candidates. This amortizes
        # graph sync/selection/recovery overhead while still yielding between
        # substantial tactic batches for newly ready work.
        portfolio_bound = max(1, int(self.max_candidates or 1))
        max_scheduler_quanta = max(
            1,
            int(self.ROOT_TACTIC_PORTFOLIO_MAX_SCHEDULER_QUANTA),
        )
        candidate_attempt_limit = max(
            1,
            (portfolio_bound + max_scheduler_quanta - 1)
            // max_scheduler_quanta,
        )
        execution_status: dict[str, Any] = {}
        ok, proof, helpers = await _try_proof_state_child_closures(
            conv=session.conv,
            lean=session.lean,
            dossier=session.dossier,
            proof_state=session.proof_state,
            recorder=session.recorder,
            trace_prefix=session.trace_prefix,
            turn=int(getattr(session, "iteration", 0)),
            timeout_s=self.timeout_s,
            max_candidates=self.max_candidates,
            max_nodes=self.max_nodes,
            max_decl_applications=self.max_decl_applications,
            batch_parallelism=self.batch_parallelism,
            proof_cache=session.proof_cache,
            target_node_ids=selected_ids or None,
            target_work_types=selected_work_types or None,
            formal_search_config=self.formal_search_config,
            formal_search_client=getattr(session, "prover_client", None),
            cost_controller=getattr(session, "cost_controller", None),
            action_deadline_monotonic=action_deadline_monotonic,
            candidate_attempt_limit=candidate_attempt_limit,
            status_out=execution_status,
        )
        sync_proof_state_to_graph(
            session.proof_state,
            session.dossier,
            session=session,
            phase="child_closure",
            turn_index=int(getattr(session, "iteration", 0)),
            refresh_target_node_ids=selected_ids or None,
        )
        cost = time.monotonic() - started
        root_candidate = self._already_applied_root_candidate(session, proof if ok else None)
        metadata = {
            "target_node_ids": list(selected_ids),
            "target_work_types": list(selected_work_types),
            "selected_work_item": dict(
                getattr(session, "selected_work_item_record", {}) or {}
            ),
            "child_closure_execution_status": dict(execution_status),
            "child_closure_action_budget_remaining_s": (
                remaining_budget_s
                if remaining_budget_s is not None
                else 0.0
            ),
            "child_closure_action_deadline_enabled": bool(
                action_deadline_monotonic > 0.0
            ),
            "root_tactic_candidate_attempt_limit": candidate_attempt_limit,
            "root_tactic_portfolio_max_scheduler_quanta": max_scheduler_quanta,
        }
        pending_residual_node_ids = self._pending_typed_residual_node_ids(
            session,
            include_cooling=True,
        )
        pending_helper_node_ids = self._pending_helper_acceptance_node_ids(
            session,
            include_cooling=True,
        )
        if pending_residual_node_ids:
            metadata["pending_residual_goal_extraction_node_ids"] = list(
                pending_residual_node_ids
            )
        if pending_helper_node_ids:
            metadata["pending_helper_acceptance_node_ids"] = list(
                pending_helper_node_ids
            )
        root_node = getattr(session.proof_state, "nodes", {}).get(
            getattr(session.proof_state, "root_node_id", "")
        )
        root_tactic_continuation_pending = bool(
            execution_status.get("root_tactic_candidate_quantum_exhausted")
            and not execution_status.get(
                "root_tactic_candidate_quantum_timeout_preserved"
            )
            and dict(
                getattr(root_node, "root_tactic_portfolio_continuation", {}) or {}
            )
        )
        if root_tactic_continuation_pending:
            # This outcome settled exactly one candidate, not the proof-work
            # identity. Keep the scheduler and semantic budgets neutral until
            # the persisted exact portfolio reaches a terminal candidate,
            # while reserving one real scheduler iteration for its suffix.
            metadata["root_tactic_candidate_continuation_pending"] = True
            metadata["preserve_action_budget"] = True
            metadata["semantic_budget_step_consumed"] = True
            metadata["stagnation_neutral"] = True
            metadata["hard_pivot_neutral"] = True
        retryable_execution_defer = bool(
            execution_status.get("deadline_deferred")
            or execution_status.get("retryable_timeout")
            or execution_status.get("retryable_infrastructure")
        )
        if not ok and not helpers and retryable_execution_defer:
            metadata["preserve_frontier_work"] = True
            # This is a local Lean/executor deferral, not an LLM transport
            # failure.  ``defer_selected_frontier_action`` is consumed by the
            # session's model-call retry ledger and would permanently suppress
            # this exact child-closure action (there is no LLM retry
            # classification to release it).  Preserving the frontier work is
            # sufficient: normal budget/applicability admission decides when
            # the deterministic lane can run again.
            metadata["child_closure_retryable"] = True
        pending_verifier_work = bool(
            pending_residual_node_ids or pending_helper_node_ids
        )
        pending_verifier_work_at_start = bool(
            pending_residual_node_ids_at_start or pending_helper_node_ids_at_start
        )
        if not ok and pending_verifier_work and retryable_execution_defer:
            # A partial tactic/decl proof has already paid for generation;
            # only the authoritative typed residual receipt remains. Do not
            # charge either dispatch against the cumulative action budget:
            # doing so can leave <300s and make verifier-only replay
            # permanently inapplicable. The initial transition to a pending
            # receipt is iteration-neutral so one fully funded verifier replay
            # remains possible at the final iteration. A dispatch that began
            # pending must consume a normal iteration, however, so repeated
            # verifier failures cannot form a zero-cost loop.
            metadata["preserve_frontier_work"] = True
            metadata["preserve_action_budget"] = True
            metadata["pending_residual_goal_extraction_retry"] = True
            metadata["pending_residual_goal_extraction_started_with_pending"] = bool(
                pending_verifier_work_at_start
            )
            if pending_helper_node_ids:
                metadata["pending_helper_acceptance_retry"] = True
            if not pending_verifier_work_at_start:
                metadata["iteration_neutral"] = True
                metadata["scheduler_neutral"] = True
                metadata["stagnation_neutral"] = True
                metadata["hard_pivot_neutral"] = True
        if not ok and helpers and pending_verifier_work_at_start:
            # Accepting a durable child/root helper is a one-shot semantic
            # transition, but it may expose assembly/root-exact work only
            # after this action returns. Reserve that continuation even at the
            # nominal final iteration. The pending frame is already cleared,
            # so this cannot repeat on the same verifier identity.
            metadata["verified_helper_continuation"] = True
            metadata["iteration_neutral"] = True
            metadata["stagnation_neutral"] = True
            metadata["hard_pivot_neutral"] = True
        if root_candidate is not None:
            metadata["root_finalization_already_applied"] = True
        if not metadata.get("preserve_action_budget"):
            # ``proof_work`` is a semantic budget scope. Durable frontier
            # identities prevent replay of the same work, while this marker
            # keeps the outer loop open for the next declaration/context item.
            metadata["semantic_budget_step_consumed"] = True
        return MiniOutcome(
            action_id=self.id,
            solved=bool(ok),
            proof=proof if ok else None,
            helpers_added=tuple(helpers or ()),
            progress=bool(ok or helpers),
            cost_seconds=cost,
            metadata=metadata,
            root_candidate=root_candidate,
        )
