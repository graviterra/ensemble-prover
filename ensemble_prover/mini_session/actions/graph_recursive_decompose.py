"""Recursively decompose unresolved proof-graph obligations under hard bounds.

The action consumes missing-obligation and route-replan work, proves a smaller
statement through the recursive attempt machinery, and writes verified helper
evidence back to the parent graph and dossier. Ancestor-cycle checks, depth and
invocation caps, a separate budget pool, and pre-dispatch action marking prevent
unbounded redispatch while preserving durable helper progress.
"""

from __future__ import annotations

import asyncio
import copy
import hashlib
import json
import time
import weakref
from ensemble_prover.mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ensemble_prover.mini_recursive_identity import (
    mini_recursive_operational_action_spec_paths,
)
from dataclasses import asdict, fields as dataclass_fields
from dataclasses import is_dataclass, replace as dataclass_replace
from enum import Enum
from typing import Any, Callable, ClassVar, FrozenSet, List, Optional, Tuple

from ..action import MiniOutcome
from ..state_codec import StateSnapshotCompatibilityError
from ...llm_error_policy import (
    classify_llm_exception,
    is_terminal_llm_failure_reason,
    llm_failure_scope,
    projected_scoped_llm_failure_is_retryable,
)
from ...llm_usage import llm_usage_context_metadata
from ...proof_graph import (
    graph_statement_is_executable,
    graph_statement_root_equivalent,
)
from ...proof_dossier import (
    active_root_equivalence_statements,
    strong_progress_for_accepted_helpers,
    text_hash,
)
from ...helper_salvage import dependency_ordered_verified_helper_items
from ...helper_quality import verified_helper_admission_quality
from ...mini_branching import (
    merge_recursive_child_structural_progress,
    merge_relevant_child_proof_ideas,
    selected_child_proof_idea_packet,
    seed_relevant_proof_ideas_for_child,
)
from ..planner_jobs import PlannerJobLaunch, PlannerJobYield


def _secret_capability_field(name: Any) -> bool:
    """Whether a config field is credential material rather than capability."""

    normalized = str(name or "").strip().lower().replace("-", "_")
    return bool(
        normalized
        in {
            "api_key",
            "access_token",
            "auth_token",
            "bearer_token",
            "password",
            "passwd",
            "secret",
            "token",
            "credential",
            "credentials",
        }
        or normalized.endswith(
            (
                "_api_key",
                "_password",
                "_passwd",
                "_secret",
                "_token",
                "_credential",
                "_credentials",
            )
        )
    )


def _stable_capability_identity(value: Any, *, depth: int = 0) -> Any:
    """Return deterministic, JSON-safe configuration identity without locks."""

    if depth > 6:
        return f"{type(value).__module__}.{type(value).__qualname__}"
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, Enum):
        return _stable_capability_identity(value.value, depth=depth + 1)
    if isinstance(value, dict):
        return {
            str(key): _stable_capability_identity(item, depth=depth + 1)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
            if not _secret_capability_field(key)
        }
    if isinstance(value, (list, tuple)):
        return [
            _stable_capability_identity(item, depth=depth + 1) for item in value
        ]
    if isinstance(value, (set, frozenset)):
        items = [
            _stable_capability_identity(item, depth=depth + 1) for item in value
        ]
        return sorted(items, key=lambda item: json.dumps(item, sort_keys=True))
    if is_dataclass(value):
        return {
            field.name: _stable_capability_identity(
                getattr(value, field.name), depth=depth + 1
            )
            for field in dataclass_fields(value)
            if not _secret_capability_field(field.name)
        }
    public = (
        {
            str(key): item
            for key, item in vars(value).items()
            if not str(key).startswith("_")
            and not _secret_capability_field(key)
        }
        if hasattr(value, "__dict__")
        else {}
    )
    if public:
        return _stable_capability_identity(public, depth=depth + 1)
    return f"{type(value).__module__}.{type(value).__qualname__}:{str(value)}"


def _active_root_target_statements(session: Any) -> Tuple[str, ...]:
    dossier = getattr(session, "dossier", None)
    current_frame = getattr(
        dossier,
        "active_root_equivalence_statements_for_current_frame",
        None,
    )
    if callable(current_frame):
        try:
            current_targets = tuple(dict.fromkeys(current_frame()))
            if current_targets:
                return current_targets
        except Exception:
            pass
    hypothesis_targets = [
        item
        for item in list(getattr(dossier, "active_root_targets", []) or [])
        if isinstance(item, dict) and list(item.get("hypotheses") or [])
    ]
    if hypothesis_targets:
        return tuple(dict.fromkeys(active_root_equivalence_statements(hypothesis_targets)))
    return ()


class GraphRecursiveDecomposeAction:
    """Consume obligation/replan work items by recursive mini_recursive_plan.

    Wired into ``MiniSession._map_work_item_to_action`` as the first candidate
    for ``mine_missing_obligation`` and ``route_replan`` work types, ahead of
    ``graph_native_shortcut`` and ``conversation_turn_prove``. Priority 12
    keeps the action ahead of ``graph_native_shortcut`` (13) in the static
    fallback as well.
    """

    id: str = "graph_recursive_decompose"
    priority: int = 12
    cost_estimate_s: float = 60.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier"})
    REPLAY_OPERATIONAL_SPEC_PATHS: ClassVar[FrozenSet[str]] = (
        mini_recursive_operational_action_spec_paths()
    )
    WORK_TYPES: ClassVar[FrozenSet[str]] = frozenset(
        {"mine_missing_obligation", "route_replan"}
    )
    FRONTIER_ACTION_FAMILY: ClassVar[str] = "graph_recursive_decompose"
    SELECTED_FRONTIER_PRECHECK: ClassVar[bool] = True

    DEFAULT_MAX_INVOCATIONS: ClassVar[int] = 6
    DEFAULT_MAX_HELPER_ONLY_PASSES_PER_OBLIGATION: ClassVar[int] = 1
    FAILED_DISPATCH_DURABLE_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {"_recursive_driver_state"}
    )
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS: ClassVar[FrozenSet[str]] = frozenset(
        {
            "_recursive_driver_state",
            "_pending_planner_job_launch",
            "_planner_job_receipt_identities",
        }
    )

    def scheduler_runtime_state(self) -> dict[str, Any]:
        """Return versioned provider-free sub-pass cursor state."""

        return {
            "schema_version": 1,
            "recursive_driver_state": copy.deepcopy(self._recursive_driver_state),
        }

    def apply_scheduler_runtime_state(self, state: Any) -> None:
        """Restore a cursor emitted by :meth:`scheduler_runtime_state`."""

        record = dict(state or {}) if isinstance(state, dict) else {}
        if int(record.get("schema_version", 0) or 0) != 1:
            raise StateSnapshotCompatibilityError(
                "graph recursive runtime-state schema is unsupported"
            )
        driver_state = record.get("recursive_driver_state")
        if not isinstance(driver_state, dict):
            raise StateSnapshotCompatibilityError(
                "graph recursive driver cursor is malformed"
            )
        self._recursive_driver_state = copy.deepcopy(driver_state)

    def __init__(
        self,
        *,
        action_id: str = "graph_recursive_decompose",
        priority: int = 12,
        phase_label: str = "[graph-recursive-decompose]",
        config: Any = None,
        run_conversation_fn: Optional[Callable[..., Any]] = None,
        max_tool_calls_per_turn: int = 10,
        lean_check_tool_enabled: bool = True,
        try_lean_tool_enabled: bool = False,
        compute_examples_tool_enabled: bool = False,
        apply_decl_to_goal_tool_enabled: bool = False,
        raw_feedback: bool = False,
        repair_retrieval_enabled: bool = False,
        repair_retrieval_top_k: int = 6,
        proof_state_child_tactics_enabled: bool = False,
        proof_state_child_tactic_timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        proof_state_child_tactic_max_candidates: int = 32,
        root_tactic_timeout_s: float = 40.0,
        root_tactic_max_candidates: int = 64,
        proof_state_child_goal_limit: int = 3,
        proof_state_decl_application_limit: int = 6,
        proof_state_batch_parallelism: int = 1,
        max_recursion_depth: int = 2,
        max_invocations: int = DEFAULT_MAX_INVOCATIONS,
        max_helper_only_passes_per_obligation: int = (
            DEFAULT_MAX_HELPER_ONLY_PASSES_PER_OBLIGATION
        ),
        min_statement_length: int = 20,
        max_internal_turns: int = 20,
    ) -> None:
        self.id = str(action_id or "graph_recursive_decompose")
        self.priority = int(priority)
        self.cost_estimate_s = float(60.0)
        self.phase_label = str(phase_label or "[graph-recursive-decompose]")
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
        self.max_recursion_depth = max(0, int(max_recursion_depth or 0))
        self.max_invocations = max(0, int(max_invocations or 0))
        self.max_helper_only_passes_per_obligation = max(
            0,
            int(max_helper_only_passes_per_obligation or 0),
        )
        self.min_statement_length = max(0, int(min_statement_length or 0))
        try:
            configured_subpass_turn_capacity = max(
                1,
                int(getattr(config, "max_claims", 1) or 1),
            ) * max(
                1,
                int(getattr(config, "turns_per_claim", 1) or 1),
            )
        except (TypeError, ValueError):
            configured_subpass_turn_capacity = 1
        # Each graph-recursive invocation is already clamped to one pass by
        # ``_scale_sub_config``.  The safety ceiling must therefore cover that
        # complete, explicitly bounded pass; otherwise production's 20-claim
        # configuration rejects the action before ``run`` and silently removes
        # this proof family from the scheduler.
        self.max_internal_turns = max(
            1,
            int(max_internal_turns or 1),
            configured_subpass_turn_capacity,
        )
        # Search-continuation accounting uses this explicit attribute rather
        # than ``budget_attr``: the latter also participates in unrelated
        # recursive-controller recovery paths.
        self.progress_continuation_pool_attr = (
            "graph_recursive_decompose_remaining"
        )
        self._nested_execution_frame: dict[str, Any] = {}
        self._recursive_driver_state: dict[str, Any] = {}
        self._pending_planner_job_launch: Optional[PlannerJobLaunch] = None
        self._planner_job_receipt_identities: dict[tuple[str, str], Any] = {}

    def on_outcome_applied(self, session: Any, outcome: MiniOutcome) -> None:
        planner_pending = bool(outcome.metadata.get("planner_job_pending"))
        identity_record = outcome.metadata.get("planner_job_identity")
        pending_key = (
            str(identity_record.get("job_id") or ""),
            str(identity_record.get("request_fingerprint") or ""),
        ) if isinstance(identity_record, dict) else ("", "")
        broker_getter = getattr(session, "planner_job_broker", None)
        broker = broker_getter(create=False) if callable(broker_getter) else None
        retained: dict[tuple[str, str], Any] = {}
        for key, identity in self._planner_job_receipt_identities.items():
            if planner_pending and key == pending_key:
                retained[key] = identity
            elif broker is not None:
                broker.acknowledge(identity)
        self._planner_job_receipt_identities = retained
        if planner_pending:
            return
        self._nested_execution_frame = {}
        self._recursive_driver_state = {}

    def take_pending_planner_job_launch(self) -> Optional[PlannerJobLaunch]:
        """Transfer prepared raw provider work after action commit."""

        launch = self._pending_planner_job_launch
        self._pending_planner_job_launch = None
        return launch

    # ---------------------------------------------------------------------
    # Session-state helpers (lazy-init the action's session-scoped fields).
    # ---------------------------------------------------------------------

    @staticmethod
    def _bump_metric(session: Any, key: str, amount: int = 1) -> None:
        """Increment a metric key on the session's dossier, if available."""
        if GraphRecursiveDecomposeAction._read_only_applicability_probe(session):
            return
        bump = getattr(session, "_increment_dossier_metric", None)
        if not callable(bump):
            return
        try:
            bump(str(key or ""), int(amount or 0))
        except Exception:
            return

    @staticmethod
    def _read_only_applicability_probe(session: Any) -> bool:
        context = str(getattr(session, "_applicability_probe_context", "") or "")
        return context.endswith("_probe")

    def _budget_remaining(self, session: Any, *, initialize: bool = True) -> int:
        """Return remaining sub-pass invocations, initializing on first read."""
        if not hasattr(session, "graph_recursive_decompose_remaining"):
            if not initialize or self._read_only_applicability_probe(session):
                return self.max_invocations
            session.graph_recursive_decompose_remaining = self.max_invocations
        return int(session.graph_recursive_decompose_remaining or 0)

    def _decrement_budget(self, session: Any) -> None:
        remaining = self._budget_remaining(session)
        session.graph_recursive_decompose_remaining = max(0, remaining - 1)

    def _recover_inflight_reservation(self, session: Any) -> int:
        """Restore a graph-recursive sub-pass interrupted after checkpoint."""

        reservations = getattr(session, "recursive_inflight_reservations", None)
        if not isinstance(reservations, dict):
            return 0
        record = reservations.pop(self.id, None)
        if not isinstance(record, dict):
            return 0
        reserved = max(0, int(record.get("reserved_passes", 0) or 0))
        if str(record.get("pool_attr") or "") != (
            "graph_recursive_decompose_remaining"
        ) or reserved <= 0:
            return 0
        current = int(
            getattr(session, "graph_recursive_decompose_remaining", 0) or 0
        )
        session.graph_recursive_decompose_remaining = current + reserved

        ancestor_key = str(record.get("ancestor_key") or "").strip()
        stack = getattr(session, "graph_recursive_decompose_stack", None)
        if ancestor_key and isinstance(stack, list):
            for index in range(len(stack) - 1, -1, -1):
                if str(stack[index] or "") == ancestor_key:
                    stack.pop(index)
                    break

        consumed_key = record.get("consumed_frontier_action_key")
        consumed_keys = getattr(session, "consumed_frontier_action_keys", None)
        if consumed_key is not None and isinstance(consumed_keys, set):
            try:
                consumed_keys.discard(tuple(consumed_key))
            except (TypeError, ValueError):
                pass

        recorder = getattr(session, "_record_event", None)
        if callable(recorder):
            recorder(
                {
                    "phase": "recursive_inflight_reservation",
                    "action_id": self.id,
                    "pool_attr": "graph_recursive_decompose_remaining",
                    "reserved_passes_recredited": reserved,
                    "verdict": "unfinished_recursive_allocation_recovered",
                }
            )
        return reserved

    def _inflight_reservation_record(self, session: Any) -> Optional[dict[str, Any]]:
        """Return a valid pending graph allocation without consuming it."""
        reservations = getattr(session, "recursive_inflight_reservations", None)
        if not isinstance(reservations, dict):
            return None
        record = reservations.get(self.id)
        if not isinstance(record, dict):
            return None
        if str(record.get("pool_attr") or "").strip() != (
            "graph_recursive_decompose_remaining"
        ):
            return None
        return record

    def _inflight_reserved_passes(self, session: Any) -> int:
        """Inspect a pending graph allocation without mutating replay state."""

        record = self._inflight_reservation_record(session)
        if record is None:
            return 0
        return max(0, int(record.get("reserved_passes", 0) or 0))

    def _reserve_inflight(
        self,
        session: Any,
        *,
        ancestor_key: str,
        consumed_frontier_action_key: Any,
    ) -> None:
        reservations = getattr(session, "recursive_inflight_reservations", None)
        if not isinstance(reservations, dict):
            reservations = {}
            session.recursive_inflight_reservations = reservations
        reservations[self.id] = {
            "pool_attr": "graph_recursive_decompose_remaining",
            "reserved_passes": 1,
            "ancestor_key": str(ancestor_key or ""),
            "consumed_frontier_action_key": (
                tuple(consumed_frontier_action_key)
                if consumed_frontier_action_key is not None
                else None
            ),
        }

    def _clear_inflight_reservation(self, session: Any) -> None:
        reservations = getattr(session, "recursive_inflight_reservations", None)
        if isinstance(reservations, dict):
            reservations.pop(self.id, None)

    def _ancestor_stack(self, session: Any, *, initialize: bool = True) -> List[str]:
        if not hasattr(session, "graph_recursive_decompose_stack"):
            if not initialize or self._read_only_applicability_probe(session):
                return []
            session.graph_recursive_decompose_stack = []
        stack = session.graph_recursive_decompose_stack
        if not isinstance(stack, list):
            stack = list(stack or [])
            if not initialize or self._read_only_applicability_probe(session):
                return stack
            session.graph_recursive_decompose_stack = stack
        return stack

    # ---------------------------------------------------------------------
    # Static work-item helpers (mirror GraphNativeShortcutAction / GraphRouteAssemblyAction).
    # ---------------------------------------------------------------------

    def _selected_item(self, session: Any) -> Any:
        getter = getattr(session, "selected_work_item_for", None)
        if not callable(getter):
            return None
        return getter(
            self.id,
            work_types=tuple(sorted(GraphRecursiveDecomposeAction.WORK_TYPES)),
        )

    @staticmethod
    def _field(item: Any, key: str, default: Any = "") -> Any:
        if isinstance(item, dict):
            return item.get(key, default)
        return getattr(item, key, default)

    @staticmethod
    def _work_type(item: Any) -> str:
        return str(GraphRecursiveDecomposeAction._field(item, "work_type", "") or "").strip()

    @staticmethod
    def _graph_record(item: Any) -> dict:
        if isinstance(item, dict):
            return dict(item)
        record = getattr(item, "graph_record", None)
        return dict(record) if isinstance(record, dict) else {}

    @staticmethod
    def _graph(session: Any) -> Any:
        return getattr(getattr(session, "dossier", None), "proof_graph", None)

    @classmethod
    def _resolve_obligation_id(cls, work_item: Any, graph: Any) -> str:
        """Resolve the obligation_id for the work item.

        - ``mine_missing_obligation``: ``graph_record["obligation_id"]`` or the
          item's ``node_id`` directly.
        - ``route_replan``: prefer ``graph_record["obligation_id"]``; if absent
          fall back to the replan node's metadata; if still absent, scan
          ``graph.incoming(replan_id, kind="obligation_replan")``.
        """

        record = cls._graph_record(work_item)
        work_type = cls._work_type(work_item)

        if work_type == "mine_missing_obligation":
            obligation_id = str(record.get("obligation_id") or "").strip()
            if obligation_id:
                return obligation_id
            return str(cls._field(work_item, "node_id", "") or "").strip()

        if work_type == "route_replan":
            obligation_id = str(record.get("obligation_id") or "").strip()
            if obligation_id:
                return obligation_id
            replan_id = str(record.get("replan_id") or "").strip() or str(
                cls._field(work_item, "node_id", "") or ""
            ).strip()
            if not replan_id or graph is None:
                return ""
            replan_node = graph.nodes.get(replan_id) if hasattr(graph, "nodes") else None
            if replan_node is not None:
                meta = getattr(replan_node, "metadata", None) or {}
                from_meta = str(meta.get("obligation_id") or "").strip()
                if from_meta:
                    return from_meta
            incoming = getattr(graph, "incoming", None)
            if callable(incoming):
                for edge in incoming(replan_id, kind="obligation_replan"):
                    source = str(getattr(edge, "source", "") or "").strip()
                    if source:
                        return source
            return ""

        return str(cls._field(work_item, "node_id", "") or "").strip()

    @staticmethod
    def _obligation_statement(graph: Any, obligation_id: str) -> str:
        if graph is None or not obligation_id:
            return ""
        node = graph.nodes.get(obligation_id) if hasattr(graph, "nodes") else None
        if node is None:
            return ""
        return str(getattr(node, "statement", "") or "").strip()

    @staticmethod
    def _statement_key(statement: str) -> str:
        from ensemble_prover.proof_graph import graph_statement_key

        try:
            return str(graph_statement_key(statement) or "").strip()
        except Exception:
            return ""

    @staticmethod
    def _invalidated_statement_reason(
        session: Any,
        statement: str,
        *,
        target_environment_hash: str = "",
    ) -> str:
        dossier = getattr(session, "dossier", None)
        checker = getattr(dossier, "invalidated_statement_reason", None)
        if not callable(checker):
            return ""
        try:
            return str(
                checker(
                    statement,
                    target_environment_hash=target_environment_hash,
                )
                or ""
            ).strip()
        except Exception:
            return ""

    @staticmethod
    def _stale_planner_target_reason(
        graph: Any,
        obligation: Any,
        *,
        obligation_id: str,
        expected_statement_hash: str,
    ) -> str:
        """Return why an exact planner target no longer owns live work."""

        if obligation is None:
            return "obligation_not_found"
        obligation_status = str(getattr(obligation, "status", "") or "")
        resolved_blocked = False
        if obligation_status == "blocked":
            blocked_by_resolved = getattr(graph, "blocked_by_resolved", None)
            if callable(blocked_by_resolved):
                try:
                    resolved_blocked = bool(blocked_by_resolved(obligation_id))
                except Exception:
                    resolved_blocked = False
        tombstoned = False
        is_tombstone = getattr(graph, "is_superseded_tombstone", None)
        if callable(is_tombstone):
            try:
                tombstoned = bool(is_tombstone(obligation))
            except Exception:
                tombstoned = True
        live_statement = str(getattr(obligation, "statement", "") or "").strip()
        return (
            "obligation_no_longer_open"
            if obligation_status != "open" and not resolved_blocked
            else "obligation_tombstoned"
            if tombstoned
            else "obligation_statement_changed"
            if expected_statement_hash
            and expected_statement_hash != text_hash(live_statement)
            else ""
        )

    def _retire_invalidated_obligation(
        self,
        *,
        session: Any,
        graph: Any,
        work_item: Any,
        obligation_id: str,
        statement: str,
        reason: str,
        phase: str,
    ) -> None:
        """Mark invalidated generated work unschedulable at graph level."""

        if graph is None or not obligation_id:
            return
        nodes = getattr(graph, "nodes", {}) or {}
        obligation = nodes.get(obligation_id)
        statement_key = self._statement_key(statement)
        if obligation is not None:
            metadata = getattr(obligation, "metadata", None)
            if isinstance(metadata, dict):
                metadata["proposal_invalidated"] = True
                metadata["invalidated_statement_key"] = statement_key
                metadata["invalid_reason"] = str(reason or "")
                metadata["schedulable"] = False
            if str(getattr(obligation, "status", "") or "") == "open":
                obligation.status = "rejected"
        record = self._graph_record(work_item)
        replan_ids = [
            str(record.get("replan_id") or "").strip(),
            str(self._field(work_item, "node_id", "") or "").strip()
            if self._work_type(work_item) == "route_replan"
            else "",
        ]
        for replan_id in dict.fromkeys(item for item in replan_ids if item):
            replan = nodes.get(replan_id)
            if replan is None:
                continue
            metadata = getattr(replan, "metadata", None)
            if isinstance(metadata, dict):
                metadata["proposal_invalidated"] = True
                metadata["invalidated_statement_key"] = statement_key
                metadata["invalid_reason"] = str(reason or "")
                metadata["schedulable"] = False
            if str(getattr(replan, "status", "") or "") == "open":
                replan.status = "rejected"
        record_attempt = getattr(graph, "record_attempt", None)
        if callable(record_attempt):
            try:
                record_attempt(
                    obligation_id,
                    phase=phase,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    proof="",
                    verdict="obligation_rejected_invalidated_statement",
                    error_type="invalidated_statement",
                    source=self.id,
                    metadata={
                        "invalid_reason": str(reason or ""),
                        "invalidated_statement_key": statement_key,
                        "work_type": self._work_type(work_item),
                    },
                )
            except Exception:
                pass

    def _helper_context_hash(
        self,
        session: Any,
        *,
        refresh_quality: bool = True,
    ) -> str:
        """Fingerprint all proof evidence visible to the recursive sub-pass."""

        dossier = getattr(session, "dossier", None)
        getter = getattr(
            dossier,
            (
                "verified_helper_blocks"
                if refresh_quality
                else "verified_helper_blocks_snapshot"
            ),
            None,
        )
        if not callable(getter):
            blocks: List[str] = []
        else:
            try:
                blocks = [
                    str(block or "").strip()
                    for block in list(getter() or [])
                    if str(block or "").strip()
                ]
            except Exception:
                blocks = []
        proposed_getter = getattr(dossier, "proposed_helper_blocks", None)
        proposed_blocks: List[str] = []
        if callable(proposed_getter):
            try:
                proposed_blocks = [
                    str(block or "").strip()
                    for block in list(proposed_getter() or [])
                    if str(block or "").strip()
                ]
            except Exception:
                proposed_blocks = []
        elif isinstance(getattr(dossier, "proposed_helpers", None), dict):
            for item in getattr(dossier, "proposed_helpers", {}).values():
                source = str(getattr(item, "source", "") or "").strip()
                if source:
                    proposed_blocks.append(source)
        invalidated_reasons = getattr(
            dossier,
            "mini_recursive_invalidated_statement_reasons",
            {},
        )
        invalidated_parts: List[str] = []
        if isinstance(invalidated_reasons, dict):
            invalidated_parts = [
                f"{str(key or '').strip()}:{str(reason or '').strip()}"
                for key, reason in sorted(invalidated_reasons.items())
                if str(key or "").strip()
            ]
        payload_parts = [
            f"recursive_config:{str(self.config or '')}",
            f"max_internal_turns:{int(self.max_internal_turns or 0)}",
            f"max_recursion_depth:{int(self.max_recursion_depth or 0)}",
            f"lean_preamble:{str(getattr(getattr(session, 'conv', None), 'lean_preamble', '') or '')}",
            f"llm_preamble:{str(getattr(getattr(session, 'conv', None), 'preamble', '') or '')}",
            *(
                f"theory_bundle:{str(bundle_id or '')}"
                for bundle_id in sorted(
                    str(item or "")
                    for item in tuple(
                        getattr(session, "theory_imported_bundle_ids", ()) or ()
                    )
                    if str(item or "")
                )
            ),
            *(f"verified:{block}" for block in sorted(blocks)),
            *(f"proposed:{block}" for block in sorted(proposed_blocks)),
            *(f"invalidated:{item}" for item in invalidated_parts),
        ]
        for label, component in (
            ("prover", getattr(session, "prover_client", None)),
            ("refiner", getattr(session, "refiner_client", None)),
            ("lean", getattr(session, "lean", None)),
        ):
            cfg = getattr(component, "cfg", None)
            payload_parts.extend(
                (
                    f"{label}_class:{type(component).__module__}.{type(component).__qualname__}",
                    f"{label}_model:{str(getattr(cfg, 'model', '') or '')}",
                    f"{label}_base_url:{str(getattr(cfg, 'base_url', '') or '')}",
                    f"{label}_project_dir:{str(getattr(cfg, 'project_dir', '') or '')}",
                )
            )
        proof_cache = getattr(session, "proof_cache", None)
        payload_parts.extend(
            f"proof_cache:{str(source_hash or '')}"
            for source_hash in sorted(
                str(item or "")
                for item in set(
                    getattr(proof_cache, "_source_hashes", set()) or ()
                )
                if str(item or "")
            )
        )
        payload = "\n\n".join(payload_parts)
        return hashlib.sha256(payload.encode("utf-8", errors="replace")).hexdigest()[:16]

    def frontier_context_hash(self, session: Any) -> str:
        """Action-protocol freshness used by generic frontier deduplication."""

        return self._recursive_attempt_context_hash(session)

    def frontier_context_hash_probe(self, session: Any) -> str:
        """Explicitly pure scheduler-quotation identity hook."""

        return self._recursive_attempt_context_hash(
            session,
            refresh_quality=False,
        )

    def _recursive_attempt_context_hash(
        self,
        session: Any,
        *,
        refresh_quality: bool = True,
        selected_work_record: Optional[dict[str, Any]] = None,
    ) -> str:
        """Fingerprint proof evidence together with external toolchain epoch."""

        payload = {
            "helper_context_hash": self._helper_context_hash(
                session,
                refresh_quality=refresh_quality,
            ),
            "external_environment_hash": self._helper_only_environment_hash(session),
            # Failed recursive work is strategy-local even when several proof
            # ideas share the same formal graph obligation.  Success may
            # retire equivalent execution globally; failure must never make a
            # sibling route inherit an attempt it did not make.
            "selected_cognition": self._selected_cognition_identity(
                session,
                selected_work_record=selected_work_record,
            ),
        }
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(encoded.encode("utf-8")).hexdigest()[:16]

    @staticmethod
    def _selected_cognition_identity(
        session: Any,
        *,
        selected_work_record: Optional[dict[str, Any]] = None,
    ) -> dict[str, Any]:
        """Return the exact selected proof-idea binding without prompt text."""

        record = dict(
            selected_work_record
            if selected_work_record is not None
            else getattr(session, "selected_work_item_record", {}) or {}
        )
        primary = dict(
            record.get("primary_cognition_scope")
            or record.get("primary_consumer_binding")
            or {}
        )
        lineage = dict(primary.get("proof_lineage") or {})
        explicit = bool(
            primary
            or record.get("consumer_bindings")
            or record.get("proof_idea_id")
            or lineage.get("proof_idea_id")
        )
        if not explicit:
            return {}
        resolution_status = ""
        context_digest = str(
            getattr(session, "_selected_proof_idea_context_digest", "") or ""
        ).strip()
        resolver = getattr(getattr(session, "dossier", None), "resolve_proof_idea_context", None)
        if callable(resolver):
            try:
                resolution = resolver(record, policy="exact_selected")
                resolution_status = str(
                    getattr(resolution, "status", "") or ""
                ).strip()
                if resolution_status == "resolved":
                    context_digest = str(
                        getattr(resolution, "context_digest", "") or context_digest
                    ).strip()
                else:
                    context_digest = ""
            except Exception as exc:
                # Invalid bindings remain distinct and fail closed at the
                # execution boundary; hashing must stay total for scheduler
                # applicability probes.
                resolution_status = f"error:{type(exc).__name__}"
        return {
            "execution_scope_id": str(
                record.get("execution_scope_id") or ""
            ).strip(),
            "execution_contract_identity": str(
                record.get("execution_contract_identity") or ""
            ).strip(),
            "primary_consumer_binding": primary,
            "resolution_status": resolution_status,
            "context_digest": context_digest,
        }

    def _helper_only_environment_hash(
        self,
        session: Any,
        *,
        excluded_helper_source_hashes: FrozenSet[str] = frozenset(),
    ) -> str:
        """Fingerprint external proof capabilities, excluding local helper churn.

        A helper-only pass necessarily changes verified/proposed helpers. Those
        additions must not reset its own quota. A changed Lean/theory/model/tool
        environment may make another pass productive and therefore starts a
        new quota epoch.
        """

        dossier = getattr(session, "dossier", None)
        conv = getattr(session, "conv", None)
        lean = getattr(session, "lean", None)
        from ..session import _dispatch_capability_identity

        lean_identity = _dispatch_capability_identity(lean)

        def capability_class(identity: Any, fallback: Any) -> str:
            if (
                type(identity) is tuple
                and len(identity) == 4
                and identity[0] == "mini_dispatch_runtime_capability"
            ):
                return f"{identity[1]}.{identity[2]}"
            return f"{type(fallback).__module__}.{type(fallback).__qualname__}"

        lean_cfg = getattr(lean, "cfg", None)
        clients = []
        for role in ("prover_client", "refiner_client"):
            client = getattr(session, role, None)
            client_identity = _dispatch_capability_identity(client)
            cfg = getattr(client, "cfg", None)
            clients.append(
                {
                    "role": role,
                    "name": str(getattr(cfg, "name", "") or ""),
                    "base_url": str(getattr(cfg, "base_url", "") or ""),
                    "model": str(getattr(cfg, "model", "") or ""),
                    "revision": str(getattr(cfg, "revision", "") or ""),
                    "temperature": getattr(cfg, "temperature", None),
                    "full_config": _stable_capability_identity(cfg),
                    "class": capability_class(client_identity, client),
                }
            )
        payload = {
            "lean_environment_hash": str(
                getattr(dossier, "current_lean_environment_hash", "") or ""
            ),
            "theory_context_hash": str(
                getattr(dossier, "mini_theory_context_hash", "") or ""
            ),
            "graph_project_environment_hash": str(
                getattr(dossier, "graph_execution_project_environment_hash", "")
                or ""
            ),
            "lean_preamble": str(getattr(conv, "lean_preamble", "") or ""),
            "llm_preamble": str(getattr(conv, "preamble", "") or ""),
            "theory_bundle_ids": sorted(
                str(item or "")
                for item in tuple(
                    getattr(session, "theory_imported_bundle_ids", ()) or ()
                )
                if str(item or "")
            ),
            "lean_config": {
                "class": capability_class(lean_identity, lean),
                "project_dir": str(getattr(lean_cfg, "project_dir", "") or ""),
                "resolved_lean_executable": str(
                    getattr(lean_cfg, "resolved_lean_executable", "") or ""
                ),
                "preamble_import": str(
                    getattr(lean_cfg, "preamble_import", "") or ""
                ),
                "full_config": _stable_capability_identity(lean_cfg),
            },
            "clients": clients,
            "action": {
                "id": self.id,
                "class": f"{type(self).__module__}.{type(self).__qualname__}",
                "config": str(self.config or ""),
                "max_internal_turns": int(self.max_internal_turns or 0),
                "max_recursion_depth": int(self.max_recursion_depth or 0),
                "max_tool_calls_per_turn": int(self.max_tool_calls_per_turn or 0),
                "max_invocations": int(self.max_invocations or 0),
                "max_helper_only_passes": int(
                    self.max_helper_only_passes_per_obligation or 0
                ),
                "min_statement_length": int(self.min_statement_length or 0),
                "raw_feedback": bool(self.raw_feedback),
                "repair_retrieval_enabled": bool(self.repair_retrieval_enabled),
                "repair_retrieval_top_k": int(self.repair_retrieval_top_k or 0),
                "proof_state_child_tactics_enabled": bool(
                    self.proof_state_child_tactics_enabled
                ),
                "proof_state_child_tactic_timeout_s": float(
                    self.proof_state_child_tactic_timeout_s or 0.0
                ),
                "proof_state_child_tactic_max_candidates": int(
                    self.proof_state_child_tactic_max_candidates or 0
                ),
                "proof_state_child_goal_limit": int(
                    self.proof_state_child_goal_limit or 0
                ),
                "proof_state_decl_application_limit": int(
                    self.proof_state_decl_application_limit or 0
                ),
                "proof_state_batch_parallelism": int(
                    self.proof_state_batch_parallelism or 0
                ),
                "root_tactic_timeout_s": float(self.root_tactic_timeout_s or 0.0),
                "root_tactic_max_candidates": int(
                    self.root_tactic_max_candidates or 0
                ),
            },
            "tool_policy": {
                "lean_check": bool(self.lean_check_tool_enabled),
                "try_lean": bool(self.try_lean_tool_enabled),
                "compute_examples": bool(self.compute_examples_tool_enabled),
                "apply_decl_to_goal": bool(self.apply_decl_to_goal_tool_enabled),
            },
            "proof_cache_source_hashes": sorted(
                str(item or "")
                for item in set(
                    getattr(getattr(session, "proof_cache", None), "_source_hashes", set())
                    or ()
                )
                if str(item or "")
            ),
            "external_verified_helper_source_hashes": sorted(
                str(getattr(helper, "source_hash", "") or "")
                for helper in dict(
                    getattr(dossier, "verified_helpers", {}) or {}
                ).values()
                if str(getattr(helper, "source_hash", "") or "")
                not in excluded_helper_source_hashes
            ),
        }
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(encoded.encode("utf-8")).hexdigest()[:16]

    def _attempt_belongs_to_instance(self, attempt: Any) -> bool:
        source = str(getattr(attempt, "source", "") or "").strip()
        return source == self.id or (
            not source and self.id == GraphRecursiveDecomposeAction.id
        )

    def _has_prior_failed_recursive_attempt(
        self,
        graph: Any,
        obligation_id: str,
        *,
        statement_key: str,
        helper_context_hash: str,
        recursive_attempt_context_hash: str = "",
    ) -> bool:
        """Return True when this exact recursive pass already failed durably.

        Session-local consumed frontier keys are intentionally cleared after
        unrelated progress. Without a graph-backed check, the same expensive
        recursive sub-pass can be retried later even though neither the target
        statement nor the verified helper context changed.
        """

        if graph is None or not statement_key:
            return False
        node = getattr(graph, "nodes", {}).get(obligation_id)
        attempt_ids = set(getattr(node, "attempt_ids", []) or []) if node else set()
        for attempt in list(getattr(graph, "attempts", []) or []):
            if not self._attempt_belongs_to_instance(attempt):
                continue
            same_obligation = (
                str(getattr(attempt, "node_id", "") or "") == obligation_id
            )
            if (
                attempt_ids
                and same_obligation
                and getattr(attempt, "attempt_id", None) not in attempt_ids
            ):
                continue
            if str(getattr(attempt, "verdict", "") or "") != "recursive_decomposition_failed":
                continue
            metadata = dict(getattr(attempt, "metadata", {}) or {})
            prior_statement_key = str(metadata.get("statement_key") or "").strip()
            if prior_statement_key != statement_key:
                continue
            prior_recursive_hash = str(
                metadata.get("recursive_attempt_context_hash") or ""
            ).strip()
            if prior_recursive_hash:
                if prior_recursive_hash != recursive_attempt_context_hash:
                    continue
            elif recursive_attempt_context_hash:
                # Pre-composite checkpoints cannot prove that their failure
                # occurred in this Lean/model/tool environment. Reopen once;
                # the next durable attempt records the complete identity.
                continue
            elif str(metadata.get("helper_context_hash") or "").strip() != (
                helper_context_hash
            ):
                continue
            return True
        return False

    def _prior_helper_only_source_hashes(
        self,
        graph: Any,
        obligation_id: str,
        *,
        statement_key: str,
    ) -> FrozenSet[str]:
        """Hashes of helpers produced by prior helper-only local passes."""

        if graph is None or not statement_key:
            return frozenset()
        hashes: set[str] = set()
        for attempt in list(getattr(graph, "attempts", []) or []):
            if not self._attempt_belongs_to_instance(attempt):
                continue
            if str(getattr(attempt, "node_id", "") or "") != obligation_id:
                continue
            if (
                str(getattr(attempt, "verdict", "") or "")
                != "recursive_decomposition_helpers_propagated"
            ):
                continue
            metadata = dict(getattr(attempt, "metadata", {}) or {})
            if str(metadata.get("statement_key") or "").strip() != statement_key:
                continue
            hashes.update(
                str(value or "").strip()
                for value in dict(
                    metadata.get("helper_source_hashes") or {}
                ).values()
                if str(value or "").strip()
            )
        return frozenset(hashes)

    def _prior_helper_progress_attempt_count(
        self,
        graph: Any,
        obligation_id: str,
        *,
        statement_key: str,
        helper_only_environment_hash: str,
    ) -> int:
        """Count helper-only recursive passes for this equivalent statement.

        A helper-only pass changed the parent helper context but left the
        selected statement open. Count it only in the proof environment where
        it ran: a newly imported theory or verified helper is precisely the
        evidence that can make another recursive pass productive.
        """

        if graph is None or not statement_key:
            return 0
        node = getattr(graph, "nodes", {}).get(obligation_id)
        attempt_ids = set(getattr(node, "attempt_ids", []) or []) if node else set()
        count = 0
        for attempt in list(getattr(graph, "attempts", []) or []):
            if not self._attempt_belongs_to_instance(attempt):
                continue
            same_obligation = (
                str(getattr(attempt, "node_id", "") or "") == obligation_id
            )
            if (
                attempt_ids
                and same_obligation
                and getattr(attempt, "attempt_id", None) not in attempt_ids
            ):
                continue
            if (
                str(getattr(attempt, "verdict", "") or "")
                != "recursive_decomposition_helpers_propagated"
            ):
                continue
            metadata = dict(getattr(attempt, "metadata", {}) or {})
            if str(metadata.get("statement_key") or "").strip() != statement_key:
                continue
            prior_environment = str(
                metadata.get("helper_only_environment_hash") or ""
            ).strip()
            if prior_environment and prior_environment != helper_only_environment_hash:
                continue
            count += 1
        return count

    def _scale_sub_config(self, depth: int) -> Any:
        """Return a config for the recursive sub-pass with reduced budgets."""
        base = self.config
        if base is None:
            return None
        # Clamp passes to 1 — sub-pass must not iterate. Reduce max_claims by
        # depth so deeper recursion produces fewer sub-claims (geometric
        # backoff bounds total internal turns).
        try:
            current_claims = int(getattr(base, "max_claims", 4) or 4)
        except Exception:
            current_claims = 4
        scaled_claims = max(1, current_claims - max(0, depth))
        try:
            scaled = dataclass_replace(base, passes=1, max_claims=scaled_claims)
        except Exception:
            scaled = base
        return scaled

    def _internal_turn_budget_exceeded(self, depth: int) -> bool:
        cfg = self._scale_sub_config(depth)
        if cfg is None:
            return False
        try:
            passes = max(1, int(getattr(cfg, "passes", 1) or 1))
            claims = max(1, int(getattr(cfg, "max_claims", 1) or 1))
            turns = max(1, int(getattr(cfg, "turns_per_claim", 1) or 1))
        except Exception:
            return False
        return (passes * claims * turns) > self.max_internal_turns

    # ---------------------------------------------------------------------
    # Public action protocol.
    # ---------------------------------------------------------------------

    def is_applicable(self, session: Any) -> bool:
        if self._pending_planner_job_launch is not None:
            return False
        pending_identity = self._recursive_driver_state.get(
            "planner_job_identity"
        )
        if (
            str(self._recursive_driver_state.get("phase") or "")
            == "planner_job_pending"
            and isinstance(pending_identity, dict)
        ):
            broker_getter = getattr(session, "planner_job_broker", None)
            broker = (
                broker_getter(create=False)
                if callable(broker_getter)
                else None
            )
            if broker is not None and broker.status(
                str(pending_identity.get("job_id") or ""),
                str(pending_identity.get("request_fingerprint") or ""),
            ) == "pending":
                return False
        if self.config is None:
            return False
        graph = self._graph(session)
        pending_target = self._recursive_driver_state.get(
            "graph_recursive_target"
        )
        saved_work_record = (
            dict(pending_target.get("work_item_record") or {})
            if isinstance(pending_target, dict)
            else {}
        )
        item = saved_work_record or self._selected_item(session)
        if graph is None or item is None:
            return False
        work_type = self._work_type(item)
        if work_type not in self.WORK_TYPES:
            return False
        obligation_id = self._resolve_obligation_id(item, graph)
        if not obligation_id:
            return False
        obligation = graph.nodes.get(obligation_id) if hasattr(graph, "nodes") else None
        if obligation is None:
            return False
        available_passes = self._budget_remaining(session)
        available_passes += self._inflight_reserved_passes(session)
        if available_passes <= 0:
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_budget_exhausted"
            )
            return False
        # A blocked obligation becomes executable again once every explicit
        # graph blocker has a durable proof.  ``work_frontier`` deliberately
        # emits that state, so the action gate must use the same readiness
        # predicate instead of requiring a lifecycle rewrite first.
        obligation_status = str(getattr(obligation, "status", "") or "")
        resolved_blocked = False
        if obligation_status == "blocked":
            blocked_by_resolved = getattr(graph, "blocked_by_resolved", None)
            if callable(blocked_by_resolved):
                try:
                    resolved_blocked = bool(blocked_by_resolved(obligation_id))
                except Exception:
                    resolved_blocked = False
        # Skip proved, terminal, and still-blocked obligations (idempotency
        # and fail-closed readiness).
        if obligation_status != "open" and not resolved_blocked:
            return False
        # Skip tombstoned obligations.
        is_tombstone = getattr(graph, "is_superseded_tombstone", None)
        if callable(is_tombstone) and is_tombstone(obligation):
            return False
        obligation_metadata = dict(getattr(obligation, "metadata", {}) or {})
        route_id = str(obligation_metadata.get("route_id") or "").strip()
        route_poisoned = getattr(graph, "_route_is_terminally_poisoned", None)
        if route_id and callable(route_poisoned) and route_poisoned(route_id):
            if self._read_only_applicability_probe(session):
                return False
            obligation.status = "rejected"
            obligation.proof_hash = ""
            obligation.metadata["route_retired"] = True
            obligation.metadata["route_dependency_contradicted"] = True
            obligation.metadata["route_poisoned_descendant_suppressed"] = True
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_poisoned_route_work_skipped",
            )
            return False
        statement = str(getattr(obligation, "statement", "") or "").strip()
        try:
            from ensemble_prover.proof_dossier import is_answer_unsafe_statement_text
        except Exception:
            is_answer_unsafe_statement_text = None
        if callable(is_answer_unsafe_statement_text) and is_answer_unsafe_statement_text(
            statement,
            suppress_solution_placeholders=bool(
                getattr(
                    getattr(session, "conv", None),
                    "suppress_solution_placeholders",
                    True,
                )
            ),
            opaque_mode=bool(getattr(getattr(session, "conv", None), "opaque_mode", True)),
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
                getattr(
                    getattr(session, "dossier", None),
                    "official_answer_payload_present",
                    None,
                ),
            ),
        ):
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_answer_unsafe_skipped",
            )
            return False
        root_statement = str(
            getattr(getattr(session, "dossier", None), "root_statement", "") or ""
        ).strip()
        if root_statement and graph_statement_root_equivalent(
            statement,
            root_statement,
            active_target_statements=_active_root_target_statements(session),
        ):
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_root_equivalent_skipped",
            )
            return False
        if not graph_statement_is_executable(statement):
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_non_executable_skipped"
            )
            return False
        obligation = graph.nodes.get(obligation_id)
        target_environment_hash = str(
            (getattr(obligation, "metadata", {}) or {}).get(
                "statement_environment_hash"
            )
            or ""
        ).strip()
        invalid_reason = self._invalidated_statement_reason(
            session,
            statement,
            target_environment_hash=target_environment_hash,
        )
        if invalid_reason:
            if self._read_only_applicability_probe(session):
                return False
            self._retire_invalidated_obligation(
                session=session,
                graph=graph,
                work_item=item,
                obligation_id=obligation_id,
                statement=statement,
                reason=invalid_reason,
                phase="graph_recursive_decompose_applicability",
            )
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_invalidated_obligation_skipped",
            )
            return False
        if (
            bool(obligation_metadata.get("formalization_required"))
            or obligation_metadata.get("certified_fact") is False
        ):
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_untrusted_obligation_skipped",
            )
            return False
        if len(statement) < self.min_statement_length:
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_too_small_skipped"
            )
            return False
        statement_key = self._statement_key(statement)
        # B-HIGH (Adversary C): if a proved helper already matches the
        # obligation statement, cede to ``graph_native_shortcut`` — it can
        # close the obligation instantly without spending a sub-pass.
        # B-LOW (Adversary B-2): filter tombstones; otherwise we'd cede to a
        # shortcut that the shortcut itself would skip, deadlocking the
        # obligation.
        matcher = getattr(graph, "_proved_helper_for_statement", None)
        if callable(matcher):
            try:
                helper_match = matcher(
                    statement,
                    require_replayable_source=True,
                    consumer_node=obligation,
                )
            except Exception:
                helper_match = None
            if helper_match is not None:
                certifier = getattr(graph, "_helper_certifies_node", None)
                try:
                    helper_certifies = bool(
                        callable(certifier)
                        and certifier(helper_match, obligation)
                    )
                except Exception:
                    helper_certifies = False
                is_tombstone_fn = getattr(graph, "is_superseded_tombstone", None)
                if callable(is_tombstone_fn):
                    try:
                        tombstoned = bool(is_tombstone_fn(helper_match))
                    except Exception:
                        tombstoned = False
                else:
                    tombstoned = False
                if helper_certifies and not tombstoned:
                    return False
        if self._has_prior_failed_recursive_attempt(
            graph,
            obligation_id,
            statement_key=statement_key,
            helper_context_hash=self._helper_context_hash(
                session,
                refresh_quality=not self._read_only_applicability_probe(session),
            ),
            recursive_attempt_context_hash=(
                self._recursive_attempt_context_hash(
                    session,
                    refresh_quality=not self._read_only_applicability_probe(session),
                )
            ),
        ):
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_prior_failure_skipped",
            )
            return False
        helper_only_source_hashes = self._prior_helper_only_source_hashes(
            graph,
            obligation_id,
            statement_key=statement_key,
        )
        helper_only_pass_count = self._prior_helper_progress_attempt_count(
            graph,
            obligation_id,
            statement_key=statement_key,
            helper_only_environment_hash=self._helper_only_environment_hash(
                session,
                excluded_helper_source_hashes=helper_only_source_hashes,
            ),
        )
        if (
            self.max_helper_only_passes_per_obligation >= 0
            and helper_only_pass_count
            >= self.max_helper_only_passes_per_obligation
        ):
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_helper_progress_skipped",
            )
            return False
        # Depth cap.
        stack = self._ancestor_stack(session)
        reservation = self._inflight_reservation_record(session)
        reserved_ancestor = str(
            (reservation or {}).get("ancestor_key") or ""
        ).strip()
        if reserved_ancestor and stack and str(stack[-1] or "") == reserved_ancestor:
            # A checkpoint inside this action contains the frame it pushed.
            # Evaluate replay applicability as though recovery had atomically
            # removed that one owned frame; older identical ancestors remain
            # visible and still suppress a genuine cycle.
            stack = list(stack[:-1])
        if self.max_recursion_depth > 0 and len(stack) >= self.max_recursion_depth:
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_recursion_cap_hit"
            )
            return False
        # Cycle suppression by graph_statement_key.
        key = statement_key
        if key and key in stack:
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_cycle_suppressed"
            )
            return False
        # Total-internal-turn cap (B-P3 context-window guard).
        if self._internal_turn_budget_exceeded(len(stack)):
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_recursion_cap_hit"
            )
            return False
        return True

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Use the action's guarded observational path during quotation."""

        return self.is_applicable(session)

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.mini_recursive import (
            _support_names_for_proof,
            helper_decl_from_proof,
            run_mini_recursive_attempt,
            seed_verified_helpers,
            unique_dossier_helper_name,
        )
        from ensemble_prover.mini_prover import Conversation
        from ensemble_prover.mini_subgoal_planner import sanitize_theorem_name
        from ensemble_prover.proof_dossier import (
            ProofDossier,
            propagate_invalidated_statements,
            propagate_proposed_helpers,
        )

        started = time.monotonic()
        self._recover_inflight_reservation(session)
        graph = self._graph(session)
        pending_target = (
            self._recursive_driver_state.get("graph_recursive_target")
            if str(self._recursive_driver_state.get("phase") or "")
            == "planner_job_pending"
            else None
        )
        saved_work_record = (
            dict(pending_target.get("work_item_record") or {})
            if isinstance(pending_target, dict)
            else {}
        )
        item = saved_work_record or self._selected_item(session)
        selected_work_record = (
            saved_work_record
            or dict(getattr(session, "selected_work_item_record", {}) or {})
            or self._graph_record(item)
        )
        child_branch_key = str(
            pending_target.get("child_branch_key")
            if isinstance(pending_target, dict)
            else ""
        ).strip()

        if graph is None or item is None:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "missing_graph_work",
                    "preserve_action_budget": bool(pending_target),
                    "iteration_neutral": bool(pending_target),
                    "scheduler_neutral": bool(pending_target),
                    "stagnation_neutral": bool(pending_target),
                    "hard_pivot_neutral": bool(pending_target),
                },
            )

        work_type = self._work_type(item)
        obligation_id = self._resolve_obligation_id(item, graph)
        saved_obligation_id = str(
            pending_target.get("obligation_id")
            if isinstance(pending_target, dict)
            else ""
        ).strip()
        if saved_obligation_id and saved_obligation_id != obligation_id:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=max(0.0, time.monotonic() - started),
                metadata={
                    "verdict": "stale_graph_planner_receipt_retired",
                    "reason": "obligation_identity_changed",
                    "obligation_id": obligation_id,
                    "preserve_action_budget": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "strong_progress": False,
                },
            )
        obligation = (
            graph.nodes.get(obligation_id) if obligation_id and hasattr(graph, "nodes") else None
        )

        if obligation is None:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "obligation_not_found",
                    "work_type": work_type,
                    "obligation_id": obligation_id,
                    "preserve_action_budget": bool(pending_target),
                    "iteration_neutral": bool(pending_target),
                    "scheduler_neutral": bool(pending_target),
                    "stagnation_neutral": bool(pending_target),
                    "hard_pivot_neutral": bool(pending_target),
                },
            )

        statement = str(getattr(obligation, "statement", "") or "").strip()
        pending_identity_record = self._recursive_driver_state.get(
            "planner_job_identity"
        )
        if (
            str(self._recursive_driver_state.get("phase") or "")
            == "planner_job_pending"
            and isinstance(pending_identity_record, dict)
        ):
            saved_root_hash = str(
                pending_identity_record.get("root_statement_hash") or ""
            )
            stale_reason = self._stale_planner_target_reason(
                graph,
                obligation,
                obligation_id=obligation_id,
                expected_statement_hash=saved_root_hash,
            )
            if stale_reason:
                # A ready receipt has scheduler priority and therefore
                # bypasses ordinary applicability. Recheck the exact graph
                # authority here before parsing or publishing its response.
                # The non-pending outcome makes on_outcome_applied retire the
                # stale receipt and compact driver cursor exactly once.
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=(),
                    progress=False,
                    cost_seconds=max(0.0, time.monotonic() - started),
                    metadata={
                        "verdict": "stale_graph_planner_receipt_retired",
                        "reason": stale_reason,
                        "obligation_id": obligation_id,
                        "preserve_action_budget": True,
                        "iteration_neutral": True,
                        "scheduler_neutral": True,
                        "stagnation_neutral": True,
                        "hard_pivot_neutral": True,
                        "strong_progress": False,
                    },
                )
        parent_root_statement = str(
            getattr(getattr(session, "dossier", None), "root_statement", "") or ""
        ).strip()
        if parent_root_statement and graph_statement_root_equivalent(
            statement,
            parent_root_statement,
            active_target_statements=_active_root_target_statements(session),
        ):
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_root_equivalent_skipped",
            )
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "root_equivalent_obligation_skipped",
                    "work_type": work_type,
                    "obligation_id": obligation_id,
                    "strong_progress": False,
                },
            )
        if not graph_statement_is_executable(statement):
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "non_executable_obligation_statement",
                    "work_type": work_type,
                    "obligation_id": obligation_id,
                },
            )
        ancestor_key = self._statement_key(statement)
        helper_context_hash = self._helper_context_hash(session)
        recursive_attempt_context_hash = self._recursive_attempt_context_hash(
            session,
            selected_work_record=selected_work_record,
        )
        stack = self._ancestor_stack(session)
        depth_before = len(stack)
        if not child_branch_key:
            child_branch_key = (
                f"{obligation_id}:{depth_before + 1}:"
                f"{int(getattr(session, 'iteration', 0) or 0)}"
            )

        sub_config = self._scale_sub_config(depth_before)
        parent_problem_text = str(
            getattr(getattr(session, "problem", None), "docstring", "") or ""
        ).strip()
        parent_theorem_name = sanitize_theorem_name(
            getattr(getattr(session, "problem", None), "theorem_name", "t"),
            prefix="parent_theorem",
            max_length=48,
        )
        obligation_suffix = sanitize_theorem_name(
            obligation_id,
            prefix="obligation",
            max_length=32,
        )
        obligation_theorem_name = sanitize_theorem_name(
            f"{parent_theorem_name}_obl_{obligation_suffix}",
            prefix="graph_recursive_obligation",
            max_length=96,
        )
        obligation_lean_signature = (
            f"theorem {obligation_theorem_name} : {statement} := by\n"
            "  -- prove this recursive obligation"
        )
        problem_text = "\n\n".join(
            part
            for part in (
                parent_problem_text,
                (
                    "Focused recursive obligation selected from the parent "
                    f"proof graph `{parent_theorem_name}`. Prove the "
                    "obligation statement below; the parent theorem is "
                    "orientation only."
                ),
                (
                    "Parent root statement (orientation only, not the target "
                    f"of this sub-pass):\n{parent_root_statement}"
                    if parent_root_statement
                    else ""
                ),
                f"Selected obligation statement:\n{statement}",
                (
                    "Generated-obligation trust boundary: the selected "
                    "obligation statement is the target of this sub-pass; "
                    "the parent theorem is orientation only. Missing "
                    "local bridge facts, library declarations, or automation "
                    "steps are proof obligations to decompose or prove, not "
                    "evidence that the selected target is false or not "
                    "provable. Unchecked prose refutations are treated as "
                    "failed proof attempts and must not invalidate this "
                    "obligation without an accepted Lean negation or "
                    "counterexample check. Output should either prove the "
                    "selected obligation or manufacture strictly smaller "
                    "named local obligations with Lean propositions plus "
                    "dependency/use notes."
                ),
            )
            if str(part or "").strip()
        )
        parent_dossier = getattr(session, "dossier", None)
        official_answer_payload_present = getattr(
            session.conv,
            "official_answer_payload_present",
            getattr(parent_dossier, "official_answer_payload_present", None),
        )
        sub_dossier = ProofDossier(
            theorem_name=obligation_theorem_name,
            root_statement=statement,
            problem_text=problem_text,
            cache_owner_theorem_name=str(
                getattr(parent_dossier, "cache_owner_theorem_name", "")
                or getattr(getattr(session, "problem", None), "theorem_name", "")
                or ""
            ),
            proof_cache_publish_enabled=False,
            suppress_solution_placeholders=bool(
                getattr(session.conv, "suppress_solution_placeholders", True)
            ),
            opaque_mode=bool(getattr(session.conv, "opaque_mode", True)),
            allow_official_answer_visibility=bool(
                getattr(session.conv, "allow_official_answer_visibility", False)
            ),
            official_answer_payload_present=official_answer_payload_present,
        )
        seed_verified_helpers(sub_dossier, parent_dossier)
        child_proof_idea_ids: set[str] = set()
        child_proof_idea_branch_id = ""
        if parent_dossier is not None:
            child_proof_idea_ids, child_proof_idea_branch_id = (
                seed_relevant_proof_ideas_for_child(
                    sub_dossier,
                    parent_dossier,
                    lineage_sources=(
                        self._graph_record(item),
                        dict(getattr(obligation, "metadata", {}) or {}),
                        dict(selected_work_record),
                    ),
                    branch_source="graph-recursive-child",
                    branch_key=child_branch_key,
                )
            )
        from .conversation_turn import (
            SelectedProofIdeaContextError,
            _selected_proof_idea_context_for_prompt,
        )

        try:
            selected_parent_proof_idea_context = (
                _selected_proof_idea_context_for_prompt(
                    session,
                    selected_child_proof_idea_packet(
                        parent_dossier,
                        dict(selected_work_record),
                        graph_node=obligation,
                        session=session,
                    ),
                    audience="child",
                )
            )
        except (SelectedProofIdeaContextError, TypeError, ValueError, AttributeError) as exc:
            # Selection/cognition can become stale between frontier quotation
            # and dispatch.  This happens before the action acquires mutation
            # authority or spends its recursive pool, so request a fresh packet
            # instead of escalating an expected projection race into a terminal
            # live-action failure.
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "selected_proof_idea_context_invalidated",
                    "work_type": work_type,
                    "obligation_id": obligation_id,
                    "selected_work_projection_invalidated": True,
                    "selected_work_projection_zero_provider": True,
                    "scoped_failure_reason": (
                        "selected_proof_idea_context_invalidated"
                    ),
                    "preserve_action_budget": True,
                    "refund_local_repair_quota": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                    "strong_progress": False,
                    "projection_error_type": type(exc).__name__,
                    "projection_error": str(exc),
                },
            )
        if parent_dossier is not None:
            try:
                propagate_proposed_helpers(
                    sub_dossier,
                    parent_dossier,
                    record_graph=False,
                )
            except Exception:
                pass
            sub_dossier.superseded_verified_helper_hashes = {
                str(name): [str(value) for value in list(values or [])]
                for name, values in (
                    getattr(parent_dossier, "superseded_verified_helper_hashes", {})
                    or {}
                ).items()
            }
            sub_dossier.verified_helper_source_hash_history = {
                str(name): [str(value) for value in list(values or [])]
                for name, values in (
                    getattr(parent_dossier, "verified_helper_source_hash_history", {})
                    or {}
                ).items()
            }
            sub_dossier.mini_recursive_invalidated_statement_reasons.update(
                dict(
                    getattr(
                        parent_dossier,
                        "mini_recursive_invalidated_statement_reasons",
                        {},
                    )
                    or {}
                )
            )
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
        recursive_helper_depth = int(getattr(session, "recursion_depth", 0) or 0)
        if self.max_recursion_depth > 0:
            recursive_helper_depth += depth_before + 1

        result = None
        sub_pass_exception: Optional[BaseException] = None
        merged_helper_names: List[str] = []
        structural_progress_counts = {
            "nodes_imported": 0,
            "nodes_coalesced": 0,
            "edges_imported": 0,
            "blockers_attached": 0,
            "conflicts": 0,
        }
        structural_merge_error_count = 0
        structural_node_id_remap = {
            str(sub_dossier.proof_graph.root_node_id): obligation_id
        }

        def merge_subpass_structure() -> None:
            nonlocal structural_merge_error_count
            if parent_dossier is None or sub_dossier is parent_dossier:
                return
            try:
                merged = merge_recursive_child_structural_progress(
                    parent_dossier,
                    sub_dossier,
                    parent_obligation_id=obligation_id,
                    branch_key=(
                        child_proof_idea_branch_id
                        or recursive_attempt_context_hash
                    ),
                    node_id_remap_out=structural_node_id_remap,
                )
            except Exception:
                # Structural work is a recoverable child artifact.  A fan-in
                # defect must not turn a completed recursive pass into an
                # action/session failure; verified helpers and the ordinary
                # settlement paths remain authoritative.
                structural_merge_error_count += 1
                self._bump_metric(
                    session,
                    "mini_session_graph_recursive_decompose_structural_merge_errors",
                )
                return
            for key in structural_progress_counts:
                structural_progress_counts[key] += int(merged.get(key, 0) or 0)

        async def publish_subpass_progress(
            reason: str,
            state: Optional[dict[str, Any]] = None,
        ) -> None:
            del reason

            def prepare_state() -> None:
                if state is not None:
                    self._recursive_driver_state = copy.deepcopy(dict(state))
                if (
                    parent_dossier is None
                    or sub_dossier is parent_dossier
                ):
                    return
                sub_helper_items = list(
                    (getattr(sub_dossier, "verified_helpers", {}) or {}).items()
                )
                for name, helper in dependency_ordered_verified_helper_items(
                    sub_helper_items
                ):
                    was_existing = name in getattr(
                        parent_dossier,
                        "verified_helpers",
                        {},
                    )
                    recorded = parent_dossier.record_imported_verified_helper(
                        helper
                    )
                    recorded_name = str(
                        getattr(recorded, "name", "") or ""
                    ).strip()
                    if (
                        not was_existing
                        and recorded_name
                        and recorded_name not in merged_helper_names
                    ):
                        merged_helper_names.append(recorded_name)
                propagate_invalidated_statements(
                    parent_dossier,
                    sub_dossier,
                    record_graph=False,
                )
                parent_dossier.mini_recursive_exhausted_claim_keys.update(
                    set(
                        getattr(
                            sub_dossier,
                            "mini_recursive_exhausted_claim_keys",
                            set(),
                        )
                        or ()
                    )
                )
                merge_subpass_structure()
                merge_relevant_child_proof_ideas(
                    parent_dossier,
                    sub_dossier,
                    proof_idea_ids=child_proof_idea_ids,
                    source_to_target_node_id=structural_node_id_remap,
                    branch_source="graph-recursive-child",
                    branch_key=child_proof_idea_branch_id,
                )
            prepare_state()
            persist_cutpoint = getattr(
                session,
                "_record_pre_select_snapshot",
                None,
            )
            if callable(persist_cutpoint):
                persist_cutpoint()

        # Allocate only after all synchronous sub-pass setup succeeds. From
        # this point onward the try/finally owns every debit, stack frame,
        # reservation, and consumed frontier key.
        remaining_before = self._budget_remaining(session)
        frontier_key_fn = getattr(session, "_frontier_action_key", None)
        consumed_keys = getattr(session, "consumed_frontier_action_keys", None)
        consumed_frontier_action_key = None
        if callable(frontier_key_fn) and consumed_keys is not None:
            try:
                consumed_frontier_action_key = frontier_key_fn(item, self.id)
                consumed_keys.add(consumed_frontier_action_key)
            except Exception:
                pass
        self._reserve_inflight(
            session,
            ancestor_key=ancestor_key,
            consumed_frontier_action_key=consumed_frontier_action_key,
        )
        self._decrement_budget(session)
        self._bump_metric(
            session, "mini_session_graph_recursive_decompose_invocations"
        )
        if ancestor_key:
            stack.append(ancestor_key)

        sub_pass_interrupted = False
        try:
            result = await run_mini_recursive_attempt(
                theorem_name=obligation_theorem_name,
                root_statement=statement,
                problem_text=problem_text,
                lean_signature=obligation_lean_signature,
                prover_client=getattr(session, "prover_client", None),
                refiner_client=getattr(session, "refiner_client", None),
                planner_escalation_client=getattr(
                    session, "planner_escalation_client", None
                ),
                lean=getattr(session, "lean", None),
                llm_preamble=str(getattr(session.conv, "preamble", "") or ""),
                lean_preamble=str(getattr(session.conv, "lean_preamble", "") or ""),
                attempt_dossier=sub_dossier,
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
                selected_parent_proof_idea_context=(
                    selected_parent_proof_idea_context
                ),
                proof_state_child_goal_limit=self.proof_state_child_goal_limit,
                proof_state_decl_application_limit=self.proof_state_decl_application_limit,
                proof_state_batch_parallelism=self.proof_state_batch_parallelism,
                recorder=getattr(session, "recorder", None),
                searcher=getattr(session, "searcher", None),
                proof_cache=getattr(session, "proof_cache", None),
                cache_owner_theorem_name=str(
                    getattr(parent_dossier, "cache_owner_theorem_name", "")
                    or getattr(getattr(session, "problem", None), "theorem_name", "")
                    or ""
                ),
                cost_controller=getattr(session, "cost_controller", None),
                trace_prefix=str(getattr(session, "trace_prefix", "") or ""),
                branch_label=self.phase_label,
                opaque_mode=bool(getattr(session.conv, "opaque_mode", True)),
                allow_official_answer_visibility=bool(
                    getattr(session.conv, "allow_official_answer_visibility", False)
                ),
                official_answer_payload_present=official_answer_payload_present,
                adaptive_fallback=False,
                budget_kind="graph_recursive_decompose",
                config=sub_config,
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
                recursion_depth=recursive_helper_depth,
                strict_progress_accounting=bool(
                    getattr(session, "strict_progress_accounting", False)
                ),
                soft_progress_streak_cap=int(
                    getattr(session, "max_soft_progress_streak", 4) or 0
                ),
                # B-CRIT (Adversary C): suppress root-solved write-back —
                # the proof is for the obligation sub-claim, not the root.
                suppress_root_solved=True,
                progress_callback=publish_subpass_progress,
                verified_helper_accept_callback=getattr(
                    session,
                    "theory_verified_helper_accept_callback",
                    None,
                ),
                continuation_state=(
                    copy.deepcopy(self._recursive_driver_state)
                    if self._recursive_driver_state
                    else None
                ),
                planner_job_broker=(
                    session.planner_job_broker()
                    if callable(getattr(session, "planner_job_broker", None))
                    and (
                        not callable(
                            getattr(
                                session,
                                "owns_planner_split_scheduler",
                                None,
                            )
                        )
                        or session.owns_planner_split_scheduler()
                    )
                    else None
                ),
                planner_frontier_signature=recursive_attempt_context_hash,
                planner_owner_lane_id=f"{self.id}:{obligation_id}",
            )
        except PlannerJobYield as pending:
            # This allocation has reached raw provider I/O but has not
            # completed its mathematical transaction. Re-credit the local
            # pass/frontier reservation in ``finally`` and transfer only the
            # provider operation after this neutral outcome commits.
            sub_pass_interrupted = True
            target_environment_hash = str(
                (
                    getattr(graph.nodes.get(obligation_id), "metadata", {})
                    or {}
                ).get("statement_environment_hash")
                or ""
            ).strip()
            parent_helpers = dict(
                getattr(parent_dossier, "verified_helpers", {}) or {}
            )
            substantive_helpers_added_names = tuple(
                name
                for name in merged_helper_names
                if verified_helper_admission_quality(
                    parent_helpers.get(name, name)
                ).generic_novelty
            )
            helper_progress = bool(substantive_helpers_added_names)
            structural_progress = bool(
                structural_progress_counts["nodes_imported"]
                or structural_progress_counts["edges_imported"]
                or structural_progress_counts["blockers_attached"]
            )
            cutpoint_progress = bool(helper_progress or structural_progress)
            propagated_invalid_reason = self._invalidated_statement_reason(
                session,
                statement,
                target_environment_hash=target_environment_hash,
            )
            if propagated_invalid_reason:
                # The progress callback can import a fresh authoritative
                # invalidation immediately before the provider boundary. The
                # prepared request no longer owns live work, so retire the
                # target without publishing or launching that stale request.
                self._retire_invalidated_obligation(
                    session=session,
                    graph=graph,
                    work_item=item,
                    obligation_id=obligation_id,
                    statement=statement,
                    reason=propagated_invalid_reason,
                    phase="graph_recursive_decompose_planner_yield",
                )
                self._bump_metric(
                    session,
                    (
                        "mini_session_graph_recursive_decompose_"
                        "invalidated_obligation_skipped"
                    ),
                )
                self._recursive_driver_state = {}
                provider_exposure_tracker = getattr(
                    session,
                    "_inflight_provider_exposure_tracker",
                    None,
                )
                try:
                    provider_dispatches_started = max(
                        0,
                        int(
                            getattr(
                                provider_exposure_tracker,
                                "provider_dispatches_started",
                                0,
                            )
                            or 0
                        ),
                    )
                except (TypeError, ValueError):
                    provider_dispatches_started = 1
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=tuple(merged_helper_names),
                    progress=cutpoint_progress,
                    cost_seconds=max(0.0, time.monotonic() - started),
                    metadata={
                        "verdict": (
                            "graph_recursive_planner_target_invalidated"
                        ),
                        "work_type": work_type,
                        "obligation_id": obligation_id,
                        "selected_work_projection_invalidated": True,
                        "selected_work_projection_zero_provider": bool(
                            provider_dispatches_started == 0
                        ),
                        "provider_dispatches_started": (
                            provider_dispatches_started
                        ),
                        "invalid_reason": propagated_invalid_reason,
                        "preserve_action_budget": True,
                        "refund_local_repair_quota": bool(
                            provider_dispatches_started == 0
                        ),
                        "iteration_neutral": True,
                        "scheduler_neutral": not cutpoint_progress,
                        "stagnation_neutral": not cutpoint_progress,
                        "hard_pivot_neutral": True,
                        "helper_progress": helper_progress,
                        "structural_progress": structural_progress,
                        "structural_progress_counts": dict(
                            structural_progress_counts
                        ),
                        "strong_progress": False,
                    },
                )
            live_obligation = (
                graph.nodes.get(obligation_id)
                if obligation_id and hasattr(graph, "nodes")
                else None
            )
            stale_reason = self._stale_planner_target_reason(
                graph,
                live_obligation,
                obligation_id=obligation_id,
                expected_statement_hash=str(
                    pending.launch.identity.root_statement_hash or ""
                ),
            )
            if stale_reason:
                # Helper/structural publication can close, supersede, or
                # replace the target at the same cutpoint that prepares the
                # next planner call. Recheck live graph authority before the
                # launch enters the broker; a later ready-result fence is too
                # late because the avoidable provider cost is already paid.
                self._recursive_driver_state = {}
                provider_exposure_tracker = getattr(
                    session,
                    "_inflight_provider_exposure_tracker",
                    None,
                )
                try:
                    provider_dispatches_started = max(
                        0,
                        int(
                            getattr(
                                provider_exposure_tracker,
                                "provider_dispatches_started",
                                0,
                            )
                            or 0
                        ),
                    )
                except (TypeError, ValueError):
                    provider_dispatches_started = 1
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    helpers_added=tuple(merged_helper_names),
                    progress=cutpoint_progress,
                    cost_seconds=max(0.0, time.monotonic() - started),
                    metadata={
                        "verdict": (
                            "stale_graph_planner_target_retired_before_launch"
                        ),
                        "reason": stale_reason,
                        "work_type": work_type,
                        "obligation_id": obligation_id,
                        "selected_work_projection_invalidated": True,
                        "selected_work_projection_zero_provider": bool(
                            provider_dispatches_started == 0
                        ),
                        "provider_dispatches_started": (
                            provider_dispatches_started
                        ),
                        "preserve_action_budget": True,
                        "refund_local_repair_quota": bool(
                            provider_dispatches_started == 0
                        ),
                        "iteration_neutral": True,
                        "scheduler_neutral": not cutpoint_progress,
                        "stagnation_neutral": not cutpoint_progress,
                        "hard_pivot_neutral": True,
                        "helper_progress": helper_progress,
                        "structural_progress": structural_progress,
                        "structural_progress_counts": dict(
                            structural_progress_counts
                        ),
                        "strong_progress": False,
                    },
                )
            identity = pending.launch.identity
            identity_record = asdict(identity)
            self._planner_job_receipt_identities[
                (identity.job_id, identity.request_fingerprint)
            ] = identity
            prior_phase = str(self._recursive_driver_state.get("phase") or "")
            self._recursive_driver_state.update(
                {
                    "phase": "planner_job_pending",
                    "planner_job_prior_phase": prior_phase,
                    "planner_job_identity": identity_record,
                    "graph_recursive_target": {
                        "obligation_id": obligation_id,
                        "statement_key": ancestor_key,
                        "statement_hash": text_hash(statement),
                        "child_branch_key": child_branch_key,
                        "work_item_record": copy.deepcopy(
                            dict(selected_work_record)
                        ),
                    },
                    "outer_recursive_planner_signature": (
                        recursive_attempt_context_hash
                    ),
                }
            )
            session_ref = weakref.ref(session)

            def reconcile_provider_exposure(count: int) -> None:
                live_session = session_ref()
                if live_session is None:
                    return
                accrue = getattr(
                    live_session,
                    "_accrue_provider_exposure",
                    None,
                )
                if callable(accrue) and int(count or 0) > 0:
                    accrue({"provider_dispatches_started": int(count or 0)})

            self._pending_planner_job_launch = dataclass_replace(
                pending.launch,
                usage_context=llm_usage_context_metadata(),
                reconcile_provider_exposure=reconcile_provider_exposure,
            )
            persist_cutpoint = getattr(
                session,
                "_record_pre_select_snapshot",
                None,
            )
            if callable(persist_cutpoint):
                persist_cutpoint()
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=tuple(merged_helper_names),
                progress=cutpoint_progress,
                cost_seconds=max(0.0, time.monotonic() - started),
                metadata={
                    "planner_job_pending": True,
                    "planner_job_identity": identity_record,
                    "preserve_action_budget": True,
                    "preserve_frontier_work": True,
                    "preserve_selected_frontier_action": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": not cutpoint_progress,
                    "stagnation_neutral": not cutpoint_progress,
                    "hard_pivot_neutral": True,
                    "graph_recursive_planner_yield": True,
                    "helper_progress": helper_progress,
                    "structural_progress": structural_progress,
                    "structural_progress_counts": dict(
                        structural_progress_counts
                    ),
                    # The action reports only an already-published soft delta.
                    # MiniSession.apply remains the sole authority that can
                    # promote accepted helper evidence to strong progress.
                    "strong_progress": False,
                },
            )
        except asyncio.CancelledError:
            sub_pass_interrupted = True
            raise
        except Exception as exc:
            # B-CRIT (Adversary B): exception out of the sub-pass must NOT
            # break the MiniOutcome contract. Capture, treat as failure.
            sub_pass_exception = exc
        finally:
            if sub_pass_interrupted:
                # Return the live allocation before cancellation escapes to a
                # reusable in-process session.
                self._recover_inflight_reservation(session)
            else:
                if ancestor_key and stack and stack[-1] == ancestor_key:
                    stack.pop()
                self._clear_inflight_reservation(session)

        success = bool(getattr(result, "ok", False))
        verified_helpers_added = len(merged_helper_names)
        helpers_added_names: List[str] = list(merged_helper_names)
        if parent_dossier is not None and sub_dossier is not parent_dossier:
            sub_helper_items = list(
                (getattr(sub_dossier, "verified_helpers", {}) or {}).items()
            )
            for name, helper in dependency_ordered_verified_helper_items(
                sub_helper_items
            ):
                was_existing = name in getattr(
                    parent_dossier,
                    "verified_helpers",
                    {},
                )
                try:
                    recorded_helper = (
                        parent_dossier.record_imported_verified_helper(helper)
                    )
                    if recorded_helper is not None and not was_existing:
                        visible_checker = getattr(
                            parent_dossier,
                            "is_verified_helper_context_visible",
                            None,
                        )
                        if callable(visible_checker) and not bool(
                            visible_checker(recorded_helper)
                        ):
                            self._bump_metric(
                                session,
                                "mini_session_graph_recursive_decompose_advisory_helpers_suppressed",
                            )
                            continue
                        verified_helpers_added += 1
                        recorded_name = str(
                            getattr(recorded_helper, "name", "") or name or ""
                        ).strip()
                        if recorded_name and recorded_name not in helpers_added_names:
                            helpers_added_names.append(recorded_name)
                except Exception:
                    continue
            try:
                propagate_invalidated_statements(
                    parent_dossier,
                    sub_dossier,
                    record_graph=False,
                )
            except Exception:
                pass
            parent_dossier.mini_recursive_exhausted_claim_keys.update(
                set(
                    getattr(
                        sub_dossier,
                        "mini_recursive_exhausted_claim_keys",
                        set(),
                    )
                    or ()
                )
            )
            merge_subpass_structure()
            merge_relevant_child_proof_ideas(
                parent_dossier,
                sub_dossier,
                proof_idea_ids=child_proof_idea_ids,
                source_to_target_node_id=structural_node_id_remap,
                branch_source="graph-recursive-child",
                branch_key=child_proof_idea_branch_id,
            )
        propagated_invalid_reason = self._invalidated_statement_reason(
            session,
            statement,
            target_environment_hash=str(
                (
                    getattr(graph.nodes.get(obligation_id), "metadata", {})
                    or {}
                ).get("statement_environment_hash")
                or ""
            ).strip(),
        )
        if propagated_invalid_reason and not success:
            self._retire_invalidated_obligation(
                session=session,
                graph=graph,
                work_item=item,
                obligation_id=obligation_id,
                statement=statement,
                reason=propagated_invalid_reason,
                phase="graph_recursive_decompose_subpass",
            )
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_invalidated_obligation_skipped",
            )
        proof_text = str(getattr(result, "proof", "") or "").strip()
        terminal_failure_reason = str(
            getattr(result, "failure_reason", "") or ""
        ).strip()
        terminal_failure_kind = ""
        terminal_failure_metadata: dict[str, Any] = {}
        result_stats = getattr(result, "stats", None)
        use_latest_scoped_failure = terminal_failure_reason in {
            "",
            "recursive_passes_exhausted",
        }
        for reason_attr, kind_attr, metadata_attr in (
            (
                "last_child_failure_reason",
                "last_child_failure_kind",
                "last_child_failure_metadata",
            ),
            (
                "last_planner_failure_reason",
                "last_planner_failure_kind",
                "last_planner_failure_metadata",
            ),
        ):
            stats_reason = str(
                getattr(result_stats, reason_attr, "") or ""
            ).strip()
            if llm_failure_scope(stats_reason) != "scoped":
                continue
            if not (
                use_latest_scoped_failure
                or stats_reason == terminal_failure_reason
            ):
                # Stats are cumulative across recursive passes. Never project
                # a stale provider failure over a distinct current result.
                continue
            terminal_failure_reason = stats_reason
            terminal_failure_kind = str(
                getattr(result_stats, kind_attr, "") or ""
            ).strip()
            raw_failure_metadata = getattr(
                result_stats,
                metadata_attr,
                {},
            )
            if isinstance(raw_failure_metadata, dict):
                terminal_failure_metadata = dict(raw_failure_metadata)
            break
        if sub_pass_exception is not None:
            classification = classify_llm_exception(sub_pass_exception)
            if classification.failure_reason:
                terminal_failure_reason = classification.failure_reason
                terminal_failure_kind = classification.kind
                terminal_failure_metadata = {
                    "llm_retryable": bool(classification.retryable),
                    "llm_failure_kind": str(classification.kind or ""),
                }
        terminal_failure = is_terminal_llm_failure_reason(terminal_failure_reason)
        failure_scope = llm_failure_scope(terminal_failure_reason)
        scoped_failure_reason = (
            terminal_failure_reason if failure_scope == "scoped" else ""
        )
        scoped_failure_retryable = projected_scoped_llm_failure_is_retryable(
            reason=scoped_failure_reason,
            kind=terminal_failure_kind,
            metadata=terminal_failure_metadata,
        )
        zero_provider_failure = bool(
            scoped_failure_retryable
            and terminal_failure_metadata.get("zero_provider_failure")
            and int(
                terminal_failure_metadata.get("provider_calls_completed", 0)
                or 0
            )
            == 0
        )
        if zero_provider_failure:
            # The recursive allocation reached no provider response and did
            # no mathematical work. Reopen this exact sub-pass while the
            # scheduler durably backs off the selected frontier action.
            session.graph_recursive_decompose_remaining = remaining_before
        # B-HIGH (Adversary B): ok=True with empty proof must NOT write back —
        # would mark obligation proved with empty source_hash and cascade to
        # phantom replan resolution.
        if success and not proof_text:
            success = False

        helper_name = ""
        if success and obligation_id:
            helper_recorder = getattr(
                getattr(session, "dossier", None),
                "record_verified_helper",
                None,
            )
            if not callable(helper_recorder):
                success = False

        if success and obligation_id:
            suggested_name = (
                f"graph_recursive_{getattr(session.problem, 'theorem_name', 't')}"
                f"_{obligation_id.replace(':', '_')[:48]}"
            )
            helper_name = unique_dossier_helper_name(
                getattr(session, "dossier", None),
                suggested_name,
            )
            helper_block = helper_decl_from_proof(helper_name, statement, proof_text)
            blocks_getter = getattr(
                getattr(session, "dossier", None),
                "verified_helper_blocks",
                None,
            )
            helper_context = list(blocks_getter() if callable(blocks_getter) else [])
            support_names = _support_names_for_proof(helper_context, proof_text)
            helper_item = None
            try:
                helper_item = helper_recorder(
                    helper_block,
                    phase="graph_recursive_decompose",
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    support_names=support_names,
                )
            except Exception:
                helper_item = None
            if helper_item is None:
                success = False
            elif not bool(
                getattr(
                    getattr(session, "dossier", None),
                    "is_verified_helper_context_visible",
                    lambda _helper: True,
                )(helper_item)
            ):
                self._bump_metric(
                    session,
                    "mini_session_graph_recursive_decompose_advisory_helpers_suppressed",
                )
                success = False
            else:
                recorded_name = str(
                    getattr(helper_item, "name", "") or helper_name or ""
                ).strip()
                if recorded_name and recorded_name not in helpers_added_names:
                    helpers_added_names.append(recorded_name)
                proof_hash = str(getattr(helper_item, "source_hash", "") or "")
                if not proof_hash:
                    success = False

        if success and obligation_id:
            mark = getattr(graph, "mark_obligation_proved_by_helper", None)
            if callable(mark):
                try:
                    helper_node_id = ""
                    helper_node_lookup = getattr(graph, "helper_name_to_node_id", None)
                    if isinstance(helper_node_lookup, dict):
                        helper_node_id = str(
                            helper_node_lookup.get(helper_name, "") or ""
                        )
                    mark(
                        obligation_id,
                        helper_node_id=helper_node_id,
                        source_hash=proof_hash,
                        proof_hash=proof_hash,
                    )
                except Exception:
                    success = False
            else:
                success = False
        structural_progress = bool(
            structural_progress_counts["nodes_imported"]
            or structural_progress_counts["edges_imported"]
            or structural_progress_counts["blockers_attached"]
        )
        if (
            not success
            and not terminal_failure
            and not scoped_failure_reason
            and not structural_progress
        ):
            # Record an attempt so downstream consumers can see why the
            # obligation is still open. Covers all failure paths including
            # sub-pass exceptions and empty-proof rejection.
            record_attempt = getattr(graph, "record_attempt", None)
            if callable(record_attempt) and obligation_id:
                err_type = (
                    "recursive_decomposition_exception"
                    if sub_pass_exception is not None
                    else "recursive_decomposition_exhausted"
                )
                try:
                    record_attempt(
                        obligation_id,
                        phase="graph_recursive_decompose",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        proof="",
                        verdict="recursive_decomposition_failed",
                        error_type=err_type,
                        source=self.id,
                        metadata={
                            "statement_key": ancestor_key,
                            "helper_context_hash": helper_context_hash,
                            "recursive_attempt_context_hash": (
                                recursive_attempt_context_hash
                            ),
                            "work_type": work_type,
                        },
                    )
                except Exception:
                    pass
        elif scoped_failure_reason:
            record_attempt = getattr(graph, "record_attempt", None)
            if callable(record_attempt) and obligation_id:
                try:
                    record_attempt(
                        obligation_id,
                        phase="graph_recursive_decompose",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        proof="",
                        verdict="recursive_decomposition_llm_deferred",
                        error_type=scoped_failure_reason,
                        source=self.id,
                        metadata={
                            "statement_key": ancestor_key,
                            "helper_context_hash": helper_context_hash,
                            "recursive_attempt_context_hash": (
                                recursive_attempt_context_hash
                            ),
                            "work_type": work_type,
                            "llm_failure_scope": "scoped",
                            "scoped_failure_reason": scoped_failure_reason,
                        },
                    )
                except Exception:
                    pass

        obligation_proved = False
        if success:
            refreshed = graph.nodes.get(obligation_id) if obligation_id else None
            if refreshed is not None and str(
                getattr(refreshed, "status", "") or ""
            ) == "proved":
                obligation_proved = True

        parent_helpers = dict(
            getattr(parent_dossier, "verified_helpers", {}) or {}
        )
        substantive_helpers_added_names = tuple(
            name
            for name in helpers_added_names
            if verified_helper_admission_quality(
                parent_helpers.get(name, name)
            ).generic_novelty
        )
        helper_progress = bool(substantive_helpers_added_names)
        helper_strong_progress = bool(
            helper_progress
            and strong_progress_for_accepted_helpers(
                getattr(session, "dossier", None),
                substantive_helpers_added_names,
            )
        )
        progress = bool(
            obligation_proved or helper_progress or structural_progress
        )

        if obligation_proved:
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_obligations_proved"
            )
        if helper_progress:
            self._bump_metric(
                session,
                "mini_session_graph_recursive_decompose_helpers_propagated",
                len(substantive_helpers_added_names),
            )
        if not obligation_proved:
            self._bump_metric(
                session, "mini_session_graph_recursive_decompose_failures"
            )

        if helper_progress and not obligation_proved and obligation_id:
            record_attempt = getattr(graph, "record_attempt", None)
            if callable(record_attempt):
                try:
                    helper_source_hashes = {
                        name: str(
                            getattr(
                                dict(
                                    getattr(parent_dossier, "verified_helpers", {})
                                    or {}
                                ).get(name),
                                "source_hash",
                                "",
                            )
                            or ""
                        )
                        for name in helpers_added_names
                    }
                    locally_generated_hashes = frozenset(
                        {
                            *self._prior_helper_only_source_hashes(
                                graph,
                                obligation_id,
                                statement_key=ancestor_key,
                            ),
                            *(
                                value
                                for value in helper_source_hashes.values()
                                if value
                            ),
                        }
                    )
                    record_attempt(
                        obligation_id,
                        phase="graph_recursive_decompose",
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        proof="",
                        verdict="recursive_decomposition_helpers_propagated",
                        error_type="obligation_still_open",
                        source=self.id,
                        metadata={
                            "statement_key": ancestor_key,
                            "helper_context_hash": helper_context_hash,
                            "recursive_attempt_context_hash": (
                                recursive_attempt_context_hash
                            ),
                            "helper_only_environment_hash": (
                                self._helper_only_environment_hash(
                                    session,
                                    excluded_helper_source_hashes=(
                                        locally_generated_hashes
                                    ),
                                )
                            ),
                            "work_type": work_type,
                            "helpers_added": list(helpers_added_names),
                            "helper_source_hashes": helper_source_hashes,
                        },
                    )
                except Exception:
                    pass

        verdict = (
            "obligation_proved_by_recursive_decomposition"
            if obligation_proved
            else "recursive_decomposition_helpers_propagated"
            if helper_progress
            else "recursive_decomposition_structural_progress"
            if structural_progress
            else "recursive_decomposition_failed"
        )

        return MiniOutcome(
            action_id=self.id,
            solved=False,  # never marks ROOT solved
            proof=None,
            helpers_added=tuple(helpers_added_names),
            progress=progress,
            cost_seconds=time.monotonic() - started,
            metadata={
                **terminal_failure_metadata,
                "verdict": verdict,
                "work_type": work_type,
                "obligation_id": obligation_id,
                "obligation_theorem_name": obligation_theorem_name,
                "depth_reached": depth_before + 1,
                "sub_dossier_helpers_added": verified_helpers_added,
                "helpers_added": list(helpers_added_names),
                "obligation_proved": obligation_proved,
                "structural_progress": structural_progress,
                "structural_progress_counts": dict(structural_progress_counts),
                "structural_merge_error_count": structural_merge_error_count,
                "strong_progress": bool(obligation_proved or helper_strong_progress),
                "preserve_selected_frontier_action": bool(
                    helper_progress and not obligation_proved
                ),
                "terminal_failure": terminal_failure,
                "terminal_failure_reason": (
                    terminal_failure_reason if terminal_failure else ""
                ),
                "scoped_failure_reason": scoped_failure_reason,
                "llm_failure_scope": failure_scope,
                "llm_failure_kind": terminal_failure_kind,
                "llm_retryable": scoped_failure_retryable,
                "recursive_zero_provider_budget_refunded": zero_provider_failure,
                "preserve_frontier_work": bool(terminal_failure or scoped_failure_reason),
                "defer_selected_frontier_action": bool(scoped_failure_reason),
                "selected_work_item": dict(
                    selected_work_record
                ),
            },
        )
