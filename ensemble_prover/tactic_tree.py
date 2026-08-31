"""State-aware tactic tree search with beam and MCTS.

Maintains a tree of tactic applications where each node carries the full
Lean goal state.  Sorry-based goal extraction provides cheap intermediate
states; full Lean verification is reserved for candidate solutions.
"""

from __future__ import annotations

import asyncio
import hashlib
import json
import logging
import math
import re
import time
from dataclasses import asdict, dataclass, field, fields
from enum import IntEnum, auto
from typing import Any, Awaitable, Callable, Dict, List, Optional, Protocol, Tuple, Union

from .lean_parser import (
    PATTERN_EQUALITY,
    PATTERN_LE_GE,
    GoalStateFeatures,
    LeanDiagnostic,
    LeanGoalState,
    LeanParseResult,
    extract_goal_state_features,
)
from .math_utils import clamp_probability
from .runtime_context import hard_timeout_writeback_allowed
from .search import SearchProgress, ShouldContinueFunc, _await_with_hard_timeout
from .search_utils import MCTSScoreMixin, make_node_id, tactics_to_proof

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Type aliases for callable hooks
# ---------------------------------------------------------------------------


class TacticTreeEnsembleScorer(Protocol):
    """Minimal scoring capability accepted by the tactic-tree adapter."""

    def tactic_tree_ensemble_signal(
        self,
        statement: str,
        tactic: str,
        *,
        weight_ensemble: float,
    ) -> float: ...

# Generates multiple tactic candidates for a goal state.
# (statement, goals, tactics_so_far) -> List[(tactic, confidence)]
GenMultiTacticFunc = Callable[
    [str, List[LeanGoalState], Tuple[str, ...]],
    Awaitable[List[Tuple[str, float]]],
]
BeamGenMultiTacticFunc = Callable[
    [str, List[LeanGoalState], Tuple[str, ...]],
    Awaitable[Union[List[Tuple[str, float]], "TacticPolicyBatch"]],
]

# Sorry-check: returns goal state after applying tactics.
# (statement, tactics_tuple) -> (goals, features, parse_result, is_complete)
SorryCheckFunc = Callable[
    [str, Tuple[str, ...]],
    Awaitable[Tuple[List[LeanGoalState], GoalStateFeatures, LeanParseResult, bool]],
]

# Full verification check: confirms proof is complete.
# (statement, proof_code) -> (ok, output)
FullCheckFunc = Callable[
    [str, str],
    Awaitable[Tuple[bool, str]],
]

# Composite scoring for a tactic node.
# (node, statement) -> float
ScoreNodeFunc = Callable[
    ["TacticNode", str],
    float,
]

# Value estimate for a state (node) independent of action expansion.
# (node, statement) -> value in [0, 1]
ValueNodeFunc = Callable[
    ["TacticNode", str],
    float,
]
DurableProgressFunc = Callable[[str, "TacticBeamState", Dict[str, Any]], Awaitable[None]]


class TacticOperationTimeout(TimeoutError):
    """One provider/Lean candidate operation expired, not the search budget."""

    def __init__(self, operation: str) -> None:
        self.operation = str(operation or "candidate_operation")
        super().__init__(self.operation)


@dataclass(frozen=True)
class TacticPolicyBatch:
    """One policy response, including whether generation was authoritative.

    Legacy generators return a bare list, which means ``complete=True``.
    Mini returns an incomplete batch when its learned provider failed so cheap
    deterministic candidates can run without permanently caching a degraded
    policy or misclassifying an outage as mathematical exhaustion.
    """

    candidates: Tuple[Tuple[str, float], ...]
    complete: bool = True
    retryable_kind: str = ""


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------


class TacticNodeStatus(IntEnum):
    OPEN = auto()
    EXPANDED = auto()
    SOLVED = auto()
    FAILED = auto()
    PRUNED = auto()


@dataclass
class CachedGoalState:
    """Cached result of a sorry-check for a tactic sequence."""

    goals: List[LeanGoalState]
    features: GoalStateFeatures
    parse_result: LeanParseResult
    ok: bool
    completion_rejected: bool = False
    completion_pending: bool = False


@dataclass
class TacticNode(MCTSScoreMixin):
    """A node in the tactic proof tree.

    Root = initial goal state.  Each edge = a single tactic application.
    """

    node_id: str
    parent_id: Optional[str]
    depth: int
    tactic: Optional[str]
    tactics_from_root: Tuple[str, ...]
    goals: List[LeanGoalState]
    features: GoalStateFeatures
    status: TacticNodeStatus
    children: List[str] = field(default_factory=list)

    # Scoring
    prior: float = 0.5
    ensemble_score: float = 0.0
    composite_score: float = 0.0
    value_estimate: float = 0.0
    novelty_score: float = 1.0
    selection_score: float = 0.0
    dead_end_reason: str = ""

    # MCTS
    visits: int = 0
    total_reward: float = 0.0


@dataclass
class TacticBeamState:
    """Crash-safe continuation state for one bounded beam-search context.

    Node and transition authority is embedded as a versioned ``TacticTree``
    record.  ``beam_node_ids`` and ``reserve_node_ids`` are scheduling hints
    over those exact-prefix nodes; they never substitute displayed goals for
    Lean execution identity.
    """

    tree_record: Dict[str, Any]
    beam_node_ids: Tuple[str, ...]
    reserve_node_ids: Tuple[str, ...]
    stats: Dict[str, int]
    recovery_node_ids: Tuple[str, ...] = ()
    step: int = 0
    best_score: float = 0.0
    best_score_elapsed_s: float = 0.0
    elapsed_s: float = 0.0
    saw_max_depth: bool = False
    schema_version: int = 1

    def to_record(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "tree": dict(self.tree_record),
            "beam_node_ids": list(self.beam_node_ids),
            "reserve_node_ids": list(self.reserve_node_ids),
            "recovery_node_ids": list(self.recovery_node_ids),
            "stats": {str(key): int(value) for key, value in self.stats.items()},
            "step": int(self.step),
            "best_score": float(self.best_score),
            "best_score_elapsed_s": float(self.best_score_elapsed_s),
            "elapsed_s": float(self.elapsed_s),
            "saw_max_depth": bool(self.saw_max_depth),
        }

    def has_live_work(self) -> bool:
        """Whether this exact checkpoint still owns an executable frontier."""

        tree = TacticTree.from_execution_record(self.tree_record)
        return any(
            tree.nodes[node_id].status == TacticNodeStatus.OPEN
            for node_id in dict.fromkeys(
                (*self.beam_node_ids, *self.reserve_node_ids, *self.recovery_node_ids)
            )
            if node_id in tree.nodes
        )

    def canonicalized_frontier(
        self,
        *,
        additional_beam_node_ids: Tuple[str, ...] = (),
        recover_unowned_open_nodes: bool = False,
        max_active_beam_nodes: Optional[int] = None,
    ) -> "TacticBeamState":
        """Return a checkpoint whose scheduler owns only live nodes.

        Search mutates node status before every possible timeout/cutpoint.  A
        snapshot must therefore derive ownership from the serialized tree,
        not blindly retain the loop's stale Python lists.  During legacy
        recovery, every otherwise-unowned OPEN node is retained as active
        work so a checkpoint repair cannot silently discard checked states.
        """

        tree = TacticTree.from_execution_record(self.tree_record)
        seen: set[str] = set()

        def live_unique(node_ids: Tuple[str, ...]) -> List[str]:
            result: List[str] = []
            for raw_id in node_ids:
                node_id = str(raw_id or "")
                node = tree.nodes.get(node_id)
                if (
                    not node_id
                    or node_id in seen
                    or node is None
                    or node.status != TacticNodeStatus.OPEN
                ):
                    continue
                seen.add(node_id)
                result.append(node_id)
            return result

        beam_ids = live_unique(
            tuple(self.beam_node_ids) + tuple(additional_beam_node_ids)
        )
        reserve_ids = live_unique(tuple(self.reserve_node_ids))
        recovery_ids = live_unique(tuple(self.recovery_node_ids))
        if max_active_beam_nodes is not None:
            beam_cap = max(1, int(max_active_beam_nodes))
            overflow = beam_ids[beam_cap:]
            beam_ids = beam_ids[:beam_cap]
            recovery_ids.extend(overflow)
        if recover_unowned_open_nodes:
            unowned = sorted(
                (
                    node
                    for node in tree.nodes.values()
                    if node.status == TacticNodeStatus.OPEN
                    and node.node_id not in seen
                ),
                key=lambda node: (
                    node.depth,
                    node.tactics_from_root,
                    node.node_id,
                ),
            )
            orphan_ids = [node.node_id for node in unowned]
            if max_active_beam_nodes is None:
                beam_ids.extend(orphan_ids)
            else:
                available = max(
                    0,
                    max(1, int(max_active_beam_nodes)) - len(beam_ids),
                )
                beam_ids.extend(orphan_ids[:available])
                recovery_ids.extend(orphan_ids[available:])

        return TacticBeamState(
            tree_record=tree.to_execution_record(),
            beam_node_ids=tuple(beam_ids),
            reserve_node_ids=tuple(reserve_ids),
            stats=dict(self.stats),
            recovery_node_ids=tuple(recovery_ids),
            step=self.step,
            best_score=self.best_score,
            best_score_elapsed_s=self.best_score_elapsed_s,
            elapsed_s=self.elapsed_s,
            saw_max_depth=self.saw_max_depth,
            schema_version=self.schema_version,
        )

    def rejecting_solution(
        self,
        tactics: Tuple[str, ...],
    ) -> "TacticBeamState":
        """Return a continuation that backtracks from an acceptance veto."""

        tree = TacticTree.from_execution_record(self.tree_record)
        prefix = tuple(str(item) for item in tactics)
        solved = next(
            (
                node
                for node in tree.nodes.values()
                if node.tactics_from_root == prefix
                and node.status == TacticNodeStatus.SOLVED
            ),
            None,
        )
        if solved is None:
            raise ValueError("acceptance veto does not match a solved tactic prefix")
        solved.status = TacticNodeStatus.FAILED
        solved.dead_end_reason = "authoritative_acceptance_veto"
        cached = tree.get_cache(prefix)
        if cached is not None:
            cached.ok = False
            cached.completion_rejected = True
            cached.completion_pending = False
        return TacticBeamState(
            tree_record=tree.to_execution_record(),
            beam_node_ids=self.beam_node_ids,
            reserve_node_ids=self.reserve_node_ids,
            stats=dict(self.stats),
            recovery_node_ids=self.recovery_node_ids,
            step=self.step,
            best_score=self.best_score,
            best_score_elapsed_s=self.best_score_elapsed_s,
            elapsed_s=self.elapsed_s,
            saw_max_depth=self.saw_max_depth,
        ).canonicalized_frontier()

    @classmethod
    def from_record(cls, record: Dict[str, Any]) -> "TacticBeamState":
        data = dict(record or {})
        if int(data.get("schema_version", 0) or 0) != 1:
            raise ValueError("unsupported tactic beam checkpoint schema")
        tree_record = data.get("tree")
        if not isinstance(tree_record, dict):
            raise ValueError("tactic beam checkpoint is missing its tree")
        return cls(
            tree_record=dict(tree_record),
            beam_node_ids=tuple(str(item) for item in data.get("beam_node_ids") or ()),
            reserve_node_ids=tuple(
                str(item) for item in data.get("reserve_node_ids") or ()
            ),
            stats={
                str(key): int(value)
                for key, value in dict(data.get("stats") or {}).items()
            },
            recovery_node_ids=tuple(
                str(item) for item in data.get("recovery_node_ids") or ()
            ),
            step=max(0, int(data.get("step", 0) or 0)),
            best_score=_checkpoint_float(
                data.get("best_score", 0.0) or 0.0,
                field_name="beam best score",
            ),
            best_score_elapsed_s=max(
                0.0,
                _checkpoint_float(
                    data.get("best_score_elapsed_s", 0.0) or 0.0,
                    field_name="beam best-score elapsed time",
                ),
            ),
            elapsed_s=max(
                0.0,
                _checkpoint_float(
                    data.get("elapsed_s", 0.0) or 0.0,
                    field_name="beam elapsed time",
                ),
            ),
            saw_max_depth=bool(data.get("saw_max_depth")),
        )


@dataclass
class TacticSearchResult:
    """Result of a tactic tree search."""

    solved: bool
    proof: Optional[str]
    tactics: Optional[Tuple[str, ...]]
    nodes_created: int
    nodes_expanded: int
    max_depth_reached: int
    cache_hits: int
    lean_checks: int
    exit_reason: str = ""
    value_estimates: int = 0
    diversity_pruned: int = 0
    backtracks: int = 0
    operation_timeouts: int = 0
    infrastructure_failures: int = 0
    completion_rejections: int = 0
    bottlenecks: Tuple[Dict[str, Any], ...] = ()
    resume_state: Optional[TacticBeamState] = None


def _cap_tactic_candidates(
    candidates: List[Tuple[str, float]],
    max_candidates_per_node: int,
) -> List[Tuple[str, float]]:
    """Deduplicate exact actions, then keep the highest-prior candidates."""
    unique: List[Tuple[str, float]] = []
    index_by_tactic: Dict[str, int] = {}
    for tactic, prior in candidates:
        clean = str(tactic or "").strip()
        if not clean:
            continue
        normalized_prior = clamp_probability(prior, default=0.0)
        existing_index = index_by_tactic.get(clean)
        if existing_index is None:
            index_by_tactic[clean] = len(unique)
            unique.append((clean, normalized_prior))
            continue
        if normalized_prior > unique[existing_index][1]:
            unique[existing_index] = (clean, normalized_prior)
    cap = int(max_candidates_per_node or 0)
    if cap <= 0 or len(unique) <= cap:
        return unique
    ranked = sorted(
        enumerate(unique),
        key=lambda item: (-clamp_probability(item[1][1], default=0.0), item[0]),
    )
    return [candidate for _idx, candidate in ranked[:cap]]


# ---------------------------------------------------------------------------
# TacticTree
# ---------------------------------------------------------------------------


class TacticTree:
    """Manages the tactic proof tree and caches sorry-check results."""

    def __init__(
        self,
        statement: str,
        initial_goals: List[LeanGoalState],
        max_depth: int = 25,
        max_cache: int = 10000,
    ) -> None:
        self.statement = statement
        self.max_depth = max_depth
        self._max_cache = max_cache
        self.nodes: Dict[str, TacticNode] = {}
        # Cache of sorry-check results keyed by full tactic sequence (legacy).
        self._cache: Dict[Tuple[str, ...], CachedGoalState] = {}
        # Canonical goal-state transposition table: best-known (shallowest) depth.
        self._state_depth: Dict[str, int] = {}
        # Policy cache keyed by canonical goal-state key.
        self._policy_cache: Dict[Tuple[str, Tuple[str, ...]], List[Tuple[str, float]]] = {}
        # Value cache keyed by canonical goal-state key.
        self._value_cache: Dict[str, float] = {}
        # Transition cache: (state_key, tactic) -> resulting cached goal state.
        # This enables reusing Lean sorry-check work across different tactic
        # sequences that reach the same goal state.
        self._transition_cache: Dict[Tuple[str, str], CachedGoalState] = {}
        self.initial_goal_count = max(1, len(initial_goals))

        root_features = extract_goal_state_features(initial_goals, initial_goals)
        root_id = make_node_id()
        self.root_id = root_id
        self.nodes[root_id] = TacticNode(
            node_id=root_id,
            parent_id=None,
            depth=0,
            tactic=None,
            tactics_from_root=(),
            goals=initial_goals,
            features=root_features,
            status=TacticNodeStatus.OPEN,
            prior=1.0,
        )
        root_key = _goal_state_key(initial_goals)
        self._state_depth[root_key] = 0

    def to_execution_record(self) -> Dict[str, Any]:
        """Encode exact-prefix execution state for durable same-context resume."""

        return {
            "schema_version": 1,
            "statement": self.statement,
            "statement_hash": _text_sha256(self.statement),
            "max_depth": int(self.max_depth),
            "max_cache": int(self._max_cache),
            "initial_goal_count": int(self.initial_goal_count),
            "root_id": self.root_id,
            "nodes": [
                _tactic_node_to_record(self.nodes[node_id])
                for node_id in sorted(self.nodes)
            ],
            "prefix_receipts": [
                {
                    "tactics": list(prefix),
                    "state": _cached_goal_state_to_record(state),
                }
                for prefix, state in sorted(self._cache.items())
            ],
            "policy_cache": [
                {
                    "state_key": state_key,
                    "tactics_from_root": list(prefix),
                    "candidates": [[tactic, float(prior)] for tactic, prior in value],
                }
                for (state_key, prefix), value in sorted(self._policy_cache.items())
            ],
            "state_depth": {
                str(key): int(value)
                for key, value in sorted(self._state_depth.items())
            },
        }

    @classmethod
    def from_execution_record(
        cls,
        record: Dict[str, Any],
        *,
        expected_statement: Optional[str] = None,
    ) -> "TacticTree":
        """Restore a tree, rejecting schema/context/topology corruption."""

        data = dict(record or {})
        if int(data.get("schema_version", 0) or 0) != 1:
            raise ValueError("unsupported tactic tree checkpoint schema")
        statement = str(data.get("statement") or "")
        if str(data.get("statement_hash") or "") != _text_sha256(statement):
            raise ValueError("tactic tree statement hash mismatch")
        if expected_statement is not None and statement != str(expected_statement):
            raise ValueError("tactic tree checkpoint belongs to another statement")
        node_records = list(data.get("nodes") or ())
        if not node_records:
            raise ValueError("tactic tree checkpoint has no nodes")

        tree = cls.__new__(cls)
        tree.statement = statement
        tree.max_depth = max(0, int(data.get("max_depth", 0) or 0))
        tree._max_cache = max(1, int(data.get("max_cache", 10000) or 10000))
        tree.initial_goal_count = max(
            1, int(data.get("initial_goal_count", 1) or 1)
        )
        tree.nodes = {}
        for node_record in node_records:
            node = _tactic_node_from_record(dict(node_record or {}))
            if not node.node_id or node.node_id in tree.nodes:
                raise ValueError("duplicate or empty tactic node id")
            tree.nodes[node.node_id] = node
        tree.root_id = str(data.get("root_id") or "")
        if tree.root_id not in tree.nodes:
            raise ValueError("tactic tree root is missing")
        root = tree.nodes[tree.root_id]
        if root.parent_id is not None or root.depth != 0 or root.tactics_from_root:
            raise ValueError("invalid tactic tree root")
        for node in tree.nodes.values():
            if node.node_id == tree.root_id:
                continue
            parent = tree.nodes.get(str(node.parent_id or ""))
            if parent is None or node.node_id not in parent.children:
                raise ValueError("tactic tree parent/child topology mismatch")
            if node.depth != parent.depth + 1:
                raise ValueError("tactic tree node depth mismatch")
            expected_prefix = parent.tactics_from_root + (str(node.tactic or ""),)
            if node.tactics_from_root != expected_prefix:
                raise ValueError("tactic tree prefix topology mismatch")
        incoming_edges = {node_id: 0 for node_id in tree.nodes}
        for node in tree.nodes.values():
            if len(node.children) != len(set(node.children)):
                raise ValueError("duplicate tactic tree child reference")
            if any(child_id not in tree.nodes for child_id in node.children):
                raise ValueError("tactic tree references a missing child")
            for child_id in node.children:
                child = tree.nodes[child_id]
                if child.parent_id != node.node_id:
                    raise ValueError("tactic tree parent/child topology mismatch")
                incoming_edges[child_id] += 1
        if incoming_edges[tree.root_id] != 0 or any(
            incoming_edges[node_id] != 1
            for node_id in tree.nodes
            if node_id != tree.root_id
        ):
            raise ValueError("tactic tree node has invalid incoming edge count")

        tree._cache = {}
        for receipt in list(data.get("prefix_receipts") or ()):
            receipt_data = dict(receipt or {})
            prefix = tuple(str(item) for item in receipt_data.get("tactics") or ())
            if prefix in tree._cache:
                raise ValueError("duplicate tactic prefix receipt")
            tree._cache[prefix] = _cached_goal_state_from_record(
                dict(receipt_data.get("state") or {})
            )
        # Status labels are not proof certificates.  Durable solved nodes must
        # be backed by the exact-prefix receipt that survived the authoritative
        # full check; scheduled OPEN nodes must still have executable goals.
        for node in tree.nodes.values():
            if node.status == TacticNodeStatus.OPEN and not node.goals:
                raise ValueError("open tactic node has no remaining goals")
            if node.status != TacticNodeStatus.SOLVED:
                continue
            receipt = tree._cache.get(node.tactics_from_root)
            if node.goals:
                raise ValueError("solved tactic node retains goals")
            if (
                receipt is None
                or not receipt.ok
                or receipt.goals
                or receipt.completion_pending
                or receipt.completion_rejected
            ):
                raise ValueError("solved tactic node lacks accepted completion receipt")
        tree._policy_cache = {}
        for policy in list(data.get("policy_cache") or ()):
            policy_data = dict(policy or {})
            key = (
                str(policy_data.get("state_key") or ""),
                tuple(
                    str(item)
                    for item in policy_data.get("tactics_from_root") or ()
                ),
            )
            tree._policy_cache[key] = [
                (str(item[0]), _finite_probability(item[1], default=0.0))
                for item in list(policy_data.get("candidates") or ())
                if isinstance(item, (list, tuple)) and len(item) == 2
            ]
        tree._state_depth = {
            str(key): int(value)
            for key, value in dict(data.get("state_depth") or {}).items()
        }
        tree._value_cache = {}
        tree._transition_cache = {}
        return tree

    @property
    def root(self) -> TacticNode:
        return self.nodes[self.root_id]

    def child_for_tactic(
        self,
        parent_id: str,
        tactic: str,
    ) -> Optional[TacticNode]:
        """Return an already-materialized exact-prefix child, if any."""

        parent = self.nodes[parent_id]
        prefix = parent.tactics_from_root + (str(tactic),)
        for child_id in parent.children:
            child = self.nodes[child_id]
            if child.tactics_from_root == prefix:
                return child
        return None

    def add_child(
        self,
        parent_id: str,
        tactic: str,
        goals: List[LeanGoalState],
        features: GoalStateFeatures,
        prior: float,
    ) -> TacticNode:
        """Add a child node to the tree.

        Raises KeyError if parent_id is not a valid node in this tree.
        """
        parent = self.nodes[parent_id]
        child_tactics = parent.tactics_from_root + (tactic,)
        existing = self.child_for_tactic(parent_id, tactic)
        if existing is not None:
            return existing
        child_id = make_node_id()
        child = TacticNode(
            node_id=child_id,
            parent_id=parent_id,
            depth=parent.depth + 1,
            tactic=tactic,
            tactics_from_root=child_tactics,
            goals=goals,
            features=features,
            status=TacticNodeStatus.OPEN,
            prior=clamp_probability(prior, default=0.5),
        )
        self.nodes[child_id] = child
        parent.children.append(child_id)
        return child

    def should_expand_state(self, goals: List[LeanGoalState], depth: int) -> bool:
        if not goals:
            # Avoid collapsing all empty goal states into one hash bucket.
            return True
        key = _goal_state_key(goals)
        prev_depth = self._state_depth.get(key)
        # Strict inequality: allow re-expansion at the SAME depth (reachable
        # via different tactic sequences) but block deeper re-visits.  The
        # previous <= check blocked same-depth alternatives that could have
        # found a solution the first path missed after being pruned.
        if prev_depth is not None and prev_depth < depth:
            return False
        # Retain shallower states longer; evict deeper duplicates first.
        self._evict_if_full(
            self._state_depth,
            sort_key=lambda k: self._state_depth[k],
            reverse=True,
        )
        self._state_depth[key] = depth
        return True

    def select_leaf_puct(self, c_puct: float = 1.4) -> TacticNode:
        """PUCT tree walk from root to an unexpanded leaf."""
        node = self.root
        while node.children:
            children = [self.nodes[cid] for cid in node.children]
            live = [
                c
                for c in children
                if c.status
                not in (
                    TacticNodeStatus.FAILED,
                    TacticNodeStatus.PRUNED,
                    TacticNodeStatus.SOLVED,
                )
            ]
            if not live:
                # Mark non-root nodes FAILED to prune dead subtrees during
                # selection.  Leave root status unchanged so callers (and the
                # MCTS loop's root-terminal check) see an accurate state.
                if node is not self.root:
                    node.status = TacticNodeStatus.FAILED
                return node
            node = max(live, key=lambda c: c.puct_score(node.visits, c_puct))
        return node

    def backpropagate(self, node_id: str, reward: float) -> None:
        """Propagate reward up the tree from node_id to root.

        Raises KeyError if node_id is not a valid node in this tree.
        """
        nid: Optional[str] = node_id
        while nid is not None:
            node = self.nodes[nid]
            node.backpropagate(reward)
            nid = node.parent_id

    # ---- cache ----

    def _evict_if_full(
        self,
        cache: dict,  # type: ignore[type-arg]
        *,
        sort_key=None,
        reverse: bool = False,
    ) -> None:
        """Evict ~25% of entries from *cache* if at capacity."""
        if len(cache) < self._max_cache:
            return
        evict_count = max(1, len(cache) // 4)
        if sort_key is not None:
            victims = sorted(cache, key=sort_key, reverse=bool(reverse))[:evict_count]
        else:
            victims = list(cache.keys())[:evict_count]
        for k in victims:
            del cache[k]

    def get_cache(self, tactics: Tuple[str, ...]) -> Optional[CachedGoalState]:
        return self._cache.get(tactics)

    def set_cache(self, tactics: Tuple[str, ...], state: CachedGoalState) -> None:
        # Longer tactic histories are less reusable than short prefixes.
        self._evict_if_full(self._cache, sort_key=len, reverse=True)
        self._cache[tactics] = state

    # ---- canonical goal-state caches ----

    def goal_state_key(self, goals: List[LeanGoalState]) -> str:
        """Return canonical key for a goal state."""
        return _goal_state_key(goals)

    def get_policy_cache(
        self,
        goals: List[LeanGoalState],
        tactics_from_root: Tuple[str, ...] = (),
    ) -> Optional[List[Tuple[str, float]]]:
        return self._policy_cache.get(
            (self.goal_state_key(goals), tuple(tactics_from_root))
        )

    def set_policy_cache(
        self,
        goals: List[LeanGoalState],
        candidates: List[Tuple[str, float]],
        tactics_from_root: Tuple[str, ...] = (),
    ) -> None:
        if not candidates:
            return
        self._evict_if_full(self._policy_cache)
        self._policy_cache[
            (self.goal_state_key(goals), tuple(tactics_from_root))
        ] = list(candidates)

    def get_value_cache(self, goals: List[LeanGoalState]) -> Optional[float]:
        return self._value_cache.get(self.goal_state_key(goals))

    def set_value_cache(self, goals: List[LeanGoalState], value: float) -> None:
        self._evict_if_full(self._value_cache)
        self._value_cache[self.goal_state_key(goals)] = float(value)

    def get_transition_cache(
        self, goals: List[LeanGoalState], tactic: str
    ) -> Optional[CachedGoalState]:
        key = (self.goal_state_key(goals), tactic.strip())
        return self._transition_cache.get(key)

    def set_transition_cache(
        self, goals: List[LeanGoalState], tactic: str, state: CachedGoalState
    ) -> None:
        self._evict_if_full(self._transition_cache)
        key = (self.goal_state_key(goals), tactic.strip())
        self._transition_cache[key] = state

    # ---- solution queries ----

    def solution_path(self) -> Optional[List[TacticNode]]:
        for node in self.nodes.values():
            if node.status == TacticNodeStatus.SOLVED:
                return self._path_to(node)
        return None

    def best_path(self) -> List[TacticNode]:
        solved = [n for n in self.nodes.values() if n.status == TacticNodeStatus.SOLVED]
        if solved:
            target = max(solved, key=lambda n: n.composite_score)
        else:
            leaves = [n for n in self.nodes.values() if not n.children]
            target = max(leaves, key=lambda n: n.q_value) if leaves else self.root
        return self._path_to(target)

    def _path_to(self, node: TacticNode) -> List[TacticNode]:
        path: List[TacticNode] = []
        n: Optional[TacticNode] = node
        while n is not None:
            path.append(n)
            n = self.nodes.get(n.parent_id) if n.parent_id else None
        return list(reversed(path))


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_WS_RE = re.compile(r"\s+")


def _normalize_ws(s: str) -> str:
    """Preserve executable token text; trim only outer diagnostic trivia.

    Collapsing whitespace inside string literals or syntax quotations changes
    a Lean proposition.  Missed cache hits are preferable to unsound aliases.
    """

    return (s or "").strip()


def _text_sha256(text: str) -> str:
    return hashlib.sha256(str(text or "").encode("utf-8")).hexdigest()


def _checkpoint_float(value: Any, *, field_name: str) -> float:
    try:
        number = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"invalid {field_name} in tactic checkpoint") from exc
    if not math.isfinite(number):
        raise ValueError(f"non-finite {field_name} in tactic checkpoint")
    return number


def _goal_to_record(goal: LeanGoalState) -> Dict[str, Any]:
    return {
        "index": int(goal.index),
        "hypotheses": [str(item) for item in goal.hypotheses],
        "target": str(goal.target),
    }


def _goal_from_record(record: Dict[str, Any]) -> LeanGoalState:
    return LeanGoalState(
        index=int(record.get("index", 0) or 0),
        hypotheses=[str(item) for item in record.get("hypotheses") or ()],
        target=str(record.get("target") or ""),
    )


def _features_to_record(features: GoalStateFeatures) -> Dict[str, Any]:
    return asdict(features)


def _features_from_record(record: Dict[str, Any]) -> GoalStateFeatures:
    allowed = {item.name for item in fields(GoalStateFeatures)}
    values = {key: value for key, value in dict(record or {}).items() if key in allowed}
    try:
        return GoalStateFeatures(**values)
    except TypeError as exc:
        raise ValueError("invalid tactic goal feature record") from exc


def _parse_result_to_record(result: LeanParseResult) -> Dict[str, Any]:
    record = asdict(result)
    record["diagnostics"] = [asdict(item) for item in result.diagnostics]
    record["remaining_goals"] = [
        _goal_to_record(item) for item in result.remaining_goals
    ]
    return record


def _parse_result_from_record(record: Dict[str, Any]) -> LeanParseResult:
    data = dict(record or {})
    data["diagnostics"] = [
        LeanDiagnostic(**dict(item or {})) for item in data.get("diagnostics") or ()
    ]
    data["remaining_goals"] = [
        _goal_from_record(dict(item or {}))
        for item in data.get("remaining_goals") or ()
    ]
    allowed = {item.name for item in fields(LeanParseResult)}
    try:
        return LeanParseResult(
            **{key: value for key, value in data.items() if key in allowed}
        )
    except TypeError as exc:
        raise ValueError("invalid Lean parse-result checkpoint") from exc


def _cached_goal_state_to_record(state: CachedGoalState) -> Dict[str, Any]:
    return {
        "goals": [_goal_to_record(item) for item in state.goals],
        "features": _features_to_record(state.features),
        "parse_result": _parse_result_to_record(state.parse_result),
        "ok": bool(state.ok),
        "completion_rejected": bool(state.completion_rejected),
        "completion_pending": bool(state.completion_pending),
    }


def _cached_goal_state_from_record(record: Dict[str, Any]) -> CachedGoalState:
    data = dict(record or {})
    return CachedGoalState(
        goals=[_goal_from_record(dict(item or {})) for item in data.get("goals") or ()],
        features=_features_from_record(dict(data.get("features") or {})),
        parse_result=_parse_result_from_record(
            dict(data.get("parse_result") or {})
        ),
        ok=bool(data.get("ok")),
        completion_rejected=bool(data.get("completion_rejected")),
        completion_pending=bool(data.get("completion_pending")),
    )


def _tactic_node_to_record(node: TacticNode) -> Dict[str, Any]:
    return {
        "node_id": str(node.node_id),
        "parent_id": node.parent_id,
        "depth": int(node.depth),
        "tactic": node.tactic,
        "tactics_from_root": list(node.tactics_from_root),
        "goals": [_goal_to_record(item) for item in node.goals],
        "features": _features_to_record(node.features),
        "status": int(node.status),
        "children": list(node.children),
        "prior": float(node.prior),
        "ensemble_score": float(node.ensemble_score),
        "composite_score": float(node.composite_score),
        "value_estimate": float(node.value_estimate),
        "novelty_score": float(node.novelty_score),
        "selection_score": float(node.selection_score),
        "dead_end_reason": str(node.dead_end_reason),
        "visits": int(node.visits),
        "total_reward": float(node.total_reward),
    }


def _tactic_node_from_record(record: Dict[str, Any]) -> TacticNode:
    data = dict(record or {})
    try:
        status = TacticNodeStatus(int(data.get("status")))
    except (TypeError, ValueError) as exc:
        raise ValueError("invalid tactic node status") from exc
    return TacticNode(
        node_id=str(data.get("node_id") or ""),
        parent_id=(
            str(data.get("parent_id")) if data.get("parent_id") is not None else None
        ),
        depth=max(0, int(data.get("depth", 0) or 0)),
        tactic=(str(data.get("tactic")) if data.get("tactic") is not None else None),
        tactics_from_root=tuple(
            str(item) for item in data.get("tactics_from_root") or ()
        ),
        goals=[_goal_from_record(dict(item or {})) for item in data.get("goals") or ()],
        features=_features_from_record(dict(data.get("features") or {})),
        status=status,
        children=[str(item) for item in data.get("children") or ()],
        prior=_finite_probability(data.get("prior"), default=0.5),
        ensemble_score=_checkpoint_float(
            data.get("ensemble_score", 0.0) or 0.0,
            field_name="node ensemble score",
        ),
        composite_score=_checkpoint_float(
            data.get("composite_score", 0.0) or 0.0,
            field_name="node composite score",
        ),
        value_estimate=_checkpoint_float(
            data.get("value_estimate", 0.0) or 0.0,
            field_name="node value estimate",
        ),
        novelty_score=_checkpoint_float(
            data.get("novelty_score", 1.0) or 0.0,
            field_name="node novelty score",
        ),
        selection_score=_checkpoint_float(
            data.get("selection_score", 0.0) or 0.0,
            field_name="node selection score",
        ),
        dead_end_reason=str(data.get("dead_end_reason") or ""),
        visits=max(0, int(data.get("visits", 0) or 0)),
        total_reward=_checkpoint_float(
            data.get("total_reward", 0.0) or 0.0,
            field_name="node total reward",
        ),
    )


def _goal_state_key(goals: List[LeanGoalState]) -> str:
    """Canonical key for Lean goal states.

    Normalizes whitespace while preserving both goal order and local-context
    order.  Lean local declarations are dependent: a later hypothesis may
    refer to an earlier one, and shadowing/``let`` declarations make a sorted
    context a different executable state.  The key is used by transition,
    policy, value, and transposition caches, so it must never identify two
    differently ordered contexts as the same state.
    """
    goal_parts: List[tuple] = []
    for g in goals:
        target = _normalize_ws(g.target)
        hyps = tuple(
            normalized
            for h in (g.hypotheses or [])
            if (normalized := _normalize_ws(h))
        )
        goal_parts.append((target, hyps))
    # Structured encoding is required: delimiter-joining makes
    # target="A\nB", hyps=[] alias target="A", hyps=["B"].
    blob = json.dumps(
        goal_parts,
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha1(blob).hexdigest()


def _goal_state_tokens(goals: List[LeanGoalState]) -> frozenset[str]:
    """Return structural tokens for diversity scoring, never state identity."""

    tokens: set[str] = set()
    for goal in goals:
        for text in [str(goal.target or ""), *(goal.hypotheses or [])]:
            tokens.update(
                token
                for token in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|[^\s]", text)
                if token
            )
    return frozenset(tokens)


def _goal_state_distance(
    left: List[LeanGoalState],
    right: List[LeanGoalState],
) -> float:
    """Jaccard distance used only to preserve materially different branches."""

    left_tokens = _goal_state_tokens(left)
    right_tokens = _goal_state_tokens(right)
    if not left_tokens and not right_tokens:
        return 0.0
    union = left_tokens | right_tokens
    if not union:
        return 0.0
    return 1.0 - (len(left_tokens & right_tokens) / len(union))


def _finite_probability(value: Any, *, default: float = 0.0) -> float:
    try:
        return clamp_probability(float(value), default=default)
    except Exception:
        return clamp_probability(default, default=0.0)


def _select_diverse_frontier(
    candidates: List[TacticNode],
    *,
    width: int,
    novelty_weight: float,
) -> Tuple[List[TacticNode], List[TacticNode], int]:
    """Greedy MMR selection with deterministic tie-breaking.

    State identity and soundness remain Lean-derived.  Novelty affects only
    which already-checked branch receives the next bounded expansion.  Stale
    or duplicate objects can appear when a crash snapshot owns both an OPEN
    ancestor and one of its descendants; only unique OPEN nodes are eligible
    to own future work.
    """

    cap = max(1, int(width or 1))
    live_unique: List[TacticNode] = []
    seen_node_ids: set[str] = set()
    for node in candidates:
        if node.status != TacticNodeStatus.OPEN or node.node_id in seen_node_ids:
            continue
        seen_node_ids.add(node.node_id)
        live_unique.append(node)
    remaining = sorted(
        live_unique,
        key=lambda node: (
            -float(node.composite_score),
            node.depth,
            node.tactics_from_root,
            node.node_id,
        ),
    )
    selected: List[TacticNode] = []
    while remaining and len(selected) < cap:
        ranked: List[Tuple[float, float, TacticNode]] = []
        for node in remaining:
            novelty = (
                1.0
                if not selected
                else min(
                    _goal_state_distance(node.goals, chosen.goals)
                    for chosen in selected
                )
            )
            node.novelty_score = _finite_probability(novelty, default=0.0)
            node.selection_score = float(node.composite_score) + max(
                0.0, float(novelty_weight or 0.0)
            ) * node.novelty_score
            ranked.append((node.selection_score, node.novelty_score, node))
        ranked.sort(
            key=lambda item: (
                -item[0],
                -item[1],
                item[2].depth,
                item[2].tactics_from_root,
                item[2].node_id,
            )
        )
        chosen = ranked[0][2]
        selected.append(chosen)
        remaining.remove(chosen)
    return selected, remaining, len(remaining)


def tactic_tree_bottlenecks(
    tree: TacticTree,
    *,
    limit: int = 5,
) -> Tuple[Dict[str, Any], ...]:
    """Describe the most promising unresolved root-unlocking states.

    These records are diagnostics, not proof evidence.  They make explicit
    which exact Lean states blocked the best surviving paths and why.
    """

    candidates = [
        node
        for node in tree.nodes.values()
        if node.depth > 0
        and node.status != TacticNodeStatus.SOLVED
        and (node.status == TacticNodeStatus.OPEN or not node.children)
    ]
    candidates.sort(
        key=lambda node: (
            node.status != TacticNodeStatus.OPEN,
            -float(node.selection_score or node.composite_score),
            len(node.goals),
            -node.depth,
            node.tactics_from_root,
            node.node_id,
        )
    )
    records: List[Dict[str, Any]] = []
    for node in candidates[: max(0, int(limit or 0))]:
        records.append(
            {
                "state_key": tree.goal_state_key(node.goals),
                "depth": int(node.depth),
                "goal_count": len(node.goals),
                "targets": tuple(str(goal.target or "") for goal in node.goals),
                "tactics": tuple(node.tactics_from_root),
                "status": node.status.name.lower(),
                "score": round(float(node.composite_score), 6),
                "value_estimate": round(float(node.value_estimate), 6),
                "novelty": round(float(node.novelty_score), 6),
                "reason": str(node.dead_end_reason or "frontier_not_closed"),
                "actionable": node.status == TacticNodeStatus.OPEN,
            }
        )
    if not records and int(limit or 0) > 0:
        root = tree.root
        if root.status != TacticNodeStatus.SOLVED and root.dead_end_reason:
            records.append(
                {
                    "state_key": tree.goal_state_key(root.goals),
                    "depth": 0,
                    "goal_count": len(root.goals),
                    "targets": tuple(str(goal.target or "") for goal in root.goals),
                    "tactics": (),
                    "status": root.status.name.lower(),
                    "score": round(float(root.composite_score), 6),
                    "value_estimate": round(float(root.value_estimate), 6),
                    "novelty": round(float(root.novelty_score), 6),
                    "reason": str(root.dead_end_reason),
                    "actionable": False,
                }
            )
    return tuple(records)


_TACTIC_LINE_RE = re.compile(r"(?:TACTIC:\s*)?(.+?)\s*$")


def _split_trailing_confidence(text: str) -> Tuple[str, float]:
    """Strip a policy annotation only when it is outside Lean literals/comments."""

    raw = str(text or "").strip()
    in_double = False
    in_char = False
    in_quoted_identifier = False
    escaped = False
    block_comment_depth = 0
    comment_at: Optional[int] = None
    candidates: List[int] = []
    upper = raw.upper()
    index = 0
    while index < len(raw):
        char = raw[index]
        if escaped:
            escaped = False
            index += 1
            continue
        if char == "\\" and (in_double or in_char):
            escaped = True
            index += 1
            continue
        if in_quoted_identifier:
            if char == "»":
                in_quoted_identifier = False
            index += 1
            continue
        if block_comment_depth:
            if raw.startswith("/-", index):
                block_comment_depth += 1
                index += 2
                continue
            if raw.startswith("-/", index):
                block_comment_depth -= 1
                index += 2
                continue
            index += 1
            continue
        if char == '"':
            if not in_char:
                in_double = not in_double
            index += 1
            continue
        if char == "'" and not in_double:
            if in_char:
                in_char = False
                index += 1
                continue
            # Lean identifiers may end in apostrophes (``h'``). A character
            # literal begins at a token boundary and has a closing quote.
            previous = raw[index - 1] if index > 0 else ""
            closing = index + 2
            if index + 1 < len(raw) and raw[index + 1] == "\\":
                closing = index + 3
            if (
                (not previous or previous.isspace() or previous in "([{,=:")
                and closing < len(raw)
                and raw[closing] == "'"
            ):
                in_char = True
                index += 1
                continue
        if not in_double and not in_char:
            if char == "«":
                in_quoted_identifier = True
                index += 1
                continue
            if raw.startswith("/-", index):
                block_comment_depth = 1
                index += 2
                continue
            if raw.startswith("--", index):
                comment_at = index
                break
            if upper.startswith("CONFIDENCE:", index):
                if index == 0 or raw[index - 1].isspace():
                    candidates.append(index)
        index += 1
    code = raw[:comment_at].rstrip() if comment_at is not None else raw
    if not candidates:
        return code, 0.5
    marker = candidates[-1]
    if comment_at is not None and marker >= comment_at:
        return code, 0.5
    suffix = code[marker + len("CONFIDENCE:") :].strip()
    if suffix and any(char.isspace() for char in suffix):
        return code, 0.5
    try:
        confidence = float(suffix) if suffix else 0.5
    except ValueError:
        confidence = 0.5
    return code[:marker].rstrip(), clamp_probability(confidence, default=0.5)


def parse_multi_tactic_response(raw: str) -> List[Tuple[str, float]]:
    """Parse a multi-candidate tactic LLM response.

    Accepts lines like:
      TACTIC: simp [Nat.add_comm] CONFIDENCE: 0.8
      intro h
      omega  CONFIDENCE: 0.9
    """
    results: List[Tuple[str, float]] = []
    for line in raw.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("```"):
            continue
        # Skip numbering prefixes like "1." or "1)"
        line = re.sub(r"^\d+[.)]\s*", "", line)
        if not line or line.lower() in ("sorry", "admit", "none"):
            continue
        m = _TACTIC_LINE_RE.match(line)
        if m:
            tactic, confidence = _split_trailing_confidence(m.group(1).strip())
            # Do not rewrite executable Lean text. In particular, ``--`` and
            # whitespace may occur inside literals or syntax quotations.
            if not tactic or tactic.lower() in ("sorry", "admit"):
                continue
            results.append((tactic, confidence))
    return results


# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------


def make_score_fn(
    ensemble: Optional[TacticTreeEnsembleScorer],
    *,
    weight_progress: float = 0.5,
    weight_prior: float = 0.2,
    weight_ensemble: float = 0.2,
    depth_penalty_factor: float = 0.02,
) -> ScoreNodeFunc:
    """Create a composite scoring function for tactic nodes.

    Args:
        ensemble: Optional learned-scoring capability.
        weight_progress: Weight for progress toward closing goals.
        weight_prior: Weight for tactic prior probability.
        weight_ensemble: Weight for ensemble-based scoring.
        depth_penalty_factor: Penalty factor per depth level.
    """

    def score_node(node: TacticNode, statement: str) -> float:
        f = node.features

        # Progress toward closing goals.
        progress = f.progress_ratio * weight_progress

        # Error penalties.
        error_penalty = 0.0
        if f.has_type_mismatch:
            error_penalty += 0.5
        if f.has_unknown_identifier:
            error_penalty += 0.4
        if f.tactic_failed:
            error_penalty += 0.3

        # Complexity: lower is easier; account for depth/length signals.
        nest_norm = min(1.0, f.max_nesting_depth / 8.0)
        len_norm = min(1.0, f.avg_target_length / 240.0)
        complexity_pen = (
            0.08 * f.complexity_estimate + 0.06 * nest_norm + 0.04 * len_norm
        )
        complexity_bonus = max(0.0, 0.32 - complexity_pen)

        # Hypothesis richness: more context available.
        hyp_bonus = min(0.2, f.total_hypothesis_count * 0.02)

        # Pattern bonuses.
        pattern_bonus = 0.0
        if f.pattern_flags & PATTERN_EQUALITY:
            pattern_bonus += 0.05
        if f.pattern_flags & PATTERN_LE_GE:
            pattern_bonus += 0.03

        # Depth penalty.
        depth_pen = node.depth * depth_penalty_factor

        # LLM prior.
        prior = node.prior * weight_prior

        # Ensemble prediction.
        # Phase 2A: blend statement-domain and proof-domain models.
        ens = 0.0
        if ensemble is not None and node.tactic:
            try:
                ens = ensemble.tactic_tree_ensemble_signal(
                    statement,
                    str(node.tactic),
                    weight_ensemble=weight_ensemble,
                )
                node.ensemble_score = ens
            except Exception:
                logger.debug("Ensemble scoring failed in score_node", exc_info=True)

        composite = (
            progress
            + prior
            + ens
            + complexity_bonus
            + hyp_bonus
            + pattern_bonus
            - error_penalty
            - depth_pen
        )
        return max(0.0, composite)

    return score_node


# ---------------------------------------------------------------------------
# Shared candidate evaluation
# ---------------------------------------------------------------------------


def _accept_exact_prefix_completion(
    tree: TacticTree,
    tactics: Tuple[str, ...],
    *,
    features: GoalStateFeatures,
    solved_node: Optional[TacticNode] = None,
    parse_result: Optional[LeanParseResult] = None,
    full_check_output: str = "",
) -> CachedGoalState:
    """Commit one authoritative receipt/node completion transition.

    A sorry-check may report no displayed goals while its compatibility
    ``is_complete`` flag remains false.  Full verification is authoritative in
    that case.  Persist the accepted exact-prefix state as one synchronous
    transition.  The receipt's ``ok`` flag is committed before an attached
    node is marked solved, so no solved node can be serialized against a stale
    pending/non-complete receipt.  Full verification also owns the canonical
    empty goal state even when a compatibility adapter returned residual
    displayed goals together with ``is_complete=True``.
    """

    prefix = tuple(str(item) for item in tactics)
    receipt = tree.get_cache(prefix)
    if receipt is None:
        receipt = CachedGoalState(
            goals=[],
            features=features,
            parse_result=parse_result
            or LeanParseResult(ok=True, raw=str(full_check_output or "")),
            ok=False,
            completion_pending=True,
        )
        tree.set_cache(prefix, receipt)
    receipt.goals = []
    receipt.completion_rejected = False
    receipt.completion_pending = False
    receipt.ok = True
    if solved_node is not None:
        if solved_node.tactics_from_root != prefix:
            raise ValueError("completion receipt/node prefix mismatch")
        solved_node.goals = []
        solved_node.features = receipt.features
        solved_node.status = TacticNodeStatus.SOLVED
    return receipt


async def _evaluate_tactic_candidate(
    *,
    tree: TacticTree,
    parent: TacticNode,
    tactic: str,
    prior: float,
    sorry_check_fn: SorryCheckFunc,
    full_check_fn: FullCheckFunc,
    score_fn: ScoreNodeFunc,
    stats: dict,
    goal_explosion_penalty: bool = True,
    feedback_fn: Optional[Callable] = None,
    durable_candidate_fn: Optional[
        Callable[[str, Dict[str, Any]], Awaitable[None]]
    ] = None,
) -> Tuple[Optional[TacticSearchResult], Optional[TacticNode]]:
    """Evaluate a single tactic candidate against the tree.

    Returns ``(result, child_node)``:
    - Solution found: ``(TacticSearchResult, solved_child)``
    - Child added:    ``(None, child_node)``
    - Skipped/failed: ``(None, None)``
    """
    child_tactics = parent.tactics_from_root + (tactic,)

    def normalized_features(
        value: Any,
        goals_after_tactic: List[LeanGoalState],
        result: LeanParseResult,
    ) -> GoalStateFeatures:
        if isinstance(value, GoalStateFeatures):
            return value
        return extract_goal_state_features(
            goals_after_tactic,
            tree.root.goals,
            result,
        )

    def semantic_prefix_failure() -> bool:
        """Distinguish invalid prefixes from the expected residual-goal error."""

        error_diagnostics = [
            diagnostic
            for diagnostic in list(getattr(parse_result, "diagnostics", ()) or ())
            if str(getattr(diagnostic, "severity", "") or "").lower() == "error"
        ]
        if error_diagnostics:
            # Lean reports a valid partial tactic prefix as an ``unsolved
            # goals`` error. Warning text elsewhere may contain phrases such
            # as ``tactic 'x' failed`` and pollute broad parser flags, so only
            # a non-residual structured error makes the prefix terminal.
            return any(
                not re.match(
                    r"^\s*unsolved goals?\b",
                    str(getattr(diagnostic, "message", "") or ""),
                    flags=re.IGNORECASE,
                )
                for diagnostic in error_diagnostics
            )
        # Compatibility for adapters/tests that provide feature flags without
        # structured diagnostics.
        return bool(
            not bool(getattr(parse_result, "ok", False))
            and (
                features.has_type_mismatch
                or features.has_unknown_identifier
                or features.tactic_failed
            )
        )

    # Only a full tactic prefix under this tree's frozen context is an
    # executable cache identity.  Printed goal states omit metavariable
    # assignments, local instances, and tactic-local state, so the old
    # ``(displayed_state, tactic)`` transition cache could suppress valid
    # paths or replay the wrong successor.
    cached = tree.get_cache(child_tactics)
    if cached is not None:
        stats["cache_hits"] += 1
        if cached.completion_rejected:
            return None, None
        goals, features, parse_result, is_complete = (
            cached.goals,
            cached.features,
            cached.parse_result,
            cached.ok,
        )
        features = normalized_features(features, goals, parse_result)
        cached.features = features
    else:
        try:
            goals, features, parse_result, is_complete = await sorry_check_fn(
                tree.statement, child_tactics
            )
        except TacticOperationTimeout as exc:
            stats["operation_timeouts"] = int(stats.get("operation_timeouts", 0)) + 1
            parent.dead_end_reason = f"operation_timeout:{exc.operation}"
            # Infrastructure/latency is not mathematical evidence and must
            # not train the tactic-family value model as a semantic failure.
            return None, None
        # ``_await_with_hard_timeout`` may detach a cancellation-resistant
        # provider/Lean callback after abandoning its lease.  The late
        # coroutine still resumes, so it must return an immutable no-op
        # before touching caches, stats, the tree, or feedback learners.
        if not hard_timeout_writeback_allowed():
            return None, None
        stats["lean_checks"] += 1
        # Legacy orchestration adapters predate goal-feature scoring and may
        # return ``None`` in the feature slot.  Search used to tolerate that
        # for completed candidates, but durable checkpointing serializes
        # every transition and solved node.  Normalize before the cache/WAL
        # receipt so scoring, persistence, and exact resume share one complete
        # representation.  Passing the parse result retains diagnostic flags.
        features = normalized_features(features, goals, parse_result)
        state = CachedGoalState(
            goals=goals,
            features=features,
            parse_result=parse_result,
            ok=is_complete,
            completion_pending=bool(is_complete or not goals),
        )
        if not (
            not bool(getattr(parse_result, "ok", False))
            and bool(getattr(parse_result, "infra_failure", False))
        ):
            tree.set_cache(child_tactics, state)
            if durable_candidate_fn is not None:
                await durable_candidate_fn(
                    "transition_receipt",
                    {"tactic": tactic, "prefix": list(child_tactics)},
                )

    if (
        not bool(getattr(parse_result, "ok", False))
        and bool(getattr(parse_result, "infra_failure", False))
    ):
        stats["infrastructure_failures"] = int(
            stats.get("infrastructure_failures", 0)
        ) + 1
        parent.dead_end_reason = "infrastructure_failure"
        # No executable state transition occurred. Do not cache the displayed
        # residue or train semantic/value feedback from retryable infrastructure.
        return None, None

    # ---- completion check ------------------------------------------------
    if is_complete or not goals:
        proof = tactics_to_proof(child_tactics)
        if durable_candidate_fn is not None:
            await durable_candidate_fn(
                "full_check_intent",
                {"tactic": tactic, "prefix": list(child_tactics), "proof": proof},
            )
        try:
            ok, _ = await full_check_fn(tree.statement, proof)
        except TacticOperationTimeout:
            stats["operation_timeouts"] = int(stats.get("operation_timeouts", 0)) + 1
            # The transition was Lean-accepted but the authoritative full
            # check did not return. A watchdog timeout is not negative proof
            # evidence: retain the transition receipt and leave completion
            # retryable in a later bounded quantum.
            pending = tree.get_cache(child_tactics)
            if pending is not None:
                pending.completion_pending = True
            return None, None
        if not hard_timeout_writeback_allowed():
            return None, None
        stats["lean_checks"] += 1
        if ok:
            child = tree.add_child(
                parent.node_id,
                tactic,
                [],
                features,
                prior,
            )
            _accept_exact_prefix_completion(
                tree,
                child_tactics,
                features=features,
                solved_node=child,
                parse_result=parse_result,
            )
            child.composite_score = 1.0
            tree.backpropagate(child.node_id, 1.0)
            stats["nodes_created"] += 1
            # Phase 2A: tactic-level feedback for solved proof.
            if feedback_fn is not None:
                try:
                    feedback_fn(tree.statement, tactic, True, "", 0)
                except Exception:
                    pass
            return (
                TacticSearchResult(
                    solved=True,
                    proof=proof,
                    tactics=child_tactics,
                    exit_reason="solved",
                    **stats,
                ),
                child,
            )
        stats["completion_rejections"] = int(
            stats.get("completion_rejections", 0)
        ) + 1
        parent.dead_end_reason = "kernel_completion_rejected"
        if feedback_fn is not None:
            try:
                feedback_fn(
                    tree.statement,
                    tactic,
                    False,
                    "kernel_completion_rejected",
                    len(goals),
                )
            except Exception:
                pass
        # Full verification failed despite sorry-check reporting completion.
        # Correct the caches so future lookups don't trigger redundant checks.
        correction = CachedGoalState(
            goals=goals,
            features=features,
            parse_result=parse_result,
            ok=False,
            completion_rejected=True,
            completion_pending=False,
        )
        tree.set_cache(child_tactics, correction)
        # Don't add a child node when sorry-check was a false positive —
        # the goal state is unreliable (may be empty or misleading).
        if not goals:
            return None, None

    # Displayed goals are useful for scoring and policy hints, but not for
    # correctness pruning: they omit hidden elaborator state.  Full-prefix
    # deduplication and max depth bound the tree without dropping a distinct
    # executable history merely because Lean printed the same goals.
    if not hard_timeout_writeback_allowed():
        return None, None

    # ---- add child -------------------------------------------------------
    child = tree.add_child(
        parent.node_id,
        tactic,
        goals,
        features,
        prior,
    )
    stats["nodes_created"] += 1

    if semantic_prefix_failure():
        child.status = TacticNodeStatus.FAILED
        if features.has_type_mismatch:
            child.dead_end_reason = "type_mismatch"
        elif features.has_unknown_identifier:
            child.dead_end_reason = "unknown_identifier"
        else:
            child.dead_end_reason = "tactic_failed"
        # Phase 2A: tactic-level feedback for failures.
        if feedback_fn is not None:
            try:
                feedback_fn(
                    tree.statement,
                    tactic,
                    False,
                    child.dead_end_reason,
                    features.goal_count,
                )
            except Exception:
                pass
        return None, None

    if goal_explosion_penalty and features.goal_count > parent.features.goal_count + 1:
        child.prior *= 0.3

    # Phase 2A: tactic-level feedback for successful child creation.
    if feedback_fn is not None:
        try:
            feedback_fn(tree.statement, tactic, None, "", features.goal_count)
        except Exception:
            pass

    child.composite_score = score_fn(child, tree.statement)
    return None, child


# ---------------------------------------------------------------------------
# Beam search
# ---------------------------------------------------------------------------


async def tactic_tree_beam_search(
    tree: TacticTree,
    gen_tactic_fn: BeamGenMultiTacticFunc,
    sorry_check_fn: SorryCheckFunc,
    full_check_fn: FullCheckFunc,
    score_fn: ScoreNodeFunc,
    *,
    beam_width: int = 3,
    max_steps: int = 20,
    max_candidates_per_node: int = 5,
    time_limit: float = 300.0,
    value_fn: Optional[ValueNodeFunc] = None,
    value_weight: float = 0.25,
    novelty_weight: float = 0.15,
    backtrack_limit: int = 8,
    cancel_grace_s: Optional[float] = None,
    should_continue: Optional[ShouldContinueFunc] = None,
    feedback_fn: Optional[Callable] = None,
    resume_state: Optional[TacticBeamState] = None,
    durable_progress_fn: Optional[DurableProgressFunc] = None,
) -> TacticSearchResult:
    """Value-guided diverse beam search with a bounded reserve frontier.

    ``score_fn`` remains the cheap structural scorer.  When supplied,
    ``value_fn`` adds a learned/calibrated state value.  MMR-style novelty
    prevents a beam from collapsing into syntactic variants of one route,
    while the reserve frontier permits bounded backtracking when the active
    beam proves misleading.
    """
    t0 = time.monotonic()
    deadline = t0 + max(0.0, float(time_limit))
    exit_reason = ""
    default_stats = dict(
        nodes_created=1,
        nodes_expanded=0,
        max_depth_reached=0,
        cache_hits=0,
        lean_checks=0,
        value_estimates=0,
        diversity_pruned=0,
        backtracks=0,
        operation_timeouts=0,
        infrastructure_failures=0,
        completion_rejections=0,
    )
    stats = dict(default_stats)
    best_score = 0.0
    best_score_time = 0.0
    beam: List[TacticNode] = [tree.root]
    reserve: List[TacticNode] = []
    recovery: List[TacticNode] = []
    saw_max_depth = False
    step = 0
    elapsed_before = 0.0
    quantum_backtracks = 0
    inflight_next_beam: List[TacticNode] = []
    resumed_depth_boundary = False
    quantum_boundary_ids: set[str] = set()
    if resume_state is None:
        # ``max_steps`` is the initial bounded depth quantum.  ``tree.max_depth``
        # persists the currently authorized window after this point.
        tree.max_depth = max(
            1,
            min(
                max(1, int(tree.max_depth or max_steps or 1)),
                max(1, int(max_steps or 1)),
            ),
        )
    if resume_state is not None:
        checkpoint_root = str(resume_state.tree_record.get("root_id") or "")
        checkpoint_statement = str(resume_state.tree_record.get("statement") or "")
        if checkpoint_root != tree.root_id or checkpoint_statement != tree.statement:
            raise ValueError("beam continuation does not match the supplied tactic tree")
        unknown_ids = (
            set(resume_state.beam_node_ids)
            | set(resume_state.reserve_node_ids)
            | set(resume_state.recovery_node_ids)
        ) - set(tree.nodes)
        if unknown_ids:
            raise ValueError("beam continuation references missing tactic nodes")
        for key in default_stats:
            stats[key] = max(0, int(resume_state.stats.get(key, stats[key]) or 0))
        best_score = float(resume_state.best_score)
        best_score_time = max(0.0, float(resume_state.best_score_elapsed_s))
        beam = [tree.nodes[node_id] for node_id in resume_state.beam_node_ids]
        reserve = [tree.nodes[node_id] for node_id in resume_state.reserve_node_ids]
        recovery = [
            tree.nodes[node_id] for node_id in resume_state.recovery_node_ids
        ]
        saw_max_depth = bool(resume_state.saw_max_depth)
        step = max(0, int(resume_state.step))
        elapsed_before = max(0.0, float(resume_state.elapsed_s))
        if saw_max_depth:
            # ``max_steps`` is a bounded depth quantum, not a claim that a
            # Lean-accepted prefix at the boundary is mathematically dead.
            # A resumed search earns another bounded depth window; the outer
            # formal-progress governor decides whether successive windows are
            # genuinely improving.
            tree.max_depth = max(
                int(tree.max_depth or 0) + max(1, int(max_steps or 1)),
                max((node.depth for node in tree.nodes.values()), default=0) + 1,
            )
            saw_max_depth = False
            resumed_depth_boundary = True

        if resumed_depth_boundary:
            # Depth-boundary ownership is continuation work, not mathematical
            # backtracking. Promote it before applying a zero reserve budget,
            # and cap overflow in the ordinary recovery lane.
            boundary_nodes = [
                node
                for node in reserve
                if node.status == TacticNodeStatus.OPEN
                and node.dead_end_reason == "depth_quantum_boundary"
            ]
            boundary_ids = {node.node_id for node in boundary_nodes}
            reserve = [node for node in reserve if node.node_id not in boundary_ids]
            owned = {node.node_id for node in beam}
            for boundary in boundary_nodes:
                boundary.dead_end_reason = ""
                if boundary.node_id not in owned:
                    beam.append(boundary)
                    owned.add(boundary.node_id)
            cap = max(1, int(beam_width or 1))
            overflow = beam[cap:]
            beam = beam[:cap]
            recovery_ids = {node.node_id for node in recovery}
            for node in overflow:
                if node.node_id not in recovery_ids:
                    recovery.append(node)
                    recovery_ids.add(node.node_id)

    if max(0, int(backtrack_limit or 0)) == 0 and reserve:
        # A disabled reserve is not executable work.  Retiring it here also
        # makes checkpoints created by older versions converge instead of
        # resuming forever with an empty beam and a permanently-live reserve.
        for node in reserve:
            if node.status == TacticNodeStatus.OPEN:
                node.status = TacticNodeStatus.FAILED
                node.dead_end_reason = "backtracking_disabled"
        reserve = []

    def _time_left() -> float:
        return deadline - time.monotonic()

    def _snapshot() -> TacticBeamState:
        state = TacticBeamState(
            tree_record=tree.to_execution_record(),
            beam_node_ids=tuple(node.node_id for node in beam),
            reserve_node_ids=tuple(node.node_id for node in reserve),
            stats={key: int(value) for key, value in stats.items()},
            recovery_node_ids=tuple(node.node_id for node in recovery),
            step=int(step),
            best_score=float(best_score),
            best_score_elapsed_s=float(best_score_time),
            elapsed_s=elapsed_before + (time.monotonic() - t0),
            saw_max_depth=bool(saw_max_depth),
        )
        return state.canonicalized_frontier(
            additional_beam_node_ids=tuple(
                node.node_id for node in inflight_next_beam
            ),
            max_active_beam_nodes=max(1, int(beam_width or 1)),
        )

    def _unsolved(reason: str) -> TacticSearchResult:
        return TacticSearchResult(
            solved=False,
            proof=None,
            tactics=None,
            exit_reason=reason,
            bottlenecks=tactic_tree_bottlenecks(tree),
            resume_state=_snapshot(),
            **stats,
        )

    def _rotate_after_quantum_timeout(owner: Optional[TacticNode] = None) -> None:
        """Persist fair frontier ownership after one owner spends the quantum."""

        nonlocal beam, recovery
        selected = owner
        if selected is None:
            selected = next(
                (node for node in beam if node.status == TacticNodeStatus.OPEN),
                None,
            )
        if selected is not None:
            beam = [node for node in beam if node.node_id != selected.node_id]
            if (
                selected.status == TacticNodeStatus.OPEN
                and all(node.node_id != selected.node_id for node in recovery)
            ):
                recovery.append(selected)
        cap = max(1, int(beam_width or 1))
        while len(beam) < cap and recovery:
            candidate = recovery.pop(0)
            if (
                candidate.status == TacticNodeStatus.OPEN
                and all(node.node_id != candidate.node_id for node in beam)
            ):
                beam.append(candidate)

    async def _durable_cutpoint(
        event: str,
        payload: Optional[Dict[str, Any]] = None,
    ) -> None:
        if durable_progress_fn is None:
            return
        await durable_progress_fn(str(event), _snapshot(), dict(payload or {}))

    def _estimate_value(node: TacticNode) -> float:
        if not node.goals:
            return 1.0
        if value_fn is None:
            # The LLM action prior is already part of ``score_fn``.  This
            # fallback is deliberately structural and auditable; callers that
            # have a learned value model inject it through ``value_fn``.
            return _finite_probability(node.features.progress_ratio, default=0.0)
        try:
            value = _finite_probability(value_fn(node, tree.statement), default=0.0)
        except Exception:
            logger.debug("Beam value estimate failed", exc_info=True)
            value = 0.0
        # Supplied value functions may be action/history dependent and may
        # learn online. A displayed-state-only cache is therefore invalid.
        stats["value_estimates"] += 1
        return value

    # The authorized depth lives in the checkpointed tree. Do not collapse it
    # back to the original quantum after an intervening timeout.
    search_depth_limit = max(1, int(tree.max_depth or 1))
    while beam or reserve or recovery:
        if _time_left() <= 0.0:
            logger.info("Tactic beam search: time limit reached at step %d", step)
            _rotate_after_quantum_timeout()
            exit_reason = "time_limit"
            break
        if not beam:
            live_recovery = [
                node for node in recovery if node.status == TacticNodeStatus.OPEN
            ]
            if live_recovery:
                promote_count = max(1, int(beam_width or 1))
                beam = live_recovery[:promote_count]
                promoted_ids = {node.node_id for node in beam}
                recovery = [
                    node for node in recovery if node.node_id not in promoted_ids
                ]
                continue
            live_reserve = [node for node in reserve if node.status == TacticNodeStatus.OPEN]
            eligible_reserve = [
                node
                for node in live_reserve
                if node.node_id not in quantum_boundary_ids
            ]
            quantum_limit = max(0, int(backtrack_limit or 0))
            if eligible_reserve and quantum_backtracks < quantum_limit:
                eligible_reserve.sort(
                    key=lambda node: (
                        -float(node.selection_score or node.composite_score),
                        node.depth,
                        node.tactics_from_root,
                        node.node_id,
                    )
                )
                resumed = eligible_reserve[0]
                reserve.remove(resumed)
                beam = [resumed]
                stats["backtracks"] += 1
                quantum_backtracks += 1
            elif eligible_reserve:
                # The cap is a per-quantum scheduling guard, never evidence
                # that checked reserve branches are mathematically exhausted.
                exit_reason = (
                    "quantum_complete"
                    if quantum_limit > 0
                    else "backtracking_disabled"
                )
                break
            elif live_reserve and quantum_boundary_ids:
                exit_reason = "depth_quantum_complete"
                break
            else:
                exit_reason = (
                    "operation_timeouts_exhausted"
                    if stats["operation_timeouts"] > 0
                    and stats["nodes_created"] == 1
                    else "infrastructure_failures_exhausted"
                    if stats["infrastructure_failures"] > 0
                    and stats["nodes_created"] == 1
                    else "kernel_completion_rejected"
                    if stats["completion_rejections"] > 0
                    and stats["nodes_created"] == 1
                    else "empty_beam"
                )
                break

        next_beam: List[TacticNode] = []
        inflight_next_beam = next_beam
        retry_parents: List[TacticNode] = []

        for node in beam:
            if node.status != TacticNodeStatus.OPEN:
                continue
            if not node.goals:
                # Possible completion — verify.
                proof = tactics_to_proof(node.tactics_from_root)
                remaining = _time_left()
                if remaining <= 0.0:
                    _rotate_after_quantum_timeout(node)
                    return _unsolved("time_limit")
                try:
                    ok, full_check_output = await _await_with_hard_timeout(
                        full_check_fn(tree.statement, proof),
                        timeout=remaining,
                        cancel_grace=cancel_grace_s,
                    )
                except asyncio.TimeoutError:
                    logger.info("Tactic beam search: full check hit time limit")
                    _rotate_after_quantum_timeout(node)
                    return _unsolved("time_limit")
                stats["lean_checks"] += 1
                if ok:
                    cached = tree.get_cache(node.tactics_from_root)
                    _accept_exact_prefix_completion(
                        tree,
                        node.tactics_from_root,
                        features=node.features,
                        solved_node=node,
                        parse_result=(cached.parse_result if cached is not None else None),
                        full_check_output=str(full_check_output or ""),
                    )
                    node.composite_score = 1.0
                    tree.backpropagate(node.node_id, 1.0)
                    return TacticSearchResult(
                        solved=True,
                        proof=proof,
                        tactics=node.tactics_from_root,
                        exit_reason="solved",
                        **stats,
                    )
                node.status = TacticNodeStatus.FAILED
                continue
            if node.depth >= search_depth_limit:
                if node not in reserve:
                    reserve.append(node)
                quantum_boundary_ids.add(node.node_id)
                node.dead_end_reason = "depth_quantum_boundary"
                saw_max_depth = True
                continue

            stats["nodes_expanded"] += 1
            stats["max_depth_reached"] = max(stats["max_depth_reached"], node.depth)

            candidates = tree.get_policy_cache(
                node.goals,
                node.tactics_from_root,
            )
            policy_incomplete = False
            if candidates is None:
                remaining = _time_left()
                if remaining <= 0.0:
                    _rotate_after_quantum_timeout(node)
                    return _unsolved("time_limit")
                await _durable_cutpoint(
                    "policy_intent",
                    {
                        "node_id": node.node_id,
                        "prefix": list(node.tactics_from_root),
                    },
                )
                try:
                    policy_result = await _await_with_hard_timeout(
                        gen_tactic_fn(
                            tree.statement,
                            node.goals,
                            node.tactics_from_root,
                        ),
                        timeout=remaining,
                        cancel_grace=cancel_grace_s,
                    )
                except asyncio.TimeoutError:
                    logger.info(
                        "Tactic beam search: tactic generation hit time limit"
                    )
                    _rotate_after_quantum_timeout(node)
                    return _unsolved("time_limit")
                if isinstance(policy_result, TacticPolicyBatch):
                    candidates = list(policy_result.candidates)
                    policy_incomplete = not bool(policy_result.complete)
                    if policy_incomplete:
                        retry_kind = str(policy_result.retryable_kind or "provider_failure")
                        if "timeout" in retry_kind.lower():
                            stats["operation_timeouts"] += 1
                        else:
                            stats["infrastructure_failures"] += 1
                        node.dead_end_reason = (
                            "policy_generation_retryable:"
                            + retry_kind
                        )
                else:
                    candidates = list(policy_result)
                if not policy_incomplete:
                    tree.set_policy_cache(
                        node.goals,
                        candidates,
                        node.tactics_from_root,
                    )
                await _durable_cutpoint(
                    "policy_receipt",
                    {
                        "node_id": node.node_id,
                        "prefix": list(node.tactics_from_root),
                        "complete": not policy_incomplete,
                    },
                )
            candidates = _cap_tactic_candidates(candidates, max_candidates_per_node)
            if not candidates:
                if policy_incomplete:
                    node.status = TacticNodeStatus.OPEN
                    retry_parents.append(node)
                    continue
                node.status = TacticNodeStatus.FAILED
                node.dead_end_reason = "no_goal_conditioned_candidates"
                continue

            retryable_failures_before = (
                int(stats.get("operation_timeouts", 0)),
                int(stats.get("infrastructure_failures", 0)),
            )
            for tactic, prior in candidates:
                existing_child = tree.child_for_tactic(node.node_id, tactic)
                if existing_child is not None:
                    if existing_child.status == TacticNodeStatus.OPEN:
                        next_beam.append(existing_child)
                    continue
                cached_prefix = tree.get_cache(node.tactics_from_root + (tactic,))
                if cached_prefix is not None and cached_prefix.completion_rejected:
                    # An authoritative full-check rejection is terminal. A
                    # noncomplete transition receipt without a child is a WAL
                    # cutpoint: replay must materialize and score that child
                    # from the cached Lean state without rerunning Lean.
                    continue
                remaining = _time_left()
                if remaining <= 0.0:
                    _rotate_after_quantum_timeout(node)
                    return _unsolved("time_limit")
                await _durable_cutpoint(
                    "candidate_intent",
                    {
                        "node_id": node.node_id,
                        "tactic": tactic,
                        "prefix": list(node.tactics_from_root + (tactic,)),
                    },
                )
                try:
                    result, child = await _await_with_hard_timeout(
                        _evaluate_tactic_candidate(
                            tree=tree,
                            parent=node,
                            tactic=tactic,
                            prior=prior,
                            sorry_check_fn=sorry_check_fn,
                            full_check_fn=full_check_fn,
                            score_fn=score_fn,
                            stats=stats,
                            goal_explosion_penalty=True,
                            feedback_fn=feedback_fn,
                            durable_candidate_fn=_durable_cutpoint,
                        ),
                        timeout=remaining,
                        cancel_grace=cancel_grace_s,
                    )
                except asyncio.TimeoutError:
                    logger.info(
                        "Tactic beam search: candidate evaluation hit time limit"
                    )
                    _rotate_after_quantum_timeout(node)
                    return _unsolved("time_limit")
                if result is not None:
                    await _durable_cutpoint(
                        "candidate_solved" if result.solved else "candidate_receipt",
                        {
                            "node_id": node.node_id,
                            "tactic": tactic,
                            "proof": str(result.proof or ""),
                            "tactics": list(result.tactics or ()),
                        },
                    )
                    result.resume_state = _snapshot()
                    return result
                if child is not None:
                    if child.goals and child.depth >= search_depth_limit:
                        # Preserve the Lean-accepted boundary state for the
                        # next bounded depth quantum. It remains ordinary live
                        # frontier work and is subject to the same diversity
                        # and no-improvement controls as shallower states.
                        child.dead_end_reason = "depth_quantum_boundary"
                        saw_max_depth = True
                        await _durable_cutpoint(
                            "candidate_receipt",
                            {"node_id": node.node_id, "tactic": tactic},
                        )
                        if child not in reserve:
                            reserve.append(child)
                        quantum_boundary_ids.add(child.node_id)
                        continue
                    child.value_estimate = _estimate_value(child)
                    child.composite_score += max(0.0, float(value_weight or 0.0)) * (
                        child.value_estimate
                    )
                    child.selection_score = child.composite_score
                    if child.selection_score > best_score:
                        best_score = child.selection_score
                        best_score_time = elapsed_before + (time.monotonic() - t0)
                    next_beam.append(child)
                await _durable_cutpoint(
                    "candidate_receipt",
                    {"node_id": node.node_id, "tactic": tactic},
                )

            retryable_failures_after = (
                int(stats.get("operation_timeouts", 0)),
                int(stats.get("infrastructure_failures", 0)),
            )
            retryable_parent = bool(
                policy_incomplete
                or retryable_failures_after > retryable_failures_before
            )
            node.status = (
                TacticNodeStatus.OPEN if retryable_parent else TacticNodeStatus.EXPANDED
            )
            if retryable_parent:
                node.dead_end_reason = "retryable_operation_failure"
                retry_parents.append(node)
            elif not node.children:
                node.status = TacticNodeStatus.FAILED
                node.dead_end_reason = (
                    node.dead_end_reason
                    or "all_transitions_rejected_or_transposed"
                )

        # Keep a diverse active beam and retain the remaining checked states
        # for bounded backtracking.  They are not marked terminal merely for
        # losing one local ranking decision.
        beam, deferred, diversity_pruned = _select_diverse_frontier(
            next_beam,
            width=beam_width,
            novelty_weight=novelty_weight,
        )
        inflight_next_beam = []
        stats["diversity_pruned"] += diversity_pruned
        if max(0, int(backtrack_limit or 0)) > 0:
            reserve.extend(deferred)
        else:
            for deferred_node in deferred:
                if deferred_node.status == TacticNodeStatus.OPEN:
                    deferred_node.status = TacticNodeStatus.FAILED
                    deferred_node.dead_end_reason = "backtracking_disabled"
        beam_ids = {item.node_id for item in beam}
        recovery_ids = {item.node_id for item in recovery}
        for retry_parent in retry_parents:
            # Infrastructure retry owners are not mathematical backtracking.
            # Keep them in the separately scheduled recovery lane even when
            # backtracking is disabled. Appending them directly to the beam
            # bypassed ``beam_width`` and inflated a configured four-wide B2
            # search to 117 concurrent retry owners.
            reserve = [
                item for item in reserve if item.node_id != retry_parent.node_id
            ]
            if (
                retry_parent.node_id not in beam_ids
                and retry_parent.node_id not in recovery_ids
            ):
                recovery.append(retry_parent)
                recovery_ids.add(retry_parent.node_id)
        if retry_parents:
            return _unsolved("retryable_operation_failure")

        if should_continue is not None:
            progress = SearchProgress(
                iteration=step,
                nodes_expanded=stats["nodes_expanded"],
                max_depth_reached=stats["max_depth_reached"],
                elapsed_s=elapsed_before + (time.monotonic() - t0),
                best_score=best_score,
                best_score_elapsed_s=best_score_time,
                beam_size=len(beam),
                solved_non_root=0,
                cache_hits=stats["cache_hits"],
                cache_misses=0,
                search_time_limit=time_limit,
            )
            cont, reason = should_continue(progress)
            if not cont:
                exit_reason = reason or "callback_stop"
                break
        step += 1

    return TacticSearchResult(
        solved=False,
        proof=None,
        tactics=None,
        exit_reason=(
            exit_reason
            or (
                "max_depth"
                if saw_max_depth
                else "operation_timeouts_exhausted"
                if stats["operation_timeouts"] > 0
                and stats["nodes_created"] == 1
                else "infrastructure_failures_exhausted"
                if stats["infrastructure_failures"] > 0
                and stats["nodes_created"] == 1
                else "kernel_completion_rejected"
                if stats["completion_rejections"] > 0
                and stats["nodes_created"] == 1
                else str(tree.root.dead_end_reason or "empty_beam")
                if stats["nodes_created"] == 1
                else "all_transitions_rejected"
            )
        ),
        bottlenecks=tactic_tree_bottlenecks(tree),
        resume_state=_snapshot(),
        **stats,
    )


# ---------------------------------------------------------------------------
# MCTS
# ---------------------------------------------------------------------------


async def tactic_tree_mcts(
    tree: TacticTree,
    gen_tactic_fn: GenMultiTacticFunc,
    sorry_check_fn: SorryCheckFunc,
    full_check_fn: FullCheckFunc,
    score_fn: ScoreNodeFunc,
    *,
    simulations: int = 64,
    c_puct: float = 1.4,
    max_candidates_per_node: int = 5,
    time_limit: float = 300.0,
    value_fn: Optional[ValueNodeFunc] = None,
    should_continue: Optional[ShouldContinueFunc] = None,
    feedback_fn: Optional[Callable] = None,
) -> TacticSearchResult:
    """MCTS over the tactic tree."""
    t0 = time.monotonic()
    deadline = t0 + max(0.0, float(time_limit))
    exit_reason = ""
    stats = dict(
        nodes_created=1,
        nodes_expanded=0,
        max_depth_reached=0,
        cache_hits=0,
        lean_checks=0,
    )
    best_score = 0.0
    best_score_time = 0.0

    def _time_left() -> float:
        return deadline - time.monotonic()

    def _unsolved(reason: str) -> TacticSearchResult:
        return TacticSearchResult(
            solved=False,
            proof=None,
            tactics=None,
            exit_reason=reason,
            **stats,
        )

    def _value(node: TacticNode) -> float:
        if not node.goals:
            return 1.0
        fn = value_fn
        if fn is None:
            # Default: score_fn depends on node-specific fields (depth, prior)
            # so caching by goal state is incorrect — two nodes at different
            # depths/priors with the same goals would share a stale value.
            v = score_fn(node, tree.statement)
        else:
            # User-provided value_fn may be expensive; cache by goal state.
            cached = tree.get_value_cache(node.goals)
            if cached is not None:
                return float(cached)
            v = fn(node, tree.statement)
        try:
            v_f = float(v)
        except Exception:
            v_f = 0.0
        v_f = clamp_probability(v_f, default=0.0)
        if fn is not None:
            tree.set_value_cache(node.goals, v_f)
        return v_f

    for sim in range(simulations):
        if _time_left() <= 0.0:
            logger.info("Tactic MCTS: time limit reached at sim %d", sim)
            exit_reason = "time_limit"
            break
        # Early exit: if root is terminal, no further exploration is possible.
        if tree.root.status in (TacticNodeStatus.FAILED, TacticNodeStatus.SOLVED):
            logger.debug(
                "Tactic MCTS: root is %s, stopping at sim %d",
                tree.root.status.name,
                sim,
            )
            exit_reason = "root_terminal"
            break
        # Root exhaustion: root stays EXPANDED but all children are terminal.
        if tree.root.children and all(
            tree.nodes[cid].status
            in (
                TacticNodeStatus.FAILED,
                TacticNodeStatus.PRUNED,
                TacticNodeStatus.SOLVED,
            )
            for cid in tree.root.children
        ):
            logger.debug(
                "Tactic MCTS: root exhausted (all children terminal), stopping at sim %d",
                sim,
            )
            exit_reason = "root_exhausted"
            break

        if sim % 4 == 0 and should_continue is not None:
            progress = SearchProgress(
                iteration=sim,
                nodes_expanded=stats["nodes_expanded"],
                max_depth_reached=stats["max_depth_reached"],
                elapsed_s=time.monotonic() - t0,
                best_score=best_score,
                best_score_elapsed_s=best_score_time,
                beam_size=0,
                solved_non_root=0,
                cache_hits=stats["cache_hits"],
                cache_misses=0,
                search_time_limit=time_limit,
            )
            cont, reason = should_continue(progress)
            if not cont:
                exit_reason = reason or "callback_stop"
                break

        # 1. SELECT
        leaf = tree.select_leaf_puct(c_puct)

        if leaf.status in (
            TacticNodeStatus.SOLVED,
            TacticNodeStatus.FAILED,
            TacticNodeStatus.PRUNED,
        ):
            reward = 1.0 if leaf.status == TacticNodeStatus.SOLVED else 0.0
            tree.backpropagate(leaf.node_id, reward)
            continue

        # Guard: node returned from select has children but all terminal
        # (root protection — not marked FAILED).  Don't re-expand.
        if leaf.children:
            tree.backpropagate(leaf.node_id, 0.0)
            continue

        if leaf.depth >= tree.max_depth:
            leaf.status = TacticNodeStatus.FAILED
            tree.backpropagate(leaf.node_id, 0.0)
            continue

        # Leaf with empty goals — verify.
        if not leaf.goals:
            proof = tactics_to_proof(leaf.tactics_from_root)
            remaining = _time_left()
            if remaining <= 0.0:
                return _unsolved("time_limit")
            try:
                ok, full_check_output = await _await_with_hard_timeout(
                    full_check_fn(tree.statement, proof),
                    timeout=remaining,
                )
            except asyncio.TimeoutError:
                logger.info("Tactic MCTS: full check hit time limit")
                return _unsolved("time_limit")
            stats["lean_checks"] += 1
            if ok:
                cached = tree.get_cache(leaf.tactics_from_root)
                _accept_exact_prefix_completion(
                    tree,
                    leaf.tactics_from_root,
                    features=leaf.features,
                    solved_node=leaf,
                    parse_result=(cached.parse_result if cached is not None else None),
                    full_check_output=str(full_check_output or ""),
                )
                leaf.composite_score = 1.0
                tree.backpropagate(leaf.node_id, 1.0)
                return TacticSearchResult(
                    solved=True,
                    proof=proof,
                    tactics=leaf.tactics_from_root,
                    exit_reason="solved",
                    **stats,
                )
            leaf.status = TacticNodeStatus.FAILED
            tree.backpropagate(leaf.node_id, 0.0)
            continue

        # 2. EXPAND
        stats["nodes_expanded"] += 1
        stats["max_depth_reached"] = max(stats["max_depth_reached"], leaf.depth)

        # Policy: cache per canonical goal state.
        candidates = tree.get_policy_cache(
            leaf.goals,
            leaf.tactics_from_root,
        )
        policy_incomplete = False
        if candidates is None:
            remaining = _time_left()
            if remaining <= 0.0:
                return _unsolved("time_limit")
            try:
                policy_result = await _await_with_hard_timeout(
                    gen_tactic_fn(
                        tree.statement,
                        leaf.goals,
                        leaf.tactics_from_root,
                    ),
                    timeout=remaining,
                )
            except asyncio.TimeoutError:
                logger.info("Tactic MCTS: tactic generation hit time limit")
                return _unsolved("time_limit")
            if isinstance(policy_result, TacticPolicyBatch):
                candidates = list(policy_result.candidates)
                policy_incomplete = not bool(policy_result.complete)
                if policy_result.complete:
                    tree.set_policy_cache(
                        leaf.goals,
                        candidates,
                        leaf.tactics_from_root,
                    )
            else:
                candidates = list(policy_result)
                tree.set_policy_cache(
                    leaf.goals,
                    candidates,
                    leaf.tactics_from_root,
                )
        candidates = _cap_tactic_candidates(candidates, max_candidates_per_node)
        if not candidates:
            if policy_incomplete:
                leaf.status = TacticNodeStatus.OPEN
                leaf.dead_end_reason = "policy_generation_retryable"
                return _unsolved("retryable_operation_failure")
            leaf.status = TacticNodeStatus.FAILED
            tree.backpropagate(leaf.node_id, 0.0)
            continue

        for tactic, prior in candidates:
            remaining = _time_left()
            if remaining <= 0.0:
                return _unsolved("time_limit")
            try:
                result, child = await _await_with_hard_timeout(
                    _evaluate_tactic_candidate(
                        tree=tree,
                        parent=leaf,
                        tactic=tactic,
                        prior=prior,
                        sorry_check_fn=sorry_check_fn,
                        full_check_fn=full_check_fn,
                        score_fn=score_fn,
                        stats=stats,
                        goal_explosion_penalty=False,
                        feedback_fn=feedback_fn,
                    ),
                    timeout=remaining,
                )
            except asyncio.TimeoutError:
                logger.info("Tactic MCTS: candidate evaluation hit time limit")
                return _unsolved("time_limit")
            if result is not None:
                return result

        leaf.status = TacticNodeStatus.EXPANDED

        # All candidates pruned/failed without adding children: dead end.
        if not leaf.children:
            leaf.status = TacticNodeStatus.FAILED
            tree.backpropagate(leaf.node_id, 0.0)
            continue

        # 3. EVALUATE (explicit value) + 4. BACKPROPAGATE
        v = _value(leaf)
        if v > best_score:
            best_score = v
            best_score_time = time.monotonic() - t0
        tree.backpropagate(leaf.node_id, v)

    return TacticSearchResult(
        solved=False,
        proof=None,
        tactics=None,
        exit_reason=exit_reason or "max_simulations",
        **stats,
    )
