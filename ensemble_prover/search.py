"""Asynchronous beam-search and MCTS primitives over a shared proof tree.

``ProofTree`` owns node state while the search drivers enforce per-call and
overall time bounds around caller-supplied proof expansion functions.
"""

from __future__ import annotations

import asyncio
import logging
import time
from dataclasses import dataclass, field
from enum import IntEnum, auto
from typing import Awaitable, Callable, Dict, List, Optional, Tuple, Union, cast

from .math_utils import clamp_probability
from .runtime_context import (
    _CURRENT_HARD_TIMEOUT_LEASE,
    HardTimeoutLease,
    hard_timeout_writeback_allowed,  # noqa: F401 - compatibility re-export
    mark_runtime_owned_callback,
)
from .search_utils import MCTSScoreMixin, make_node_id

logger = logging.getLogger(__name__)

# Maximum per-call timeout to prevent runaway single operations from
# consuming the entire search budget. Each prove/expand call is capped
# at this value even if remaining_time would allow more.
_MAX_PER_CALL_TIMEOUT = 180.0
_HARD_TIMEOUT_CANCEL_GRACE_MIN_S = 0.05
_HARD_TIMEOUT_CANCEL_GRACE_MAX_S = 1.0
_HARD_TIMEOUT_CANCEL_GRACE_FRACTION = 0.01


def _default_hard_timeout_cancel_grace(timeout_s: float) -> float:
    return min(
        _HARD_TIMEOUT_CANCEL_GRACE_MAX_S,
        max(
            _HARD_TIMEOUT_CANCEL_GRACE_MIN_S,
            float(timeout_s) * _HARD_TIMEOUT_CANCEL_GRACE_FRACTION,
        ),
    )


def _consume_future_exception(fut: "asyncio.Future") -> None:
    """Done-callback that marks a Future's exception as retrieved.

    Must be attached immediately after create_future() on any Future that
    may be stamped with set_exception but can be orphaned (no awaiter) —
    e.g. the coalescing Futures used to deduplicate concurrent work in
    beam search and the Lean runner. Without this, asyncio's Future.__del__
    logs a "Future exception was never retrieved" warning at GC because
    set_exception flips __log_traceback=True and nothing flips it back.

    Real awaiters still receive the exception via their own await on the
    Future — .exception() is idempotent and the __log_traceback flag is
    independent of exception delivery.
    """
    if fut.cancelled():
        return
    try:
        fut.exception()
    except BaseException:  # pragma: no cover — defensive, exception() on a done non-cancelled future cannot raise
        pass


_consume_future_exception = mark_runtime_owned_callback(
    _consume_future_exception
)


# ---- types -------------------------------------------------------------


class NodeStatus(IntEnum):
    PENDING = auto()
    EXPANDED = auto()
    SOLVED = auto()
    FAILED = auto()
    DEAD = auto()


@dataclass
class ProofNode(MCTSScoreMixin):
    node_id: str
    statement: str
    depth: int
    parent: Optional[str] = None
    children: List[str] = field(default_factory=list)
    status: NodeStatus = NodeStatus.PENDING
    proof: Optional[str] = None
    score: float = 0.0
    visits: int = 0
    total_reward: float = 0.0
    attempts: int = 0
    prior: float = 0.5
    tried_tactics: List[str] = field(default_factory=list)
    consecutive_failures: int = 0


@dataclass
class SearchProgress:
    """Snapshot of search state passed to the should_continue callback."""

    iteration: int
    nodes_expanded: int
    max_depth_reached: int
    elapsed_s: float
    best_score: float
    best_score_elapsed_s: float
    beam_size: int
    solved_non_root: int
    cache_hits: int
    cache_misses: int
    search_time_limit: float = 0.0
    proof_potential_avg: float = 0.0
    proof_potential_best: float = 0.0
    proof_potential_samples: int = 0


@dataclass
class SearchResult:
    solved: bool
    proof: Optional[str]
    nodes_expanded: int
    max_depth_reached: int
    exit_reason: str = ""
    solved_non_root: int = 0
    solved_non_root_keys: Tuple[str, ...] = ()


@dataclass
class ExpandResult:
    """Structured expansion outcome.

    ``children`` is the normal expansion output.
    ``solved``/``proof`` allow expand_fn to report direct closure of the
    current node (e.g., planner guard fast-path) without forcing a synthetic
    child list.
    """

    children: List[Tuple[str, float]] = field(default_factory=list)
    solved: bool = False
    proof: Optional[str] = None


class ProofTree:
    """Manages a tree of proof nodes rooted at a theorem statement."""

    def __init__(self, root_statement: str, max_depth: int = 10) -> None:
        self.max_depth = max_depth
        self.nodes: Dict[str, ProofNode] = {}
        root_id = make_node_id()
        self.root_id = root_id
        root = ProofNode(node_id=root_id, statement=root_statement, depth=0)
        self.nodes[root_id] = root

    @property
    def root(self) -> ProofNode:
        return self.nodes[self.root_id]

    def add_child(
        self,
        parent_id: str,
        statement: str,
        prior: float = 0.5,
    ) -> ProofNode:
        parent = self.nodes[parent_id]
        child_id = make_node_id()
        child = ProofNode(
            node_id=child_id,
            statement=statement,
            depth=parent.depth + 1,
            parent=parent_id,
            prior=clamp_probability(prior, default=0.5),
        )
        self.nodes[child_id] = child
        parent.children.append(child_id)
        return child

    def select_leaf(
        self, c_puct: float = 1.4, *, max_failed_attempts: int = 0
    ) -> ProofNode:
        """PUCT tree walk from root to a leaf for MCTS selection.

        Failed nodes can be revisited if their attempt count is below
        max_failed_attempts (useful when context/lemmas evolve).

        T2#5 root fix (2026-04-28): SOLVED nodes are also excluded from the
        live-children filter. Without this exclusion, a SOLVED leaf with
        q=1.0 dominates PUCT selection after its first visit (siblings drop
        to q+explore < 1.0 once visited), causing the simulation budget to
        be absorbed by the no-op SOLVED-leaf early-out at the caller's
        downstream `if leaf.status == SOLVED: backprop and continue` branch
        instead of exploring live siblings. `tactic_tree.select_leaf_puct`
        already excludes SOLVED — this restores symmetry for every MCTS caller.
        """
        node = self.root
        while node.children:
            children = [self.nodes[cid] for cid in node.children]
            # Filter out DEAD and SOLVED; allow FAILED only if under retry budget.
            # SOLVED siblings have already produced their reward — they should
            # not absorb further selection budget; live siblings deserve the
            # PUCT exploration term.
            live = [
                c
                for c in children
                if c.status not in (NodeStatus.DEAD, NodeStatus.SOLVED)
                and (c.status != NodeStatus.FAILED or c.attempts < max_failed_attempts)
            ]
            if not live:
                # T2#5 amendment (2026-04-28): the empty-live branch fires
                # when ALL children are DEAD/SOLVED/FAILED-exhausted. The
                # parent's status depends on which: if any child SOLVED,
                # the decomposition succeeded → parent is SOLVED-by-children
                # (not DEAD, which would back-propagate 0.0 reward through
                # search.py:1473 and falsely train against this branch). If
                # no children SOLVED, all paths failed → parent DEAD.
                if node.node_id != self.root_id:
                    if any(
                        self.nodes[cid].status == NodeStatus.SOLVED
                        for cid in node.children
                    ):
                        node.status = NodeStatus.SOLVED
                    else:
                        node.status = NodeStatus.DEAD
                return node
            node = max(live, key=lambda c: c.puct_score(node.visits, c_puct))
        return node

    def best_path(self) -> List[ProofNode]:
        """Return the path from root to the best solved leaf (or best scored leaf)."""
        solved_nodes = [n for n in self.nodes.values() if n.status == NodeStatus.SOLVED]
        if solved_nodes:
            target = max(solved_nodes, key=lambda n: n.score)
        else:
            target = max(self.nodes.values(), key=lambda n: n.q_value)
        path = []
        node: Optional[ProofNode] = target
        while node is not None:
            path.append(node)
            node = self.nodes.get(node.parent) if node.parent else None
        return list(reversed(path))

    def backpropagate(self, node_id: str, reward: float) -> None:
        """Propagate reward up from node to root."""
        nid: Optional[str] = node_id
        while nid is not None:
            node = self.nodes.get(nid)
            if node is None:
                logger.warning("backpropagate: node %s not found, stopping early", nid)
                break
            node.backpropagate(reward)
            nid = node.parent


# ---- type aliases for callables ----------------------------------------

# prove_fn(statement) -> (solved, score, proof_text, lean_output)
ProveFunc = Callable[[str], Awaitable[Tuple[bool, float, Optional[str], str]]]

# expand_fn(statement, max_children) -> List[(child_statement, prior)] | ExpandResult
ExpandRaw = Union[List[Tuple[str, float]], ExpandResult]
ExpandFunc = Callable[[str, int], Awaitable[ExpandRaw]]

# value_fn(statement) -> value in [0, 1] (fast heuristic / model estimate).
ValueFunc = Callable[[str], Awaitable[float]]

# should_continue(progress) -> (continue, reason)
ShouldContinueFunc = Callable[[SearchProgress], Tuple[bool, str]]
# elapsed_fn() -> elapsed seconds used for budget checks/progress.
ElapsedFunc = Callable[[], float]
# potential_stats_fn() -> (avg, best, samples)
PotentialStatsFunc = Callable[[], Tuple[float, float, int]]


def _canonical_statement_key(statement: str) -> str:
    """Canonical key for statement-level transposition/caching.

    Only normalizes whitespace; does NOT attempt semantic normalization.
    """
    return " ".join((statement or "").strip().split())


def _normalize_reward(value: object, *, default: float = 0.0) -> float:
    return clamp_probability(cast(float, value), default=default)


def _normalize_solved_non_root_keys(
    keys: Tuple[str, ...] | List[str] | None,
) -> Tuple[str, ...]:
    uniq: Dict[str, None] = {}
    for key in keys or ():
        norm = _canonical_statement_key(str(key))
        if norm:
            uniq[norm] = None
    return tuple(uniq.keys())


def _solved_non_root_keys_from_tree(tree: ProofTree) -> Tuple[str, ...]:
    uniq: Dict[str, None] = {}
    for node in tree.nodes.values():
        if node.node_id == tree.root_id:
            continue
        if node.status == NodeStatus.SOLVED and node.proof:
            norm = _canonical_statement_key(node.statement)
            if norm:
                uniq[norm] = None
    return tuple(uniq.keys())


def _make_search_result(
    *,
    solved: bool,
    proof: Optional[str],
    nodes_expanded: int,
    max_depth_reached: int,
    exit_reason: str = "",
    solved_non_root: int = 0,
    solved_non_root_keys: Tuple[str, ...] | List[str] | None = None,
) -> SearchResult:
    normalized_keys = _normalize_solved_non_root_keys(solved_non_root_keys)
    normalized_count = max(int(solved_non_root or 0), len(normalized_keys))
    return SearchResult(
        solved=solved,
        proof=proof,
        nodes_expanded=nodes_expanded,
        max_depth_reached=max_depth_reached,
        exit_reason=exit_reason,
        solved_non_root=normalized_count,
        solved_non_root_keys=normalized_keys,
    )


async def _try_prove(
    prove_fn: ProveFunc,
    statement: str,
    timeout: float,
) -> Tuple[bool, float, Optional[str], str]:
    """Call prove_fn with timeout, returning a safe default on failure."""
    try:
        solved, score, proof, output = await _await_with_hard_timeout(
            prove_fn(statement),
            timeout=timeout,
        )
        return bool(solved), _normalize_reward(score), proof, str(output or "")
    except asyncio.TimeoutError:
        return False, 0.0, None, "timeout"
    except Exception as exc:
        logger.warning("prove_fn failed: %s", exc)
        return False, 0.0, None, f"error: {exc}"


async def _await_with_hard_timeout(
    awaitable: Awaitable,
    timeout: float,
    *,
    cancel_grace: Optional[float] = None,
):
    """Await with a hard wall-clock timeout.

    A proof that lands just over the nominal timeout should not be discarded.
    We therefore wait a short pre-cancel grace window. If the task still has
    not stopped by then, mark its lease abandoned before issuing cancellation
    so post-cancel writeback paths can refuse to mutate shared solver state.
    """
    if float(timeout) <= 0.0:
        # Callers commonly construct a coroutine before they discover that the
        # remaining search budget is zero. Rejecting it without closing leaves
        # a noisy un-awaited-coroutine warning and retains captured state until
        # GC. Futures/tasks have no close method, so this is intentionally
        # limited to coroutine-like awaitables.
        close = getattr(awaitable, "close", None)
        if callable(close):
            close()
        raise asyncio.TimeoutError

    timeout_f = float(timeout)
    grace_f = (
        float(cancel_grace)
        if cancel_grace is not None
        else _default_hard_timeout_cancel_grace(timeout_f)
    )
    if grace_f < 0.0:
        grace_f = 0.0

    lease = HardTimeoutLease(timeout_s=timeout_f, cancel_grace_s=grace_f)
    token = _CURRENT_HARD_TIMEOUT_LEASE.set(lease)
    try:
        task = asyncio.ensure_future(awaitable)
    finally:
        _CURRENT_HARD_TIMEOUT_LEASE.reset(token)
    task.add_done_callback(_consume_future_exception)

    def _mark_late_result_discarded(fut: "asyncio.Future") -> None:
        if fut.cancelled():
            return
        try:
            exc = fut.exception()
        except BaseException:
            return
        if exc is None:
            lease.late_result_discarded = True
            result = fut.result()
            solved = False
            proof = None
            if isinstance(result, tuple) and len(result) >= 3:
                solved = bool(result[0])
                proof = result[2]
            if solved and proof:
                logger.warning(
                    "hard-timeout task returned a proof after abandonment; "
                    "result discarded"
                )
            else:
                logger.debug(
                    "hard-timeout task returned after abandonment; result discarded"
                )

    _mark_late_result_discarded = mark_runtime_owned_callback(
        _mark_late_result_discarded
    )

    try:
        done, _pending = await asyncio.wait({task}, timeout=timeout_f)
        if task not in done:
            if grace_f > 0.0:
                done, _pending = await asyncio.wait({task}, timeout=grace_f)
                if task in done:
                    try:
                        result = task.result()
                    except asyncio.CancelledError as exc:
                        raise asyncio.TimeoutError from exc
                    lease.recovered_after_timeout = True
                    return result
            lease.cancel_requested = True
            lease.abandoned = True
            task.cancel()
            task.add_done_callback(_mark_late_result_discarded)
            raise asyncio.TimeoutError
        try:
            return task.result()
        except asyncio.CancelledError as exc:
            raise asyncio.TimeoutError from exc
    except asyncio.CancelledError:
        # The owner itself was cancelled before the nominal timeout.  Without
        # this branch the child task inherited a still-live lease, continued
        # running detached, and was allowed to mutate shared search state.
        # Abandon first, then request cancellation; cancellation-resistant
        # callbacks may finish later, but their writeback gates now fail.
        lease.cancel_requested = True
        lease.abandoned = True
        if not task.done():
            task.cancel()
        task.add_done_callback(_mark_late_result_discarded)
        raise


def _normalize_expand_result(value: ExpandRaw) -> ExpandResult:
    def _normalize_children(
        children: List[Tuple[str, float]],
    ) -> List[Tuple[str, float]]:
        return [
            (stmt, clamp_probability(prior, default=0.5)) for stmt, prior in children
        ]

    if isinstance(value, ExpandResult):
        children = _normalize_children(list(value.children or []))
        return ExpandResult(
            children=children, solved=bool(value.solved), proof=value.proof
        )
    children = _normalize_children(list(value or []))
    return ExpandResult(children=children, solved=False, proof=None)


def _final_search_result(
    tree: ProofTree,
    require_root_solved: bool,
    nodes_expanded: int,
    max_depth_reached: int,
    exit_reason: str = "",
    solved_non_root: int = 0,
    solved_non_root_keys: Tuple[str, ...] | List[str] | None = None,
) -> SearchResult:
    """Build the final SearchResult after the search loop ends."""
    merged_non_root_keys = _normalize_solved_non_root_keys(
        tuple(solved_non_root_keys or ()) + _solved_non_root_keys_from_tree(tree)
    )
    merged_non_root_count = max(int(solved_non_root or 0), len(merged_non_root_keys))
    root = tree.root
    if require_root_solved:
        if root.status == NodeStatus.SOLVED and root.proof:
            return _make_search_result(
                solved=True,
                proof=root.proof,
                nodes_expanded=nodes_expanded,
                max_depth_reached=max_depth_reached,
                exit_reason=exit_reason or "solved",
                solved_non_root=merged_non_root_count,
                solved_non_root_keys=merged_non_root_keys,
            )
    else:
        for node in tree.nodes.values():
            if node.status == NodeStatus.SOLVED and node.proof:
                return _make_search_result(
                    solved=True,
                    proof=node.proof,
                    nodes_expanded=nodes_expanded,
                    max_depth_reached=max_depth_reached,
                    exit_reason=exit_reason or "solved",
                    solved_non_root=merged_non_root_count,
                    solved_non_root_keys=merged_non_root_keys,
                )
    return _make_search_result(
        solved=False,
        proof=None,
        nodes_expanded=nodes_expanded,
        max_depth_reached=max_depth_reached,
        exit_reason=exit_reason or "exhausted",
        solved_non_root=merged_non_root_count,
        solved_non_root_keys=merged_non_root_keys,
    )


# ---- parallel beam helpers ---------------------------------------------


@dataclass
class _BeamNodeResult:
    """Result of processing one beam node in parallel mode."""

    node_id: str
    solved: bool = False
    proof: Optional[str] = None
    score: float = 0.0
    skipped: bool = False
    timed_out: bool = False
    stop_reason: str = ""
    new_child_ids: List[str] = field(default_factory=list)
    cache_hit: bool = False
    cache_miss: bool = False


async def _process_one_beam_node(
    node: ProofNode,
    tree: ProofTree,
    prove_fn: ProveFunc,
    expand_fn: ExpandFunc,
    beam_width: int,
    max_node_attempts: int,
    per_call_timeout_fn: Union[Callable[[], float], float],
    expand_cache: Dict[str, ExpandResult],
    require_root_solved: bool,
    root_id: str,
    backtrack: bool,
    cancel_event: asyncio.Event,
    stagnation_threshold: int = 0,
    expand_pending: Optional[Dict[str, "asyncio.Future[ExpandResult]"]] = None,
    stop_reason_fn: Optional[Callable[[], str]] = None,
) -> _BeamNodeResult:
    """Process a single beam node: prove then expand.

    Used by parallel beam mode via ``asyncio.gather``.  Tree mutations
    (backpropagate, add_child) are safe in asyncio because they are
    synchronous operations between ``await`` points.

    *cancel_event* is set when a root-solving proof is found so that
    other tasks can skip their expansion phase.

    *expand_pending* coalesces concurrent expand requests for the same
    canonical key: the first caller creates a Future and runs expand_fn;
    subsequent callers await that Future instead of issuing a duplicate
    LLM call.
    """
    result = _BeamNodeResult(node_id=node.node_id)

    def _timeout_value() -> float:
        if callable(per_call_timeout_fn):
            return float(per_call_timeout_fn())
        return float(per_call_timeout_fn)

    def _stop_reason() -> str:
        if stop_reason_fn is None:
            return ""
        return str(stop_reason_fn() or "")

    # Skip if terminal or exhausted
    if node.status in (NodeStatus.SOLVED, NodeStatus.DEAD):
        result.skipped = True
        return result
    if node.attempts >= max_node_attempts:
        node.status = NodeStatus.DEAD
        result.skipped = True
        return result
    if node.depth > tree.max_depth:
        node.status = NodeStatus.DEAD
        result.skipped = True
        return result

    # ---- prove ----
    per_call_timeout = _timeout_value()
    if per_call_timeout <= 0.0:
        result.timed_out = True
        result.skipped = True
        return result
    solved, score, proof, output = await _try_prove(
        prove_fn,
        node.statement,
        per_call_timeout,
    )
    node.attempts += 1
    if score > node.score:
        node.consecutive_failures = 0
        node.score = score
    else:
        node.consecutive_failures += 1
    if stagnation_threshold > 0 and node.consecutive_failures >= stagnation_threshold:
        node.status = NodeStatus.DEAD
        logger.info(
            "[beam] node %s stagnated (%d consecutive failures) — marked dead",
            node.node_id[:12],
            node.consecutive_failures,
        )
        result.skipped = True
        return result
    result.score = score

    if solved and proof:
        node.status = NodeStatus.SOLVED
        node.proof = proof
        tree.backpropagate(node.node_id, 1.0)
        result.solved = True
        result.proof = proof
        # Signal other tasks to skip their expansion phase
        if (not require_root_solved) or (node.node_id == root_id):
            cancel_event.set()
        return result

    tree.backpropagate(node.node_id, score)

    # ---- expand (skip if root already solved) ----
    if cancel_event.is_set():
        return result

    if node.depth < tree.max_depth:
        if not node.children:
            stop_reason = _stop_reason()
            if stop_reason:
                result.stop_reason = stop_reason
                result.timed_out = stop_reason in {"time_limit", "time_limit_policy"}
                return result
            try:
                key = _canonical_statement_key(node.statement)
                if not key:
                    # Degenerate statement — skip cache/pending to avoid
                    # empty-string key collisions across unrelated nodes.
                    per_call_timeout = _timeout_value()
                    if per_call_timeout <= 0.0:
                        result.timed_out = True
                        return result
                    raw_expand = await _await_with_hard_timeout(
                        expand_fn(node.statement, beam_width),
                        timeout=per_call_timeout,
                    )
                    expand_result = _normalize_expand_result(raw_expand)
                    result.cache_miss = True
                elif key in expand_cache:
                    expand_result = expand_cache[key]
                    result.cache_hit = True
                elif expand_pending is not None and key in expand_pending:
                    # Another concurrent task is already expanding this key.
                    # Shield prevents our timeout from cancelling the owner's
                    # Future; we just stop waiting.
                    try:
                        per_call_timeout = _timeout_value()
                        if per_call_timeout <= 0.0:
                            result.timed_out = True
                            return result
                        expand_result = await _await_with_hard_timeout(
                            asyncio.shield(expand_pending[key]),
                            timeout=per_call_timeout,
                        )
                        result.cache_hit = True
                    except asyncio.TimeoutError:
                        # Our wait expired; owner may still be running.
                        # Check if the owner finished in the meantime.
                        expand_result = expand_cache.get(
                            key, ExpandResult(children=[])
                        )
                    except asyncio.CancelledError:
                        # Genuine task cancellation — propagate.
                        raise
                else:
                    # First caller for this key: create a Future so concurrent
                    # tasks can coalesce onto this expansion.
                    per_call_timeout = _timeout_value()
                    if per_call_timeout <= 0.0:
                        result.timed_out = True
                        return result
                    future: Optional[asyncio.Future[ExpandResult]] = None
                    if expand_pending is not None:
                        future = asyncio.get_running_loop().create_future()
                        # Guarantee exception retrieval even if no waiter ever
                        # attaches — otherwise set_exception(TimeoutError) on
                        # a solo leader produces "Future exception was never
                        # retrieved" warnings at GC.
                        future.add_done_callback(_consume_future_exception)
                        expand_pending[key] = future
                    try:
                        raw_expand = await _await_with_hard_timeout(
                            expand_fn(node.statement, beam_width),
                            timeout=per_call_timeout,
                        )
                        expand_result = _normalize_expand_result(raw_expand)
                        expand_cache[key] = expand_result
                        if future is not None and not future.done():
                            future.set_result(expand_result)
                    except BaseException as exc:
                        if future is not None and not future.done():
                            if isinstance(exc, asyncio.CancelledError):
                                future.cancel()
                            else:
                                # Propagate the real error to waiters so they
                                # can fall back gracefully instead of getting
                                # an opaque CancelledError that drops their
                                # nodes from the frontier permanently.
                                future.set_exception(exc)
                                # Retrieve immediately as well: the done
                                # callback is loop-scheduled, so a solo leader
                                # can otherwise be GC'd before the callback
                                # runs and still emit a "Future exception was
                                # never retrieved" warning.
                                _consume_future_exception(future)
                        raise
                    finally:
                        if expand_pending is not None:
                            expand_pending.pop(key, None)
                    result.cache_miss = True
            except asyncio.TimeoutError:
                expand_result = ExpandResult(children=[])
            except Exception as exc:
                logger.warning("expand_fn failed: %s", exc)
                expand_result = ExpandResult(children=[])
            if expand_result.solved and expand_result.proof:
                node.status = NodeStatus.SOLVED
                node.proof = expand_result.proof
                tree.backpropagate(node.node_id, 1.0)
                result.solved = True
                result.proof = expand_result.proof
                if (not require_root_solved) or (node.node_id == root_id):
                    cancel_event.set()
                return result
            for stmt, prior in expand_result.children:
                child = tree.add_child(node.node_id, stmt, prior=prior)
                result.new_child_ids.append(child.node_id)
            node.status = (
                NodeStatus.EXPANDED if expand_result.children else NodeStatus.FAILED
            )
        else:
            # Already expanded: keep existing children
            for cid in node.children:
                result.new_child_ids.append(cid)
    else:
        node.status = NodeStatus.FAILED

    return result


# ---- beam search -------------------------------------------------------


async def beam_search(
    tree: ProofTree,
    prove_fn: ProveFunc,
    expand_fn: ExpandFunc,
    beam_width: int = 4,
    max_iterations: int = 50,
    time_limit: float = 300.0,
    *,
    max_nodes: Optional[int] = None,
    require_root_solved: bool = True,
    max_node_attempts: int = 10,
    backtrack: bool = True,
    should_continue: Optional[ShouldContinueFunc] = None,
    elapsed_fn: Optional[ElapsedFunc] = None,
    time_limit_fn: Optional[Callable[[], float]] = None,
    parallel_nodes: bool = False,
    potential_stats_fn: Optional[PotentialStatsFunc] = None,
    stale_decay_rate: float = 0.0,
    per_call_timeout_cap: Optional[float] = None,
    stagnation_threshold: int = 0,
) -> SearchResult:
    """Iterative beam search over the proof tree.

    At each iteration, the best ``beam_width`` pending nodes are expanded:
    first a direct proof is attempted; if that fails, subgoals are
    generated as children.  Nodes are scored and pruned to beam_width.

    When *parallel_nodes* is True, all beam nodes are proved concurrently
    via ``asyncio.gather`` instead of sequentially.  This overlaps LLM
    wait times across nodes.  MEO policy updates use last-writer-wins
    semantics (acceptable for incremental policy adjustments).
    """
    start = time.time()
    elapsed = elapsed_fn or (lambda: max(0.0, time.time() - start))
    nodes_expanded = 0
    max_depth_reached = 0
    # Tracking vars for SearchProgress / exit_reason.
    cache_hits = 0
    cache_misses = 0
    best_score = 0.0
    best_score_time = 0.0
    solved_non_root_keys: Dict[str, None] = {}
    exit_reason = ""

    root = tree.root
    # Keep the competitive frontier separate from mandatory root retries.
    frontier: List[ProofNode] = [] if require_root_solved else [root]
    # Canonical-state caches (safe within a single search invocation).
    expand_cache: Dict[str, ExpandResult] = {}
    # Coalescing dict for parallel beam: the first task to expand a key
    # stores a Future here; concurrent tasks await it instead of issuing
    # duplicate expand_fn calls (prevents TOCTOU on expand_cache).
    expand_pending: Dict[str, asyncio.Future[ExpandResult]] = {}
    timeout_cap = (
        float(per_call_timeout_cap)
        if per_call_timeout_cap is not None
        else float(_MAX_PER_CALL_TIMEOUT)
    )
    if timeout_cap <= 0.0:
        timeout_cap = float(_MAX_PER_CALL_TIMEOUT)

    def _root_retry_needed() -> bool:
        return (
            require_root_solved
            and root.status not in (NodeStatus.SOLVED, NodeStatus.DEAD)
            and root.attempts < max_node_attempts
            and root.depth <= tree.max_depth
        )

    def _solved_non_root_count() -> int:
        return len(solved_non_root_keys)

    def _record_non_root_solution(statement: str, score: float) -> None:
        nonlocal best_score, best_score_time
        key = _canonical_statement_key(statement)
        if key:
            solved_non_root_keys[key] = None
        if score > best_score:
            best_score = score
            best_score_time = max(0.0, float(elapsed()))

    def _current_time_limit() -> float:
        current = max(0.0, float(time_limit))
        if time_limit_fn is None:
            return current
        try:
            dynamic = float(time_limit_fn())
        except Exception:
            logger.debug("beam_search time_limit_fn failed", exc_info=True)
            return current
        if dynamic < 0.0:
            return current
        return min(current, dynamic)

    def _remaining_time() -> float:
        return max(0.0, _current_time_limit() - max(0.0, float(elapsed())))

    def _progress_snapshot(iteration: int, beam_size: int) -> SearchProgress:
        if potential_stats_fn is not None:
            p_avg, p_best, p_samples = potential_stats_fn()
        else:
            p_avg, p_best, p_samples = (0.0, 0.0, 0)
        return SearchProgress(
            iteration=iteration,
            nodes_expanded=nodes_expanded,
            max_depth_reached=max_depth_reached,
            elapsed_s=max(0.0, float(elapsed())),
            best_score=best_score,
            best_score_elapsed_s=best_score_time,
            beam_size=max(beam_size, 0),
            solved_non_root=_solved_non_root_count(),
            cache_hits=cache_hits,
            cache_misses=cache_misses,
            search_time_limit=_current_time_limit(),
            proof_potential_avg=float(p_avg),
            proof_potential_best=float(p_best),
            proof_potential_samples=int(p_samples),
        )

    def _should_stop_now(iteration: int, beam_size: int) -> str:
        if should_continue is None:
            return ""
        cont, reason = should_continue(_progress_snapshot(iteration, beam_size))
        if cont:
            return ""
        return reason or "callback_stop"

    def _sequential_timeout_for(batch_size: int) -> float:
        remaining_time = _remaining_time()
        if remaining_time <= 0.0:
            return 0.0
        return max(
            0.001,
            min(
                timeout_cap,
                remaining_time,
                remaining_time / max(1, batch_size) * 2,
            ),
        )

    for iteration in range(max_iterations):
        elapsed_s = max(0.0, float(elapsed()))
        current_time_limit = _current_time_limit()
        if elapsed_s > current_time_limit:
            exit_reason = "time_limit"
            break

        current_beam = list(frontier)
        root_retry_now = bool(require_root_solved and _root_retry_needed())
        stop_reason = _should_stop_now(
            iteration,
            len(current_beam) + (1 if root_retry_now else 0),
        )
        if stop_reason:
            exit_reason = stop_reason
            break
        if not current_beam and not root_retry_now:
            exit_reason = "empty_beam"
            break

        logger.info(
            "[beam] iter %d/%d beam=%d nodes=%d elapsed=%.0fs%s",
            iteration + 1,
            max_iterations,
            len(current_beam) + (1 if root_retry_now else 0),
            nodes_expanded,
            elapsed_s,
            " (parallel)" if parallel_nodes and len(current_beam) > 1 else "",
        )

        next_frontier: List[ProofNode] = []

        # ==================================================================
        # PARALLEL path: prove all beam nodes concurrently
        # ==================================================================
        if parallel_nodes and len(current_beam) > 1:
            # Hard-cap dispatch to remaining node budget to avoid overshoot.
            if max_nodes is not None:
                remaining_nodes = max_nodes - nodes_expanded
                if remaining_nodes <= 0:
                    exit_reason = "max_nodes"
                    break
                current_beam = current_beam[:remaining_nodes]

            remaining_time = _remaining_time()
            if remaining_time <= 0.0:
                exit_reason = "time_limit"
                break
            # In parallel mode, all nodes share the same time window
            def _parallel_timeout() -> float:
                remaining = _remaining_time()
                if remaining <= 0.0:
                    return 0.0
                return max(0.001, min(timeout_cap, remaining))

            def _parallel_stop_reason() -> str:
                return _should_stop_now(iteration, len(current_beam))

            cancel_event = asyncio.Event()

            tasks = [
                _process_one_beam_node(
                    node,
                    tree,
                    prove_fn,
                    expand_fn,
                    beam_width,
                    max_node_attempts,
                    _parallel_timeout,
                    expand_cache,
                    require_root_solved,
                    root.node_id,
                    backtrack,
                    cancel_event,
                    stagnation_threshold=stagnation_threshold,
                    expand_pending=expand_pending,
                    stop_reason_fn=_parallel_stop_reason,
                )
                for node in current_beam
            ]
            raw_results = await asyncio.gather(*tasks, return_exceptions=True)

            solved_result: Optional[_BeamNodeResult] = None
            for r in raw_results:
                if isinstance(r, BaseException):
                    logger.warning("Parallel beam node failed: %s", r)
                    continue
                if r.stop_reason and not exit_reason:
                    exit_reason = r.stop_reason
                if r.timed_out and not exit_reason:
                    exit_reason = "time_limit"
                if r.skipped:
                    continue

                nodes_expanded += 1
                rnode = tree.nodes.get(r.node_id)
                if rnode is not None:
                    max_depth_reached = max(max_depth_reached, rnode.depth)

                if r.cache_hit:
                    cache_hits += 1
                if r.cache_miss:
                    cache_misses += 1
                if r.score > best_score:
                    best_score = r.score
                    best_score_time = max(0.0, float(elapsed()))

                if r.solved and r.proof:
                    if rnode is not None and rnode.node_id != root.node_id:
                        _record_non_root_solution(rnode.statement, r.score)
                    if (not require_root_solved) or (r.node_id == root.node_id):
                        # Take the first root-solving result
                        if solved_result is None:
                            solved_result = r
                        continue
                    continue

                # Not solved — add children + node itself to next beam
                for cid in r.new_child_ids:
                    child_node = tree.nodes.get(cid)
                    if child_node is not None:
                        next_frontier.append(child_node)
                if backtrack and rnode is not None:
                    if not (require_root_solved and rnode.node_id == root.node_id):
                        next_frontier.append(rnode)

            if exit_reason and solved_result is None:
                break

            # Check max_nodes
            if max_nodes is not None and nodes_expanded >= max_nodes:
                exit_reason = "max_nodes"
                if solved_result is None:
                    break

            # Immediate return if root was solved
            if solved_result is not None:
                return _make_search_result(
                    solved=True,
                    proof=solved_result.proof,
                    nodes_expanded=nodes_expanded,
                    max_depth_reached=max_depth_reached,
                    exit_reason="solved",
                    solved_non_root=_solved_non_root_count(),
                    solved_non_root_keys=tuple(solved_non_root_keys.keys()),
                )

        # ==================================================================
        # SEQUENTIAL path: original behavior (unchanged)
        # ==================================================================
        else:
            for node in current_beam:
                if node.status in (NodeStatus.SOLVED, NodeStatus.DEAD):
                    continue
                if node.attempts >= max_node_attempts:
                    node.status = NodeStatus.DEAD
                    continue
                if node.depth > tree.max_depth:
                    node.status = NodeStatus.DEAD
                    continue

                nodes_expanded += 1
                max_depth_reached = max(max_depth_reached, node.depth)

                if max_nodes is not None and nodes_expanded >= max_nodes:
                    exit_reason = "max_nodes"
                    break

                per_call_timeout = _sequential_timeout_for(len(current_beam))
                if per_call_timeout <= 0.0:
                    exit_reason = "time_limit"
                    break

                solved, score, proof, output = await _try_prove(
                    prove_fn,
                    node.statement,
                    per_call_timeout,
                )
                node.attempts += 1
                if score > node.score:
                    node.consecutive_failures = 0
                    node.score = score
                else:
                    node.consecutive_failures += 1

                if (
                    stagnation_threshold > 0
                    and node.consecutive_failures >= stagnation_threshold
                ):
                    node.status = NodeStatus.DEAD
                    logger.info(
                        "[beam] node %s stagnated (%d consecutive failures) — marked dead",
                        node.node_id[:12],
                        node.consecutive_failures,
                    )
                    continue

                if solved and proof:
                    node.status = NodeStatus.SOLVED
                    node.proof = proof
                    tree.backpropagate(node.node_id, 1.0)
                    if node.node_id != root.node_id:
                        _record_non_root_solution(node.statement, score)
                    if (not require_root_solved) or (node.node_id == root.node_id):
                        return _make_search_result(
                            solved=True,
                            proof=proof,
                            nodes_expanded=nodes_expanded,
                            max_depth_reached=max_depth_reached,
                            exit_reason="solved",
                            solved_non_root=_solved_non_root_count(),
                            solved_non_root_keys=tuple(solved_non_root_keys.keys()),
                        )
                    continue

                tree.backpropagate(node.node_id, score)
                if score > best_score:
                    best_score = score
                    best_score_time = max(0.0, float(elapsed()))

                if node.depth < tree.max_depth:
                    if not node.children:
                        stop_reason = _should_stop_now(
                            iteration,
                            len(current_beam) + (1 if root_retry_now else 0),
                        )
                        if stop_reason:
                            exit_reason = stop_reason
                            break
                        expand_timeout = _sequential_timeout_for(len(current_beam))
                        if expand_timeout <= 0.0:
                            exit_reason = "time_limit"
                            break
                        try:
                            key = _canonical_statement_key(node.statement)
                            if key in expand_cache:
                                expand_result = expand_cache[key]
                                cache_hits += 1
                            else:
                                raw_expand = await _await_with_hard_timeout(
                                    expand_fn(node.statement, beam_width),
                                    timeout=expand_timeout,
                                )
                                expand_result = _normalize_expand_result(raw_expand)
                                expand_cache[key] = expand_result
                                cache_misses += 1
                        except asyncio.TimeoutError:
                            expand_result = ExpandResult(children=[])
                        except Exception as exc:
                            logger.warning("expand_fn failed: %s", exc)
                            expand_result = ExpandResult(children=[])
                        if expand_result.solved and expand_result.proof:
                            node.status = NodeStatus.SOLVED
                            node.proof = expand_result.proof
                            tree.backpropagate(node.node_id, 1.0)
                            if node.node_id != root.node_id:
                                _record_non_root_solution(node.statement, score)
                            if (not require_root_solved) or (
                                node.node_id == root.node_id
                            ):
                                return _make_search_result(
                                    solved=True,
                                    proof=expand_result.proof,
                                    nodes_expanded=nodes_expanded,
                                    max_depth_reached=max_depth_reached,
                                    exit_reason="solved",
                                    solved_non_root=_solved_non_root_count(),
                                    solved_non_root_keys=tuple(
                                        solved_non_root_keys.keys()
                                    ),
                                )
                            continue
                        for stmt, prior in expand_result.children:
                            child = tree.add_child(node.node_id, stmt, prior=prior)
                            next_frontier.append(child)
                        node.status = (
                            NodeStatus.EXPANDED
                            if expand_result.children
                            else NodeStatus.FAILED
                        )
                    else:
                        for cid in node.children:
                            next_frontier.append(tree.nodes[cid])
                else:
                    node.status = NodeStatus.FAILED

                if backtrack:
                    if not (require_root_solved and node.node_id == root.node_id):
                        next_frontier.append(node)

        # ==================================================================
        # Common post-iteration logic (both paths)
        # ==================================================================
        if exit_reason:  # max_nodes hit inside inner loop
            break

        if root_retry_now and _root_retry_needed():
            if max_nodes is not None and nodes_expanded >= max_nodes:
                exit_reason = "max_nodes"
                break
            root_timeout = _sequential_timeout_for(1)
            if root_timeout <= 0.0:
                exit_reason = "time_limit"
                break
            root_result = await _process_one_beam_node(
                root,
                tree,
                prove_fn,
                expand_fn,
                beam_width,
                max_node_attempts,
                lambda: _sequential_timeout_for(1),
                expand_cache,
                require_root_solved,
                root.node_id,
                backtrack,
                asyncio.Event(),
            )
            if not root_result.skipped:
                nodes_expanded += 1
                max_depth_reached = max(max_depth_reached, root.depth)
                if root_result.timed_out and not exit_reason:
                    exit_reason = "time_limit"
                if root_result.cache_hit:
                    cache_hits += 1
                if root_result.cache_miss:
                    cache_misses += 1
                if root_result.score > best_score:
                    best_score = root_result.score
                    best_score_time = max(0.0, float(elapsed()))
                if root_result.solved and root_result.proof:
                    return _make_search_result(
                        solved=True,
                        proof=root_result.proof,
                        nodes_expanded=nodes_expanded,
                        max_depth_reached=max_depth_reached,
                        exit_reason="solved",
                        solved_non_root=_solved_non_root_count(),
                        solved_non_root_keys=tuple(solved_non_root_keys.keys()),
                    )
                for cid in root_result.new_child_ids:
                    child_node = tree.nodes.get(cid)
                    if child_node is not None:
                        next_frontier.append(child_node)
            elif root_result.timed_out and not exit_reason:
                exit_reason = "time_limit"

        if exit_reason:
            break

        root_retry_pending = bool(require_root_solved and _root_retry_needed())
        if not next_frontier and not root_retry_pending:
            exit_reason = "empty_beam"
            break

        # De-dup by node_id to keep the beam stable.
        uniq: Dict[str, ProofNode] = {}
        for n in next_frontier:
            uniq[n.node_id] = n
        next_frontier = list(uniq.values())

        # Prune to beam_width by score then prior (with optional stale decay).
        _decay = stale_decay_rate
        if _decay > 0.0:
            next_frontier.sort(
                key=lambda n: (
                    n.score / (1.0 + _decay * n.consecutive_failures),
                    n.prior,
                ),
                reverse=True,
            )
        else:
            next_frontier.sort(key=lambda n: (n.score, n.prior), reverse=True)
        frontier = next_frontier[: max(1, beam_width)]

    if not exit_reason:
        exit_reason = "max_iterations"
    return _final_search_result(
        tree,
        require_root_solved,
        nodes_expanded,
        max_depth_reached,
        exit_reason,
        solved_non_root=_solved_non_root_count(),
        solved_non_root_keys=tuple(solved_non_root_keys.keys()),
    )


# ---- MCTS --------------------------------------------------------------


async def mcts_search(
    tree: ProofTree,
    prove_fn: ProveFunc,
    expand_fn: ExpandFunc,
    simulations: int = 32,
    c_puct: float = 1.4,
    time_limit: float = 300.0,
    *,
    require_root_solved: bool = True,
    max_expand_children: int = 4,
    max_node_attempts: int = 2,
    backtrack: bool = True,
    value_fn: Optional[ValueFunc] = None,
    should_continue: Optional[ShouldContinueFunc] = None,
    elapsed_fn: Optional[ElapsedFunc] = None,
    time_limit_fn: Optional[Callable[[], float]] = None,
    potential_stats_fn: Optional[PotentialStatsFunc] = None,
) -> SearchResult:
    """Monte Carlo Tree Search over the proof tree.

    Each simulation: select leaf (UCB1), evaluate (prove_fn), expand
    with subgoals, backpropagate reward.
    """
    start = time.time()
    elapsed = elapsed_fn or (lambda: max(0.0, time.time() - start))
    nodes_expanded = 0
    max_depth_reached = 0
    root = tree.root
    # Tracking vars for SearchProgress / exit_reason.
    cache_hits = 0
    cache_misses = 0
    best_score = 0.0
    best_score_time = 0.0
    solved_non_root_keys: Dict[str, None] = {}
    exit_reason = ""
    # Canonical-state caches (safe within a single search invocation).
    expand_cache: Dict[str, ExpandResult] = {}
    value_cache: Dict[str, float] = {}

    def _solved_non_root_count() -> int:
        return len(solved_non_root_keys)

    def _record_non_root_solution(statement: str, score: float) -> None:
        nonlocal best_score, best_score_time
        key = _canonical_statement_key(statement)
        if key:
            solved_non_root_keys[key] = None
        if score > best_score:
            best_score = score
            best_score_time = max(0.0, float(elapsed()))

    def _current_time_limit() -> float:
        current = max(0.0, float(time_limit))
        if time_limit_fn is None:
            return current
        try:
            dynamic = float(time_limit_fn())
        except Exception:
            logger.debug("mcts_search time_limit_fn failed", exc_info=True)
            return current
        if dynamic < 0.0:
            return current
        return min(current, dynamic)

    def _remaining_time() -> float:
        return max(0.0, _current_time_limit() - max(0.0, float(elapsed())))

    def _per_call_timeout(remaining_work: int) -> float:
        remaining_time = _remaining_time()
        if remaining_time <= 0.0:
            return 0.0
        return max(
            0.001,
            min(
                _MAX_PER_CALL_TIMEOUT,
                remaining_time,
                remaining_time / max(1, remaining_work) * 2,
            ),
        )

    def _progress_snapshot(sim: int) -> SearchProgress:
        if potential_stats_fn is not None:
            p_avg, p_best, p_samples = potential_stats_fn()
        else:
            p_avg, p_best, p_samples = (0.0, 0.0, 0)
        return SearchProgress(
            iteration=sim,
            nodes_expanded=nodes_expanded,
            max_depth_reached=max_depth_reached,
            elapsed_s=max(0.0, float(elapsed())),
            best_score=best_score,
            best_score_elapsed_s=best_score_time,
            beam_size=0,  # N/A for MCTS
            solved_non_root=_solved_non_root_count(),
            cache_hits=cache_hits,
            cache_misses=cache_misses,
            search_time_limit=_current_time_limit(),
            proof_potential_avg=float(p_avg),
            proof_potential_best=float(p_best),
            proof_potential_samples=int(p_samples),
        )

    def _should_stop_now(sim: int) -> str:
        if should_continue is None:
            return ""
        cont, reason = should_continue(_progress_snapshot(sim))
        if cont:
            return ""
        return reason or "callback_stop"

    async def _value(stmt: str, sim: int) -> float:
        if value_fn is None:
            return 0.0
        key = _canonical_statement_key(stmt)
        if key in value_cache:
            return value_cache[key]
        value_timeout = min(30.0, _per_call_timeout(1))
        if value_timeout <= 0.0:
            return 0.0
        try:
            # Cap value_fn timeout to avoid hanging
            v = await _await_with_hard_timeout(value_fn(stmt), timeout=value_timeout)
            v_f = _normalize_reward(v)
        except asyncio.TimeoutError:
            logger.debug("value_fn timeout for statement")
            v_f = 0.0
        except Exception:
            v_f = 0.0
        value_cache[key] = v_f
        return v_f

    for sim in range(simulations):
        elapsed_s = max(0.0, float(elapsed()))
        if elapsed_s > _current_time_limit():
            exit_reason = "time_limit"
            break

        if sim % 4 == 0:
            logger.info(
                "[mcts] sim %d/%d nodes=%d elapsed=%.0fs",
                sim + 1,
                simulations,
                nodes_expanded,
                elapsed_s,
            )

        # should_continue callback: check every iteration for timely response.
        stop_reason = _should_stop_now(sim)
        if stop_reason:
            exit_reason = stop_reason
            break

        # Always re-try proving the root periodically; solving child nodes can
        # introduce lemmas that make the root solvable later.
        root_retry_result: Optional[Tuple[bool, float, Optional[str], str]] = None
        if (
            backtrack
            and require_root_solved
            and root.status != NodeStatus.SOLVED
            and (sim == 0 or sim % 4 == 0)
        ):
            stop_reason = _should_stop_now(sim)
            if stop_reason:
                exit_reason = stop_reason
                break
            per_call_timeout = _per_call_timeout(simulations - sim)
            if per_call_timeout <= 0.0:
                exit_reason = "time_limit"
                break
            solved, score, proof, output = await _try_prove(
                prove_fn, root.statement, per_call_timeout
            )
            root.attempts += 1
            if score > root.score:
                root.consecutive_failures = 0
                root.score = score
            else:
                root.consecutive_failures += 1
            if solved and proof:
                root.status = NodeStatus.SOLVED
                root.proof = proof
                tree.backpropagate(root.node_id, 1.0)
                return _make_search_result(
                    solved=True,
                    proof=proof,
                    nodes_expanded=nodes_expanded,
                    max_depth_reached=max_depth_reached,
                    exit_reason="solved",
                    solved_non_root=_solved_non_root_count(),
                    solved_non_root_keys=tuple(solved_non_root_keys.keys()),
                )
            root_retry_result = (solved, score, proof, output)
            if score > best_score:
                best_score = score
                best_score_time = max(0.0, float(elapsed()))

        # Selection: UCB1 walk to leaf
        leaf = tree.select_leaf(c_puct, max_failed_attempts=max_node_attempts)

        # Root exhaustion: select_leaf returned root despite root having
        # children — all children are terminal.  No further tree exploration
        # is possible; the root retry above already handles periodic re-prove.
        if leaf.node_id == root.node_id and root.children:
            tree.backpropagate(leaf.node_id, 0.0)
            if not root_retry_result:
                # Root was not retried this sim — no work done, stop early.
                exit_reason = "root_exhausted"
                break
            continue

        if leaf.status in (NodeStatus.SOLVED, NodeStatus.DEAD):
            # Already terminal — backprop existing value
            reward = 1.0 if leaf.status == NodeStatus.SOLVED else 0.0
            tree.backpropagate(leaf.node_id, reward)
            continue

        if leaf.depth > tree.max_depth:
            leaf.status = NodeStatus.DEAD
            tree.backpropagate(leaf.node_id, 0.0)
            continue

        nodes_expanded += 1
        max_depth_reached = max(max_depth_reached, leaf.depth)

        per_call_timeout = _per_call_timeout(simulations - sim)
        if per_call_timeout <= 0.0:
            exit_reason = "time_limit"
            break

        # Evaluation: try to prove directly (with timeout). If we already retried
        # the root this simulation and selection returned root, reuse that result.
        reused_root_retry = bool(
            root_retry_result is not None and leaf.node_id == root.node_id
        )
        if reused_root_retry and root_retry_result is not None:
            solved, score, proof, output = root_retry_result
        else:
            stop_reason = _should_stop_now(sim)
            if stop_reason:
                exit_reason = stop_reason
                break
            solved, score, proof, output = await _try_prove(
                prove_fn, leaf.statement, per_call_timeout
            )
            leaf.attempts += 1
            if score > leaf.score:
                leaf.consecutive_failures = 0
                leaf.score = score
            else:
                leaf.consecutive_failures += 1

        if solved and proof:
            leaf.status = NodeStatus.SOLVED
            leaf.proof = proof
            tree.backpropagate(leaf.node_id, 1.0)
            if leaf.node_id != root.node_id:
                _record_non_root_solution(leaf.statement, score)
            if (not require_root_solved) or (leaf.node_id == root.node_id):
                return _make_search_result(
                    solved=True,
                    proof=proof,
                    nodes_expanded=nodes_expanded,
                    max_depth_reached=max_depth_reached,
                    exit_reason="solved",
                    solved_non_root=_solved_non_root_count(),
                    solved_non_root_keys=tuple(solved_non_root_keys.keys()),
                )
            continue

        if score > best_score:
            best_score = score
            best_score_time = max(0.0, float(elapsed()))

        # Expansion: generate subgoal children (with timeout)
        if leaf.depth < tree.max_depth and not leaf.children:
            stop_reason = _should_stop_now(sim)
            if stop_reason:
                exit_reason = stop_reason
                break
            expand_timeout = _per_call_timeout(simulations - sim)
            if expand_timeout <= 0.0:
                exit_reason = "time_limit"
                break
            try:
                key = _canonical_statement_key(leaf.statement)
                if key in expand_cache:
                    expand_result = expand_cache[key]
                    cache_hits += 1
                else:
                    raw_expand = await _await_with_hard_timeout(
                        expand_fn(leaf.statement, max_expand_children),
                        timeout=expand_timeout,
                    )
                    expand_result = _normalize_expand_result(raw_expand)
                    expand_cache[key] = expand_result
                    cache_misses += 1
            except asyncio.TimeoutError:
                expand_result = ExpandResult(children=[])
            except Exception as exc:
                logger.warning("expand_fn failed (MCTS): %s", exc)
                expand_result = ExpandResult(children=[])
            if expand_result.solved and expand_result.proof:
                leaf.status = NodeStatus.SOLVED
                leaf.proof = expand_result.proof
                tree.backpropagate(leaf.node_id, 1.0)
                if leaf.node_id != root.node_id:
                    _record_non_root_solution(leaf.statement, score)
                if (not require_root_solved) or (leaf.node_id == root.node_id):
                    return _make_search_result(
                        solved=True,
                        proof=expand_result.proof,
                        nodes_expanded=nodes_expanded,
                        max_depth_reached=max_depth_reached,
                        exit_reason="solved",
                        solved_non_root=_solved_non_root_count(),
                        solved_non_root_keys=tuple(solved_non_root_keys.keys()),
                    )
                continue
            for stmt, prior in expand_result.children:
                tree.add_child(leaf.node_id, stmt, prior=prior)
            leaf.status = (
                NodeStatus.EXPANDED if expand_result.children else NodeStatus.FAILED
            )
        elif not leaf.children:
            leaf.status = NodeStatus.FAILED

        # Backpropagation
        # Blend direct attempt score with an explicit value estimate (fast).
        stop_reason = _should_stop_now(sim)
        if stop_reason:
            exit_reason = stop_reason
            break
        v = await _value(leaf.statement, sim)
        tree.backpropagate(leaf.node_id, max(float(score), float(v)))

    if not exit_reason:
        exit_reason = "max_simulations"
    return _final_search_result(
        tree,
        require_root_solved,
        nodes_expanded,
        max_depth_reached,
        exit_reason,
        solved_non_root=_solved_non_root_count(),
        solved_non_root_keys=tuple(solved_non_root_keys.keys()),
    )
