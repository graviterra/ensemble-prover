"""ProofStateRetrievalAction — target-aware retrieval for one child node."""

from __future__ import annotations

import copy
import time
from typing import Any, ClassVar, FrozenSet

from ..action import MiniOutcome
from ..graph_sync import sync_proof_state_to_graph


class ProofStateRetrievalAction:
    id: str = "proof_state_retrieval"
    priority: int = 25
    cost_estimate_s: float = 5.0
    # H2 fix (2026-05-08): run() calls sync_to_graph(session.dossier, ...)
    # which mutates the dossier's proof_graph. Every other action that
    # touches sync_to_graph declares "dossier" in WRITES; preserving the
    # invariant lets a write-conflict scheduler reason about safe
    # interleavings.
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})

    def __init__(
        self,
        *,
        max_nodes: int = 3,
        max_results: int = 6,
    ) -> None:
        self.max_nodes = int(max_nodes or 0)
        self.max_results = int(max_results or 0)

    def _is_applicable(self, session: Any, *, refresh_quality: bool) -> bool:
        if self.max_nodes <= 0 or self.max_results <= 0:
            return False
        if session.proof_state is None or session.dossier is None:
            return False
        helper_blocks = []
        blocks_getter = getattr(
            session.dossier,
            (
                "verified_helper_blocks"
                if refresh_quality
                else "verified_helper_blocks_snapshot"
            ),
            None,
        )
        if callable(blocks_getter):
            try:
                helper_blocks = list(blocks_getter() or [])
            except Exception:
                helper_blocks = []
        if session.searcher is None and not helper_blocks:
            return False

        def needs_retrieval(node: Any) -> bool:
            try:
                from ensemble_prover.proof_state_scheduler import (
                    _proof_state_node_needs_retrieval,
                )

                return bool(
                    _proof_state_node_needs_retrieval(
                        session.searcher,
                        node,
                        max_results=self.max_results,
                        local_helper_blocks=helper_blocks,
                    )
                )
            except Exception:
                return not bool(getattr(node, "retrieval_attempted", False))

        selected_getter = getattr(session, "selected_work_item_node_ids", None)
        if callable(selected_getter):
            selected_ids = selected_getter(self.id, work_types=("retrieval",))
            if selected_ids:
                node = getattr(session.proof_state, "nodes", {}).get(selected_ids[0])
                return bool(
                    node is not None
                    and getattr(node, "kind", "") == "child_goal"
                    and getattr(node, "status", "") == "open"
                    and needs_retrieval(node)
                )
        child_frontier = getattr(session.proof_state, "child_frontier", None)
        if not callable(child_frontier):
            return False
        try:
            return any(
                needs_retrieval(node)
                for node in child_frontier(max_nodes=max(1, self.max_nodes))
            )
        except Exception:
            return False

    def is_applicable(self, session: Any) -> bool:
        return self._is_applicable(session, refresh_quality=True)

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Return applicability without refreshing helper-quality state."""

        return self._is_applicable(session, refresh_quality=False)

    def next_eligible_at(self, session: Any) -> float:
        proof_state = getattr(session, "proof_state", None)
        nodes = getattr(proof_state, "nodes", {}) or {}
        retry_times = [
            float(getattr(node, "retrieval_retry_after_epoch_s", 0.0) or 0.0)
            for node in nodes.values()
            if getattr(node, "kind", "") == "child_goal"
            and getattr(node, "status", "") == "open"
            and bool(getattr(node, "retrieval_error_transient", False))
            and float(
                getattr(node, "retrieval_retry_after_epoch_s", 0.0) or 0.0
            )
            > time.time()
        ]
        return min(retry_times, default=0.0)

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.proof_state_scheduler import (
            _capture_proof_state_retrieval_commit_guards,
            _commit_current_proof_state_retrieval_records,
            _proof_state_retrieval_exception_is_transient,
            _record_current_proof_state_retrieval_failures,
            _retrieve_proof_state_node_candidates,
        )

        started = time.monotonic()
        selected_ids = ()
        selected_getter = getattr(session, "selected_work_item_node_ids", None)
        if callable(selected_getter):
            selected_ids = selected_getter(self.id, work_types=("retrieval",))

        def current_helper_blocks() -> list[str]:
            blocks_getter = getattr(
                session.dossier,
                "verified_helper_blocks",
                None,
            )
            if not callable(blocks_getter):
                return []
            try:
                return list(blocks_getter() or [])
            except Exception:
                return []

        helper_blocks = current_helper_blocks()
        from ensemble_prover.mathematical_retrieval.async_runtime import (
            RetrievalWorkerCapacityError,
            run_sync_abandonment_safe,
        )

        commit_guards = _capture_proof_state_retrieval_commit_guards(
            session.searcher,
            session.proof_state,
            max_nodes=max(self.max_nodes, len(selected_ids) or 0),
            max_results=self.max_results,
            local_helper_blocks=helper_blocks,
            target_node_ids=selected_ids or None,
        )
        worker_searcher = session.searcher
        try:
            fork_searcher = getattr(
                session.searcher,
                "fork_session_context",
                None,
            )
            if callable(fork_searcher):
                worker_searcher = fork_searcher()
            operation_timeout_s = max(
                0.05,
                float(
                    getattr(worker_searcher, "operation_timeout_s", 30.0)
                    or 30.0
                ),
            )
            records = await run_sync_abandonment_safe(
                lambda: _retrieve_proof_state_node_candidates(
                    worker_searcher,
                    copy.deepcopy(session.proof_state),
                    max_nodes=max(self.max_nodes, len(selected_ids) or 0),
                    max_results=self.max_results,
                    local_helper_blocks=helper_blocks,
                    target_node_ids=selected_ids or None,
                ),
                timeout_s=operation_timeout_s,
            )
        except Exception as exc:
            cost = time.monotonic() - started
            publish_failure = getattr(
                session.searcher,
                "publish_boundary_failure",
                None,
            )
            if callable(publish_failure):
                try:
                    publish_failure(
                        consumer="proof_state",
                        elapsed_s=cost,
                        capacity_exhausted=isinstance(
                            exc,
                            RetrievalWorkerCapacityError,
                        ),
                    )
                except Exception:
                    pass
            live_helper_blocks = current_helper_blocks()
            _record_current_proof_state_retrieval_failures(
                session.searcher,
                session.proof_state,
                commit_guards,
                error=f"{type(exc).__name__}: {exc}",
                transient=_proof_state_retrieval_exception_is_transient(exc),
                max_results=self.max_results,
                local_helper_blocks=live_helper_blocks,
            )
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "record_count": 0,
                    "hit_count": 0,
                    "target_node_ids": list(selected_ids),
                    "retrieval_error": f"{type(exc).__name__}: {exc}",
                },
            )
        # Commit only records whose exact live goal and retrieval context still
        # match the authority captured before the worker was started.
        live_helper_blocks = current_helper_blocks()
        records = _commit_current_proof_state_retrieval_records(
            session.searcher,
            session.proof_state,
            commit_guards,
            records,
            max_results=self.max_results,
            local_helper_blocks=live_helper_blocks,
        )
        publish = getattr(session.searcher, "publish_result_metrics", None)
        if callable(publish):
            try:
                publish(
                    getattr(worker_searcher, "last_result", None),
                    consumer="proof_state",
                )
            except Exception:
                pass
        sync_proof_state_to_graph(
            session.proof_state,
            session.dossier,
            session=session,
            phase="proof_state_retrieval",
            turn_index=int(getattr(session, "iteration", 0)),
            refresh_target_node_ids=selected_ids or None,
        )
        # M6 fix (2026-05-08): bare ``bool(records)`` reports True even
        # when retrieval scanned a node and got zero hits — _retrieve_*
        # emits a record per scanned node regardless of result count.
        # That false-positive cleared ``consumed_frontier_work_keys`` and
        # masked stagnation. Gate progress on actual hit count.
        hit_count = 0
        for rec in records or ():
            if not isinstance(rec, dict):
                continue
            if rec.get("error"):
                continue
            decl_names = rec.get("decl_names")
            if isinstance(decl_names, (list, tuple)) and decl_names:
                hit_count += len(decl_names)
                continue
            result_count = rec.get("result_count")
            if (
                isinstance(result_count, int)
                and not isinstance(result_count, bool)
                and result_count > 0
            ):
                hit_count += result_count
        cost = time.monotonic() - started
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            helpers_added=(),
            progress=hit_count > 0,
            cost_seconds=cost,
            metadata={
                "record_count": len(records),
                "hit_count": hit_count,
                "target_node_ids": list(selected_ids),
                "selected_work_item": dict(getattr(session, "selected_work_item_record", {}) or {}),
            },
        )
