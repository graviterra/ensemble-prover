"""Run the proof-state assembly fixpoint between conversation turns.

When the work frontier exposes an ``assembly`` item, this action rolls newly
verified child evidence into parents without waiting for another LLM turn. It
wraps the shared assembly primitive and returns any root-finalization candidate
through the normal typed outcome path.
"""

from __future__ import annotations

import time
from typing import Any, ClassVar, FrozenSet

from ensemble_prover.proof_dossier import helper_decl_name
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)

from ..action import MiniOutcome
from ..graph_sync import sync_proof_state_to_graph


class InterTurnAssemblyAction:
    id: str = "inter_turn_assembly"
    priority: int = 15
    cost_estimate_s: float = 5.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier", "proof_state"})

    def __init__(
        self,
        *,
        timeout_s: float = 30.0,
        max_nodes: int = 3,
    ) -> None:
        self.timeout_s = float(timeout_s or 0.0)
        self.max_nodes = int(max_nodes or 0)

    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0 or self.max_nodes <= 0:
            return False
        if session.dossier is None or session.proof_state is None or session.lean is None:
            return False
        if session.conv is None:
            return False
        # The work_frontier already filtered for ``assembly`` items; if
        # the action is invoked unconditionally (static priority path),
        # fall back to checking whether assembly_frontier has any node.
        ps = session.proof_state
        getter = getattr(ps, "assembly_frontier", None)
        if callable(getter):
            selected_ids = ()
            selected_getter = getattr(session, "selected_work_item_node_ids", None)
            if callable(selected_getter):
                selected_ids = selected_getter(self.id, work_types=("assembly",))
            if selected_ids:
                target_getter = getattr(ps, "assembly_targets", None)
                if callable(target_getter):
                    try:
                        ready_nodes = target_getter(selected_ids)
                    except Exception:
                        return False
                    if not ready_nodes:
                        return False
                    # M8 fix (2026-05-08): when the scheduler selected a
                    # specific (node_id, assembly_id) pair, validate the
                    # assembly_id against the node's actual ready
                    # assembly groups. ``assembly_targets`` ignores
                    # assembly_id, so without this check a parent with
                    # ready group Y1 could be dispatched as Y2 work.
                    selected_item_getter = getattr(session, "selected_work_item_for", None)
                    if callable(selected_item_getter):
                        item = selected_item_getter(self.id, work_types=("assembly",))
                        wanted = str(getattr(item, "assembly_id", "") or "").strip()
                        if wanted:
                            for node in ready_nodes:
                                ready_groups = self._ready_assembly_ids_for(
                                    proof_state=ps,
                                    node=node,
                                )
                                if wanted in ready_groups:
                                    return True
                            return False
                    return True
            graph = getattr(session.dossier, "proof_graph", None)
            try:
                ready = getter(max_nodes=max(1, self.max_nodes), graph=graph)
            except TypeError:
                try:
                    ready = getter()
                except Exception:
                    return False
            except Exception:
                return False
            return bool(ready)
        return False

    @staticmethod
    def _ready_assembly_ids_for(
        *,
        proof_state: Any,
        node: Any,
    ) -> "frozenset[str]":
        """Return the set of assembly group ids ready on a parent node.

        Tolerant of node shape variations: looks at
        ``node.ready_assembly_ids`` first, then derives from
        ``assembly_groups`` (each group with status=='ready' or
        ``ready==True`` contributes its id).
        """

        ready_getter = getattr(proof_state, "ready_assembly_groups", None)
        if callable(ready_getter):
            try:
                groups = ready_getter(node)
                out = frozenset(
                    str(getattr(group, "assembly_id", "") or "")
                    for group in groups
                    if str(getattr(group, "assembly_id", "") or "").strip()
                )
                if out:
                    return out
            except Exception:
                pass
        try:
            ready_ids = getattr(node, "ready_assembly_ids", None) or ()
            out = {
                str(item or "").strip()
                for item in list(ready_ids)
                if str(item or "").strip()
            }
            if out:
                return frozenset(out)
        except Exception:
            pass
        try:
            groups = getattr(node, "assembly_attempt_groups", None) or ()
            out = set()
            iterator = groups.values() if hasattr(groups, "values") else iter(groups)
            for group in iterator:
                gid = str(getattr(group, "assembly_id", "") or "")
                if not gid:
                    continue
                ready_flag = bool(getattr(group, "ready", False)) or str(
                    getattr(group, "status", "") or ""
                ) == "open"
                if ready_flag:
                    out.add(gid)
            if out:
                return frozenset(out)
        except Exception:
            pass
        try:
            groups = getattr(node, "assembly_groups", None) or {}
            out = set()
            iterator = (
                groups.values() if hasattr(groups, "values") else iter(groups)
            )
            for group in iterator:
                gid = str(getattr(group, "assembly_id", "") or "")
                if not gid:
                    continue
                ready_flag = bool(getattr(group, "ready", False)) or str(
                    getattr(group, "status", "") or ""
                ) == "open"
                if ready_flag:
                    out.add(gid)
            return frozenset(out)
        except Exception:
            return frozenset()

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.proof_state_executor import _run_proof_state_assembly_fixpoint

        started = time.monotonic()
        selected_ids = ()
        selected_assembly_ids = ()
        selected_getter = getattr(session, "selected_work_item_node_ids", None)
        if callable(selected_getter):
            selected_ids = selected_getter(self.id, work_types=("assembly",))
        selected_item_getter = getattr(session, "selected_work_item_for", None)
        if callable(selected_item_getter):
            selected_item = selected_item_getter(self.id, work_types=("assembly",))
            assembly_id = str(getattr(selected_item, "assembly_id", "") or "").strip()
            if assembly_id:
                selected_assembly_ids = (assembly_id,)
        ok, proof, accepted_helpers, records = await _run_proof_state_assembly_fixpoint(
            conv=session.conv,
            lean=session.lean,
            dossier=session.dossier,
            proof_state=session.proof_state,
            turn=int(getattr(session, "iteration", 0)),
            timeout_s=self.timeout_s,
            max_nodes=max(self.max_nodes, len(selected_ids) or 0),
            proof_cache=session.proof_cache,
            target_node_ids=selected_ids or None,
            target_assembly_ids=selected_assembly_ids or None,
        )
        stale_attempts = [
            attempt
            for record in records
            if isinstance(record, dict)
            for attempt in list(record.get("assembly_attempts") or [])
            if isinstance(attempt, dict)
            and str(attempt.get("verdict") or "")
            == "selected_assembly_not_executable"
        ]
        stale_selected = bool(
            selected_assembly_ids
            and stale_attempts
            and not accepted_helpers
            and not ok
        )
        # Sync graph after assembly attempts so subsequent frontier
        # queries reflect the new state.
        sync_proof_state_to_graph(
            session.proof_state,
            session.dossier,
            session=session,
            phase="inter_turn_assembly",
            turn_index=int(getattr(session, "iteration", 0)),
            refresh_target_node_ids=selected_ids or None,
        )
        cost = time.monotonic() - started
        replay_helpers = (
            tuple(session.dossier.verified_helper_blocks())
            if ok and proof and getattr(session, "dossier", None) is not None
            else ()
        )
        helper_names = tuple(
            name
            for block in replay_helpers
            for name in [helper_decl_name(block)]
            if name
        )
        return MiniOutcome(
            action_id=self.id,
            solved=bool(ok),
            proof=proof if ok else None,
            helpers_added=tuple(accepted_helpers or ()),
            progress=bool(ok or accepted_helpers),
            cost_seconds=cost,
            root_candidate=(
                RootFinalizationCandidate(
                    proof=proof or "",
                    replay_helpers=replay_helpers,
                    helper_names=helper_names,
                    phase="inter_turn_assembly",
                    turn_index=int(getattr(session, "iteration", 0)),
                    source_action_id=self.id,
                    target_statement=str(
                        getattr(session.dossier, "root_statement", "")
                        or getattr(getattr(session, "conv", None), "goal_statement", "")
                        or ""
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=proof or "",
                        phase="inter_turn_assembly",
                        turn_index=int(getattr(session, "iteration", 0)),
                        target_statement=str(
                            getattr(session.dossier, "root_statement", "")
                            or getattr(
                                getattr(session, "conv", None),
                                "goal_statement",
                                "",
                            )
                            or ""
                        ),
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        source=self.id,
                    ),
                    metadata={"root_finalization_already_applied": True},
                )
                if ok and proof
                else None
            ),
            metadata={
                "record_count": len(records),
                "assembly_helper_count": len(accepted_helpers or ()),
                "target_node_ids": list(selected_ids),
                "target_assembly_ids": list(selected_assembly_ids),
                "replay_helpers": list(replay_helpers),
                "helper_names": list(helper_names),
                "root_finalization_already_applied": bool(ok and proof),
                "selected_assembly_stale": stale_selected,
                "preserve_frontier_work": stale_selected,
                "selected_work_item": dict(getattr(session, "selected_work_item_record", {}) or {}),
            },
        )
