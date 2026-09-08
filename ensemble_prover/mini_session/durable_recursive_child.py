"""Prepared controller frames and independently verified child continuation."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from functools import wraps
import hashlib
import json
from types import SimpleNamespace
from typing import Any

from ensemble_prover.state_data import clone_json_value

from .action import require_current_action_dispatch


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                     separators=(",", ":")).encode()).hexdigest()


def _pool_attr(action: Any) -> str:
    return str(getattr(action, "budget_attr", "")
               or getattr(action, "progress_continuation_pool_attr", ""))


def bind_controller_checkpoint_callback(
    action: Any, session: Any, *, graph_subpass_context: Any = None,
) -> Any:
    """Carry the exact action owner into its existing factory callback."""
    callback = action.run_conversation_fn
    if callback is None or getattr(session, "checkpoint_registry", None) is None:
        return callback

    @wraps(callback)
    async def invoke(**kwargs: Any) -> Any:
        return await callback(
            **kwargs, checkpoint_parent_action=action,
            checkpoint_graph_subpass_context=(
                graph_subpass_context() if graph_subpass_context is not None else None
            ),
        )

    return invoke


async def restore_controller_children(action: Any, session: Any, frames: dict[str, Any]) -> None:
    """Recover the latest prepared action absent from its committed parent."""
    registry = session.checkpoint_registry
    parent_record = registry.lane_record(session.checkpoint_lane_key)
    if parent_record is None:
        return
    parent_hash = _digest(parent_record)
    candidates = []
    for lane, frame in frames.items():
        descriptor = frame.get("descriptor", {})
        if (descriptor.get("kind") != "controller_conversation"
                or descriptor.get("owner_action_id") != action.id
                or descriptor.get("parent_record_hash") != parent_hash):
            continue
        ordinal = descriptor.get("preparation_ordinal")
        work = frame.get("selected_work", {})
        if (descriptor.get("child_lane") != lane
                or descriptor.get("parent_root_statement") != session.problem.statement_type
                or type(ordinal) is not int or ordinal <= 0
                or work.get("pool_attr") != _pool_attr(action)
                or type(work.get("remaining_passes")) is not int
                or work["remaining_passes"] < 0
                or type(work.get("reservation")) is not dict):
            raise ValueError("Invalid prepared controller allocation")
        candidates.append((ordinal, frame))
    if not candidates:
        return
    candidates.sort(key=lambda item: item[0])
    if len({ordinal for ordinal, _frame in candidates}) != len(candidates):
        raise ValueError("Conflicting prepared controller child order")
    frame = candidates[-1][1]
    work = frame["selected_work"]
    # The planner can create graph routes and strategy lifecycle data before
    # it invokes a child. Keep only those explicit value projections beside
    # the immutable committed parent; proof authority is rechecked normally.
    from .durable_checkpoint import restore_session_record

    prepared_parent = clone_json_value(parent_record)
    prepared_parent["dossier"] = work["parent_dossier"]
    prepared_parent["proof_state"] = work["parent_proof_state"]
    await restore_session_record(session, prepared_parent,
                                 expected_identity=parent_record["identity"])
    action.apply_scheduler_runtime_state(frame["action_runtime"])
    setattr(session, _pool_attr(action), work["remaining_passes"])
    session.recursive_inflight_reservations[action.id] = clone_json_value(work["reservation"])
    graph_context = work.get("graph_subpass_context")
    if graph_context is not None:
        if _pool_attr(action) != "graph_recursive_decompose_remaining":
            raise ValueError("Graph child context has the wrong allocation owner")
        _validate_graph_subpass_context(graph_context, session)
        action._checkpoint_graph_subpass_context = clone_json_value(graph_context)
        session.graph_recursive_decompose_stack = list(graph_context["ancestor_stack"])
        consumed = work["reservation"].get("consumed_frontier_action_key")
        if consumed is not None:
            session.consumed_frontier_action_keys.add(tuple(consumed))
    owner = getattr(session, "_recursive_lane_authority", None) or session
    counts = getattr(owner, "_recursive_conversation_lane_attempt_counts", {})
    counts = dict(counts)
    for key, value in work.get("lane_attempt_counts", {}).items():
        if type(key) is not str or not key or type(value) is not int or value < 0:
            raise ValueError("Invalid prepared recursive lane attempt count")
        counts[key] = max(counts.get(key, 0), value)
    owner._recursive_conversation_lane_attempt_counts = counts
    session._checkpoint_prepared_controller_action = {
        "action_id": action.id, "parent_record_hash": parent_hash,
        "child_lane": frame["descriptor"]["child_lane"],
    }
    action._checkpoint_prepared_controller_marker = session._checkpoint_prepared_controller_action
    if graph_context is not None:
        action._checkpoint_graph_owner_marker = session._checkpoint_prepared_controller_action


def select_prepared_controller_action(session: Any) -> Any:
    """Resume one registry-bound invocation before new frontier maintenance."""
    marker = getattr(session, "_checkpoint_prepared_controller_action", None)
    if not marker:
        return None
    registry = getattr(session, "checkpoint_registry", None)
    if registry is None or type(marker) is not dict:
        raise ValueError("Prepared controller action lacks its checkpoint owner")
    frame = registry.child_record(marker.get("child_lane", ""))
    parent_record = registry.lane_record(session.checkpoint_lane_key)
    descriptor = frame.get("descriptor", {}) if frame else {}
    action_id = marker.get("action_id", "")
    if (parent_record is None or marker.get("parent_record_hash") != _digest(parent_record)
            or descriptor.get("parent_record_hash") != marker["parent_record_hash"]
            or descriptor.get("owner_action_id") != action_id
            or descriptor.get("kind") != "controller_conversation"):
        raise ValueError("Prepared controller action no longer owns its parent frame")
    action = session.registered_action(action_id)
    if (action is None
            or getattr(action, "_checkpoint_prepared_controller_marker", None) is not marker
            or not session.recursive_inflight_reservations.get(action_id)):
        raise ValueError("Prepared controller action lost its reserved allocation")
    if not session.action_dispatchable(action_id, context="checkpoint_prepared_child"):
        return None
    work = frame["selected_work"]
    selected = work.get("selected_work_item_record", {})
    if selected:
        if (work.get("selected_work_item_action_id") != action_id
                or not session._restore_selected_work_record(
                    selected, action_id, context="checkpoint_prepared_child")):
            return None
    else:
        session._clear_selected_work_item()
    if not session._safe_is_applicable(action, context="checkpoint_prepared_child"):
        return None
    session._checkpoint_prepared_controller_action = {}
    if not getattr(action, "_checkpoint_graph_subpass_context", None):
        action._checkpoint_prepared_controller_marker = None
    return action


def owns_graph_child_blocker(action: Any, session: Any, obligation_id: str) -> bool:
    """Recognize only the blocked target of this exact prepared invocation."""
    context = getattr(action, "_checkpoint_graph_subpass_context", None)
    marker = getattr(action, "_checkpoint_graph_owner_marker", None)
    registry = getattr(session, "checkpoint_registry", None)
    if (not context or type(marker) is not dict or registry is None
            or marker is not getattr(action, "_checkpoint_prepared_controller_marker", None)
            or session.registered_action(action.id) is not action
            or marker.get("action_id") != action.id
            or context.get("obligation_id") != obligation_id):
        return False
    frame = registry.child_record(marker.get("child_lane", ""))
    parent_record = registry.lane_record(session.checkpoint_lane_key)
    if (not frame or parent_record is None
            or _digest(parent_record) != marker.get("parent_record_hash")
            or frame["descriptor"].get("parent_record_hash") != marker["parent_record_hash"]
            or frame["descriptor"].get("owner_action_id") != action.id
            or frame["selected_work"].get("graph_subpass_context") != context
            or session.recursive_inflight_reservations.get(action.id)
            != frame["selected_work"]["reservation"]):
        return False
    selected = frame["selected_work"]["selected_work_item_record"]
    if context["parent_context_hash"] != action._recursive_attempt_context_hash(
            session, refresh_quality=False, selected_work_record=selected):
        return False
    saved_graph = frame["selected_work"]["parent_dossier"]["proof_graph"]
    saved_nodes = {node["node_id"]: node for node in saved_graph["nodes"]}
    current_graph = session.dossier.proof_graph
    current = current_graph.nodes.get(obligation_id)
    if (current is None or current.status != "blocked"
            or current.metadata.get("blocker") != "recursive_child_structural_work"
            or saved_nodes.get(obligation_id) != asdict(current)):
        return False
    saved_edges = [edge for edge in saved_graph["edges"]
                   if edge["kind"] == "blocked_by"
                   and obligation_id in {edge["source"], edge["target"]}]
    live_edges = [asdict(edge) for edge in current_graph.edges
                  if edge.kind == "blocked_by"
                  and obligation_id in {edge.source, edge.target}]
    if not saved_edges or sorted(saved_edges, key=_digest) != sorted(live_edges, key=_digest):
        return False
    related_ids = {edge[key] for edge in saved_edges for key in ("source", "target")}
    return all(node_id in current_graph.nodes
               and saved_nodes.get(node_id) == asdict(current_graph.nodes[node_id])
               for node_id in related_ids)


def _validate_graph_subpass_context(context: Any, session: Any) -> None:
    required = {
        "obligation_id", "theorem_name", "root_statement", "branch_key",
        "selected_parent_context", "parent_context_hash", "dossier", "ancestor_stack",
        "child_proof_idea_ids", "child_proof_idea_branch_id",
    }
    if type(context) is not dict or set(context) != required:
        raise ValueError("Invalid graph recursive driver context")
    for key in required - {"dossier", "ancestor_stack", "child_proof_idea_ids"}:
        if type(context[key]) is not str:
            raise ValueError("Invalid graph recursive driver identity")
    for key in ("ancestor_stack", "child_proof_idea_ids"):
        if type(context[key]) is not list or any(type(value) is not str for value in context[key]):
            raise ValueError("Invalid graph recursive driver lineage")
    dossier = context["dossier"]
    graph = session.dossier.proof_graph
    obligation = graph.nodes.get(context["obligation_id"])
    if (type(dossier) is not dict or obligation is None
            or obligation.statement != context["root_statement"]
            or dossier.get("root_statement") != context["root_statement"]
            or dossier.get("theorem_name") != context["theorem_name"]):
        raise ValueError("Graph recursive driver target differs from its obligation")


async def restore_graph_subpass_dossier(
    action: Any, session: Any, *, obligation_id: str, theorem_name: str,
    root_statement: str, selected_work_record: dict[str, Any],
) -> Any:
    """Recheck a saved graph driver's separate dossier under its own target."""
    context = getattr(action, "_checkpoint_graph_subpass_context", None)
    if not context:
        return None
    _validate_graph_subpass_context(context, session)
    if (context["obligation_id"] != obligation_id
            or context["theorem_name"] != theorem_name
            or context["root_statement"] != root_statement
            or context["parent_context_hash"] != action._recursive_attempt_context_hash(
                session, refresh_quality=False, selected_work_record=selected_work_record)):
        raise ValueError("Graph recursive driver no longer owns its current proof context")
    from .durable_session_record import _prepare_dossier

    verifier_view = SimpleNamespace(
        lean=session.lean,
        conv=SimpleNamespace(goal_statement=root_statement, lean_preamble=session.conv.lean_preamble),
    )
    return await _prepare_dossier(verifier_view, context["dossier"])


@dataclass
class PreparedControllerChild:
    registry: Any
    parent: Any
    child: Any
    lane: str
    dispatch_id: str
    record: dict[str, Any]

    def publication_allowed(self) -> bool:
        require_current_action_dispatch(self.parent, self.dispatch_id)
        return True

    def replay_result(self) -> tuple[bool, str | None, bool] | None:
        """Only fresh child restoration can establish a saved proof's authority."""
        result = self.record.get("result")
        if result is not None:
            if (type(result) is not dict or set(result) != {"ok", "proof", "timed_out"}
                    or type(result["ok"]) is not bool or type(result["timed_out"]) is not bool
                    or (result["proof"] is not None and type(result["proof"]) is not str)
                    or result["ok"] != bool(self.child.root_finalized)
                    or (result["ok"] and result["proof"] != self.child.final_proof)):
                raise ValueError("Invalid completed controller child receipt")
            return result["ok"], result["proof"], result["timed_out"]
        if self.child.root_finalized:
            return True, self.child.final_proof, False
        return None

    async def complete(self, *, ok: bool, proof: str | None, timed_out: bool) -> None:
        if self.record.get("result") is None:
            await self.registry.complete_child(
                self.lane, {"ok": ok, "proof": proof, "timed_out": timed_out},
                publication_guard=self.publication_allowed,
            )


async def prepare_controller_child(
    *, parent: Any, child: Any, action: Any, nested_invocation_id: str,
    max_turns: int, deadline_epoch_s: float, graph_subpass_context: Any = None,
) -> PreparedControllerChild | None:
    registry = getattr(parent, "checkpoint_registry", None)
    if registry is None or action is None:
        return None
    if parent.registered_action(action.id) is not action or not nested_invocation_id:
        raise ValueError("A durable controller child needs its exact action and invocation")
    dispatch_id = str(getattr(parent, "_inflight_action_dispatch_id", "") or "")

    def publication_allowed() -> bool:
        require_current_action_dispatch(parent, dispatch_id)
        return True

    parent_lane = parent.checkpoint_lane_key
    parent_record = registry.lane_record(parent_lane)
    if parent_record is None:
        raise ValueError("Controller child has no committed parent")
    descriptor = {
        "kind": "controller_conversation", "owner_action_id": action.id,
        "parent_record_hash": _digest(parent_record),
        "parent_root_statement": parent.problem.statement_type,
        "nested_invocation_id": nested_invocation_id,
        "target_statement": child.problem.statement_type,
        "theorem_name": child.problem.theorem_name, "max_turns": max_turns,
    }
    lane = f"{parent_lane}/controller:{_digest(descriptor)}"
    existing = registry.child_record(lane)
    if existing is None:
        frames = registry.child_records_for_parent(parent_lane)
        ordinal = 1 + max((int(item["descriptor"].get("preparation_ordinal", 0))
                           for item in frames.values()), default=0)
        descriptor.update(child_lane=lane, preparation_ordinal=ordinal,
                          action_deadline_epoch_s=deadline_epoch_s)
        owner = getattr(parent, "_recursive_lane_authority", None) or parent
        await registry.prepare_child(
            parent_lane, descriptor, action.scheduler_runtime_state(),
            {"pool_attr": _pool_attr(action),
             "remaining_passes": getattr(parent, _pool_attr(action)),
             "reservation": parent.recursive_inflight_reservations.get(action.id, {}),
             "parent_dossier": parent.dossier.to_execution_record(),
             "parent_proof_state": (parent.proof_state.to_execution_record()
                                    if parent.proof_state is not None else None),
             "selected_work_item_record": parent.selected_work_item_record,
             "selected_work_item_action_id": parent.selected_work_item_action_id,
             "graph_subpass_context": graph_subpass_context,
             "lane_attempt_counts": getattr(owner, "_recursive_conversation_lane_attempt_counts", {})},
            publication_guard=publication_allowed,
        )
        existing = registry.child_record(lane)
    else:
        if any(existing["descriptor"].get(key) != value for key, value in descriptor.items()):
            raise ValueError("Controller child checkpoint identity mismatch")
        saved_deadline = existing["descriptor"]["action_deadline_epoch_s"]
        if saved_deadline > 0:
            child.recursive_elapsed_deadline_epoch_s = (
                min(deadline_epoch_s, saved_deadline) if deadline_epoch_s > 0 else saved_deadline
            )
    publication_allowed()
    await registry.bind_session(lane, child)
    publication_allowed()
    return PreparedControllerChild(registry, parent, child, lane, dispatch_id, existing)
