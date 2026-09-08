"""Preserve inert graph history without undoing conservative proof repairs."""

from __future__ import annotations

import copy
from dataclasses import asdict, fields
from typing import Any

from ensemble_prover.proof_graph import ProofGraph, ProofGraphAttempt, ProofGraphEdge, ProofGraphNode
from ensemble_prover.state_data import clone_json_value


def exact_graph_record(graph: ProofGraph, reporting_record: dict[str, Any]) -> dict[str, Any]:
    """Keep the familiar schema while excluding reporting-side annotations."""
    record = dict(reporting_record)
    record.update(
        nodes=[asdict(node) for node in graph.nodes.values()],
        edges=[asdict(edge) for edge in graph.edges],
        attempts=[asdict(attempt) for attempt in graph.attempts],
        branch_frames=[asdict(frame) for frame in graph.branch_frames.values()],
        helper_name_to_node_id=dict(graph.helper_name_to_node_id),
        attempt_history_pruned=graph.attempt_history_pruned,
        next_attempt_index=graph._next_attempt_index,
    )
    return clone_json_value(record, label="exact execution graph memory")


def _typed(raw: Any, cls: Any) -> Any:
    if type(raw) is not dict or set(raw) != {field.name for field in fields(cls)}:
        raise ValueError("Invalid execution graph value fields")
    for name, value in raw.items():
        if name == "metadata":
            valid = type(value) is dict
        elif name in {"helper_names", "support_names", "attempt_ids"}:
            valid = type(value) is list and all(type(item) is str for item in value)
        elif name == "turn_index":
            valid = type(value) is int
        else:
            valid = type(value) is str
        if not valid:
            raise ValueError(f"Invalid execution graph field {name}")
    return cls(**copy.deepcopy(raw))


def _authority_record(node: ProofGraphNode) -> dict[str, Any]:
    record = asdict(node)
    metadata = record["metadata"]
    # These are derived search scores and unverified surface cognition labels.
    # Typed Lean identities, receipts, statuses and every other field remain
    # part of the comparison against the conservative inverse.
    metadata.pop("search_value", None)
    if not metadata.get("claim_id"):
        metadata.pop("claim_id", None)
    identity = metadata.get("statement_identity")
    if type(identity) is str and identity.startswith("surface-statement:"):
        metadata.pop("statement_identity", None)
    return record


def restore_graph_memory(record: dict[str, Any], graph: ProofGraph) -> None:
    """Recover exact diagnostics only when proof-authoritative fields agree."""
    raw = clone_json_value(record, label="execution graph memory restore")
    if type(raw) is not dict or raw.get("schema_version") != 1:
        raise ValueError("Invalid execution graph schema")
    raw_nodes = [_typed(item, ProofGraphNode) for item in raw.get("nodes", [])]
    raw_attempts = [_typed(item, ProofGraphAttempt) for item in raw.get("attempts", [])]
    raw_edges = [_typed(item, ProofGraphEdge) for item in raw.get("edges", [])]
    if len({node.node_id for node in raw_nodes}) != len(raw_nodes):
        raise ValueError("Duplicate execution graph node identity")
    if len({attempt.attempt_id for attempt in raw_attempts}) != len(raw_attempts):
        raise ValueError("Duplicate execution graph attempt identity")

    diagnostic_nodes = set()
    for node in raw_nodes:
        checked = graph.nodes.get(node.node_id)
        if checked is None:
            # Failed subgoal probes create helper-shaped history without ever
            # admitting a declaration. Preserve that history, never a fact.
            if (node.kind == "helper" and node.status == "rejected"
                    and not node.proof_hash and not node.source_hash
                    and not node.support_names
                    and not any("verified" in key or "certificate" in key for key in node.metadata)):
                graph.nodes[node.node_id] = node
                diagnostic_nodes.add(node.node_id)
            continue
        original_authority = _authority_record(node)
        checked_authority = _authority_record(checked)
        # Legacy consumer repair can fill an absent descriptive claim label;
        # an explicit saved label or any other changed field stays checked.
        if not node.metadata.get("claim_id"):
            checked_authority["metadata"].pop("claim_id", None)
        if original_authority == checked_authority:
            graph.nodes[node.node_id] = node

    checked_attempts = {attempt.attempt_id: attempt for attempt in graph.attempts}
    attempts = []
    for attempt in raw_attempts:
        checked = checked_attempts.pop(attempt.attempt_id, None)
        if checked is not None:
            attempts.append(checked)
        elif (attempt.node_id in diagnostic_nodes and not attempt.proof_hash
              and attempt.verdict in {"variant_type_ok", "variant_type_inconclusive", "tactic_rejected"}):
            attempts.append(attempt)
    graph.attempts = [*attempts, *checked_attempts.values()]
    edge_keys = {(edge.source, edge.target, edge.kind) for edge in graph.edges}
    for edge in raw_edges:
        key = (edge.source, edge.target, edge.kind)
        if (key not in edge_keys and edge.kind == "decomposes_to"
                and edge.source in graph.nodes and edge.target in diagnostic_nodes):
            graph.edges.append(edge)
            edge_keys.add(key)
    graph._rebuild_edge_index()
    graph._sync_next_attempt_index()
