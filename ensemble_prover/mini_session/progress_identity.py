"""Progress-only identities; never used as Lean authority or replay receipts."""
from __future__ import annotations

import hashlib
import json
from typing import Any, Callable

from ..contract_identity import parse_lean_contract_identity
from ..proof_dossier import helper_decl_statement, text_hash, verified_helper_bound_contract_identity
from ..proof_graph import graph_node_bound_contract_identity, graph_statement_key


def _key(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def _unique(values):
    return sorted({json.dumps(value, sort_keys=True, separators=(",", ":")) for value in values})


def _statement(statement: str, identity: str, environment: str) -> tuple:
    parsed = parse_lean_contract_identity(identity)
    # Without elaboration evidence, retain exact typed text. Surface matchers
    # intentionally forget details that a progress/budget boundary must keep.
    return ("lean", parsed[0], environment) if parsed else ("surface", statement.strip(), environment)


def helper_progress_keys(dossier: Any) -> dict[str, str]:
    result = {}
    for name, helper in dict(getattr(dossier, "verified_helpers", {}) or {}).items():
        source = str(getattr(helper, "source", "") or "")
        source_hash = str(getattr(helper, "source_hash", "") or text_hash(source))
        statement = helper_decl_statement(source)
        if not statement or source_hash != text_hash(source):
            result[name] = _key((name, source_hash, source))
            continue
        result[name] = _key((
            _statement(statement, verified_helper_bound_contract_identity(helper),
                       str(getattr(helper, "verification_environment_hash", "") or "")),
            str(getattr(helper, "visibility_policy", "") or ""),
            str(getattr(helper, "render_policy", "") or ""),
        ))
    return result


_METADATA = (
    "statement_environment_hash", "helper_context_hash", "proof_authority", "obligation_trust",
    "target_integrity_adjudication", "allow_root_equivalent_target_integrity_adjudication",
    "advisory_only", "route_scope", "activation_status", "candidate_proof", "tactic_candidates",
    "proof_state_node", "proof_state_assembly",
    "verified_helper_render_policy", "verified_helper_visibility_policy", "verified_helper_answer_safety_policy",
    "verified_helper_environment_hash", "verified_helper_open_premise_statements",
    "graph_open_root_reducer_premises", "graph_hollow_root_reducer_certificate_blocked",
    "needs_replay_materialization", "replay_materialization_reason",
)


def graph_progress_projection(dossier: Any, node_record: Callable, *, helper_keys=None) -> tuple[list, list, dict[str, str]]:
    """Quotient alias nodes while preserving route-local dependency grouping.

    Exact proof-state execution/assembly records stay exact. Only graph names,
    diagnostic scratch and duplicate attestations are removed from progress.
    The underlying graph, source hashes and replay closures are untouched.
    """
    graph = getattr(dossier, "proof_graph", None)
    raw_nodes = dict(getattr(graph, "nodes", {}) or {})
    helpers = dict(getattr(dossier, "verified_helpers", {}) or {})
    if helper_keys is None:
        helper_keys = helper_progress_keys(dossier)
    attestations: dict[str, list[tuple[str, Any]]] = {}
    for name, helper in helpers.items():
        attestations.setdefault(str(getattr(helper, "source_hash", "")), []).append((name, helper))
    nodes, records = {}, {}
    for node_id, node in raw_nodes.items():
        if getattr(node, "kind", "") == "scratch":
            continue
        is_tombstone = getattr(graph, "is_superseded_tombstone", None)
        if callable(is_tombstone) and is_tombstone(node):
            continue
        nodes[node_id] = node
        record = node_record(node, fallback_id=node_id)
        metadata = dict(getattr(node, "metadata", {}) or {})
        record.pop("node_id", None)
        record["metadata"].pop("route_id", None)
        record["metadata"].pop("obligation_id", None)
        record["metadata"].update({k: metadata[k] for k in _METADATA if k in metadata})
        helper = helpers.get(getattr(node, "name", "")) if record["kind"] == "helper" else None
        if (helper is not None and record["status"] == "proved"
                and getattr(node, "source_hash", "") == getattr(helper, "source_hash", "")
                and str(getattr(node, "statement", "")).strip() == helper_decl_statement(helper.source).strip()
                and getattr(helper, "source_hash", "") == text_hash(getattr(helper, "source", ""))):
            record = {"kind": "helper", "status": "proved", "fact": helper_keys[node.name],
                      "metadata": record["metadata"],
                      "source_bound": metadata.get("verified_helper_source") == helper.source,
                      "proof_bound": getattr(node, "proof_hash", "") == helper.source_hash}
            replayable = getattr(graph, "_helper_has_replayable_source", None)
            if callable(replayable):
                # These checks are read-only. Keep admission results, never
                # raw receipts whose hashes change when a helper is renamed.
                record["replayable"] = replayable(node)
                record["bridge_replayable"] = replayable(node, allow_formalization_bridge_support=True)
                record["exact_replayable"] = replayable(
                    node, allow_advisory_negative_evidence_exact=True,
                    exact_statement_key=graph_statement_key(node.statement),
                )
        else:
            environment = str(metadata.get("statement_environment_hash") or "")
            bound = graph_node_bound_contract_identity(node)
            record["target"] = _statement(record["target"], bound, environment)
            if record["status"] == "proved" and record["kind"] != "root":
                # A proposition receipt is not proof authority. Canonicalize
                # an attestation only when it matches a registered helper's
                # source and the exact proposition/environment it certifies.
                for name, candidate in attestations.get(record["proof"], ()):
                    if (getattr(candidate, "source_hash", "") == text_hash(candidate.source)
                            and record["target"] == _statement(
                                helper_decl_statement(candidate.source), verified_helper_bound_contract_identity(candidate),
                                str(getattr(candidate, "verification_environment_hash", "") or ""))):
                        record["proof"] = helper_keys[name]
                        if record["source_hash"] == candidate.source_hash:
                            record["source_hash"] = helper_keys[name]
                        break
            if record["kind"] == "strategy_route":
                # A route's formal dependencies and contract are its work;
                # the statement field here contains only strategy narration.
                record["target"] = "route"
                record["source_hash"] = ""
            for field in ("dependencies", "children"):
                record[field] = sorted({helper_keys.get(x, x) for x in record[field]})
            record["proved_helper_name"] = helper_keys.get(record["proved_helper_name"], record["proved_helper_name"])
        records[node_id] = record

    keys = {node_id: _key(record) for node_id, record in records.items()}
    excluded = raw_nodes.keys() - nodes.keys()
    edges = [edge for edge in getattr(graph, "edges", ())
             if edge.source not in excluded and edge.target not in excluded]
    # Refine each route by its own dependency set. A union of global edges
    # would confuse routes {A,B} with two separate routes {A} and {B}.
    base_keys = dict(keys)

    def dependency_key(node_id: str) -> str:
        # Nested routes (including cycles) need a recursive graph identity.
        # Retain exact references there instead of conflating different joint
        # dependencies through their pre-refinement route placeholders.
        if getattr(nodes.get(node_id), "kind", "") == "strategy_route":
            return "route-reference:" + node_id
        return base_keys.get(node_id, "missing:" + node_id)

    for node_id, node in nodes.items():
        if getattr(node, "kind", "") != "strategy_route":
            continue
        contract_getter = getattr(graph, "_route_assembly_contract_signature", None)
        contract = contract_getter(node) if callable(contract_getter) else {}
        contract = dict(contract)
        if contract:
            contract["target_node_id"] = dependency_key(contract["target_node_id"])
            contract["required_node_ids"] = sorted({dependency_key(x) for x in contract["required_node_ids"]})
            contract["required_helper_names"] = sorted({helper_keys.get(x, "missing:" + x) for x in contract["required_helper_names"]})
            # Source hashes bind replay, not new facts. Missing/stale helper
            # references must remain distinguishable from a valid dependency.
            contract["required_helper_source_hashes"] = sorted({
                helper_keys[name] if name in helpers and helpers[name].source_hash == digest
                else "stale:" + name + ":" + digest
                for name, digest in contract["required_helper_source_hashes"].items()
            })
        frames = []
        for frame in dict(getattr(graph, "branch_frames", {}) or {}).values():
            if getattr(frame, "route_id", "") == node_id:
                frames.append({k: getattr(frame, k, "") for k in (
                    "branch_index", "assumption_statement", "case_full_statement", "reducer_statement", "status",
                )})
        records[node_id]["route_contract"] = contract
        records[node_id]["branch_frames"] = _unique(frames)
        records[node_id]["route_dependencies"] = _unique(
            (edge.kind, dependency_key(edge.target))
            for edge in edges if edge.source == node_id
        )
        keys[node_id] = _key(records[node_id])

    for node_id, record in records.items():
        metadata = dict(getattr(nodes[node_id], "metadata", {}) or {})
        route_id = str(metadata.get("route_id") or "")
        if route_id and "metadata" in record:
            record["metadata"]["route_id"] = keys.get(route_id, "missing:" + route_id)
    return _unique(records.values()), _unique((
        keys.get(e.source, "missing:" + e.source), keys.get(e.target, "missing:" + e.target), e.kind,
    ) for e in edges), keys
