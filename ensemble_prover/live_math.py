"""Small observational descriptions of the work actually dispatched by Mini."""
from __future__ import annotations

from typing import Any


def _text(value: Any, limit: int = 4096) -> str:
    return value[:limit] if isinstance(value, str) else ""


def describe_dispatch(work: Any, graph: Any, action_id: str, *, scope: str = "") -> dict[str, Any]:
    """Explain a selected target without validating or changing proof authority."""
    work = work if isinstance(work, dict) else {}
    record = work.get("graph_record")
    record = record if isinstance(record, dict) else {}
    quote = record.get("root_value_scheduler", work.get("root_value_scheduler"))
    quote = quote if isinstance(quote, dict) else {}
    # A mapper may fall through to a different action after ranking.
    if quote.get("action_id") != action_id:
        quote = {}
    work_type = _text(work.get("work_type"), 80)
    assembly = work_type in {"assembly", "assemble_route"}
    route_id = _text(
        quote.get("root_consumer_id")
        or (work.get("assembly_id") if assembly else "")
        or record.get("route_id") or work.get("route_id"), 160,
    )
    obligation_id = _text(work.get("graph_node_id") or work.get("node_id"), 160)
    name = ""
    direct_root = False
    try:
        nodes = getattr(graph, "nodes", {})
        route = nodes.get(route_id) if isinstance(nodes, dict) else None
        name = _text(getattr(route, "name", ""), 240)
        direct_root = bool(obligation_id and obligation_id == getattr(graph, "root_node_id", None))
    except Exception:
        # Optional observation must never become an admission gate to solving.
        pass
    target_label = "original theorem" if scope == "problem" else "session target"
    if not route_id and direct_root:
        name = f"Direct work on the {target_label}"
    connection = _text(quote.get("root_connection"), 80) or "unclassified"
    count = quote.get("open_and_siblings")
    count = count if type(count) is int and count >= 0 else None
    if quote.get("exploration_reserved") is True:
        reason = "Reserved exploration turn for speculative mathematics; root relevance remains unestablished."
    elif assembly:
        reason = f"Selected route assembly to attempt the reduction back to the {target_label}."
    elif connection == "declared_requirement":
        remaining = f" {count} unresolved route requirements remain." if count is not None else ""
        reason = "Declared root requirement prioritized by estimated contribution and cost." + remaining
    elif quote:
        reason = "Selected using estimated contribution, cost, and within-action fairness; root connection is unclassified."
    else:
        reason = "Action dispatched; a ranking explanation was not recorded for this selection."
    reason += " Scheduling is heuristic, not a proof."
    statement = work.get("exact_target_statement") or work.get("target_statement")
    return {
        "approach_id": route_id,
        "approach": name or route_id,
        "obligation_id": obligation_id,
        "statement": _text(statement),
        "statement_truncated": isinstance(statement, str) and len(statement) > 4096,
        "work_type": work_type,
        "connection": connection,
        "reason": reason,
        "open_requirements": count,
    }


def prepared_request_event(reservation: Any) -> dict[str, Any]:
    """Copy only bounded configuration observations, never transport authority."""
    metadata = reservation.metadata if isinstance(reservation.metadata, dict) else {}
    raw = metadata.get("mini_request_envelopes")
    raw = raw if isinstance(raw, list) else []
    envelopes = []
    for value in raw[:32]:
        if not isinstance(value, dict):
            continue
        envelope = {
            key: _text(value.get(key), 160)
            for key in (
                "model", "work_type", "request_kind", "effective_reasoning_effort",
                "reasoning_transport_mode", "cap_source",
            )
        }
        limit = value.get("max_output_tokens")
        envelope["max_output_tokens"] = limit if type(limit) is int and 0 < limit < 10**12 else None
        envelopes.append(envelope)
    return {
        "phase": "llm_request_prepared",
        "verdict": "request_prepared",
        "llm_request_id": _text(reservation.request_id, 160),
        "llm_reservation_id": _text(reservation.reservation_id, 160),
        "role": _text(reservation.role, 80),
        "session_scope": _text(reservation.scope, 160),
        "action_id": _text(reservation.action_id, 160),
        "call_kind": _text(reservation.call_kind, 80),
        "action_dispatch_id": _text(metadata.get("action_dispatch_id"), 160),
        "session_activation_id": _text(metadata.get("session_activation_id"), 160),
        "mini_request_envelopes": envelopes,
        "envelopes_truncated": len(raw) > 32,
    }
