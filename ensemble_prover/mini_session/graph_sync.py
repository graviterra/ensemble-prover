"""Best-effort proof-state → graph projection with recorded failures."""

from __future__ import annotations

from typing import Any

GRAPH_SYNC_FAILED_METRIC = "mini_session_proof_state_graph_sync_failed"


def sync_proof_state_to_graph(
    proof_state: Any,
    dossier: Any,
    *,
    session: Any = None,
    phase: str = "",
    turn_index: int = 0,
    **sync_kwargs: Any,
) -> bool:
    """Call ``proof_state.sync_to_graph`` without dropping Lean-accepted work.

    Projection failures stay non-fatal. They increment a dossier metric and
    emit a session event so graph-native lanes are not silently desynced.
    """

    if proof_state is None:
        return True
    sync = getattr(proof_state, "sync_to_graph", None)
    if not callable(sync):
        return True
    try:
        sync(
            dossier,
            phase=str(phase or ""),
            turn_index=int(turn_index or 0),
            **sync_kwargs,
        )
        return True
    except Exception as exc:
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            increment(GRAPH_SYNC_FAILED_METRIC)
        else:
            dossier_increment = getattr(dossier, "increment_tool_metric", None)
            if callable(dossier_increment):
                dossier_increment(GRAPH_SYNC_FAILED_METRIC)
        record_event = getattr(session, "_record_event", None)
        if callable(record_event):
            record_event(
                {
                    "phase": "proof_state_graph_sync_failed",
                    "sync_phase": str(phase or ""),
                    "turn_index": int(turn_index or 0),
                    "error_type": type(exc).__name__,
                    "error": str(exc)[:240],
                    "verdict": "graph_sync_failed",
                }
            )
        return False
