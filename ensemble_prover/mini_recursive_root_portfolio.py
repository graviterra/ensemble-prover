"""Provider-free root tactic receipts shared by recursive controller lanes.

Execution keys already bind the exact candidate generator, Lean environment,
ordered helper sources and tactic budget. Only these receipts may cross lanes;
the surrounding recursive driver frame also owns plans and pass allocations.
"""

from collections.abc import Mapping, Sequence
from typing import Any


def _record_keys(value: Any) -> list[str]:
    if not isinstance(value, (list, tuple, set, frozenset)):
        return []
    return [item for item in value if isinstance(item, str) and item]


def root_portfolio_state(record: Mapping[str, Any]) -> dict[str, Any]:
    """Copy only root tactic receipt fields from a driver checkpoint."""

    phases = record.get("root_tactic_portfolio_phases", {})
    phases = phases if isinstance(phases, Mapping) else {}
    raw_offsets = record.get("root_tactic_portfolio_continuations", {})
    offsets: dict[str, int] = {}
    if isinstance(raw_offsets, Mapping):
        for key, raw_offset in list(raw_offsets.items())[:256]:
            if not isinstance(key, str) or len(key) != 64 or isinstance(raw_offset, bool):
                continue
            try:
                offset = int(raw_offset)
            except (TypeError, ValueError, OverflowError):
                continue
            if 0 < offset <= 4096 or (
                offset == 0 and phases.get(key) in ("active", "fallback")
            ):
                offsets[key] = offset
    return {
        "root_tactic_attempted_context_keys": sorted({
            *_record_keys(record.get("root_tactic_attempted_context_keys")),
        }),
        "root_tactic_portfolio_continuations": offsets,
        "root_tactic_portfolio_phases": {
            key: phases[key] for key in offsets
            if phases.get(key) in ("active", "fallback")
        },
        "root_tactic_direct_portfolio_exhausted_execution_keys": sorted({
            item for item in _record_keys(record.get(
                "root_tactic_direct_portfolio_exhausted_execution_keys"
            )) if len(item) == 64
        })[:256],
    }


def merge_legacy_root_portfolios(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    """Recover pre-ledger checkpoints whose lanes kept independent cursors.

    Within a phase the larger offset has completed more candidates. Fallback
    is a later phase even when its offset is smaller than the active offset.
    New checkpoints instead carry a revision so corrections and removals can
    supersede stale offsets, rather than taking their maximum forever.
    """

    result = root_portfolio_state({})
    offsets = result["root_tactic_portfolio_continuations"]
    phases = result["root_tactic_portfolio_phases"]
    for record in records:
        state = root_portfolio_state(record)
        for field in (
            "root_tactic_attempted_context_keys",
            "root_tactic_direct_portfolio_exhausted_execution_keys",
        ):
            result[field] = sorted(set(result[field]) | set(state[field]))
        for key, offset in state["root_tactic_portfolio_continuations"].items():
            phase = state["root_tactic_portfolio_phases"].get(key)
            rank = (phase == "fallback", offset)
            if key not in offsets or rank > (phases.get(key) == "fallback", offsets[key]):
                offsets[key] = offset
                if phase is None:
                    phases.pop(key, None)
                else:
                    phases[key] = phase
    return root_portfolio_state(result)
