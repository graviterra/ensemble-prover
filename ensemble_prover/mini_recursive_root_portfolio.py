"""Provider-free root tactic receipts shared by recursive controller lanes.

Execution keys already bind the exact candidate generator, Lean environment,
ordered helper sources and tactic budget. Only these receipts may cross lanes;
the surrounding recursive driver frame also owns plans and pass allocations.
"""

from collections.abc import Mapping, Sequence
import math
import re
from typing import Any

from .tactic_service_history import validate_service_history


def validated_portfolio_generation(value: Any) -> dict[str, Any]:
    """Validate saved search text and its exact ordered execution binding.

    Retain the configured portfolio in full. These candidates are pending work;
    each resumed proof still requires verification in its current context.
    """
    if not isinstance(value, Mapping) or type(value.get("schema_version")) is not int or value["schema_version"] != 1:
        return {}
    for name, width in (("obligation_key", 16), ("execution_key", 64),
                        ("generation_context_key", 64), ("generation_execution_key", 64),
                        ("generation_policy_key", 64)):
        if not isinstance(value.get(name), str) or re.fullmatch(rf"[0-9a-f]{{{width}}}", value[name]) is None:
            return {}
    hashes = value.get("execution_helper_hashes")
    if not isinstance(hashes, (list, tuple)) or any(
        not isinstance(item, str) or re.fullmatch(r"[0-9a-f]{16}", item) is None for item in hashes
    ):
        return {}
    phase, offset, candidates = value.get("phase"), value.get("next_candidate_index"), value.get("candidates")
    if (phase not in {"direct", "active", "lift", "fallback"} or type(offset) is not int
            or not isinstance(candidates, (list, tuple))
            or not (0 <= offset < len(candidates)
                    or (phase == "fallback" and not candidates and offset == 0))):
        return {}
    clean, proofs = [], set()
    for candidate in candidates:
        if not isinstance(candidate, Mapping) or any(
            not isinstance(candidate.get(key), str) or not candidate[key].strip()
            for key in ("proof", "tactic", "source")
        ) or (candidate.get("helper") is not None and not isinstance(candidate["helper"], str)):
            return {}
        if candidate["proof"] in proofs:
            return {}
        proofs.add(candidate["proof"])
        clean.append({key: candidate.get(key) for key in ("proof", "tactic", "source", "helper")})
    floor = value.get("candidate_timeout_floor_s", 0.0)
    try:
        valid_floor = type(floor) in (int, float) and math.isfinite(floor) and floor >= 0
    except OverflowError:
        valid_floor = False
    pending_reference = value.get("pending_reference_confirmation", False)
    if not valid_floor or type(pending_reference) is not bool:
        return {}
    return {
        "schema_version": 1,
        **{name: value[name] for name in ("obligation_key", "execution_key", "generation_context_key", "generation_execution_key", "generation_policy_key")},
        "execution_helper_hashes": list(hashes), "phase": phase,
        "next_candidate_index": offset, "candidates": clean,
        "candidate_timeout_floor_s": float(floor),
        "pending_reference_confirmation": pending_reference,
    }


def resumable_portfolio_generation(
    value: Any, *, obligation_key: str, execution_key: str, helper_hashes: Sequence[str],
    generation_policy_key: str,
) -> dict[str, Any]:
    """Carry an unfinished finite generation only across exact helper append.

    This preserves candidate work, never a verdict. Every remaining proof is
    elaborated and audited again in the currently supplied Lean environment.
    """
    generation = validated_portfolio_generation(value)
    if (not generation or generation["obligation_key"] != obligation_key
            or generation["generation_policy_key"] != generation_policy_key):
        return {}
    old_helpers = generation["execution_helper_hashes"]
    if list(helper_hashes[:len(old_helpers)]) != old_helpers:
        return {}
    generation["execution_key"] = execution_key
    generation["execution_helper_hashes"] = list(helper_hashes)
    return generation


def _timing_state(value: Any) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        return {}
    from .mini_tactic_closer import TacticPatternCache

    cache = TacticPatternCache(max_entries=256, record_verdicts=False)
    try:
        cache.restore_checkpoint_state(value)
        return cache.checkpoint_state()
    except (TypeError, ValueError, OverflowError):
        return {}


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
        for key, raw_offset in raw_offsets.items():
            if not isinstance(key, str) or len(key) != 64 or isinstance(raw_offset, bool):
                continue
            try:
                offset = int(raw_offset)
            except (TypeError, ValueError, OverflowError):
                continue
            if offset > 0 or (
                offset == 0 and phases.get(key) in ("direct", "active", "lift", "fallback")
            ):
                offsets[key] = offset
    return {
        "root_tactic_attempted_context_keys": sorted({
            *_record_keys(record.get("root_tactic_attempted_context_keys")),
        }),
        "root_tactic_portfolio_continuations": offsets,
        "root_tactic_portfolio_phases": {
            key: phases[key] for key in offsets
            if phases.get(key) in ("direct", "active", "lift", "fallback")
        },
        "root_tactic_portfolio_generation": validated_portfolio_generation(record.get("root_tactic_portfolio_generation")),
        "root_tactic_service_history": validate_service_history(record.get("root_tactic_service_history")),
        "root_tactic_timing_cache": _timing_state(record.get("root_tactic_timing_cache")),
        "root_tactic_direct_portfolio_exhausted_execution_keys": sorted({
            item for item in _record_keys(record.get(
                "root_tactic_direct_portfolio_exhausted_execution_keys"
            )) if len(item) == 64
        }),
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
        generation = state["root_tactic_portfolio_generation"]
        if generation:
            result["root_tactic_portfolio_generation"] = generation
        for field in ("root_tactic_timing_cache", "root_tactic_service_history"):
            if state[field]:
                result[field] = state[field]
        for field in (
            "root_tactic_attempted_context_keys",
            "root_tactic_direct_portfolio_exhausted_execution_keys",
        ):
            result[field] = sorted(set(result[field]) | set(state[field]))
        for key, offset in state["root_tactic_portfolio_continuations"].items():
            phase = state["root_tactic_portfolio_phases"].get(key)
            phase_ranks = {"direct": 0, "active": 0, "lift": 1, "fallback": 2}
            rank = (phase_ranks.get(phase, 0), offset)
            if key not in offsets or rank > (phase_ranks.get(phases.get(key), 0), offsets[key]):
                offsets[key] = offset
                if phase is None:
                    phases.pop(key, None)
                else:
                    phases[key] = phase
    return root_portfolio_state(result)
