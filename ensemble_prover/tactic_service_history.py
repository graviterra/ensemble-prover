"""Durable ordering hints for candidate exploration across helper contexts.

These records describe service, never a Lean verdict. Every selected candidate
must still be checked in the current ordered environment and under its policy.
"""

from __future__ import annotations

import hashlib
import math
import re
from collections.abc import Callable, Mapping, Sequence
from typing import Any, cast

_KEY = re.compile(r"[0-9a-f]{16}")
_PROOF_KEY = re.compile(r"[0-9a-f]{64}")
_MAX_COUNTER = (1 << 63) - 1


def validate_service_history(value: Any) -> dict[str, Any]:
    """Discard malformed scheduling hints without granting proof authority."""
    if not isinstance(value, Mapping) or type(value.get("schema_version")) is not int:
        return {}
    if value["schema_version"] != 1 or not isinstance(value.get("obligation_key"), str):
        return {}
    if not _KEY.fullmatch(value["obligation_key"]):
        return {}
    sequence = value.get("sequence")
    entries = value.get("entries")
    if (
        type(sequence) is not int
        or not 0 <= sequence <= _MAX_COUNTER
        or not isinstance(entries, Mapping)
    ):
        return {}
    clean = {}
    for key, entry in entries.items():
        if (
            not isinstance(key, str)
            or not _PROOF_KEY.fullmatch(key)
            or not isinstance(entry, Mapping)
        ):
            return {}
        seq, allowance = entry.get("sequence"), entry.get("allowance_s")
        if type(allowance) not in {int, float}:
            return {}
        allowance = cast("int | float", allowance)
        if (
            type(seq) is not int
            or not 0 < seq <= sequence
            or not 0 <= allowance <= 1e15
            or not math.isfinite(allowance)
            or type(entry.get("resource_inconclusive")) is not bool
        ):
            return {}
        clean[key] = {
            "sequence": seq,
            "allowance_s": float(allowance),
            "resource_inconclusive": entry["resource_inconclusive"],
        }
    result = {
        "schema_version": 1,
        "obligation_key": value["obligation_key"],
        "sequence": sequence,
        "entries": clean,
    }
    lanes = value.get("renewal_lanes", {})
    if not isinstance(lanes, Mapping):
        return {}
    clean_lanes = {}
    for key, lane in lanes.items():
        if (
            not isinstance(key, str)
            or not _KEY.fullmatch(key)
            or not isinstance(lane, Mapping)
        ):
            return {}
        hashes, seen = lane.get("helper_hashes"), lane.get("seen")
        if (
            not isinstance(hashes, list)
            or not isinstance(seen, list)
            or any(
                not isinstance(item, str) or not _KEY.fullmatch(item) for item in hashes
            )
            or any(
                not isinstance(item, str) or not _PROOF_KEY.fullmatch(item)
                for item in seen
            )
        ):
            return {}
        sequence = lane.get("provider_sequence")
        allowance = lane.get("allowance_s")
        if type(allowance) not in {int, float}:
            return {}
        allowance = cast("int | float", allowance)
        if (
            type(sequence) is not int
            or not 0 <= sequence <= _MAX_COUNTER
            or not 0 <= allowance <= 1e15
            or not math.isfinite(allowance)
        ):
            return {}
        deferred = lane.get("deferred")
        if not isinstance(deferred, list):
            return {}
        normalized: list[dict[str, Any]] = []
        for candidate in deferred:
            if (
                not isinstance(candidate, Mapping)
                or any(
                    not isinstance(candidate.get(field), str)
                    or not candidate[field].strip()
                    for field in ("proof", "tactic", "source")
                )
                or (
                    candidate.get("helper") is not None
                    and not isinstance(candidate["helper"], str)
                )
            ):
                return {}
            normalized.append(
                {
                    field: candidate.get(field)
                    for field in ("proof", "tactic", "source", "helper")
                }
            )
        if len({_proof_key(item["proof"]) for item in normalized}) != len(normalized):
            return {}
        admitted = lane.get("admitted", [])
        resource_wait = lane.get("resource_wait", [])
        if (
            not isinstance(admitted, list)
            or not isinstance(resource_wait, list)
            or any(not isinstance(item, str) for item in admitted)
            or any(not isinstance(item, str) for item in resource_wait)
            or not set(admitted).issubset(
                {_proof_key(item["proof"]) for item in normalized}
            )
            or not set(resource_wait).issubset(
                {_proof_key(item["proof"]) for item in normalized}
            )
        ):
            return {}
        clean_lanes[key] = {
            "helper_hashes": list(hashes),
            "seen": list(dict.fromkeys(seen)),
            "provider_sequence": sequence,
            "allowance_s": float(allowance),
            "deferred": normalized,
            "admitted": list(dict.fromkeys(admitted)),
            "resource_wait": list(dict.fromkeys(resource_wait)),
        }
    if clean_lanes:
        result["renewal_lanes"] = clean_lanes
    return result


def history_for_obligation(value: Any, obligation_key: str) -> dict[str, Any]:
    state = validate_service_history(value)
    if state.get("obligation_key") != obligation_key:
        state = {
            "schema_version": 1,
            "obligation_key": obligation_key,
            "sequence": 0,
            "entries": {},
        }
    return state


def _proof_key(proof: str, lane_key: str = "") -> str:
    return hashlib.sha256(
        (lane_key + "\0" + proof if lane_key else proof).encode("utf-8")
    ).hexdigest()


def _stronger_allowance(requested: float, served: float) -> bool:
    # Match the closer's full-funding tolerance. Ordinary dispatch overhead
    # must not renew a check that already received its configured opportunity.
    return requested > served + max(0.01, requested * 0.01)


def renewal_work_available(
    state: Any,
    *,
    provider_sequence: int = 0,
    drain: bool = False,
    allowance_s: float = 0.0,
    include_admitted: bool = True,
) -> bool:
    """Read-only eligibility for a funded deferred queue in its current context."""
    checked = validate_service_history(state)
    for key, lane in checked.get("renewal_lanes", {}).items():
        admitted = set(lane["admitted"])
        resource_wait = set(lane["resource_wait"])
        waiting = [
            item
            for item in lane["deferred"]
            if include_admitted or _proof_key(item["proof"]) not in admitted
            if (
                _proof_key(item["proof"]) not in resource_wait
                or _stronger_allowance(allowance_s, checked["entries"]
                                      .get(_proof_key(item["proof"], key), {})
                                      .get("allowance_s", 0.0))
            )
        ]
        if waiting and (
            drain
            or (include_admitted and lane["admitted"])
            or provider_sequence > lane["provider_sequence"]
            or any(
                _proof_key(item["proof"], key) not in checked["entries"]
                for item in waiting
            )
            or any(
                (entry := checked["entries"].get(_proof_key(item["proof"], key), {}))
                .get("resource_inconclusive")
                and _stronger_allowance(allowance_s, entry.get("allowance_s", 0.0))
                for item in waiting
            )
        ):
            return True
    return False


def resource_retry_allowances(
    state: Any, *, lane_key: str, helper_hashes: Sequence[str], allowance_s: float,
) -> dict[str, float]:
    """Return prior grants for exact queued resource retries in this context."""
    checked = validate_service_history(state)
    lane = checked.get("renewal_lanes", {}).get(lane_key)
    if not lane or lane["helper_hashes"] != list(helper_hashes):
        return {}
    queued = set(lane["resource_wait"]) | set(lane["admitted"])
    retries = {}
    for candidate in lane["deferred"]:
        proof = candidate["proof"]
        entry = checked["entries"].get(_proof_key(proof, lane_key), {})
        if (_proof_key(proof) in queued and entry.get("resource_inconclusive")
                and _stronger_allowance(allowance_s, entry["allowance_s"])):
            retries[proof] = entry["allowance_s"]
    return retries


def admit_candidates(
    candidates: Sequence[Any],
    state: Mapping[str, Any],
    *,
    lane_key: str,
    helper_hashes: Sequence[str],
    allowance_s: float,
    provider_sequence: int = 0,
    drain: bool = False,
    max_candidates: int = 0,
    candidate_filter: Callable[[Any], bool] | None = None,
) -> tuple[list[Any], dict[str, Any]]:
    """Admit new work and bounded refresh; retain exact deferred proof texts.

    A coalesced helper append or paid provider dispatch grants broad exploration.
    An explicit final drain releases one finite suffix under the caller's existing
    elapsed budget. Repeated closure dispatches cannot create further grants.
    Filtered work retains its deferred text and any unspent prior admission.
    """
    checked = validate_service_history(state)
    if not checked:
        return [item for item in candidates if candidate_filter is None or candidate_filter(item)], {}
    from .mini_tactic_closer import TacticCandidate

    previous = checked.get("renewal_lanes", {}).get(lane_key, {})
    old_hashes = previous.get("helper_hashes", [])
    changed = bool(previous and old_hashes != list(helper_hashes))
    replaced = bool(changed and list(helper_hashes[: len(old_hashes)]) != old_hashes)
    entries = {} if replaced else checked["entries"]
    seen = set(previous.get("seen", ())) if not changed else set()
    # Deferred text survives generator caps and changes in helper priorities.
    pending = {
        item["proof"]: TacticCandidate(**item) for item in previous.get("deferred", ())
    }
    already_admitted = set(previous.get("admitted", ()))
    resource_wait = set(previous.get("resource_wait", ())) if not changed else set()
    stronger = _stronger_allowance(allowance_s, float(previous.get("allowance_s", 0.0)))
    for item in candidates:
        key = _proof_key(item.proof)
        entry = entries.get(_proof_key(item.proof, lane_key), {})
        if key not in seen or (stronger and entry.get("resource_inconclusive")):
            pending[item.proof] = item
    fresh, refresh, filtered_admitted = [], [], []
    for item in pending.values():
        if candidate_filter is not None and not candidate_filter(item):
            if _proof_key(item.proof) in already_admitted:
                filtered_admitted.append(_proof_key(item.proof))
            continue
        entry = entries.get(_proof_key(item.proof, lane_key))
        if (
            _proof_key(item.proof) in resource_wait
            and entry
            and not _stronger_allowance(allowance_s, entry["allowance_s"])
        ):
            continue
        if (
            _proof_key(item.proof) in already_admitted
            or entry is None
            or (entry["resource_inconclusive"] and _stronger_allowance(allowance_s, entry["allowance_s"]))
        ):
            fresh.append(item)
        else:
            refresh.append(item)
    refresh.sort(key=lambda item: entries[_proof_key(item.proof, lane_key)]["sequence"])
    paid_grants = max(
        0, provider_sequence - int(previous.get("provider_sequence", provider_sequence))
    )
    refresh_grants = max(paid_grants, int(changed or not previous))
    admitted_refresh = refresh if drain else refresh[:refresh_grants]
    # Alternate lanes so expensive fresh helper streams do not starve broad work.
    admitted = order_candidates(
        [*fresh, *admitted_refresh], checked, allowance_s=allowance_s, lane_key=lane_key
    )
    granted = [_proof_key(item.proof) for item in admitted]
    if max_candidates > 0 and len(admitted) > max_candidates:
        admitted = admitted[:max_candidates]
    lane = {
        "helper_hashes": list(helper_hashes),
        "seen": sorted({*seen, *(_proof_key(item.proof) for item in pending.values())}),
        "provider_sequence": max(
            provider_sequence, int(previous.get("provider_sequence", 0))
        ),
        "allowance_s": max(0.0, float(allowance_s)),
        "admitted": [*granted, *filtered_admitted],
        "resource_wait": sorted(resource_wait - set(granted)),
        "deferred": [
            {
                field: getattr(item, field)
                for field in ("proof", "tactic", "source", "helper")
            }
            for item in pending.values()
        ],
    }
    return admitted, {lane_key: lane}


def commit_renewal(
    state: Mapping[str, Any], metadata: Mapping[str, Any]
) -> dict[str, Any]:
    """Commit admission only after the enclosing Lean operation returned."""
    checked = validate_service_history(state)
    updates = metadata.get("portfolio_renewal_lanes")
    if not checked or not isinstance(updates, Mapping):
        return checked
    checked["renewal_lanes"] = {**checked.get("renewal_lanes", {}), **updates}
    return validate_service_history(checked)


def retain_acceptance_retry(
    state: Mapping[str, Any],
    candidate: Any,
    *,
    lane_key: str,
) -> dict[str, Any]:
    """Keep a Lean-positive proof whose separate helper acceptance was vetoed.

    The existing acceptance policy permits a later retry. Keep its exact text
    outside the active cursor, so a veto still advances the current portfolio.
    """
    checked = validate_service_history(state)
    lane = checked.get("renewal_lanes", {}).get(lane_key)
    if lane is None:
        return checked
    proof_key = _proof_key(candidate.proof)
    if not any(item["proof"] == candidate.proof for item in lane["deferred"]):
        lane["deferred"].append(
            {
                field: getattr(candidate, field)
                for field in ("proof", "tactic", "source", "helper")
            }
        )
    if proof_key not in lane["admitted"]:
        lane["admitted"].append(proof_key)
    lane["resource_wait"] = [key for key in lane["resource_wait"] if key != proof_key]
    return validate_service_history(checked)


def retain_context_retries(
    state: Mapping[str, Any], attempts: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Keep executed candidates whose results belong to a stale context.

    Preserve each target's lane and all service costs. The retained texts are
    pending checks, with no positive or negative authority in the new context.
    """
    checked = validate_service_history(state)
    lanes = checked.get("renewal_lanes", {})
    indexes = {}
    for attempt in attempts:
        lane_key = str(attempt.get("portfolio_lane_key") or "")
        lane = lanes.get(lane_key)
        proof = attempt.get("proof")
        if lane is None or not isinstance(proof, str) or not proof.strip():
            continue
        if lane_key not in indexes:
            indexes[lane_key] = (
                {item["proof"] for item in lane["deferred"]}, set(lane["admitted"]),
                set(lane["resource_wait"]),
            )
        deferred, admitted, resource_wait = indexes[lane_key]
        key = _proof_key(proof)
        if proof not in deferred:
            lane["deferred"].append({
                "proof": proof, "tactic": str(attempt.get("tactic") or "context_retry"),
                "source": str(attempt.get("source") or "context_retry"),
                "helper": attempt.get("helper"),
            })
            deferred.add(proof)
        if key not in admitted:
            lane["admitted"].append(key)
            admitted.add(key)
        resource_wait.discard(key)
    for lane_key, (_deferred, _admitted, resource_wait) in indexes.items():
        lanes[lane_key]["resource_wait"] = sorted(resource_wait)
    return validate_service_history(checked)


def order_candidates(
    candidates: Sequence[Any],
    state: Mapping[str, Any],
    *,
    allowance_s: float,
    lane_key: str = "",
) -> list[Any]:
    """Serve untouched candidates and stronger resource retries before repeats.

    Newly generated helper routes and broad tactics alternate. The durable
    sequence chooses the starting lane, so a single expensive check per slice
    cannot starve either lane as helpers arrive. No candidate is removed.
    """
    checked = validate_service_history(state)
    if not checked or not checked["entries"]:
        return list(candidates)
    entries = checked["entries"]

    def rank(item: Any) -> tuple[int, int]:
        entry = entries.get(_proof_key(item.proof, lane_key))
        if entry is None:
            return (0, 0)
        if entry["resource_inconclusive"] and allowance_s > entry["allowance_s"]:
            return (0, entry["sequence"])
        return (1, entry["sequence"])

    # Helper and stitching opportunities are regenerated from the full current
    # context. Generic candidates retain their service order across growth.
    specific: list[Any] = []
    broad: list[Any] = []
    for item in candidates:
        lane = (
            specific
            if (
                item.helper is not None
                or str(item.source).startswith(("helper", "stitch", "decl_application"))
            )
            else broad
        )
        lane.append(item)
    specific.sort(key=rank)
    broad.sort(key=rank)
    queues = [specific, broad]
    lane = checked["sequence"] % 2
    offsets = [0, 0]
    ordered: list[Any] = []
    while len(ordered) < len(candidates):
        if offsets[lane] >= len(queues[lane]):
            lane = 1 - lane
        ordered.append(queues[lane][offsets[lane]])
        offsets[lane] += 1
        lane = 1 - lane
    return ordered


def record_attempts(
    state: dict[str, Any], attempts: Sequence[Mapping[str, Any]], *, allowance_s: float
) -> dict[str, Any]:
    checked = validate_service_history(state)
    if not checked:
        return {}
    lane_indexes: dict[str, tuple[
        dict[str, dict[str, Any]], dict[str, None], dict[str, None],
    ]] = {}
    for attempt in attempts:
        proof = attempt.get("proof")
        if not isinstance(proof, str) or not proof:
            continue
        if checked["sequence"] >= _MAX_COUNTER:
            # Rebase relative service order without wrapping the counter.
            ordered = sorted(
                checked["entries"].items(), key=lambda item: item[1]["sequence"]
            )
            for index, (_, entry) in enumerate(ordered, 1):
                entry["sequence"] = index
            checked["sequence"] = len(ordered)
        checked["sequence"] += 1
        lane_key = str(attempt.get("portfolio_lane_key") or "")
        allocated = attempt.get("check_timeout_s")
        served_allowance_s = max(0.0, float(allowance_s))
        native_allowance_cap = max(0.1, served_allowance_s) if served_allowance_s > 0 else 0.0
        if type(allocated) in (int, float):
            allocated = cast("int | float", allocated)
            if 0 < allocated <= native_allowance_cap and math.isfinite(allocated):
                # A late phase may only receive the tail of the enclosing lease.
                # The native checker also applies a 0.1-second minimum to explicit
                # tiny budgets. Record either allocation without inventing grants.
                served_allowance_s = float(allocated)
        inconclusive = str(attempt.get("error_type") or "") in {
            "timeout", "lean_timeout", "infra_failure", "exception", "cancelled",
        }
        checked["entries"][_proof_key(proof, lane_key)] = {
            "sequence": checked["sequence"],
            "allowance_s": served_allowance_s,
            "resource_inconclusive": inconclusive,
        }
        lane = checked.get("renewal_lanes", {}).get(lane_key)
        if lane and not attempt.get("pending_reference_confirmation"):
            if lane_key not in lane_indexes:
                # Ordered dictionaries preserve queue order while each attempt
                # updates membership without rescanning or rehashing the batch.
                lane_indexes[lane_key] = (
                    {item["proof"]: item for item in lane["deferred"]},
                    dict.fromkeys(lane["admitted"]),
                    dict.fromkeys(lane["resource_wait"]),
                )
            deferred, admitted, resource_wait = lane_indexes[lane_key]
            key = _proof_key(proof)
            if inconclusive:
                if proof in deferred:
                    resource_wait.setdefault(key, None)
            else:
                deferred.pop(proof, None)
                resource_wait.pop(key, None)
            admitted.pop(key, None)
    for lane_key, (deferred, admitted, resource_wait) in lane_indexes.items():
        lane = checked["renewal_lanes"][lane_key]
        lane["deferred"] = list(deferred.values())
        lane["admitted"] = list(admitted)
        lane["resource_wait"] = list(resource_wait)
    # Prior allowances govern resource retries. Evicting an executed candidate
    # would make its retained deferred proof look like unserved work again.
    return validate_service_history(checked)
