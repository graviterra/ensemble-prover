"""Read-only, explicitly dated valuation of checkpoint-bounded usage receipts.

Run with ``python -m ensemble_prover.mini_cost_reconcile --help``. This writes
a separate estimate, never alters ledger history, and never queries providers.
Ambiguous/duplicate observations or a mismatched capture fail closed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import Counter
from datetime import date
from decimal import Decimal
from pathlib import Path
from typing import Any

from .pricing import quote_model_pricing

_TOKENS = ("input_tokens", "cached_input_tokens", "cache_write_tokens", "output_tokens")
_LATE_DISPATCH = "llm_late_dispatch_missing_usage"
_LATE_REJECTION = "llm_late_pre_generation_rejection_recorded"


def _count(value: Any, label: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{label} must be an explicit nonnegative integer")
    return value


def _reject_constant(value: str) -> None:
    raise ValueError(f"Non-finite JSON constant: {value}")


def _json(data: bytes) -> Any:
    return json.loads(data, parse_constant=_reject_constant)


def _mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    return value


def reconcile_checkpoint_cost(
    checkpoint_path: Path,
    trace_path: Path,
    *,
    valuation_date: date,
    assumed_service_tier: str | None = None,
) -> dict[str, Any]:
    """Value reconciled observations under a named date and optional tier assumption.

    The checkpoint must contain the controller state and recorder cutoff. Trace
    token/event totals must agree with it. Receipt identities must be unique;
    unsupported legacy captures cannot silently become authoritative totals.
    Completeness here concerns captured usage only, never invoice reconciliation.
    """
    checkpoint_bytes = Path(checkpoint_path).read_bytes()
    checkpoint = _mapping(_json(checkpoint_bytes), "checkpoint")
    try:
        cutoff = _count(checkpoint["recorder"]["turn_count"], "recorder.turn_count")
        ledger = _mapping(checkpoint["cost_ledger"]["state"], "ledger")
        prefix = _mapping(checkpoint["recorder"]["prefixes"]["turns.jsonl"], "trace prefix")
    except (KeyError, TypeError) as exc:
        raise ValueError("Checkpoint lacks recorder cutoff, trace prefix or controller state") from exc
    rows = []
    prefix_hash = hashlib.sha256()
    prefix_bytes = 0
    with Path(trace_path).open("rb") as stream:
        for ordinal in range(1, cutoff + 1):
            line = stream.readline()
            if not line.endswith(b"\n"):
                raise ValueError(f"Trace truncated before checkpoint turn {ordinal}")
            row = _mapping(_json(line), "trace event")
            if _count(row.get("turn_index"), "turn_index") != ordinal:
                raise ValueError(f"Trace is not contiguous at turn {ordinal}")
            prefix_hash.update(line)
            prefix_bytes += len(line)
            if row.get("phase") == "llm_usage" and row.get("verdict") in {
                "llm_usage_recorded", "llm_usage_missing",
                _LATE_DISPATCH, _LATE_REJECTION,
            }:
                rows.append(row)
    if (prefix_bytes != _count(prefix.get("size"), "trace prefix size")
            or prefix_hash.hexdigest() != prefix.get("sha256")):
        raise ValueError("Trace prefix does not match checkpoint size/hash binding")
    if len(rows) != _count(ledger.get("_events"), "ledger._events"):
        raise ValueError("Trace usage event count does not match checkpoint")
    for key in _TOKENS:
        actual = sum(_count(row.get(key, 0) if row["verdict"] in {
            _LATE_DISPATCH, _LATE_REJECTION,
        } else row.get(key), key) for row in rows)
        if actual != _count(ledger.get("_" + key), "ledger." + key):
            raise ValueError(f"Trace {key} does not match checkpoint")

    seen: set[tuple[str, str, int]] = set()
    response_ids: set[tuple[str, str]] = set()
    observed: Counter[tuple[str, str]] = Counter()
    exposed: dict[tuple[str, str], int] = {}
    late_dispatches: set[tuple[str, str, int]] = set()
    retired_dispatches: set[tuple[str, str, int]] = set()
    details = []
    assumptions: set[str] = set()
    subtotal = Decimal(0)
    unvalued = 0
    for event in rows:
        reservation = event.get("llm_reservation_id")
        if not isinstance(reservation, str) or not reservation:
            raise ValueError("Usage event lacks reservation identity")
        if event["verdict"] in {_LATE_DISPATCH, _LATE_REJECTION}:
            target = event.get("target_id")
            if event["verdict"] == _LATE_DISPATCH:
                targets = event.get("missing_provider_target_ids")
                if not isinstance(targets, list) or len(targets) != 1:
                    raise ValueError("Late dispatch lacks exactly one missing target")
                target = targets[0]
            ordinal = _count(event.get("reservation_dispatch_ordinal"), "late dispatch ordinal")
            if not isinstance(target, str) or not target or not ordinal:
                raise ValueError("Late transition lacks concrete dispatch identity")
            identity = (reservation, target, ordinal)
            transition_set = late_dispatches if event["verdict"] == _LATE_DISPATCH else retired_dispatches
            if identity in transition_set:
                raise ValueError("Duplicate late dispatch transition")
            transition_set.add(identity)
            continue
        counts = event.get("provider_exposed_target_counts")
        if not isinstance(counts, dict):
            raise ValueError("Usage event lacks exposed dispatch counts")
        for target, value in counts.items():
            count = _count(value, "exposed dispatch count")
            if not event.get("late_usage", False):
                exposed[(reservation, target)] = max(exposed.get((reservation, target), 0), count)
        observations = event.get("provider_observations")
        if not isinstance(observations, list):
            raise ValueError("Usage event lacks provider observations")
        token_sum: Counter[str] = Counter()
        for record in observations:
            record = _mapping(record, "provider observation")
            for key in ("base_url", "model", "provider_response_id"):
                if not isinstance(record.get(key, ""), str):
                    raise ValueError(f"Observation {key} must be a string")
            response_id = record.get("provider_response_id", "")
            if response_id:
                response_identity = (record.get("base_url", ""), response_id)
                if response_identity in response_ids:
                    raise ValueError("Duplicate or ambiguous provider response identity")
                response_ids.add(response_identity)
            target = record.get("reservation_target_id")
            ordinal = _count(record.get("reservation_dispatch_ordinal"), "dispatch ordinal")
            if not isinstance(target, str) or not target or not ordinal:
                raise ValueError("Observation lacks a concrete dispatch identity")
            identity = (reservation, target, ordinal)
            if identity in seen:
                raise ValueError(f"Duplicate or ambiguous dispatch observation: {identity}")
            seen.add(identity)
            observed[(reservation, target)] += 1
            tokens = {key: _count(record.get(key), key) for key in _TOKENS}
            token_sum.update(tokens)
            i, c, w, o = (tokens[key] for key in _TOKENS)
            if c + w > i:
                raise ValueError("Cache categories exceed total input tokens")
            tier = record.get("service_tier", "")
            if not isinstance(tier, str):
                raise ValueError("Service tier must be a string")
            tier = tier.strip()
            policy = quote_model_pricing(
                record.get("base_url", ""), record.get("model", ""),
                input_tokens=i, service_tier=tier or assumed_service_tier or "",
                at_date=valuation_date,
            )
            amount = None
            if tier or assumed_service_tier or policy["provider"] != "openai":
                if not tier and assumed_service_tier and policy["provider"] == "openai":
                    assumptions.add(f"missing_service_tier_assumed_{assumed_service_tier}")
                if policy["pricing_known"]:
                    rates = {k: Decimal(str(v)) for k, v in policy["rates_per_million"].items()}
                    amount = ((i - c - w) * rates["input"] + c * rates["cached_input"]
                              + w * rates["cache_write"] + o * rates["output"]) / Decimal(1_000_000)
                    subtotal += amount
            if amount is None:
                unvalued += 1
            details.append({"turn_index": event["turn_index"], "dispatch_identity": list(identity),
                            **tokens, "actual_service_tier": tier,
                            "original_cost_usd": record.get("cost_usd"),
                            "original_pricing_policy": record.get("pricing_policy"),
                            "valuation_policy": policy,
                            "estimated_cost_usd": str(amount) if amount is not None else None})
        if any(token_sum[key] != event[key] for key in _TOKENS):
            raise ValueError("Observation token totals do not match usage event")
    if seen & retired_dispatches:
        raise ValueError("A dispatch has both usage and no-generation receipts")
    for reservation, target, _ in late_dispatches:
        exposed[(reservation, target)] = exposed.get((reservation, target), 0) + 1
    retired = Counter((reservation, target) for reservation, target, _ in retired_dispatches)
    if any(count + retired[key] > exposed.get(key, 0) for key, count in observed.items()):
        raise ValueError("Observed/retired receipts exceed recorded exposed dispatch counts")
    if any(count > exposed.get(key, 0) for key, count in retired.items()):
        raise ValueError("Retired receipts exceed recorded exposed dispatch counts")
    unobserved = sum(max(0, count - observed[key] - retired[key]) for key, count in exposed.items())
    original_cost = ledger.get("_exact_cost_usd")
    if (isinstance(original_cost, bool) or not isinstance(original_cost, (float, int))
            or not math.isfinite(original_cost) or original_cost < 0):
        raise ValueError("Checkpoint lacks a valid original cost subtotal")
    return {
        "schema_version": 1,
        "valuation_date": valuation_date.isoformat(),
        "cutoff_turn_index": cutoff,
        "sources": {
            "checkpoint": {"sha256": hashlib.sha256(checkpoint_bytes).hexdigest(), "bytes": len(checkpoint_bytes)},
            "trace_prefix": {"sha256": prefix_hash.hexdigest(), "bytes": prefix_bytes},
        },
        "original_ledger_subtotal_usd": original_cost,
        "known_subtotal_usd": str(subtotal),
        "captured_usage_valuation_complete": not unvalued and not unobserved,
        "unvalued_observations": unvalued,
        "unobserved_dispatches": unobserved,
        "assumptions": sorted(assumptions),
        "limitations": [
            "Published-rate estimate for captured usage; not a provider invoice or ledger mutation.",
            "Pending activity, contract discounts, credits, taxes and activity outside the capture are excluded.",
            "Checkpoint/trace reconciliation does not authenticate the cost journal hash chain.",
        ],
        "observations": details,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--valuation-date", type=date.fromisoformat, required=True)
    parser.add_argument("--assume-service-tier", choices=("standard", "fast", "priority", "flex", "batch"))
    parser.add_argument("--output", type=Path, help="New sidecar path; existing files are never overwritten")
    args = parser.parse_args()
    try:
        result = reconcile_checkpoint_cost(
            args.checkpoint, args.trace, valuation_date=args.valuation_date,
            assumed_service_tier=args.assume_service_tier,
        )
        rendered = json.dumps(result, indent=2, allow_nan=False) + "\n"
        if args.output:
            with args.output.open("x") as stream:
                stream.write(rendered)
        else:
            print(rendered, end="")
    except (ValueError, OSError) as exc:
        parser.exit(2, f"Reconciliation failed: {exc}\n")


if __name__ == "__main__":
    main()
