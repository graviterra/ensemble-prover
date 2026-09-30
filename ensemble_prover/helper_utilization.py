"""Descriptive observations of helper constants in elaborated proof terms.

These receipts inform scheduling only. They never establish proof authority,
logical necessity, or mathematical contribution from mere context inclusion.
"""
from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from typing import Any, Mapping

_OBSERVED = object()


def source_digest(text: str) -> str:
    return hashlib.sha256(str(text).strip().encode()).hexdigest()


def strip_helper_usage_output(output: str, *, marker_identity: str) -> str:
    """Consume machine telemetry while retaining ordinary compiler diagnostics."""
    marker = "ENSEMBLE_HELPER_USAGE:" + marker_identity + ":"
    pattern = re.compile(
        r"^(?:(?:[^\r\n]+:\d+:\d+: )?info: )?"
        + re.escape(marker) + r"(\{[^\r\n]*\})$"
    )
    kept = []
    # Unicode separators can occur inside quoted Lean names in JSON strings.
    # Only LF (optionally preceded by CR) terminates a compiler output line.
    for line in re.findall(r"[^\n]*\n|[^\n]+$", output):
        match = pattern.fullmatch(line.rstrip("\r\n"))
        if match:
            try:
                payload = json.loads(match[1])
            except ValueError:
                payload = None
            if (
                isinstance(payload, dict)
                and type(payload.get("complete")) is bool
                and all(isinstance(payload.get(key), list) for key in
                        ("bindings", "declarations", "direct", "reachable"))
            ):
                continue
        kept.append(line)
    return "".join(kept)


@dataclass(frozen=True)
class HelperUsageObservation:
    statement_hash: str
    proof_hash: str
    preamble_hash: str
    lemma_sources: tuple[str, ...]
    declarations: tuple[str, ...]
    direct_constants: tuple[str, ...]
    reachable_constants: tuple[str, ...]
    complete: bool
    helper_bindings: tuple[tuple[str, str], ...] = ()
    _authority: object = field(default=None, repr=False, compare=False)

    @property
    def observed(self) -> bool:
        return self._authority is _OBSERVED


def parse_helper_usage_observation(
    output: str, *, marker_identity: str, statement: str, proof: str,
    lemmas: tuple[str, ...], preamble: str,
) -> HelperUsageObservation | None:
    matches = re.findall(
        r"ENSEMBLE_HELPER_USAGE:" + re.escape(marker_identity) + r":([^\r\n]+)", output
    )
    if len(matches) != 1:
        return None
    try:
        data = json.loads(matches[0])
    except (ValueError, TypeError):
        return None
    if not isinstance(data, dict) or type(data.get("complete")) is not bool:
        return None
    for key in ("direct", "reachable", "declarations"):
        value = data.get(key)
        if not isinstance(value, list) or len(value) > 10000 or any(
            not isinstance(name, str) or not name for name in value
        ):
            return None
    if not set(data["direct"]).issubset(data["reachable"]):
        return None
    bindings = data.get("bindings")
    if not isinstance(bindings, list) or len(bindings) > 10000:
        return None
    requested = set()
    pairs = []
    for entry in bindings:
        if (
            not isinstance(entry, dict)
            or not isinstance(entry.get("requested"), str) or not entry["requested"]
            or not isinstance(entry.get("resolved"), str) or not entry["resolved"]
            or entry["requested"] in requested
            or entry["resolved"] not in data["declarations"]
        ):
            return None
        requested.add(entry["requested"])
        pairs.append((entry["requested"], entry["resolved"]))
    return HelperUsageObservation(
        source_digest(statement), source_digest(proof), source_digest(preamble),
        tuple(lemmas), tuple(sorted(set(data["declarations"]))), tuple(sorted(set(data["direct"]))),
        tuple(sorted(set(data["reachable"]))), data["complete"], tuple(pairs), _OBSERVED,
    )


def utilization_summary(records: Mapping[str, Any], helpers: Mapping[str, Any]) -> dict[str, Any]:
    """Count unique observed consumers for the currently stored helper source."""
    result: dict[str, Any] = {
        name: {
            "source_hash": source_digest(getattr(helper, "source", "")),
            "observed_consumers": 0, "direct_consumers": 0,
            "transitive_consumers": 0, "root_consumers": 0, "status": "unknown",
        }
        for name, helper in helpers.items()
    }
    for record in records.values():
        if not isinstance(record, dict) or not isinstance(record.get("helpers"), dict):
            continue
        for name, entry in record["helpers"].items():
            current = result.get(name)
            if (
                current is None or not isinstance(entry, dict)
                or entry.get("source_hash") != current["source_hash"]
                or entry.get("usage") not in {"direct", "transitive", "unused"}
            ):
                continue
            usage = entry["usage"]
            current["observed_consumers"] += 1
            current["direct_consumers"] += int(usage == "direct")
            current["transitive_consumers"] += int(usage == "transitive")
            current["root_consumers"] += int(
                record.get("consumer_kind") == "root" and usage != "unused"
            )
            if usage != "unused":
                current["status"] = "used"
            elif current["status"] == "unknown":
                current["status"] = "observed_unused"
    return result


def record_runner_helper_utilization(
    runner: Any, dossier: Any, *, statement: str, proof: str,
    preamble: str, lemmas: Any, consumer_kind: str,
) -> bool:
    """Best-effort observation at an accepted proof boundary; never authority."""
    try:
        lookup = getattr(runner, "helper_usage_observation", None)
        record = getattr(dossier, "record_helper_utilization", None)
        if not callable(lookup) or not callable(record):
            return False
        observation = lookup(statement=statement, proof=proof, preamble=preamble, lemmas=lemmas)
        return bool(record(
            observation, statement=statement, proof=proof, consumer_kind=consumer_kind,
            environment_hash=str(dossier.current_lean_environment_hash or ""),
        ))
    except Exception:
        return False
