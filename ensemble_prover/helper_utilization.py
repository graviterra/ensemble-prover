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
    consumer_source: str = ""
    consumer_name: str = ""

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
        if not isinstance(value, list) or any(
            not isinstance(name, str) or not name for name in value
        ):
            return None
    if not set(data["direct"]).issubset(data["reachable"]):
        return None
    bindings = data.get("bindings")
    if not isinstance(bindings, list):
        return None
    declarations = set(data["declarations"])
    requested = set()
    pairs = []
    for entry in bindings:
        if (
            not isinstance(entry, dict)
            or not isinstance(entry.get("requested"), str) or not entry["requested"]
            or not isinstance(entry.get("resolved"), str) or not entry["resolved"]
            or entry["requested"] in requested
            or entry["resolved"] not in declarations
        ):
            return None
        requested.add(entry["requested"])
        pairs.append((entry["requested"], entry["resolved"]))
    return HelperUsageObservation(
        source_digest(statement), source_digest(proof), source_digest(preamble),
        tuple(lemmas), tuple(sorted(declarations)), tuple(sorted(set(data["direct"]))),
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


def declaration_usage_kwargs(runner: Any, sources: Any) -> dict[str, Any]:
    """Request optional telemetry only from adapters exposing this capability."""
    import inspect

    checker = getattr(runner, "check", None)
    try:
        parameters = inspect.signature(checker).parameters
    except (TypeError, ValueError):
        return {}
    if "helper_usage_sources" not in parameters:
        # Capability proxies forward check through **kwargs and expose the
        # generation-safe lookup; old adapters must keep their old API.
        if not callable(getattr(runner, "declaration_usage_observation", None)):
            return {}
        if not any(item.kind == inspect.Parameter.VAR_KEYWORD for item in parameters.values()):
            return {}
    return {"helper_usage_sources": tuple(sources)}


def parse_declaration_usage_observation(
    output: str, *, marker_identity: str, source: str,
    lemmas: tuple[str, ...], preamble: str,
) -> HelperUsageObservation | None:
    from dataclasses import replace
    from .proof_graph import helper_decl_name, helper_decl_statement

    name = helper_decl_name(source)
    if not name or source not in lemmas:
        return None
    matches = re.findall(
        r"ENSEMBLE_HELPER_USAGE:" + re.escape(marker_identity) + r":([^\r\n]+)", output
    )
    if len(matches) != 1:
        return None
    try:
        payload = json.loads(matches[0])
    except (ValueError, TypeError):
        return None
    if not isinstance(payload, dict) or payload.get("consumer") != name:
        return None
    observation = parse_helper_usage_observation(
        output, marker_identity=marker_identity, statement=helper_decl_statement(source),
        proof=source, lemmas=tuple(block for block in lemmas if block != source), preamble=preamble,
    )
    if (
        observation is None
        or dict(observation.helper_bindings).get(name) != payload.get("resolvedConsumer")
    ):
        return None
    return replace(observation, consumer_source=source, consumer_name=name)


def record_runner_declaration_utilization(
    runner: Any, dossier: Any, *, source: str, statement: str,
    proof: str, preamble: str, lemmas: Any,
) -> bool:
    """Publish observed declaration usage only after the exact helper landed."""
    from .proof_graph import helper_decl_statement

    try:
        lookup = getattr(runner, "declaration_usage_observation", None)
        record = getattr(dossier, "record_helper_utilization", None)
        if not callable(lookup) or not callable(record):
            return False
        observation = lookup(
            source=source, statement=statement, proof=proof, preamble=preamble, lemmas=lemmas,
        )
        return bool(record(
            observation, statement=helper_decl_statement(source), proof=source,
            consumer_kind="helper", environment_hash=str(dossier.current_lean_environment_hash or ""),
        ))
    except Exception:
        return False


def transfer_declaration_utilization(source_dossier: Any, target_dossier: Any, names: Any) -> None:
    """Carry committed usage with exact helpers imported from a live route dossier."""
    import copy
    from .mini_deadline_transaction import active_deadline_transaction
    from .proof_dossier import ProofDossier

    if not isinstance(source_dossier, ProofDossier) or not isinstance(target_dossier, ProofDossier):
        return
    selected = frozenset(names)
    if not selected:
        return
    transaction = active_deadline_transaction()
    if transaction is not None and not transaction.can_mutate():
        return
    environment = str(target_dossier.current_lean_environment_hash or "")
    if str(source_dossier.current_lean_environment_hash or "") != environment:
        return

    def eligible(payload: Mapping[str, Any]) -> bool:
        name = payload.get("consumer_declaration_name")
        helper = target_dossier.verified_helpers.get(name)
        return bool(
            name in selected and helper is not None
            and str(target_dossier.current_lean_environment_hash or "") == environment
            and payload.get("environment_hash") == environment
            and payload.get("consumer_declaration_source_hash") == source_digest(helper.source)
            and all(
                dependency in target_dossier.verified_helpers
                and entry.get("source_hash") == source_digest(target_dossier.verified_helpers[dependency].source)
                for dependency, entry in payload.get("helpers", {}).items()
            )
        )

    for key, record in list(source_dossier.helper_utilization_observations.items()):
        payload = copy.deepcopy(record)
        if not eligible(payload) or target_dossier.helper_utilization_observations.get(key) == payload:
            continue

        def publish(key: str = key, payload: dict[str, Any] = payload) -> None:
            if not eligible(payload):
                return
            target_dossier.helper_utilization_observations[key] = payload
            while len(target_dossier.helper_utilization_observations) > 4096:
                target_dossier.helper_utilization_observations.pop(next(iter(target_dossier.helper_utilization_observations)))

        if transaction is not None:
            if not transaction.after_commit(publish):
                continue
        else:
            publish()
        try:
            from .mathematical_memory.service import observe_use

            observe_use(target_dossier, payload)
        except Exception:
            pass
