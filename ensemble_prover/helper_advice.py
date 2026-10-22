"""Bounded search advice attached to an exact checked helper and problem.

Advice is prompt context only. It never restores graph edges, proof status,
failure certificates, or permission to reuse a declaration.
"""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from typing import Any

_TEXT_FIELDS = ("mathematical_purpose", "rationale", "reason", "purpose")
_FAILURE_FIELDS = (
    "identity", "target_statement_hash", "target_source_hash", "environment_hash",
    "helper_context_hash", "proof_hash", "verdict", "error_type", "phase",
    "first_turn_index", "last_turn_index", "count",
)
_MAX_TEXT = 512
_MAX_FAILURES = 3
_MAX_TARGETS = 2


def _digest(value: str) -> str:
    return hashlib.sha256(value.strip().encode("utf-8")).hexdigest()


def normalize_helper_advice(value: Any) -> dict[str, Any]:
    """Copy a small whitelist; ignore nested authority and previous envelopes."""
    if not isinstance(value, Mapping):
        return {}
    result: dict[str, Any] = {}
    for key in _TEXT_FIELDS:
        text = value.get(key)
        if isinstance(text, str) and text.strip():
            result[key] = text[:_MAX_TEXT]
    failures = value.get("failure_memory")
    if isinstance(failures, list):
        kept = []
        for record in failures[-_MAX_FAILURES:]:
            if not isinstance(record, Mapping):
                continue
            item = {}
            for key in _FAILURE_FIELDS:
                field = record.get(key)
                if isinstance(field, str):
                    item[key] = field[:120]
                elif type(field) is int:
                    item[key] = max(-1, min(field, 2**63 - 1))
            if item:
                kept.append(item)
        if kept:
            result["failure_memory"] = kept
    # Linked target descriptions remain historical advice, never live nodes.
    targets = value.get("proved_targets")
    if isinstance(targets, list):
        kept_targets = []
        for target in targets[:_MAX_TARGETS]:
            if not isinstance(target, Mapping):
                continue
            advice = target.get("advisory")
            if not isinstance(advice, Mapping):
                continue
            # No recursive target lists: the envelope has a fixed depth.
            flat = normalize_helper_advice({
                key: advice[key] for key in (*_TEXT_FIELDS, "failure_memory")
                if key in advice
            })
            if flat:
                kept_targets.append({
                    "target_statement": str(target.get("target_statement") or "")[:_MAX_TEXT],
                    "advisory": flat,
                })
        if kept_targets:
            result["proved_targets"] = kept_targets
    return result


def validate_cached_helper_advice(
    envelope: Any, *, source: str, theorem_name: str, preamble_hash: str,
) -> dict[str, Any]:
    if not isinstance(preamble_hash, str) or not preamble_hash:
        return {}
    if not isinstance(envelope, Mapping) or type(envelope.get("version")) is not int:
        return {}
    if envelope["version"] != 1 or any(
        envelope.get(key) != expected for key, expected in (
            ("source_digest", _digest(source)),
            ("theorem_name", theorem_name.strip()),
            ("preamble_hash", preamble_hash),
        )
    ):
        return {}
    root = envelope.get("root_digest")
    if not isinstance(root, str) or len(root) != 64 or any(c not in "0123456789abcdef" for c in root):
        return {}
    advice = normalize_helper_advice(envelope.get("advice"))
    if not advice:
        return {}
    return {
        "version": 1, "source_digest": _digest(source),
        "theorem_name": theorem_name.strip(), "preamble_hash": preamble_hash,
        "root_digest": root, "advice": advice,
    }


def current_cached_helper_advice(
    dossier: Any, source: str, *, preamble: str | None = None,
) -> dict[str, Any]:
    """Read history only while its source, problem and restored frame match."""
    from .proof_dossier import helper_decl_name, text_hash

    name = helper_decl_name(source)
    helper = getattr(dossier, "verified_helpers", {}).get(name)
    graph = getattr(dossier, "proof_graph", None)
    node = graph.nodes.get(graph.helper_name_to_node_id.get(name, "")) if graph else None
    if (helper is None or node is None or str(helper.source).strip() != source.strip()
            or node.source_hash != helper.source_hash):
        return {}
    saved = node.metadata.get("cached_search_advice")
    if not isinstance(saved, Mapping) or saved.get("restored_context") != {
        "dossier_environment": str(getattr(dossier, "current_lean_environment_hash", "") or ""),
        "helper_environment": str(getattr(helper, "verification_environment_hash", "") or ""),
    }:
        return {}
    owner = str(getattr(dossier, "cache_owner_theorem_name", "") or dossier.theorem_name)
    envelope = validate_cached_helper_advice(
        saved, source=source, theorem_name=owner,
        preamble_hash=text_hash(preamble) if preamble is not None else saved.get("preamble_hash"),
    )
    if not envelope or envelope["root_digest"] != _digest(str(dossier.root_statement)):
        return {}
    return envelope["advice"]


def capture_helper_advice(dossier: Any, source: str, preamble: str) -> dict[str, Any]:
    from .helper_inventory import helper_advisory
    from .proof_dossier import helper_decl_name, text_hash

    name = helper_decl_name(source)
    helper = getattr(dossier, "verified_helpers", {}).get(name)
    if helper is None or str(helper.source).strip() != source.strip():
        return {}
    graph = getattr(dossier, "proof_graph", None)
    node = graph.nodes.get(graph.helper_name_to_node_id.get(name, "")) if graph else None
    if node is None or node.source_hash != helper.source_hash:
        return {}
    current = helper_advisory(dossier, name)
    previous = current_cached_helper_advice(dossier, source, preamble=preamble)
    advice = normalize_helper_advice({**previous, **current})
    if not advice:
        return {}
    owner = str(getattr(dossier, "cache_owner_theorem_name", "") or dossier.theorem_name)
    return {
        "version": 1, "source_digest": _digest(source),
        "theorem_name": owner.strip(), "preamble_hash": text_hash(preamble),
        "root_digest": _digest(str(dossier.root_statement)), "advice": advice,
    }


def restore_helper_advice(dossier: Any, record: Mapping[str, Any], preamble: str) -> bool:
    """Attach advice only after current-environment helper admission succeeds."""
    from .proof_dossier import helper_decl_name, text_hash

    source = str(record.get("source") or "").strip()
    owner = str(getattr(dossier, "cache_owner_theorem_name", "") or dossier.theorem_name)
    envelope = validate_cached_helper_advice(
        record.get("helper_advice"), source=source, theorem_name=owner,
        preamble_hash=text_hash(preamble),
    )
    if not envelope or envelope["root_digest"] != _digest(str(dossier.root_statement)):
        return False
    name = helper_decl_name(source)
    helper = getattr(dossier, "verified_helpers", {}).get(name)
    if helper is None or str(helper.source).strip() != source:
        return False
    graph = getattr(dossier, "proof_graph", None)
    node = graph.nodes.get(graph.helper_name_to_node_id.get(name, "")) if graph else None
    if node is None or node.source_hash != helper.source_hash:
        return False
    node.metadata["cached_search_advice"] = {
        **envelope,
        "restored_context": {
            "dossier_environment": str(getattr(dossier, "current_lean_environment_hash", "") or ""),
            "helper_environment": str(getattr(helper, "verification_environment_hash", "") or ""),
        },
    }
    return True
