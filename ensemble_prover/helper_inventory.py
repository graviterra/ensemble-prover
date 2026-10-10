"""Compact helper presentation with exact, scope-bound access to every fact.

Presentation never changes the admitted Lean context. A helper omitted from a
prompt remains in the dossier and in the complete replay environment.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any, Mapping, Sequence


HELPER_PROMPT_CHAR_BUDGET = 16_000
READ_VERIFIED_HELPERS_TOOL = {
    "type": "function",
    "function": {
        "name": "read_verified_helpers",
        "description": (
            "Read verified helpers available in this exact Lean context. Use name "
            "for an exact declaration lookup, query for text filtering, or neither "
            "to read the complete inventory. Results include complete signatures "
            "and advisory purpose/failure history. Long results are paginated by "
            "character offset: repeat the same name/query with next_offset and "
            "snapshot_id until next_offset is null. No helper is lost from the "
            "global proof state when the prompt shows only selected facts."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Exact Lean declaration name."},
                "query": {"type": "string", "description": "Terms to find in names and signatures."},
                "offset": {"type": "integer", "minimum": 0},
                "length": {"type": "integer", "minimum": 1, "maximum": 12000},
                "snapshot_id": {"type": "string", "description": "Required when continuing a previous page."},
            },
        },
    },
}


def _redact_solution_refs(dossier: Any) -> bool:
    from .proof_dossier import effective_solution_placeholder_suppression

    return effective_solution_placeholder_suppression(
        suppress_solution_placeholders=getattr(dossier, "suppress_solution_placeholders", True),
        opaque_mode=bool(getattr(dossier, "opaque_mode", True)),
        allow_official_answer_visibility=bool(getattr(dossier, "allow_official_answer_visibility", False)),
        official_answer_payload_present=getattr(dossier, "official_answer_payload_present", None),
    )


def select_prompt_helpers(
    helpers: Sequence[Any], *, target: str, char_budget: int = HELPER_PROMPT_CHAR_BUDGET,
) -> list[Any]:
    """Select complete signatures; the budget never limits retained facts."""
    from .proof_dossier import helper_decl_statement, helper_prompt_signature

    tokens = set(re.findall(r"[\w'.]+", target.casefold()))
    tokens = {token for token in tokens if len(token) > 1}
    ranked = []
    for index, helper in enumerate(helpers):
        statement = helper_decl_statement(helper.source)
        words = set(re.findall(r"[\w'.]+", (helper.name + " " + statement).casefold()))
        score = len(tokens & words)
        ranked.append((-score, -index, helper))
    ranked.sort(key=lambda row: (row[0], row[1]))
    selected = []
    remaining = max(0, char_budget)
    for _score, negative_index, helper in ranked:
        cost = len(helper_prompt_signature(helper.source, name=helper.name)) + len(helper.name) + 12
        if cost <= remaining:
            selected.append((-negative_index, helper))
            remaining -= cost
    selected.sort(key=lambda row: row[0])
    return [helper for _index, helper in selected]


def helper_advisory(
    dossier: Any, name: str, *, linked_nodes: Sequence[Any] | None = None,
) -> dict[str, Any]:
    """Read advisory graph metadata without creating a second proof authority."""
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {}
    node = graph.nodes.get(graph.helper_name_to_node_id.get(name, ""))
    metadata = getattr(node, "metadata", {}) or {}
    from .proof_dossier import _prompt_safe_natural_language_text

    def safe_text(value: str) -> str:
        return _prompt_safe_natural_language_text(
            value, limit=0, truncate=False, redact_solution_refs=_redact_solution_refs(dossier),
        )

    def summary(metadata: Mapping[str, Any]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key in ("mathematical_purpose", "rationale", "reason", "purpose"):
            if isinstance(metadata.get(key), str):
                result[key] = safe_text(metadata[key])
        failures = metadata.get("failure_memory")
        if isinstance(failures, list):
            fields = {
                "identity", "target_statement_hash", "target_source_hash", "environment_hash",
                "helper_context_hash", "proof_hash", "verdict", "error_type", "phase",
                "first_turn_index", "last_turn_index", "count",
            }
            result["failure_memory"] = [
                {key: safe_text(value) if isinstance(value, str) else value
                 for key, value in record.items()
                 if key in fields and (isinstance(value, str) or type(value) is int)}
                for record in failures if isinstance(record, Mapping)
            ]
        return result

    result = summary(metadata)
    helper = getattr(dossier, "verified_helpers", {}).get(name)
    if node is None or helper is None or node.source_hash != helper.source_hash:
        return result
    linked = []
    for target in linked_nodes if linked_nodes is not None else graph.nodes.values():
        target_metadata = target.metadata or {}
        if (target_metadata.get("verified_by_helper_node_id") != node.node_id
                or target.status != "proved" or target.source_hash != helper.source_hash
                or graph.is_superseded_tombstone(target)
                or not graph._helper_certifies_node(node, target)):
            continue
        advice = summary(target_metadata)
        if advice:
            linked.append({
                "node_id": safe_text(target.node_id),
                "target_statement": safe_text(target.statement),
                "current_source_hash": target.source_hash,
                "advisory": advice,
            })
    if linked:
        result["proved_targets"] = linked
    return result


def read_verified_helpers(
    dossier: Any, blocks: Sequence[str], args: Mapping[str, Any],
) -> dict[str, Any]:
    """Read only a freshly validated dispatch scope; never admit retrieved facts."""
    from .proof_dossier import helper_decl_name, helper_prompt_signature
    from .prompt_page_text import prompt_page_text
    from .utils import canonical_lean_identifier

    name = args.get("name", "")
    query = args.get("query", "")
    snapshot = args.get("snapshot_id", "")
    offset = args.get("offset", 0)
    length = args.get("length", 6000)
    if (not isinstance(name, str) or not isinstance(query, str)
            or not isinstance(snapshot, str)
            or type(offset) is not int or offset < 0
            or type(length) is not int or not 1 <= length <= 12000):
        raise ValueError("helper lookup requires text filters and valid integer page bounds")
    if name and query:
        raise ValueError("use either an exact name or a text query")
    if offset and not snapshot:
        raise ValueError("continuing helper lookup requires snapshot_id")
    sources = dossier.validate_helper_context(tuple(blocks))
    terms = query.casefold().split()
    exact_name = canonical_lean_identifier(name.strip().removeprefix("_root_."))
    redact_solution_refs = _redact_solution_refs(dossier)
    graph = getattr(dossier, "proof_graph", None)
    linked_nodes: dict[str, list[Any]] = {}
    if graph is not None:
        for node in graph.nodes.values():
            owner = (node.metadata or {}).get("verified_by_helper_node_id")
            if isinstance(owner, str) and owner:
                linked_nodes.setdefault(owner, []).append(node)
    records = []
    for source in sources:
        helper_name = helper_decl_name(source)
        helper = dossier.verified_helpers[helper_name]
        if name and exact_name != canonical_lean_identifier(helper_name.removeprefix("_root_.")):
            continue
        signature = helper_prompt_signature(
            source, name=helper_name, redact_solution_refs=redact_solution_refs,
        )
        if terms and not all(term in (helper_name + " " + signature).casefold() for term in terms):
            continue
        records.append({
            "name": helper_name,
            "signature": signature,
            "source_hash": helper.source_hash,
            "support_names": list(helper.support_names),
            "replay_context_names": list(helper.replay_context_names),
            "advisory": helper_advisory(dossier, helper_name, linked_nodes=(
                linked_nodes.get(graph.helper_name_to_node_id.get(helper_name, ""), ())
                if graph is not None else ()
            )),
        })
    def ordered_fields(value: Any) -> Any:
        if isinstance(value, list):
            return [ordered_fields(item) for item in value]
        if not isinstance(value, dict):
            return value
        keys = sorted(value)
        # A hexadecimal source identity separates ordinary partial symbols
        # from name fields, whose initial letter could complete a reference.
        for identity, name in (("source_hash", "name"), ("current_source_hash", "node_id")):
            if identity in value and name in value:
                keys.remove(identity)
                keys.insert(keys.index(name), identity)
        return {key: ordered_fields(value[key]) for key in keys}

    content = json.dumps(ordered_fields(records), ensure_ascii=False)
    content = prompt_page_text(content, redact_solution_refs=redact_solution_refs)
    identity = hashlib.sha256(json.dumps({
        "scope": list(sources), "name": name, "query": query, "content": content,
    }, ensure_ascii=False, sort_keys=True).encode()).hexdigest()
    if snapshot and snapshot != identity:
        return {"status": "context_changed", "restart_offset": 0, "snapshot_id": identity}
    end = min(len(content), offset + length)
    return {
        "status": "ok", "snapshot_id": identity,
        "total_available": len(sources), "matched_helpers": len(records),
        "offset": offset, "total_chars": len(content),
        "next_offset": end if end < len(content) else None,
        "advisory_policy": "Purpose and failure history guide search; they do not prove or refute a statement.",
        # Keep the page last: later metadata could complete a partial symbol
        # at the page boundary when provider answer visibility is applied.
        "content": content[offset:end],
    }


def run_read_verified_helpers_tool(
    dossier: Any, blocks: Sequence[str], args: Mapping[str, Any],
) -> str:
    """Return correctable request errors without inventing infrastructure retries."""
    try:
        result = read_verified_helpers(dossier, blocks, args)
    except (TypeError, ValueError) as exc:
        from .proof_dossier import _prompt_safe_natural_language_text

        result = {
            "status": "unavailable",
            "error": _prompt_safe_natural_language_text(str(exc), limit=500),
            "execution_disposition": "completed_semantic",
        }
    return json.dumps(result, ensure_ascii=False)
