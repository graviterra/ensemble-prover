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
            "global proof state when the prompt shows only selected facts. "
            "Default pages prefer complete records; include_provenance adds the "
            "full replay context when that history is needed."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Exact Lean declaration name."},
                "query": {"type": "string", "description": "Terms to find in names and signatures."},
                "offset": {"type": "integer", "minimum": 0},
                "length": {"type": "integer", "minimum": 1, "maximum": 12000},
                "snapshot_id": {"type": "string", "description": "Required when continuing a previous page."},
                "include_provenance": {"type": "boolean", "description": "Include full replay context names; repeat on subsequent pages."},
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


def _helper_source_and_name(helper: Any) -> tuple[str, str]:
    from .proof_dossier import helper_decl_name

    source = str(getattr(helper, "source", None) or helper or "").strip()
    return source, helper_decl_name(source) or str(getattr(helper, "name", "") or "")


def helper_presentation_kind(helper: Any, *, target: str) -> str:
    """Describe a helper's search role without changing its proof authority.

    Local hypotheses are ordinary theorem parameters. A conditional reaching
    the current target, or reducing a global existence claim to another
    quantified bound, is presented as a conditional route.
    Surface matching is deliberately advisory and never retires a helper.
    """
    from .finite_claim_check import _split_top_level_arrow, _unwrap_transparent_parens
    from .helper_quality import _split_top_level_connective
    from .proof_graph import (
        graph_statement_key, graph_statement_leading_contract, graph_statement_root_equivalent,
    )
    from .proof_dossier import helper_decl_statement

    source, _name = _helper_source_and_name(helper)
    statement = helper_decl_statement(source)
    def contract(text: str) -> tuple[str, list[str]]:
        premises = []
        current = text
        while current:
            current, _names, binder_premises = graph_statement_leading_contract(current)
            premises.extend(binder_premises)
            current = _unwrap_transparent_parens(current)
            # Arrows within an existential body are part of that proposition,
            # not extra hypotheses of the helper declaration.
            if current.startswith(("∃", "Exists ")):
                break
            arrow = _split_top_level_arrow(current)
            if arrow is None:
                break
            premise, current = arrow
            premises.append(_unwrap_transparent_parens(premise))
        return current, premises

    conclusion, premises = contract(statement)
    root_conclusion, _ = contract(target)

    def matches_root(candidate: str) -> bool:
        return bool(target.strip()) and (
            graph_statement_root_equivalent(candidate, target)
            or (bool(root_conclusion.strip())
                and graph_statement_key(candidate) == graph_statement_key(root_conclusion))
        )

    equivalence = _split_top_level_connective(conclusion, ("↔", "<->"))
    if equivalence:
        return "reformulation"
    proof_premises = list(premises)
    proof_premises.extend(getattr(helper, "contract_proof_binder_types", ()) or ())
    proof_premises.extend(getattr(helper, "open_premise_statements", ()) or ())
    global_reduction = conclusion.startswith(("∃", "Exists ")) and any(
        _unwrap_transparent_parens(str(premise)).startswith(("∀", "forall ", "∃", "Exists "))
        for premise in proof_premises
    )
    if proof_premises and (matches_root(conclusion) or global_reduction):
        return "conditional_route"
    return "fact"


def select_prompt_helpers(
    helpers: Sequence[Any], *, target: str, char_budget: int = HELPER_PROMPT_CHAR_BUDGET,
) -> list[Any]:
    """Select diverse complete signatures from helper objects or source strings.

    Facts, reformulations and conditional routes share the display.
    Root vocabulary alone cannot let hundreds of conditional routes crowd out
    the independently useful facts. The budget never limits retained facts.
    """
    from .proof_dossier import helper_decl_statement, helper_prompt_signature
    from .proof_graph import graph_statement_key

    tokens = {token for token in re.findall(r"[\w'.]+", target.casefold()) if len(token) > 1}
    rows = []
    for index, helper in enumerate(helpers):
        source, name = _helper_source_and_name(helper)
        statement = helper_decl_statement(source)
        words = set(re.findall(r"[\w'.]+", statement.casefold()))
        cost = len(helper_prompt_signature(source, name=name)) + len(name) + 12
        rows.append((index, helper, statement, len(tokens & words), cost))
    remaining = max(0, char_budget)
    if sum(row[4] for row in rows) <= remaining:
        return list(helpers)

    buckets: dict[str, list[tuple[int, Any, str, int, int]]] = {
        "fact": [], "reformulation": [], "conditional_route": [],
    }
    seen: set[str] = set()
    for row in sorted(rows, key=lambda row: (-row[3], -row[0])):
        key = graph_statement_key(row[2])
        if key and key in seen:
            continue
        seen.add(key)
        buckets[helper_presentation_kind(row[1], target=target)].append(row)
    selected = []
    # Give building blocks three opportunities for each reformulation/route;
    # empty categories immediately yield their capacity to the others.
    while any(buckets.values()):
        for kind in ("fact", "fact", "reformulation", "fact", "conditional_route"):
            bucket = buckets[kind]
            while bucket:
                row = bucket.pop(0)
                if row[4] <= remaining:
                    selected.append(row)
                    remaining -= row[4]
                    break
    return [row[1] for row in sorted(selected, key=lambda row: row[0])]


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
    from .helper_advice import current_cached_helper_advice

    def safe_history(value: Any) -> Any:
        if isinstance(value, str):
            return safe_text(value)
        if isinstance(value, list):
            return [safe_history(item) for item in value]
        if isinstance(value, dict):
            return {key: safe_history(item) for key, item in value.items()}
        return value

    helper = getattr(dossier, "verified_helpers", {}).get(name)
    previous = current_cached_helper_advice(dossier, helper.source) if helper else {}
    if previous:
        result["previous_search_advice"] = safe_history(previous)
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


def _lookup_filters(args: Mapping[str, Any]) -> tuple[str, str, str, int, int, bool]:
    name = args.get("name", "")
    query = args.get("query", "")
    snapshot = args.get("snapshot_id", "")
    offset = args.get("offset", 0)
    length = args.get("length", 6000)
    include_provenance = args.get("include_provenance", False)
    if (not isinstance(name, str) or not isinstance(query, str)
            or not isinstance(snapshot, str)
            or type(offset) is not int or offset < 0
            or type(length) is not int or not 1 <= length <= 12000
            or type(include_provenance) is not bool):
        raise ValueError("helper lookup requires text filters and valid integer page bounds")
    if name and query:
        raise ValueError("use either an exact name or a text query")
    if offset and not snapshot:
        raise ValueError("continuing helper lookup requires snapshot_id")
    return name, query, snapshot, offset, length, include_provenance


def read_verified_helpers(
    dossier: Any, blocks: Sequence[str], args: Mapping[str, Any],
) -> dict[str, Any]:
    """Read only a freshly validated dispatch scope; never admit retrieved facts."""
    from .proof_dossier import helper_decl_name, helper_prompt_signature
    from .utils import canonical_lean_identifier

    name, query, _snapshot, _offset, _length, include_provenance = _lookup_filters(args)
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
        if helper_name is None:
            raise ValueError("validated helper context contains an unnamed declaration")
        helper = dossier.verified_helpers[helper_name]
        if name and exact_name != canonical_lean_identifier(helper_name.removeprefix("_root_.")):
            continue
        signature = helper_prompt_signature(
            source, name=helper_name, redact_solution_refs=redact_solution_refs,
        )
        if terms and not all(term in (helper_name + " " + signature).casefold() for term in terms):
            continue
        record = {
            "name": helper_name,
            "signature": signature,
            "source_hash": helper.source_hash,
            "support_names": list(helper.support_names),
            "advisory": helper_advisory(dossier, helper_name, linked_nodes=(
                linked_nodes.get(graph.helper_name_to_node_id.get(helper_name, ""), ())
                if graph is not None else ()
            )),
        }
        if include_provenance:
            record["replay_context_names"] = list(helper.replay_context_names)
        records.append(record)
    return _page_helper_records(records, sources, args, redact_solution_refs=redact_solution_refs)


def read_helper_catalog(
    helpers: Sequence[Any], args: Mapping[str, Any], *, redact_solution_refs: bool = True,
) -> dict[str, Any]:
    """Page exact signatures from a caller's frozen, authorized helper inventory.

    This adapter does not admit helpers or broaden the caller's access. The
    caller must apply its current scope and answer-visibility policy first.
    """
    from .proof_dossier import helper_prompt_signature, text_hash
    from .utils import canonical_lean_identifier

    name, query, _snapshot, _offset, _length, _provenance = _lookup_filters(args)
    exact_name = canonical_lean_identifier(name.strip().removeprefix("_root_."))
    terms = query.casefold().split()
    sources = []
    records = []
    for helper in helpers:
        source, helper_name = _helper_source_and_name(helper)
        sources.append(source)
        if not helper_name:
            raise ValueError("helper inventory contains an unnamed declaration")
        if name and exact_name != canonical_lean_identifier(helper_name.removeprefix("_root_.")):
            continue
        signature = helper_prompt_signature(source, name=helper_name, redact_solution_refs=redact_solution_refs)
        if terms and not all(term in (helper_name + " " + signature).casefold() for term in terms):
            continue
        records.append({"name": helper_name, "source_hash": text_hash(source), "signature": signature})
    return _page_helper_records(records, sources, args, redact_solution_refs=redact_solution_refs)


def _page_helper_records(
    records: Sequence[dict[str, Any]], sources: Sequence[str], args: Mapping[str, Any],
    *, redact_solution_refs: bool,
) -> dict[str, Any]:
    from .prompt_page_text import prompt_page_json

    name, query, snapshot, offset, length, include_provenance = _lookup_filters(args)

    def ordered_fields(value: Any) -> Any:
        if isinstance(value, list):
            return [ordered_fields(item) for item in value]
        if not isinstance(value, dict):
            return value
        keys = sorted(value)
        if "signature" in value:
            leading = [key for key in ("source_hash", "name", "signature") if key in value]
            keys = leading + [key for key in keys if key not in leading]
        # A hexadecimal source identity separates ordinary partial symbols
        # from name fields, whose initial letter could complete a reference.
        for identity, name in (("source_hash", "name"), ("current_source_hash", "node_id")):
            if identity in value and name in value:
                keys.remove(identity)
                keys.insert(keys.index(name), identity)
        return {key: ordered_fields(value[key]) for key in keys}

    independent_names = frozenset(
        (record_index, field_name, name_index)
        for record_index, record in enumerate(records)
        for field_name in ("support_names", "replay_context_names")
        for name_index in range(len(record.get(field_name, ())))
    )
    content = prompt_page_json(
        ordered_fields(records), redact_solution_refs=redact_solution_refs,
        isolated_string_paths=independent_names,
    )
    identity = hashlib.sha256(json.dumps({
        "scope": list(sources), "name": name, "query": query, "content": content,
        "include_provenance": include_provenance,
    }, ensure_ascii=False, sort_keys=True).encode()).hexdigest()
    if snapshot and snapshot != identity:
        return {"status": "context_changed", "restart_offset": 0, "snapshot_id": identity}
    end = min(len(content), offset + length)
    if "length" not in args and end < len(content):
        # Preserve the existing character-offset wire format. Default pages
        # finish between records whenever one whole record fits; explicit
        # lengths and oversized records retain exact character access.
        decoder = json.JSONDecoder()
        cursor = 1
        boundaries = []
        while cursor < len(content):
            while cursor < len(content) and (content[cursor].isspace() or content[cursor] == ","):
                cursor += 1
            if cursor == len(content) or content[cursor] == "]":
                break
            _record, cursor = decoder.raw_decode(content, cursor)
            while cursor < len(content) and (content[cursor].isspace() or content[cursor] == ","):
                cursor += 1
            if offset < cursor <= end:
                boundaries.append(cursor)
            elif cursor > end:
                break
        if boundaries:
            end = boundaries[-1]
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
