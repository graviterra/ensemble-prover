"""Pure operator retrieval from authorized values in an issued view."""

from __future__ import annotations

from collections.abc import Iterator
import json
from typing import Any

from .policy import AccessContext, HostPolicy
from .references import canonical_json, sha256_digest, validate_ref
from .render import _selected_text

MAX_QUERY_CHARS = 4096
MAX_SEARCH_RESULTS = 1000
MAX_LABEL_CHARS = 160

_RESEARCH_COLLECTIONS = (
    ("questions", "question"), ("claims", "claim"),
    ("frontier_records", "frontier_record"), ("discovery_jobs", "job"),
    ("subjects", "subject"), ("revisions", "claim_revision"),
    ("evidence", "evidence"), ("reviews", "review"),
    ("contributions", "contribution"), ("operations", "operation"),
)


def _records(value: Any, path: list[str | int], category: str
             ) -> Iterator[tuple[list[str | int], str, dict[str, Any]]]:
    if isinstance(value, list):
        for index, record in enumerate(value):
            if isinstance(record, dict):
                yield [*path, index], category, record


def _candidates(values: dict[str, Any]
                ) -> Iterator[tuple[list[str | int], str, dict[str, Any]]]:
    proof = values.get("proof", {})
    sessions = proof.get("sessions", []) if isinstance(proof, dict) else []
    if isinstance(sessions, list):
        for index, session in enumerate(sessions):
            if not isinstance(session, dict):
                continue
            path: list[str | int] = ["proof", "sessions", index]
            yield from _records(session.get("helpers"), [*path, "helpers"], "helper")
            graph = session.get("graph", {})
            if isinstance(graph, dict):
                for collection, category in (("nodes", "graph_node"), ("edges", "graph_edge")):
                    yield from _records(graph.get(collection), [*path, "graph", collection], category)
    research = values.get("research", {})
    if isinstance(research, dict):
        for collection, category in _RESEARCH_COLLECTIONS:
            yield from _records(research.get(collection), ["research", collection], category)
    yield from _records(values.get("associations"), ["associations"], "association")


def _label(category: str, record: dict[str, Any], index: str | int) -> str:
    # Only identify the record. Mathematical statements and argument excerpts
    # require expansion, even when a shortened statement would fit the label.
    identifier = None
    for container in (record.get("ref"), record.get("association_ref"), record.get("record")):
        if isinstance(container, dict):
            for key in ("helper_name", "question_id", "node_id", "relation_id",
                        "record_id", "job_id", "claim_id", "subject_id", "name"):
                if isinstance(container.get(key), str) and container[key]:
                    identifier = container[key]
                    break
        if identifier is not None:
            break
    title = category.replace("_", " ").capitalize() + " reference: "
    identifier = str(index + 1 if isinstance(index, int) else index) if identifier is None else " ".join(identifier.split())
    return (title + identifier)[:MAX_LABEL_CHARS]


def search_view(store: Any, view_ref: dict[str, Any], query: str, *,
                policy: HostPolicy, context: AccessContext, limit: int = 50) -> dict[str, Any]:
    """Find records without source reads, writes, or abbreviated conclusions.

    Results carry exact value paths and digests. Expand their paths through the
    page resolver to inspect complete contracts, assumptions, and provenance.
    Association records include argument text pinned when the view was issued;
    matching never opens a current relation or argument object. Repeated
    source-qualified records in research convenience collections are returned
    once; distinct lane occurrences retain their separate paths.
    """
    if (not isinstance(query, str) or len(query) > MAX_QUERY_CHARS
            or type(limit) is not int or not 1 <= limit <= MAX_SEARCH_RESULTS):
        return {"status": "invalid_request"}
    result = store._read_view_authorized(view_ref, policy=policy, context=context,
                                         include_original_values=True)
    if result.get("status") != "ok":
        return {"status": result["status"]}
    try:
        values = result["snapshot"]["values"]
        if not isinstance(values, dict):
            return {"status": "view_unavailable"}
        needle = query.casefold()
        seen: set[str] = set()
        items = []
        for path, category, record in _candidates(values):
            serialized = canonical_json(record)
            digest = sha256_digest(serialized)
            if isinstance(record.get("source_ref"), dict):
                if digest in seen:
                    continue
                seen.add(digest)
            visible_text = _selected_text(result, path, "json-v1", policy, context)
            if needle not in visible_text.casefold():
                continue
            visible_record = json.loads(visible_text)
            if not isinstance(visible_record, dict):
                continue
            ref = validate_ref({"kind": "view_item", "version": 1,
                "namespace": view_ref["namespace"], "view_ref": view_ref,
                # Bind the value actually rendered for this selection. Its
                # contextual filter may differ from the enclosing snapshot's.
                "path": path, "value_digest": sha256_digest(visible_text.encode("utf-8"))})
            items.append({"ref": ref, "path": path, "category": category,
                          "label": _label(category, visible_record, path[-1]),
                          "unexpanded_contract": True})
            if len(items) == limit:
                break
        return {"status": "ok", "items": items}
    except (ValueError, TypeError, KeyError, UnicodeError, RecursionError):
        return {"status": "view_unavailable"}
