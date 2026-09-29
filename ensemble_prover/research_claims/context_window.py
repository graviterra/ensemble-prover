"""Bound working context while preserving exact, addressable source records."""

from copy import deepcopy
from typing import Any

from .model import json_text


def outcome_index(value: Any) -> list[dict[str, Any]]:
    """Small exact control fields, with paths; never summarize mathematics."""
    import json

    if isinstance(value, str):
        try:
            value = json.loads(value)
        except (ValueError, RecursionError):
            return []
    found: list[dict[str, Any]] = []
    frontier: list[tuple[Any, list[str]]] = [(value, [])]
    while frontier and len(found) < 12:
        current, path = frontier.pop(0)
        if not isinstance(current, dict) or len(path) > 3:
            continue
        for key, item in current.items():
            if key in {
                "status",
                "reason",
                "feedback_status",
                "next_action",
                "kernel_verified",
            } and isinstance(item, (str, bool)):
                if len(json_text(item)) <= 600:
                    found.append({"path": path + [key], "value": item})
            elif isinstance(item, dict):
                frontier.append((item, path + [key]))
    return found


def window(store: Any, value: dict[str, Any], *, limit: int) -> dict[str, Any]:
    if type(limit) is not int or limit < 2:
        raise ValueError("context limit must be an integer of at least 2")
    result = deepcopy(value)
    if len(json_text(result)) <= limit:
        return result
    archive = store.put_artifact(
        json_text(value).encode(), name="complete-context.json"
    )
    # Metadata is part of the context budget, not extra bytes appended afterward.
    result["archive_policy"] = (
        "Exact omitted fields are in complete_context_artifact. Omission is not evidence."
    )
    result["complete_context_artifact"] = archive
    # Replace large historical fields before active mathematical obligations.
    priority = {
        "target": 3,
        "original_root": 3,
        "active_subject": 3,
        "claim": 3,
        "assignment": 2,
        "assigned_strategy_objection": 2,
    }
    ordered = sorted(
        (key for key in value if key not in {"archive_policy", "complete_context_artifact"}),
        key=lambda key: (priority.get(key, 0), -len(json_text(value[key]))),
    )
    for key in ordered:
        if len(json_text(result)) <= limit:
            break
        original = value[key]
        if len(json_text(original)) < 256:
            continue
        # Preserve the historical path API, but do not make an unchanged field
        # acquire a new reference whenever a budget or another field changes.
        field_archive = store.put_artifact(
            json_text({key: original}).encode(), name="context-field.json"
        )
        pointer = {
            "artifact_id": field_archive,
            "path": [key],
            "coverage": "not_in_this_window",
            "read_with": "read_artifact",
            "characters": len(json_text(original)),
            "control_outcomes": outcome_index(original),
        }
        if len(json_text(pointer)) < len(json_text(original)):
            result[key] = pointer
    if len(json_text(result)) > limit:
        # Many individually short fields can exceed the cap together. Their
        # complete keys and values remain in the full archive even when an
        # individual pointer would cost more than the original field.
        for key in ordered:
            if key not in {"archive_policy", "complete_context_artifact"}:
                result.pop(key, None)
            if len(json_text(result)) <= limit:
                break
    if len(json_text(result)) > limit:
        result = {"artifact_id": archive, "coverage": "not_in_this_window", "read_with": "read_artifact"}
    if len(json_text(result)) > limit:
        raise ValueError("context limit cannot fit the exact archive reference")
    return result


def _json_structure(content: str, artifact_id: str) -> dict[str, Any] | None:
    """An exact, shallow navigation index; omitted children remain unknown."""
    import json

    if not content.lstrip().startswith(("{", "[")):
        return None
    try:
        value = json.loads(content)
    except (ValueError, RecursionError):
        return None
    if not isinstance(value, (dict, list)):
        return None
    kinds = {dict: "object", list: "array", str: "string", bool: "boolean",
             int: "integer", float: "number", type(None): "null"}
    result: dict[str, Any] = {
        "artifact_id": artifact_id, "type": kinds[type(value)],
        "total_children": len(value), "children": [], "coverage": "partial",
    }
    items = value.items() if isinstance(value, dict) else enumerate(value)
    for key, child in items:
        # A key is never shortened into a different, apparently valid path.
        # Huge keys are left in the canonical artifact with partial coverage.
        if isinstance(key, str) and len(key) > 200:
            continue
        entry = {"path": [key], "type": kinds[type(child)]}
        if isinstance(child, (dict, list)):
            entry["child_count"] = len(child)
        elif isinstance(child, str):
            entry["characters"] = len(child)
        result["children"].append(entry)
        if len(json_text(result)) > 4400:
            result["children"].pop()
            break
        if len(result["children"]) == 40:
            break
    if len(result["children"]) == len(value):
        result["coverage"] = "complete"
    return result


def read_page(
    store: Any,
    artifact_id: str,
    *,
    path: list[Any] | None = None,
    offset: int = 0,
    length: int = 6000,
) -> dict[str, Any]:
    if (
        type(offset) is not int
        or offset < 0
        or type(length) is not int
        or not 1 <= length <= 12000
    ):
        raise ValueError(
            "offset must be nonnegative; length must be 1..12000 characters"
        )
    if path is not None:
        if (
            not isinstance(path, list)
            or len(path) > 32
            or any(type(key) not in {str, int} for key in path)
        ):
            raise ValueError("path must contain at most 32 JSON keys/indices")
    content = store.read_artifact(artifact_id).decode("utf-8")
    if path:
        import json

        try:
            value = json.loads(content)
            for key in path:
                value = value[key]
        except (ValueError, TypeError, KeyError, IndexError, RecursionError) as exc:
            raise ValueError("artifact path does not exist") from exc
        content = value if isinstance(value, str) else json_text(value)
    # Full selected text, independent of the containing envelope/path alias.
    # Archival adds a derived artifact; original source bytes stay untouched.
    canonical = store.put_artifact(content.encode(), name="retrieval-content.txt")
    result = {
        "artifact_id": artifact_id,
        "content_id": canonical,
        "content_artifact": canonical,
        "path": path or [],
        "offset": offset,
        "text": content[offset : offset + length],
        "total_characters": len(content),
        "next_offset": offset + length if offset + length < len(content) else None,
        "coverage": "complete" if offset == 0 and len(content) <= length else "partial",
    }
    structure = _json_structure(content, canonical)
    if structure is not None:
        result["json_structure"] = structure
    return result
