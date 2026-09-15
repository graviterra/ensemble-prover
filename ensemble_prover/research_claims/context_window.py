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
    result = deepcopy(value)
    if len(json_text(result)) <= limit:
        return result
    archive = store.put_artifact(
        json_text(value).encode(), name="complete-context.json"
    )
    # Replace large historical fields before active mathematical obligations.
    priority = {
        "target": 3,
        "original_root": 3,
        "active_subject": 3,
        "claim": 3,
        "assignment": 2,
        "assigned_strategy_objection": 2,
    }
    for key in sorted(
        result, key=lambda key: (priority.get(key, 0), -len(json_text(result[key])))
    ):
        if len(json_text(result)) <= limit:
            break
        original = result[key]
        if len(json_text(original)) < 256:
            continue
        result[key] = {
            "artifact_id": archive,
            "path": [key],
            "coverage": "not_in_this_window",
            "read_with": "read_artifact",
            "characters": len(json_text(original)),
            "control_outcomes": outcome_index(original),
        }
    result["archive_policy"] = (
        "Exact omitted fields remain in the artifact. Retrieve paths/pages before judging them. Omission is not negative evidence."
    )
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
    content = store.read_artifact(artifact_id).decode("utf-8")
    if path:
        import json

        if (
            not isinstance(path, list)
            or len(path) > 32
            or any(type(key) not in {str, int} for key in path)
        ):
            raise ValueError("path must contain at most 32 JSON keys/indices")
        try:
            value = json.loads(content)
            for key in path:
                value = value[key]
        except (ValueError, TypeError, KeyError, IndexError, RecursionError) as exc:
            raise ValueError("artifact path does not exist") from exc
        content = value if isinstance(value, str) else json_text(value)
    return {
        "artifact_id": artifact_id,
        "path": path or [],
        "offset": offset,
        "text": content[offset : offset + length],
        "total_characters": len(content),
        "next_offset": offset + length if offset + length < len(content) else None,
        "coverage": "complete" if offset == 0 and len(content) <= length else "partial",
    }
