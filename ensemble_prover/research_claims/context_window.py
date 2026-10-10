"""Bound working context while preserving exact, addressable source records."""

from copy import deepcopy
from typing import Any, Callable

from .model import json_text


def research_view(store: Any, key: str, value: dict[str, Any], *, limit: int) -> dict[str, Any]:
    """Bound an inline research packet using exact values and explicit coverage."""
    if len(json_text(value)) <= limit:
        return deepcopy(value)
    artifact = store.put_artifact(json_text({key: value}).encode(), name="context-field.json")
    reference = {"artifact_id": artifact, "path": [key], "read_with": "read_artifact"}
    result: dict[str, Any] = {"complete_packet": reference, "coverage": "partial"}
    if key == "research_allocation":
        fields = [name for name in ("requests_remaining", "must_conclude",
                                    "context_reaudit_required", "context_transfer", "requests_used",
                                    "job_requests_remaining", "phase_requests_remaining",
                                    "global_requests_available", "reading_is_not_mathematical_progress")
                  if name in value]
    elif key == "native_current_context":
        fields = [name for name in ("first_uncertain_inference", "active_target", "formal_context",
                                    "objections", "failure") if name in value]
    else:
        fields = [name for name in ("target_claim_id", "context_binding", "baseline_artifact_ids",
                                    "prior_report_artifact_ids") if name in value]
        result["comparison_requirement"] = "Inspect the complete packet and every listed artifact before claiming novelty."
        if len(json_text(result)) > limit:
            result.pop("comparison_requirement")
    for name in fields:
        item = value[name]
        candidate = deepcopy(result)
        candidate[name] = item
        if len(json_text(candidate)) <= limit:
            result = candidate
            continue
        pointer = {**reference, "path": [key, name], "coverage": "not_in_this_window"}
        if isinstance(item, str):
            pointer.update(exact_excerpt=item[:160], characters=len(item), coverage="partial")
        elif isinstance(item, list):
            pointer["total_entries"] = len(item)
        candidate = {**result, name: pointer}
        if len(json_text(candidate)) <= limit:
            result = candidate
    # Recent reports help researchers avoid repeating diagnoses. These are exact
    # excerpts, never substituted mathematical summaries or complete coverage.
    if key == "cumulative_research_comparison":
        for name in ("reviewed_findings", "prior_reports"):
            selected = []
            for entry in reversed(value.get(name, [])):
                entry = {field: item[:120] if isinstance(item, str) and field in {
                    "method", "derivation_excerpt", "remaining_gap_excerpt", "conclusion"} else item
                    for field, item in entry.items()}
                entry["coverage"] = "exact excerpts; inspect complete packet and report artifacts"
                candidate = {**result, name: list(reversed(selected + [entry]))}
                if len(json_text(candidate)) > limit:
                    break
                selected.append(entry)
            if selected:
                result[name] = list(reversed(selected))
    return result


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
    if limit < 3000:
        compact = {"complete_context_artifact": archive}
        for key in ("research_allocation", "native_current_context", "cumulative_research_comparison"):
            if isinstance(value.get(key), dict):
                packet_limit = max(300 if key == "research_allocation" else 200, limit // 4)
                compact[key] = research_view(store, key, value[key], limit=packet_limit)
        for key in ("cumulative_research_comparison", "native_current_context"):
            if len(json_text(compact)) <= limit:
                break
            compact.pop(key, None)
        if len(compact) > 1 and len(json_text(compact)) <= limit:
            return compact
    for key, packet_limit in (("research_allocation", 900),
                              ("native_current_context", 2600),
                              ("cumulative_research_comparison", 2400)):
        if isinstance(result.get(key), dict):
            result[key] = research_view(store, key, result[key], limit=packet_limit)
    # Replace large historical fields before active mathematical obligations.
    priority = {
        "target": 3,
        "original_root": 3,
        "active_subject": 3,
        "claim": 3,
        "assignment": 4,
        "assigned_strategy_objection": 4,
        "native_current_context": 4,
        "cumulative_research_comparison": 4,
        "research_allocation": 5,
    }
    ordered = sorted(
        (key for key in value if key not in {"archive_policy", "complete_context_artifact"}),
        key=lambda key: (priority.get(key, 0), -len(json_text(value[key]))),
    )
    for key in ordered:
        if len(json_text(result)) <= limit:
            break
        # A pile of historical pointers must not evict the active assignment
        # and allocation. The full archive already retains these exact fields.
        if priority.get(key, 0) >= 2:
            for historical in ordered:
                if priority.get(historical, 0) >= priority.get(key, 0):
                    break
                result.pop(historical, None)
                if len(json_text(result)) <= limit:
                    break
            if len(json_text(result)) <= limit:
                break
        original = result[key]
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
        # At small windows, preserve usable allocation controls and exact
        # current-context excerpts before falling back to a single archive.
        protected = {}
        for key in ("research_allocation", "native_current_context", "cumulative_research_comparison"):
            if isinstance(value.get(key), dict):
                protected[key] = research_view(store, key, value[key], limit=max(200, limit // 4))
        compact = {"complete_context_artifact": archive, **protected}
        if protected and len(json_text(compact)) <= limit:
            return compact
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
    text_transform: Callable[[str], str] | None = None,
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
    if text_transform is not None:
        content = text_transform(content)
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
