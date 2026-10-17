"""Pure bounded rendering and immutable, policy checked derived pages."""
from __future__ import annotations
from typing import Any, Sequence

from .policy import (
    AccessContext, HostPolicy, PolicyRedactionError, _merge_filtered_values,
    assert_visible_output, context_binding, redact_output,
)
from .references import DerivedRef, canonical_json, sha256_digest, validate_ref

MAX_PAGE_CHARS = 65536
MAX_RENDER_CHARS = 1024 * 1024


def select_value(values: Any, path: Sequence[str | int]) -> Any:
    if len(path) > 64:
        raise ValueError("path exceeds the projection bound")
    value = values
    for part in path:
        if isinstance(value, dict) and type(part) is str:
            value = value[part]
        elif isinstance(value, list) and type(part) is int and 0 <= part < len(value):
            value = value[part]
        else:
            raise ValueError("path does not identify an installed value")
    return value


def transform_value(value: Any, transform: str) -> str:
    if transform == "json-v1":
        return canonical_json(value).decode("utf-8")
    if transform == "text-v1" and isinstance(value, str):
        return value
    raise ValueError("unsupported transform for this installed value")


def _selected_values(result: dict[str, Any], path: Sequence[str | int],
                     policy: HostPolicy, context: AccessContext) -> tuple[Any, Any]:
    """Resolve corresponding original and visible selections without filtering twice.

    The original selection supplies transform-specific policy conditions, while
    the visible selection retains whole-view restrictions. Ambiguous paths
    through renamed keys cannot issue a faithful page or authoring input.
    """
    if not isinstance(path, (list, tuple)) or len(path) > 64:
        raise ValueError("invalid selection path")
    original = result["_original_values"]
    visible = result["snapshot"]["values"]
    for part in path:
        if isinstance(original, dict) and isinstance(visible, dict) and type(part) is str:
            keys = {policy.redact(key, context): key for key in original}
            if len(keys) != len(original) or keys.keys() != visible.keys():
                raise PolicyRedactionError("ambiguous original selection keys")
            original, visible = original[keys[part]], visible[part]
        elif (isinstance(original, list) and isinstance(visible, list)
              and len(original) == len(visible) and type(part) is int
              and 0 <= part < len(visible)):
            original, visible = original[part], visible[part]
        else:
            raise ValueError("path does not identify an installed value")
    return original, visible


def _selected_text(result: dict[str, Any], path: Sequence[str | int], transform: str,
                   policy: HostPolicy, context: AccessContext) -> str:
    original, visible = _selected_values(result, path, policy, context)
    if transform == "json-v1":
        filtered = redact_output(original, policy, context)
    elif transform == "text-v1" and isinstance(original, str) and isinstance(visible, str):
        filtered = policy.redact(original, context)
    else:
        raise ValueError("unsupported transform for this installed value")
    selected = _merge_filtered_values(original, visible, filtered)
    assert_visible_output(selected, context)
    return transform_value(selected, transform)


def render_context(snapshot: dict[str, Any], *, max_chars: int = 8192) -> str:
    """Format an already authorized snapshot without storage or policy callbacks.

    A truncated card asserts no mathematical conclusion; expanding the issued
    view is required to inspect all contracts and premises.
    """
    if type(max_chars) is not int or not 0 <= max_chars <= MAX_RENDER_CHARS:
        raise ValueError("invalid render bound")
    rendered = canonical_json({"coverage": snapshot.get("coverage"), "values": snapshot.get("values")}).decode()
    if len(rendered) <= max_chars:
        return rendered
    marker = "[unexpanded contract; expand the issued view]"
    return marker[:max_chars]


def issue_page(store: Any, view_ref: dict[str, Any], *, policy: HostPolicy, context: AccessContext,
               path: Sequence[str | int] = (), transform: str = "json-v1", start: int = 0,
               limit: int = 4096) -> dict[str, Any]:
    if type(start) is not int or start < 0 or type(limit) is not int or not 1 <= limit <= MAX_PAGE_CHARS:
        return {"status": "invalid_reference"}
    result = store._read_view_authorized(view_ref, policy=policy, context=context,
                                         include_original_values=True)
    if result["status"] != "ok":
        return {"status": result["status"]}
    try:
        if transform not in result["transforms"]:
            return {"status": "view_unavailable"}
        selected = _selected_text(result, path, transform, policy, context)
        if start > len(selected):
            return {"status": "invalid_reference"}
        end = min(start + limit, len(selected))
        text = selected[start:end]
        ref = DerivedRef(namespace=view_ref["namespace"], view=view_ref, path=list(path), transform=transform,
                         start=start, end=end, content_digest=sha256_digest(text.encode()),
                         selection_digest=sha256_digest(selected.encode()), policy_binding=context_binding(context)).to_dict()
        return {"status": "ok", "page_ref": ref, "text": text,
                "next_start": end if end < len(selected) else None, "total_chars": len(selected)}
    except (ValueError, TypeError, KeyError, IndexError):
        return {"status": "view_unavailable"}


def read_view_page(store: Any, page_ref: dict[str, Any], *, policy: HostPolicy,
                   context: AccessContext) -> dict[str, Any]:
    try:
        page_ref = validate_ref(page_ref)
        if page_ref["kind"] != "derived" or page_ref["policy_binding"] != context_binding(context):
            return {"status": "not_authorized"}
        if page_ref["end"] - page_ref["start"] > MAX_PAGE_CHARS:
            return {"status": "invalid_reference"}
        result = store._read_view_authorized(page_ref["view"], policy=policy, context=context,
                                             include_original_values=True)
        if result["status"] != "ok":
            return {"status": result["status"]}
        if page_ref["transform"] not in result["transforms"]:
            return {"status": "view_unavailable"}
        selected = _selected_text(result, page_ref["path"], page_ref["transform"], policy, context)
        if sha256_digest(selected.encode()) != page_ref["selection_digest"]:
            return {"status": "stale_policy"}
        text = selected[page_ref["start"]:page_ref["end"]]
        if page_ref["end"] > len(selected) or sha256_digest(text.encode()) != page_ref["content_digest"]:
            return {"status": "view_unavailable"}
        return {"status": "ok", "page_ref": page_ref, "text": text,
                "next_start": page_ref["end"] if page_ref["end"] < len(selected) else None, "total_chars": len(selected)}
    except (ValueError, TypeError, KeyError, IndexError):
        return {"status": "view_unavailable"}
