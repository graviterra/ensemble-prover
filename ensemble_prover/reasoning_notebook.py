"""Lossless, searchable historical reasoning without granting proof authority."""

from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping, Sequence

from .prompt_page_text import prompt_page_json


READ_REASONING_NOTEBOOK_TOOL = {
    "type": "function",
    "function": {
        "name": "read_reasoning_notebook",
        "description": (
            "Recover reasoning, assumptions, partial derivations and formalization "
            "diagnostics removed by compaction. This is unverified historical work, "
            "not proof. Search with query or leave it empty to read all entries. "
            "Continue pages with next_offset and snapshot_id."
        ),
        "parameters": {"type": "object", "properties": {
            "query": {"type": "string"},
            "offset": {"type": "integer", "minimum": 0},
            "length": {"type": "integer", "minimum": 1, "maximum": 12000},
            "snapshot_id": {"type": "string"},
        }},
    },
}


def readable_reasoning_parts(message: Mapping[str, Any]) -> list[str]:
    """Extract explicit text fields without interpreting opaque transport data."""
    parts = []

    def add(value: Any) -> None:
        if isinstance(value, str) and value.strip() and value not in parts:
            parts.append(value)

    for key in ("reasoning_content", "reasoning"):
        add(message.get(key))
    details = message.get("reasoning_details")
    for item in details if isinstance(details, list) else ():
        if not isinstance(item, dict):
            continue
        if item.get("type") == "reasoning.text":
            add(item.get("text"))
        elif item.get("type") == "reasoning.summary":
            add(item.get("summary"))
    for key in ("_responses_reasoning_items", "_responses_output_items"):
        items = message.get(key)
        for item in items if isinstance(items, list) else ():
            if not isinstance(item, dict) or item.get("type") != "reasoning":
                continue
            for field, kind in (("summary", "summary_text"), ("content", "reasoning_text")):
                values = item.get(field)
                for part in values if isinstance(values, list) else ():
                    if isinstance(part, dict) and part.get("type") == kind:
                        add(part.get("text"))
    return parts



def archive_reasoning(conv: Any, messages: Sequence[Mapping[str, Any]]) -> None:
    """Retain content and diagnostics, excluding provider-owned continuations.

    Store ordinary values on the conversation so the existing durable session
    projection and prover/refiner handoff preserve them. Tool calls are inert
    quoted records here; reading the notebook never dispatches them.
    """
    def is_target_anchor(message: Mapping[str, Any]) -> bool:
        marker = message.get("_required_prompt_context")
        return message.get("role") == "user" and (
            str(message.get("content") or "").startswith("Graph-selected proof task:")
            or isinstance(marker, Mapping) and marker.get("kind") == "selected_work"
        )

    source_anchors = {}
    current_anchor = ""
    for message in getattr(conv, "history", ()):
        if is_target_anchor(message):
            current_anchor = str(message.get("content") or "")
        source_anchors[id(message)] = current_anchor
    retained = []
    notebook_call_ids: set[str] = set()
    last_anchor = ""
    has_target_anchor = False
    for message in messages:
        role = message.get("role")
        if role not in {"assistant", "tool", "user"}:
            continue
        content = str(message.get("content") or "")
        for reasoning in readable_reasoning_parts(message) if role == "assistant" else ():
            content += "\n\nUnverified historical reasoning:\n" + reasoning
        if content.startswith("[history compaction]"):
            continue
        if role == "assistant":
            notebook_call_ids = {
                str(call.get("id") or "") for call in message.get("tool_calls", ())
                if isinstance(call, Mapping) and isinstance(call.get("function"), Mapping)
                and call["function"].get("name") == "read_reasoning_notebook"
            }
        elif role == "tool" and str(message.get("tool_call_id") or "") in notebook_call_ids:
            # The original records are already retained. Archiving read echoes
            # recursively duplicates the notebook without adding mathematics.
            continue
        if is_target_anchor(message):
            last_anchor = content
            has_target_anchor = True
        else:
            anchor = source_anchors.get(id(message), "")
            if anchor and anchor != last_anchor:
                retained.append({"role": "user", "content": anchor})
                last_anchor = anchor
                has_target_anchor = True
        item = {"role": role, "content": content}
        if role == "tool":
            item["tool_call_id"] = str(message.get("tool_call_id") or "")
        if role == "assistant" and message.get("tool_calls"):
            # Normalize to JSON data; signed reasoning and provider IDs are not
            # a continuation authority for another model or another target.
            item["tool_calls"] = [
                {"id": str(call.get("id") or ""), "type": "function", "function": {
                    "name": str(call["function"].get("name") or ""),
                    "arguments": json.loads(json.dumps(call["function"].get("arguments", "{}"))),
                }}
                for call in message["tool_calls"]
                if isinstance(call, Mapping) and isinstance(call.get("function"), Mapping)
                and call["function"].get("name") != "read_reasoning_notebook"
            ]
            if not item["tool_calls"] and not content.strip():
                continue
        retained.append(item)
    if not has_target_anchor and not any(item["role"] == "assistant" for item in retained):
        return
    entry = {
        "goal": str(getattr(conv, "goal_statement", "") or ""),
        "scope_at_compaction": str(getattr(conv, "_graph_selected_work_last_scope_key", "") or ""),
        "messages": retained,
    }
    # Copy on append also isolates dataclasses.replace handoffs.
    entries = list(getattr(conv, "reasoning_notebook", ()) or ())
    if entry not in entries:
        conv.reasoning_notebook = [*entries, entry]


def archive_pending_tool_candidates(conv: Any, state: Mapping[str, Any], *, target: str = "") -> None:
    """Keep full pending arguments as inert history before their owner retires."""
    calls = state.get("pending_tool_replay", ())
    if calls:
        # Advertisements in visible history may already be shortened. The
        # notebook normalizer retains candidate text without transport fields.
        archive_reasoning(conv, [{
            "role": "assistant",
            "content": "Unfinished tool requests retained as historical candidates; recheck before use.\n"
                       + "Original target: " + target,
            "tool_calls": calls,
        }])


def read_reasoning_notebook(conv: Any, args: Mapping[str, Any]) -> dict[str, Any]:
    from .mini_policy import _conversation_should_redact_solution_refs

    query = args.get("query", "")
    offset, length = args.get("offset", 0), args.get("length", 6000)
    if (not isinstance(query, str) or type(offset) is not int or offset < 0
            or type(length) is not int or not 1 <= length <= 12000):
        raise ValueError("invalid reasoning notebook query or page bounds")
    entries = list(getattr(conv, "reasoning_notebook", ()) or ())
    expected = args.get("snapshot_id")
    if offset and not expected:
        raise ValueError("reasoning notebook snapshot is required for continuation")
    count = len(entries)
    if expected is not None:
        try:
            count_text, _ = expected.split(":", 1)
            count = int(count_text)
        except (AttributeError, TypeError, ValueError) as error:
            raise ValueError("invalid reasoning notebook snapshot") from error
        if not 0 <= count <= len(entries):
            raise ValueError("reasoning notebook snapshot is no longer available")
        # A notebook is append-only. Later work must not invalidate a reader's
        # immutable prefix; replacing earlier entries still fails the hash.
        entries = entries[:count]
    # Apply visibility to the entire text before filtering and paging; neither
    # query matches nor page boundaries may expose hidden answer references.
    visible = json.loads(prompt_page_json(
        entries, redact_solution_refs=_conversation_should_redact_solution_refs(conv),
    ))
    selected = [entry for entry in visible
                if query.casefold() in json.dumps(entry, ensure_ascii=False).casefold()]
    text = prompt_page_json(selected, redact_solution_refs=False)
    snapshot = f"{count}:" + hashlib.sha256(text.encode()).hexdigest()
    if (offset and not expected) or (expected is not None and expected != snapshot):
        raise ValueError("reasoning notebook snapshot changed; restart at offset zero")
    if offset > len(text):
        raise ValueError("reasoning notebook offset exceeds snapshot")
    end = min(len(text), offset + length)
    return {
        "authority": "unverified_history", "matched_entries": len(selected),
        "text": text[offset:end], "snapshot_id": snapshot, "offset": offset,
        "next_offset": end if end < len(text) else None,
    }


def notebook_notice(conv: Any) -> str:
    entries = getattr(conv, "reasoning_notebook", ()) or ()
    if not entries:
        return ""
    return (
        f"[reasoning notebook]\n{len(entries)} historical reasoning entries are retained. "
        "Use read_reasoning_notebook to search or page through earlier assumptions, "
        "derivations, tool requests and diagnostics. A formalization failure does "
        "not refute the mathematical idea. These entries are unverified history; "
        "check their assumptions and original target before reuse. Numerical "
        "evidence is not a proof."
    )
