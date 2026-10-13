"""Reference exact copies of previously delivered notebook excerpts."""

from __future__ import annotations

import json
from typing import Any, Callable, Mapping


_RECENT_READ_LIMIT = 64
_SEED_CHARS = 64
_MIN_QUOTATION_CHARS = 128


def remember_notebook_read(
    conv: Any, args: Mapping[str, Any], page: Mapping[str, Any], *, redact: bool,
) -> None:
    """Keep bounded replay descriptions, never another copy of notebook text."""
    descriptor = {
        "read": {"query": args.get("query", ""), "snapshot_id": page["snapshot_id"],
                 "offset": page["offset"], "length": args.get("length", 6000)},
        "redact": redact,
    }
    for key in ("entry_start", "entry_end"):
        if key in args:
            descriptor["read"][key] = args[key]
    previous = getattr(conv, "reasoning_notebook_reads", ()) or ()
    if not isinstance(previous, (list, tuple)):
        previous = ()
    conv.reasoning_notebook_reads = [
        *[item for item in previous if item != descriptor][-(_RECENT_READ_LIMIT - 1):],
        descriptor,
    ]


def _representations(page: Mapping[str, Any]):
    for ascii_only in (False, True):
        suffix = ":ascii" if ascii_only else ""
        for name, value in (("page_text", page["text"]),
                            ("tool_reply_json", json.dumps(page, ensure_ascii=ascii_only))):
            yield name + suffix, value
            for depth in (1, 2):
                value = json.dumps(value, ensure_ascii=ascii_only)
                yield f"{name}{suffix}:json_string:{depth}", value
                yield f"{name}{suffix}:json_string_body:{depth}", value[1:-1]
    yield "page_text:blockquote", "> " + page["text"].replace("\n", "\n> ")


def _common_prefix(text: str, start: int, source: str, position: int) -> int:
    low, high = _SEED_CHARS, min(len(text) - start, len(source) - position)
    while low < high:
        middle = (low + high + 1) // 2
        if text[start:start + middle] == source[position:position + middle]:
            low = middle
        else:
            high = middle - 1
    return low


def _common_suffix(text: str, start: int, source: str, position: int, cursor: int) -> int:
    low, high = 0, min(start - cursor, position)
    while low < high:
        middle = (low + high + 1) // 2
        if text[start - middle:start] == source[position - middle:position]:
            low = middle
        else:
            high = middle - 1
    return low


class NotebookQuotations:
    """Compact exact substantial excerpts, retaining every unmatched character.

    Each reference describes an immutable notebook prefix and a range in a
    delivered page's representation. Short, transformed, or unrecognized text
    remains verbatim. Thus novel derivations are never clipped to a size cap.
    """

    def __init__(self, conv: Any, read_page: Callable[..., dict[str, Any]]) -> None:
        self.references: list[dict[str, Any]] = []
        self._sources: list[tuple[str, dict[str, Any]]] = []
        self._seeds: dict[str, list[tuple[int, int]]] = {}
        seen: set[str] = set()
        projection_cache = {}
        descriptors = getattr(conv, "reasoning_notebook_reads", ()) or ()
        if not isinstance(descriptors, (list, tuple)):
            descriptors = ()
        for descriptor in descriptors[-_RECENT_READ_LIMIT:]:
            if not isinstance(descriptor, dict) or type(descriptor.get("redact")) is not bool:
                continue
            args = descriptor.get("read")
            if not isinstance(args, dict) or not isinstance(args.get("snapshot_id"), str):
                continue
            try:
                origin = {}
                page = read_page(conv, args, redact=descriptor["redact"],
                                 projection_cache=projection_cache, origin_output=origin)
            except (ValueError, TypeError, KeyError):
                # Old or damaged metadata must not discard the original math.
                continue
            for representation, source in _representations(page):
                if source in seen or len(source) < _MIN_QUOTATION_CHARS:
                    continue
                seen.add(source)
                index = len(self._sources)
                self._sources.append((source, {
                    "read": dict(args), "redacted": descriptor["redact"],
                    "representation": representation, "original_read": origin,
                }))
                # Aligned seeds bound index size. Any exact excerpt containing
                # 128 characters includes at least one complete 64-character seed.
                for start in range(0, len(source) - _SEED_CHARS + 1, _SEED_CHARS):
                    self._seeds.setdefault(source[start:start + _SEED_CHARS], []).append((index, start))

    def replace(self, text: str) -> str:
        if not self._sources or len(text) < _MIN_QUOTATION_CHARS:
            return text
        pieces = []
        cursor = scanned = 0
        while scanned <= len(text) - _SEED_CHARS:
            candidates = self._seeds.get(text[scanned:scanned + _SEED_CHARS], ())
            best = None
            for index, position in candidates:
                source, descriptor = self._sources[index]
                before = _common_suffix(text, scanned, source, position, cursor)
                after = _common_prefix(text, scanned, source, position)
                left, source_left = scanned - before, position - before
                right, source_right = scanned + after, position + after
                if right - left >= _MIN_QUOTATION_CHARS and (best is None or right - left > best[1] - best[0]):
                    best = (left, right, source_left, source_right, descriptor)
            if best is None:
                scanned += 1
                continue
            left, right, source_left, source_right, descriptor = best
            reference = {**descriptor, "start": source_left, "end": source_right}
            if reference not in self.references:
                self.references.append(reference)
            number = self.references.index(reference) + 1
            pieces.extend((text[cursor:left], f"[Retained notebook excerpt {number}]"))
            cursor = scanned = right
        return "".join((*pieces, text[cursor:]))
