"""Bounded JSON event pages for streaming lossless state storage.

The event grammar contains no references or executable values. Large strings
span pages, and reconstruction allocates the final value without also building
its complete JSON representation.
"""
from __future__ import annotations

import hashlib
import json
import math
import threading
from typing import Any, Iterable, Iterator

from .state_data import StateDataError, clone_json_value

PAGE_BYTES = 64 * 1024


def canonical_parts(value: Any) -> Iterator[bytes]:
    """Yield the established canonical JSON encoding with bounded string parts."""
    try:
        value = clone_json_value(value, label="JSON storage")
    except StateDataError as error:
        raise ValueError(str(error)) from error

    def visit(item: Any) -> Iterator[bytes]:
        if type(item) is str:
            yield b'"'
            for offset in range(0, len(item), 8192):
                yield json.dumps(item[offset:offset + 8192], ensure_ascii=False)[1:-1].encode("utf-8")
            yield b'"'
        elif type(item) is dict:
            if any(type(key) is not str for key in item):
                raise ValueError("snapshot JSON object keys must be strings")
            yield b"{"
            for index, key in enumerate(sorted(item)):
                if index:
                    yield b","
                yield from visit(key)
                yield b":"
                yield from visit(item[key])
            yield b"}"
        elif type(item) in {list, tuple}:
            yield b"["
            for index, child in enumerate(item):
                if index:
                    yield b","
                yield from visit(child)
            yield b"]"
        else:
            yield json.dumps(item, ensure_ascii=False, allow_nan=False,
                             separators=(",", ":")).encode("utf-8")

    yield from visit(value)


def canonical_identity(value: Any) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    for part in canonical_parts(value):
        digest.update(part)
        size += len(part)
    return digest.hexdigest(), size


def encode_segments(value: Any, *, limit: int = PAGE_BYTES) -> Iterator[bytes | str]:
    """Encode deterministic pages with content boundaries for local edits."""
    if type(limit) is not int or limit < 128:
        raise ValueError("JSON page size limit is too small")
    try:
        value = clone_json_value(value, label="JSON storage")
    except StateDataError as error:
        raise ValueError(str(error)) from error
    string_size = max(1, (limit - 64) // 6)

    def events(item: Any) -> Iterator[list[Any] | str]:
        if type(item) is dict:
            if any(type(key) is not str for key in item):
                raise ValueError("snapshot JSON object keys must be strings")
            yield ["object"]
            for key in sorted(item):
                yield from events(key)
                yield from events(item[key])
            yield ["end"]
        elif type(item) in {list, tuple}:
            yield ["array"]
            for child in item:
                yield from events(child)
            yield ["end"]
        elif type(item) is str and len(item) > string_size:
            yield item
        else:
            yield ["value", item]

    page = bytearray()
    for event in events(value):
        if type(event) is str:
            if page:
                yield bytes(page)
                page.clear()
            yield event
            continue
        encoded = json.dumps(event, ensure_ascii=False, allow_nan=False,
                             separators=(",", ":")).encode("utf-8") + b"\n"
        if len(encoded) > limit:
            raise ValueError("JSON event exceeds page size limit")
        if page and len(page) + len(encoded) > limit:
            yield bytes(page)
            page.clear()
        page.extend(encoded)
        # Content boundaries let insertion settle at the next unchanged event.
        # Long string fragments are independent pages, preserving append reuse.
        if (event[0] == "part" or (len(page) >= 1024
                and hashlib.sha256(encoded).digest()[0] == 0)):
            yield bytes(page)
            page.clear()
    if page:
        yield bytes(page)


def string_pages(value: str, *, limit: int = PAGE_BYTES) -> Iterator[bytes]:
    yield b'["string"]\n'
    offset = 0
    while offset < len(value):
        size = min(limit - 64, len(value) - offset)
        while True:
            raw = json.dumps(["part", value[offset:offset + size]],
                             ensure_ascii=False, separators=(",", ":")).encode("utf-8") + b"\n"
            if len(raw) <= limit:
                break
            size //= 2
            if size == 0:
                raise ValueError("JSON string event exceeds page size limit")
        yield raw
        offset += size
    yield b'["end"]\n'


def encode_pages(value: Any, *, limit: int = PAGE_BYTES) -> Iterator[bytes]:
    for segment in encode_segments(value, limit=limit):
        if isinstance(segment, str):
            yield from string_pages(segment, limit=limit)
        else:
            yield segment


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON page key")
        result[key] = value
    return result


def strict_loads(raw: bytes) -> Any:
    def reject(value: str) -> None:
        raise ValueError(f"invalid JSON constant: {value}")

    def finite(value: str) -> float:
        number = float(value)
        if not math.isfinite(number):
            raise ValueError("non-finite JSON number")
        return number

    try:
        return json.loads(raw, object_pairs_hook=_unique_object,
                          parse_constant=reject, parse_float=finite)
    except RecursionError as error:
        raise ValueError("JSON page exceeds supported nesting") from error
    except (UnicodeError, json.JSONDecodeError) as error:
        raise ValueError("invalid JSON page") from error


def decode_pages(pages: Iterable[bytes], *, max_bytes: int | None = None) -> Any:
    """Read one strict event stream; repeated data pages cost their input size."""
    if max_bytes is not None and (type(max_bytes) is not int or max_bytes < 0):
        raise ValueError("invalid caller JSON size limit")
    expanded_bytes = 0

    def charge(amount: int) -> None:
        nonlocal expanded_bytes
        expanded_bytes += amount
        if max_bytes is not None and expanded_bytes > max_bytes:
            raise ValueError("snapshot exceeds caller size limit")

    stack: list[tuple[str, Any, list[str]]] = []
    absent = object()
    result: Any = absent

    def accept(value: Any) -> None:
        nonlocal result
        if not stack:
            if result is not absent:
                raise ValueError("trailing JSON page value")
            result = value
            return
        kind, container, key = stack[-1]
        if kind == "array":
            charge(int(bool(container)))
            container.append(value)
        elif kind == "object":
            if not key:
                if type(value) is not str or value in container:
                    raise ValueError("invalid or duplicate JSON object key")
                charge(1 + int(bool(container)))  # Colon and preceding comma.
                key.append(value)
            else:
                container[key.pop()] = value
        else:
            raise ValueError("invalid JSON string event")

    for raw in pages:
        if not raw or not raw.endswith(b"\n"):
            raise ValueError("truncated JSON event page")
        for line in raw.splitlines():
            event = strict_loads(line)
            if type(event) is not list or not event or type(event[0]) is not str:
                raise ValueError("invalid JSON event")
            op = event[0]
            if op in {"object", "array", "string"} and len(event) == 1:
                if stack and stack[-1][0] == "string":
                    raise ValueError("invalid JSON string event")
                charge(1)  # Opening brace, bracket, or string quote.
                stack.append((op, {} if op == "object" else [], []))
            elif op == "value" and len(event) == 2 and type(event[1]) in {str, int, float, bool, type(None)}:
                if max_bytes is not None:
                    charge(canonical_identity(event[1])[1])
                accept(event[1])
            elif op == "part" and len(event) == 2 and type(event[1]) is str:
                if not stack or stack[-1][0] != "string":
                    raise ValueError("unexpected JSON string fragment")
                if max_bytes is not None:
                    charge(canonical_identity(event[1])[1] - 2)
                stack[-1][1].append(event[1])
            elif op == "end" and len(event) == 1:
                if not stack:
                    raise ValueError("unexpected JSON container end")
                kind, container, key = stack.pop()
                if key:
                    raise ValueError("missing JSON object value")
                charge(1)
                accept("".join(container) if kind == "string" else container)
            else:
                raise ValueError("invalid JSON event")
    if stack or result is absent:
        raise ValueError("incomplete JSON event stream")
    return result


class MerkleHasher:
    """Versioned JSON tree hashes with bounded immutable-string memoization.

    A node is SHA-256 of its ASCII type plus a NUL, followed by canonical
    scalar JSON or fixed-width child digests in array order / sorted key order.
    Tuple and list have the same JSON array representation. Only exact strings
    are cached; containers are always visited so external mutations are visible.
    The cache retains at most 128 strings from the most recent value. References
    share existing immutable strings and never copy their contents. Cache access
    is synchronized; independent callers hash their values concurrently.
    """

    def __init__(self) -> None:
        from collections import OrderedDict
        self._strings: OrderedDict[int, tuple[str, bytes]] = OrderedDict()
        self._characters = 0
        self._cache_lock = threading.Lock()

    def clear(self) -> None:
        with self._cache_lock:
            self._strings.clear()
            self._characters = 0

    def digest(self, value: Any) -> str:
        try:
            value = clone_json_value(value, label="checkpoint tree hash")
        except StateDataError as error:
            raise ValueError(str(error)) from error
        used: set[int] = set()

        def visit(item: Any) -> bytes:
            if type(item) is str and len(item) >= 4096:
                key = id(item)
                with self._cache_lock:
                    cached = self._strings.get(key)
                    if cached is not None and cached[0] is item:
                        used.add(key)
                        self._strings.move_to_end(key)
                        return cached[1]
            digest = hashlib.sha256()
            if type(item) is dict:
                if any(type(key) is not str for key in item):
                    raise ValueError("snapshot JSON object keys must be strings")
                digest.update(b"object\0")
                for key in sorted(item):
                    digest.update(visit(key))
                    digest.update(visit(item[key]))
            elif type(item) in {list, tuple}:
                digest.update(b"array\0")
                for child in item:
                    digest.update(visit(child))
            else:
                digest.update(b"scalar\0")
                for part in canonical_parts(item):
                    digest.update(part)
            result = digest.digest()
            if type(item) is str and len(item) >= 4096:
                key = id(item)
                used.add(key)
                with self._cache_lock:
                    previous = self._strings.pop(key, None)
                    self._strings[key] = item, result
                    self._characters += len(item) - (len(previous[0]) if previous else 0)
                    while len(self._strings) > 128:
                        _, (old, _) = self._strings.popitem(last=False)
                        self._characters -= len(old)
            return result

        result = visit(value).hex()
        with self._cache_lock:
            for key in list(self._strings):
                if key not in used:
                    old, _ = self._strings.pop(key)
                    self._characters -= len(old)
        return result
