"""JSON codecs that retain standard bytes without a Python container-depth limit."""

from __future__ import annotations

import json
import re
from typing import Any


_JSON_NUMBER_TOKEN_RE = re.compile(
    r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?"
)


def decode_json_iterative(source: str, *, reject_duplicates: bool = True, allow_nonfinite: bool = False) -> Any:
    """Decode JSON with an explicit container stack.

    Lean expressions are naturally much deeper than Python call stacks. The
    standard decoder rejects otherwise valid, bounded receipt payloads around
    that implementation limit, so the receipt boundary uses a non-recursive
    decoder rather than imposing a mathematical expression-depth cap.
    """

    text = str(source)
    length = len(text)
    position = 0
    unset = object()
    root: Any = unset
    # frame: [kind, container, state, pending_key]
    stack: list[list[Any]] = []

    def skip_space(index: int) -> int:
        while index < length and text[index] in " \t\r\n":
            index += 1
        return index

    def parse_value(index: int) -> tuple[Any, list[Any] | None, int]:
        index = skip_space(index)
        if index >= length:
            raise ValueError("unexpected end of JSON input")
        token = text[index]
        if token == "[":
            container: list[Any] = []
            return container, ["array", container, "value_or_end", None], index + 1
        if token == "{":
            container = {}
            return container, ["object", container, "key_or_end", None], index + 1
        if token == '"':
            value, end = json.decoder.scanstring(text, index + 1, True)
            return value, None, end
        for literal, value in (("true", True), ("false", False), ("null", None)):
            if text.startswith(literal, index):
                return value, None, index + len(literal)
        if allow_nonfinite:
            for literal, value in (("NaN", float("nan")), ("Infinity", float("inf")), ("-Infinity", -float("inf"))):
                if text.startswith(literal, index):
                    return value, None, index + len(literal)
        match = _JSON_NUMBER_TOKEN_RE.match(text, index)
        if match is None:
            raise ValueError(f"invalid JSON token at offset {index}")
        token_text = match.group(0)
        value = (
            float(token_text)
            if any(marker in token_text for marker in ".eE")
            else int(token_text)
        )
        return value, None, match.end()

    while True:
        position = skip_space(position)
        if not stack:
            if root is not unset:
                if position != length:
                    raise ValueError(f"trailing JSON data at offset {position}")
                return root
            root, frame, position = parse_value(position)
            if frame is not None:
                stack.append(frame)
            continue

        frame = stack[-1]
        kind, container, state, pending_key = frame
        position = skip_space(position)
        if kind == "array":
            if state in {"value_or_end", "value"}:
                if (
                    state == "value_or_end"
                    and position < length
                    and text[position] == "]"
                ):
                    stack.pop()
                    position += 1
                    continue
                value, child_frame, position = parse_value(position)
                container.append(value)
                frame[2] = "comma_or_end"
                if child_frame is not None:
                    stack.append(child_frame)
                continue
            if position < length and text[position] == ",":
                frame[2] = "value"
                position += 1
                continue
            if position < length and text[position] == "]":
                stack.pop()
                position += 1
                continue
            raise ValueError(f"expected ',' or ']' at offset {position}")

        if state in {"key_or_end", "key"}:
            if (
                state == "key_or_end"
                and position < length
                and text[position] == "}"
            ):
                stack.pop()
                position += 1
                continue
            if position >= length or text[position] != '"':
                raise ValueError(f"expected object key at offset {position}")
            key, position = json.decoder.scanstring(text, position + 1, True)
            frame[3] = key
            frame[2] = "colon"
            continue
        if state == "colon":
            if position >= length or text[position] != ":":
                raise ValueError(f"expected ':' at offset {position}")
            frame[2] = "value"
            position += 1
            continue
        if state == "value":
            value, child_frame, position = parse_value(position)
            if reject_duplicates and pending_key in container:
                raise ValueError(f"duplicate object key {pending_key!r}")
            container[pending_key] = value
            frame[3] = None
            frame[2] = "comma_or_end"
            if child_frame is not None:
                stack.append(child_frame)
            continue
        if position < length and text[position] == ",":
            frame[2] = "key"
            position += 1
            continue
        if position < length and text[position] == "}":
            stack.pop()
            position += 1
            continue
        raise ValueError(f"expected ',' or '}}' at offset {position}")



def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate object key {key!r}")
        result[key] = value
    return result


def _invalid_constant(value: str) -> Any:
    raise ValueError(f"invalid JSON constant {value}")


def loads_deep_json(source: str, *, reject_duplicates: bool = False) -> Any:
    """Use the native decoder first, then a stack for deeply nested JSON.

    Strict observation payloads reject duplicate keys and non-JSON constants;
    ordinary compatibility readers retain the standard decoder's behavior.
    """
    try:
        if reject_duplicates:
            return json.loads(source, object_pairs_hook=_unique_object, parse_constant=_invalid_constant)
        return json.loads(source)
    except RecursionError:
        return decode_json_iterative(source, reject_duplicates=reject_duplicates,
                                     allow_nonfinite=not reject_duplicates)


def dumps_deep_json(value: Any, *, sort_keys: bool = False,
                    ensure_ascii: bool = True, separators: tuple[str, str] = (",", ":")) -> str:
    """Keep the native encoder fast path and its exact bytes at any depth."""
    try:
        return json.dumps(value, sort_keys=sort_keys, ensure_ascii=ensure_ascii, separators=separators)
    except RecursionError:
        pass
    output: list[str] = []
    active: set[int] = set()
    stack: list[tuple[str, Any]] = [("value", value)]
    item_separator, key_separator = separators
    while stack:
        operation, item = stack.pop()
        if operation == "raw":
            output.append(item)
        elif operation == "end":
            active.remove(item[0])
            output.append(item[1])
        elif isinstance(item, (list, tuple, dict)):
            identity = id(item)
            if identity in active:
                raise ValueError("Circular reference detected")
            active.add(identity)
            dictionary = isinstance(item, dict)
            output.append("{" if dictionary else "[")
            stack.append(("end", (identity, "}" if dictionary else "]")))
            operations: list[tuple[str, Any]] = []
            entries = (sorted(item.items()) if sort_keys else item.items()) if isinstance(item, dict) else enumerate(item)
            for index, (key, child) in enumerate(entries):
                if index:
                    operations.append(("raw", item_separator))
                if dictionary:
                    if not isinstance(key, str):
                        if key is True:
                            key = "true"
                        elif key is False:
                            key = "false"
                        elif key is None:
                            key = "null"
                        elif isinstance(key, (int, float)):
                            key = json.dumps(key)
                        else:
                            raise TypeError(f"keys must be str, int, float, bool or None, not {type(key).__name__}")
                    operations.extend((("raw", json.dumps(key, ensure_ascii=ensure_ascii)), ("raw", key_separator)))
                operations.append(("value", child))
            stack.extend(reversed(operations))
        else:
            output.append(json.dumps(item, ensure_ascii=ensure_ascii, separators=separators))
    return "".join(output)
