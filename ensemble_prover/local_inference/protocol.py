"""Local OpenAI-compatible chat protocol.

Keyword-only request, response, and SSE helpers for OpenAICompatClient.
Model ids and token limits are explicit arguments. No sockets, retries,
prices, or profile/capacity imports.
"""

from __future__ import annotations

import codecs
import json
import math
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any, Iterator, NoReturn

PROTECTED_MARKER = "_required_prompt_context"
_ROLES = frozenset({"system", "developer", "user", "assistant", "tool"})
_MODES = frozenset({"on", "off"})
_DEFAULTS = frozenset({"", "provider-default", "provider_default"})
_FORMATS = frozenset({"none", "deepseek", "deepseek-legacy"})
_USAGE = ("prompt_tokens", "completion_tokens", "total_tokens")
_DIALECTS = {
    "generic": (frozenset({"reasoning_effort"}), frozenset()),
    "vllm": (
        frozenset({"chat_template_kwargs", "reasoning_effort"}),
        frozenset({"reasoning", "reasoning_content"}),
    ),
    "ollama": (
        frozenset({"reasoning_effort"}),
        frozenset({"reasoning", "reasoning_content"}),
    ),
    "llamacpp": (
        frozenset({"chat_template_kwargs", "reasoning_format", "reasoning_effort"}),
        frozenset({"reasoning_content"}),
    ),
}


class LocalProtocolError(Exception):
    def __init__(self, code: str, message: str, **details: Any) -> None:
        super().__init__(message)
        self.code, self.details = code, details

    def __str__(self) -> str:
        code = self.code
        if (
            not isinstance(code, str)
            or re.fullmatch(r"[a-z][a-z0-9_]{0,63}", code) is None
        ):
            code = "invalid_local_error"
        return f"[local_protocol:{code}] {super().__str__()}"

    def __reduce__(self) -> tuple[Any, tuple[str, str], dict[str, Any]]:
        # Exception.args contains only the safe display message; reconstruction
        # also needs the stable code. Preserve details as state, never in str().
        return type(self), (self.code, self.args[0]), self.__dict__


def _fail(code: str, message: str, **details: Any) -> NoReturn:
    raise LocalProtocolError(code, message, **details)


def _dialect(dialect: str) -> tuple[frozenset[str], frozenset[str]]:
    if type(dialect) is not str or dialect not in _DIALECTS:
        _fail("unsupported_dialect", "dialect is not supported", dialect=dialect)
    return _DIALECTS[dialect]


def dialect_contract(dialect: str) -> dict[str, Any]:
    """Return supported fields. A model-name prefix never selects a dialect."""
    reasoning, history = _dialect(dialect)
    return {
        "dialect": dialect,
        "reasoning_fields": sorted(reasoning),
        "history_fields": sorted(history),
        "explicit_reasoning_modes": ["off", "on"],
        "output_limit_field": "max_tokens",
        "argument_encodings": ["json_string", "object"],
        "native_batching": False,
    }


def _pairs(pairs: list[tuple[Any, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if type(key) is not str or key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number: {value}")


def _finite(value: str) -> float:
    number = float(value)
    if not math.isfinite(number):
        raise ValueError("non-finite JSON number")
    return number


def loads_strict(raw: str, *, code: str, max_depth: int = 64) -> Any:
    """Parse JSON, rejecting duplicates, non-finite numbers, and truncated text."""
    if type(raw) is not str:
        _fail(code, "JSON text must be a string")
    try:
        value = json.loads(
            raw, object_pairs_hook=_pairs, parse_constant=_constant, parse_float=_finite
        )
        _walk(value, code=code, depth=0, limit=max_depth)
        return value
    except LocalProtocolError:
        raise
    except RecursionError:
        raise LocalProtocolError(code, "JSON value is too deep") from None
    except (json.JSONDecodeError, ValueError):
        raise LocalProtocolError(code, "JSON value is invalid") from None


def _walk(value: Any, *, code: str, depth: int, limit: int) -> None:
    if depth > limit:
        _fail(code, "JSON value is nested too deeply")
    if type(value) is str:
        _utf8(value)
        return
    if value is None or type(value) in (bool, int):
        return
    if type(value) is float:
        if not math.isfinite(value):
            _fail(code, "JSON value contains a non-finite number")
        return
    if type(value) is list:
        for item in value:
            _walk(item, code=code, depth=depth + 1, limit=limit)
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                _fail(code, "JSON object keys must be strings")
            _walk(item, code=code, depth=depth + 1, limit=limit)
        return
    _fail(code, "JSON value contains an unsupported type")


def _int(name: str, value: Any, minimum: int) -> int:
    if type(value) is not int or value < minimum:
        _fail("invalid_request", f"{name} is outside its integer range", field=name)
    return value


def _seq(name: str, value: Any) -> Sequence[Any]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        _fail("invalid_request", f"{name} must be a sequence", field=name)
    return value


def _utf8(value: str) -> int:
    try:
        return len(value.encode("utf-8"))
    except UnicodeError:
        raise LocalProtocolError("invalid_unicode", "text is not valid UTF-8") from None


def _dumps(value: Any) -> str:
    if isinstance(value, _JsonSnapshot):
        return value.encoded
    try:
        return json.dumps(
            value, ensure_ascii=False, separators=(",", ":"), allow_nan=False
        )
    except (ValueError, TypeError, RecursionError):
        raise LocalProtocolError(
            "invalid_json", "value cannot be encoded as JSON"
        ) from None


def _arguments(
    value: Any,
    *,
    objects: bool,
    code: str,
    bound: int | None,
    depth: int,
    index: int | None = None,
) -> tuple[dict[str, Any], str]:
    detail = {} if index is None else {"index": index}
    if type(value) is str:
        if bound is not None and _utf8(value) > bound:
            _fail(code, "tool arguments exceed the size limit", **detail)
        try:
            parsed = loads_strict(value, code=code, max_depth=depth)
        except LocalProtocolError as exc:
            if index is not None:
                exc.details.setdefault("index", index)
            raise
        if type(parsed) is not dict:
            _fail(code, "tool arguments must be a JSON object", **detail)
        _walk(parsed, code=code, depth=1, limit=depth)
        return parsed, value
    if type(value) is dict and objects:
        _walk(value, code=code, depth=1, limit=depth)
        encoded = _dumps(value)
        if bound is not None and _utf8(encoded) > bound:
            _fail(code, "tool arguments exceed the size limit", **detail)
        parsed = loads_strict(encoded, code=code, max_depth=depth)
        if type(parsed) is not dict:
            _fail(code, "tool arguments must be a JSON object", **detail)
        return parsed, encoded
    _fail(code, "tool arguments must be a JSON object string", **detail)


def _text(content: Any, *, code: str) -> str:
    if content is None or type(content) is str:
        _utf8(content or "")
        return content or ""
    if type(content) is not list:
        _fail(code, "message content is not text")
    parts: list[str] = []
    for part in content:
        if (
            type(part) is not dict
            or part.get("type") != "text"
            or type(part.get("text")) is not str
        ):
            _fail(code, "non-text message content is not supported")
        parts.append(part["text"])
    combined = "".join(parts)
    _utf8(combined)
    return combined


def _content(content: Any) -> Any:
    if content is None or type(content) is str:
        return content
    _text(content, code="unsupported_control")
    return [{"type": "text", "text": part["text"]} for part in content]


def _protected(message: Mapping[str, Any], marker: str) -> bool:
    if message.get("protected") is True:
        return True
    value = message.get(marker)
    return bool(value.get("required", True)) if type(value) is dict else value is True


def _kind(message: Mapping[str, Any], marker: str) -> str:
    value = message.get(marker)
    if type(value) is dict and type(value.get("kind")) is str and value["kind"].strip():
        return value["kind"].strip()
    return (
        "protected" if message.get("protected") is True else "required_prompt_context"
    )


def _history_call(call: Any, *, depth: int) -> dict[str, Any]:
    function = call.get("function") if type(call) is dict else None
    name = function.get("name") if type(function) is dict else None
    if (
        type(call) is not dict
        or type(call.get("id")) is not str
        or not call.get("id")
        or call.get("type") != "function"
        or type(name) is not str
        or not name
        or type(function) is not dict
        or "arguments" not in function
    ):
        _fail(
            "invalid_request",
            "history tool call id, type, name, or arguments are invalid",
        )
    assert isinstance(function, dict)
    _parsed, encoded = _arguments(
        function["arguments"],
        objects=True,
        code="invalid_request",
        bound=None,
        depth=depth,
    )
    return {
        "id": call["id"],
        "type": "function",
        "function": {"name": name, "arguments": encoded},
    }


def _body(dialect: str, body: Any) -> dict[str, Any]:
    allowed = _dialect(dialect)[0]
    if type(body) is not dict or not body or set(body) - allowed:
        _fail(
            "unsupported_control",
            "reasoning control uses a field this dialect does not support",
        )
    cleaned: dict[str, Any] = {}
    if "reasoning_effort" in body:
        effort = body["reasoning_effort"]
        if type(effort) is not str or not effort.strip():
            _fail(
                "unsupported_control",
                "reasoning_effort must name a verified model effort",
            )
        cleaned["reasoning_effort"] = effort
    if "chat_template_kwargs" in body:
        kwargs = body["chat_template_kwargs"]
        if (
            type(kwargs) is not dict
            or set(kwargs) != {"enable_thinking"}
            or type(kwargs.get("enable_thinking")) is not bool
        ):
            _fail(
                "unsupported_control",
                "chat_template_kwargs accepts only enable_thinking",
            )
        cleaned["chat_template_kwargs"] = {"enable_thinking": kwargs["enable_thinking"]}
    if "reasoning_format" in body:
        if (
            type(body["reasoning_format"]) is not str
            or body["reasoning_format"] not in _FORMATS
        ):
            _fail("unsupported_control", "reasoning_format is not supported")
        cleaned["reasoning_format"] = body["reasoning_format"]
    if set(cleaned) != set(body):
        _fail("unsupported_control", "reasoning control was not fully recognized")
    return cleaned


def _controls(
    dialect: str, controls: Mapping[str, Any] | None
) -> dict[str, dict[str, Any]]:
    if controls is None:
        return {}
    if type(controls) is not dict:
        _fail("invalid_request", "reasoning_controls must be an object")
    cleaned = {}
    for mode, body in controls.items():
        if type(mode) is not str or mode not in _MODES:
            _fail(
                "unsupported_control",
                "reasoning mode is not supported and was not dropped",
                reasoning_mode=mode,
            )
        cleaned[mode] = _body(dialect, body)
    return cleaned


def _messages(
    messages: Any,
    *,
    dialect: str,
    replay: Sequence[str],
    required: bool,
    marker: str,
    depth: int,
    limit: int,
) -> tuple[list[dict[str, Any]], int, int, tuple[str, ...]]:
    rows, fields = list(_seq("messages", messages)), tuple(
        _seq("history_replay_fields", replay)
    )
    if not rows or type(marker) is not str or not marker or type(required) is not bool:
        _fail("invalid_request", "messages and protection settings are invalid")
    if any(type(field) is not str or not field for field in fields) or len(
        set(fields)
    ) != len(fields):
        _fail("invalid_request", "history replay fields must be unique strings")
    if any(field not in _dialect(dialect)[1] for field in fields):
        _fail(
            "unsupported_control",
            "history replay field is not supported by this dialect",
        )
    if required and not fields:
        _fail(
            "unsupported_control",
            "reasoning replay was required but no history field is declared",
        )
    out: list[dict[str, Any]] = []
    tokens = replay_tokens = 0
    kinds: list[str] = []
    for message in rows:
        if (
            type(message) is not dict
            or type(message.get("role")) is not str
            or message.get("role") not in _ROLES
        ):
            _fail("invalid_request", "message role is not supported")
        role = message["role"]
        if "content" not in message and role != "assistant":
            _fail("invalid_request", "message content is required")
        content = _content(message["content"]) if "content" in message else None
        if _protected(message, marker) and _text(
            content, code="invalid_request"
        ) != _text(message.get("content"), code="invalid_request"):
            _fail("protected_context_lost", "protected message text changed")
        calls = None
        raw_calls = message.get("tool_calls")
        if raw_calls is not None:
            if (
                role != "assistant"
                or type(raw_calls) is not list
                or len(raw_calls) > limit
            ):
                _fail("invalid_request", "tool_calls must be a bounded assistant list")
            calls = [_history_call(item, depth=depth) for item in raw_calls]
            if len({item["id"] for item in calls}) != len(calls):
                _fail("invalid_request", "history tool call ids are duplicated")
        kept: dict[str, str] = {}
        for field in fields:
            if message.get(field) is not None:
                if type(message[field]) is not str:
                    _fail(
                        "invalid_request",
                        "replayed reasoning must be a string",
                        field=field,
                    )
                kept[field] = message[field]
                replay_tokens += _utf8(message[field])
            elif required and role == "assistant":
                _fail(
                    "invalid_request",
                    "assistant message is missing declared reasoning replay",
                    field=field,
                )
        wired: dict[str, Any] = {"role": role, "content": content, **kept}
        if calls is not None:
            wired["tool_calls"] = calls
        if type(message.get("name")) is str:
            wired["name"] = message["name"]
        elif message.get("name") is not None:
            _fail("invalid_request", "message name must be a string")
        if role == "tool" and (
            type(message.get("tool_call_id")) is not str
            or not message.get("tool_call_id")
        ):
            _fail("invalid_request", "tool message is missing tool_call_id")
        if role == "tool":
            wired["tool_call_id"] = message["tool_call_id"]
        if _protected(message, marker):
            kinds.append(_kind(message, marker))
        tokens += 8 + _utf8(_dumps(wired))
        out.append(wired)
    return out, tokens, replay_tokens, tuple(kinds)


_SCHEMA_TYPES = frozenset(
    {"object", "array", "string", "number", "integer", "boolean", "null"}
)
_SCHEMA_KEYS = frozenset(
    {
        "type",
        "properties",
        "required",
        "additionalProperties",
        "items",
        "enum",
        "const",
        "anyOf",
        "allOf",
        "oneOf",
        "minimum",
        "maximum",
        "exclusiveMinimum",
        "exclusiveMaximum",
        "minLength",
        "maxLength",
        "minItems",
        "maxItems",
        "uniqueItems",
        "description",
        "title",
        "default",
        "examples",
    }
)


def _check_schema(schema: Any, *, depth: int) -> None:
    """Check the supported JSON Schema subset, including unused branches.

    Unsupported constraints fail explicitly instead of being silently ignored.
    This covers the schemas emitted by Mini's proof and research tools.
    """
    if depth > 32:
        _fail("unsupported_schema", "tool schema is too deeply nested")
    if type(schema) is bool:
        return
    if type(schema) is not dict or set(schema) - _SCHEMA_KEYS:
        _fail("unsupported_schema", "tool schema contains unsupported constraints")
    if "type" in schema:
        types = schema["type"] if type(schema["type"]) is list else [schema["type"]]
        if (
            not types
            or any(type(item) is not str or item not in _SCHEMA_TYPES for item in types)
            or len(set(types)) != len(types)
        ):
            _fail("unsupported_schema", "tool schema has an invalid type")
    if "properties" in schema:
        properties = schema["properties"]
        if type(properties) is not dict or any(
            type(key) is not str for key in properties
        ):
            _fail("unsupported_schema", "tool schema properties must be an object")
        for child in properties.values():
            _check_schema(child, depth=depth + 1)
    if "required" in schema:
        required = schema["required"]
        if (
            type(required) is not list
            or any(type(key) is not str for key in required)
            or len(set(required)) != len(required)
        ):
            _fail("unsupported_schema", "tool schema required fields are invalid")
    for keyword in ("additionalProperties", "items"):
        if keyword in schema:
            _check_schema(schema[keyword], depth=depth + 1)
    for keyword in ("anyOf", "allOf", "oneOf"):
        if keyword in schema:
            choices = schema[keyword]
            if type(choices) is not list or not choices:
                _fail(
                    "unsupported_schema",
                    "tool schema alternatives must be a nonempty list",
                )
            for child in choices:
                _check_schema(child, depth=depth + 1)
    if "enum" in schema:
        enum = schema["enum"]
        if type(enum) is not list or not enum:
            _fail("unsupported_schema", "tool schema enum must be a nonempty list")
        if any(
            _json_equal(value, earlier)
            for index, value in enumerate(enum)
            for earlier in enum[:index]
        ):
            _fail("unsupported_schema", "tool schema enum contains duplicates")
    for keyword in ("minimum", "maximum", "exclusiveMinimum", "exclusiveMaximum"):
        if keyword in schema and not _is_number(schema[keyword]):
            _fail("unsupported_schema", "tool schema numeric bound is invalid")
    for keyword in ("minLength", "maxLength", "minItems", "maxItems"):
        if keyword in schema and (
            type(schema[keyword]) is not int or schema[keyword] < 0
        ):
            _fail("unsupported_schema", "tool schema length bound is invalid")
    if "uniqueItems" in schema and type(schema["uniqueItems"]) is not bool:
        _fail("unsupported_schema", "tool schema uniqueItems must be boolean")


def _is_number(value: Any) -> bool:
    return type(value) is int or (type(value) is float and math.isfinite(value))


def _json_equal(left: Any, right: Any) -> bool:
    if _is_number(left) and _is_number(right):
        return bool(left == right)
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys() == right.keys() and all(
            _json_equal(value, right[key]) for key, value in left.items()
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            _json_equal(a, b) for a, b in zip(left, right)
        )
    return bool(left == right)


def _matches_type(value: Any, name: str) -> bool:
    if name == "number":
        return _is_number(value)
    if name == "integer":
        return _is_number(value) and value == int(value)
    return (
        type(value)
        is {
            "object": dict,
            "array": list,
            "string": str,
            "boolean": bool,
            "null": type(None),
        }[name]
    )


def _matches_schema(value: Any, schema: Any) -> bool:
    """Evaluate an already checked schema against a bounded, inert JSON value."""
    if type(schema) is bool:
        return schema
    if "type" in schema:
        types = schema["type"] if type(schema["type"]) is list else [schema["type"]]
        if not any(_matches_type(value, name) for name in types):
            return False
    if "enum" in schema and not any(
        _json_equal(value, item) for item in schema["enum"]
    ):
        return False
    if "const" in schema and not _json_equal(value, schema["const"]):
        return False
    for keyword in ("anyOf", "allOf", "oneOf"):
        if keyword in schema:
            results = [_matches_schema(value, child) for child in schema[keyword]]
            if (
                (keyword == "anyOf" and not any(results))
                or (keyword == "allOf" and not all(results))
                or (keyword == "oneOf" and sum(results) != 1)
            ):
                return False
    if type(value) is dict:
        if any(key not in value for key in schema.get("required", [])):
            return False
        properties = schema.get("properties", {})
        if any(
            not _matches_schema(
                item, properties.get(key, schema.get("additionalProperties", True))
            )
            for key, item in value.items()
        ):
            return False
    if type(value) is list:
        if any(not _matches_schema(item, schema.get("items", True)) for item in value):
            return False
        if len(value) < schema.get("minItems", 0) or (
            "maxItems" in schema and len(value) > schema["maxItems"]
        ):
            return False
        if schema.get("uniqueItems", False) and any(
            _json_equal(item, earlier)
            for index, item in enumerate(value)
            for earlier in value[:index]
        ):
            return False
    if type(value) is str and (
        len(value) < schema.get("minLength", 0)
        or ("maxLength" in schema and len(value) > schema["maxLength"])
    ):
        return False
    if _is_number(value):
        for keyword, invalid in (
            ("minimum", lambda bound: value < bound),
            ("maximum", lambda bound: value > bound),
            ("exclusiveMinimum", lambda bound: value <= bound),
            ("exclusiveMaximum", lambda bound: value >= bound),
        ):
            if keyword in schema and invalid(schema[keyword]):
                return False
    return True


def _tools(tools: Any, *, depth: int) -> tuple[list[dict[str, Any]] | None, int]:
    if tools is None:
        return None, 0
    rows = list(_seq("tools", tools))
    if not rows:
        _fail("invalid_request", "tools must be omitted or non-empty")
    wired, names = [], []
    for tool in rows:
        function = tool.get("function") if type(tool) is dict else None
        name = function.get("name") if type(function) is dict else None
        if (
            type(tool) is not dict
            or tool.get("type") != "function"
            or type(name) is not str
            or not name
            or name in names
        ):
            _fail("invalid_request", "tool schema must be a unique function")
        assert isinstance(function, dict)
        _walk(function, code="invalid_request", depth=1, limit=depth)
        _check_schema(function.get("parameters", {}), depth=0)
        names.append(name)
        wired.append(
            {
                "type": "function",
                "function": loads_strict(_dumps(function), code="invalid_request"),
            }
        )
    return wired, _utf8(_dumps(wired))


def _choice(choice: Any, names: Sequence[str]) -> Any:
    if choice is None:
        return None
    if type(choice) is str and choice in {"auto", "none", "required"}:
        return choice
    function = choice.get("function") if type(choice) is dict else None
    if (
        type(choice) is dict
        and set(choice) == {"type", "function"}
        and choice.get("type") == "function"
        and type(function) is dict
        and set(function) == {"name"}
        and function.get("name") in names
    ):
        return {"type": "function", "function": {"name": function["name"]}}
    _fail("unsupported_control", "tool_choice is not supported")


def _sample(name: str, value: Any, *, enabled: bool) -> Any:
    if value is None:
        return None
    if not enabled:
        _fail(
            "unsupported_control",
            "explicit sampling control is not supported and was not dropped",
            field=name,
        )
    if (
        type(value) is bool
        or type(value) not in (int, float)
        or (type(value) is float and not math.isfinite(value))
    ):
        _fail("invalid_request", "sampling control must be a finite number", field=name)
    if value < 0 or value > (2 if name == "temperature" else 1):
        _fail("invalid_request", "sampling control is outside its range", field=name)
    return value


@dataclass(frozen=True, eq=False)
class _JsonSnapshot(Mapping[str, Any]):
    """Canonical immutable backing; nested values returned to callers are copies."""

    encoded: str

    @classmethod
    def capture(cls, value: Mapping[str, Any]) -> _JsonSnapshot:
        encoded = _dumps(dict(value))
        _utf8(encoded)
        return cls(encoded)

    def __getitem__(self, key: str) -> Any:
        return json.loads(self.encoded)[key]

    def __iter__(self) -> Iterator[str]:
        return iter(json.loads(self.encoded))

    def __len__(self) -> int:
        return len(json.loads(self.encoded))


@dataclass(frozen=True)
class ChatRequest:
    dialect: str
    model: str
    payload: Mapping[str, Any]
    token_evidence: Mapping[str, Any]
    reasoning_mode: str
    reasoning_sent: Mapping[str, Any]

    def __post_init__(self) -> None:
        for name in ("payload", "token_evidence", "reasoning_sent"):
            object.__setattr__(self, name, _JsonSnapshot.capture(getattr(self, name)))

    def as_dict(self) -> dict[str, Any]:
        return {
            "dialect": self.dialect,
            "model": self.model,
            "payload": json.loads(_dumps(self.payload)),
            "token_evidence": json.loads(_dumps(dict(self.token_evidence))),
            "reasoning_mode": self.reasoning_mode,
            "reasoning_sent": dict(self.reasoning_sent),
        }


@dataclass(frozen=True)
class SealedChat:
    model: str
    text: str
    reasoning: str
    reasoning_fields: Mapping[str, str]
    tool_calls: tuple[Mapping[str, Any], ...]
    finish_reason: str
    usage: Mapping[str, int] | None
    usage_status: str
    usage_fields: Mapping[str, str]
    arguments_schema_validated: bool = False

    def __post_init__(self) -> None:
        for name in ("reasoning_fields", "usage_fields"):
            object.__setattr__(self, name, _JsonSnapshot.capture(getattr(self, name)))
        if self.usage is not None:
            object.__setattr__(self, "usage", _JsonSnapshot.capture(self.usage))
        object.__setattr__(
            self,
            "tool_calls",
            tuple(_JsonSnapshot.capture(call) for call in self.tool_calls),
        )

    def as_dict(self) -> dict[str, Any]:
        body = {
            "model": self.model,
            "text": self.text,
            "reasoning": self.reasoning,
            "reasoning_fields": dict(self.reasoning_fields),
            "tool_calls": [dict(call) for call in self.tool_calls],
            "finish_reason": self.finish_reason,
            "usage": None if self.usage is None else dict(self.usage),
            "usage_status": self.usage_status,
            "usage_fields": dict(self.usage_fields),
            "arguments_schema_validated": self.arguments_schema_validated,
        }
        return json.loads(_dumps(body))


def build_chat_request(
    *,
    dialect: str,
    model: str,
    messages: Sequence[Mapping[str, Any]],
    context_tokens: int,
    max_output_tokens: int,
    tools: Sequence[Mapping[str, Any]] | None = None,
    tool_choice: str | Mapping[str, Any] | None = None,
    temperature: float | None = None,
    top_p: float | None = None,
    sampling_supported: bool = True,
    reasoning_mode: str = "provider-default",
    reasoning_controls: Mapping[str, Mapping[str, Any]] | None = None,
    reasoning_control_evidence: str | None = None,
    reasoning_body: Mapping[str, Any] | None = None,
    history_replay_fields: Sequence[str] = (),
    require_history_replay: bool = False,
    template_overhead_tokens: int = 0,
    output_includes_reasoning: bool | None = None,
    protected_marker: str = PROTECTED_MARKER,
    extensions: Mapping[str, Any] | None = None,
    stop: Any = None,
    n: int | None = None,
    stream: bool = False,
    usage_request_supported: bool = False,
    supplied_prompt_tokens: int | None = None,
    verified_prompt_tokens: int | None = None,
    tokenizer_evidence_id: str | None = None,
    max_argument_depth: int = 32,
    max_tool_calls: int = 32,
) -> ChatRequest:
    """Encode one chat payload without shortening the transcript.

    ``reasoning_body`` is an explicit model-specific mapping; its evidence
    source must be supplied. Configured evidence is an operator declaration,
    not a claim that the server honored the setting.

    ``verified_prompt_tokens`` must count the entire server-rendered prompt,
    including tools and template framing, for this request and deployment.
    The caller binds ``tokenizer_evidence_id`` to that verified measurement.
    Previous response usage or a count for a different prompt is insufficient.
    """
    _dialect(dialect)
    if type(model) is not str or not model:
        _fail("invalid_request", "deployed model id is required")
    if (
        type(sampling_supported) is not bool
        or type(stream) is not bool
        or type(usage_request_supported) is not bool
    ):
        _fail("invalid_request", "boolean request controls must be booleans")
    if (
        output_includes_reasoning is not None
        and type(output_includes_reasoning) is not bool
    ):
        _fail("invalid_request", "output_includes_reasoning must be boolean or null")
    if (
        extensions
        or stop is not None
        or (n is not None and (type(n) is not int or n != 1))
    ):
        _fail(
            "unsupported_control",
            "extra_body, stop, or native batching is not supported and was not dropped",
        )
    context, output = _int("context_tokens", context_tokens, 1), _int(
        "max_output_tokens", max_output_tokens, 1
    )
    overhead = _int("template_overhead_tokens", template_overhead_tokens, 0)
    if supplied_prompt_tokens is not None:
        supplied_prompt_tokens = _int(
            "supplied_prompt_tokens", supplied_prompt_tokens, 0
        )
    if reasoning_control_evidence is not None and (
        type(reasoning_control_evidence) is not str
        or reasoning_control_evidence not in {"configured", "discovered", "probed"}
    ):
        _fail("invalid_request", "reasoning evidence source is invalid")
    if reasoning_body is not None and reasoning_controls:
        _fail(
            "invalid_request", "supply reasoning_body or reasoning_controls, not both"
        )
    controls = _controls(dialect, reasoning_controls)
    label = "provider-default" if reasoning_mode is None else reasoning_mode
    if type(label) is not str:
        _fail("invalid_request", "reasoning_mode must be a string")
    label = label.strip()
    if reasoning_body is not None:
        if label not in _DEFAULTS | _MODES | {"auto"}:
            _fail("unsupported_control", "reasoning mode is unsupported")
        sent = (
            {}
            if type(reasoning_body) is dict
            and not reasoning_body
            and label in _DEFAULTS | {"auto"}
            else _body(dialect, reasoning_body)
        )
    else:
        sent = (
            {}
            if label in _DEFAULTS | {"auto"}
            else (
                dict(controls[label])
                if label in controls
                else _fail(
                    "unsupported_control",
                    "explicit reasoning mode is not supported and was not dropped",
                    reasoning_mode=label,
                )
            )
        )
    if sent and reasoning_control_evidence is None:
        _fail(
            "unsupported_control",
            "explicit reasoning mapping requires model-bound capability evidence",
        )
    mode = "provider-default" if label in _DEFAULTS else label
    depth, call_limit = _int("max_argument_depth", max_argument_depth, 1), _int(
        "max_tool_calls", max_tool_calls, 1
    )
    wired, message_tokens, replay_tokens, kinds = _messages(
        messages,
        dialect=dialect,
        replay=history_replay_fields,
        required=require_history_replay,
        marker=protected_marker,
        depth=depth,
        limit=call_limit,
    )
    tool_payload, tool_tokens = _tools(tools, depth=depth)
    if tool_choice is not None and tool_payload is None:
        _fail("invalid_request", "tool_choice requires tools")
    estimated = message_tokens + tool_tokens + overhead
    if supplied_prompt_tokens is not None:
        estimated = max(estimated, supplied_prompt_tokens)
    if (verified_prompt_tokens is None) != (tokenizer_evidence_id is None):
        _fail(
            "invalid_request",
            "verified prompt count requires tokenizer/template evidence",
        )
    if verified_prompt_tokens is not None:
        if type(tokenizer_evidence_id) is not str or not tokenizer_evidence_id.strip():
            _fail("invalid_request", "tokenizer evidence id is required")
        estimated = _int("verified_prompt_tokens", verified_prompt_tokens, 0)
    available = context - output
    evidence: dict[str, Any] = {
        "estimated_tokens": estimated,
        "needed_tokens": estimated,
        "available_tokens": available,
        "accuracy": "conservative_not_exact",
        "exact": False,
        "fit_guarantee": False,
        "method": "utf8_byte_upper_bound",
        "context_tokens": context,
        "max_output_tokens": output,
        "template_overhead_tokens": overhead,
        "message_tokens": message_tokens,
        "tool_schema_tokens": tool_tokens,
        "replayed_reasoning_tokens": replay_tokens,
        "message_framing_tokens": 8,
        "output_limit_field": "max_tokens",
        "output_includes_reasoning": output_includes_reasoning,
        "output_limit_honored": "unverified",
        "supplied_prompt_tokens": supplied_prompt_tokens,
        "supplied_accuracy": None if supplied_prompt_tokens is None else "unverified",
        "protected_kinds": list(kinds),
        "truncated": False,
    }
    evidence["reasoning_control_evidence"] = (
        reasoning_control_evidence if sent else None
    )
    if verified_prompt_tokens is not None:
        evidence.update(
            exact=True,
            accuracy="verified_tokenizer",
            method="verified_rendered_prompt",
            tokenizer_evidence_id=tokenizer_evidence_id,
        )
    if estimated > available:
        _fail(
            "context_capacity_insufficient",
            "context capacity is insufficient for the full protected transcript",
            **evidence,
        )
    payload: dict[str, Any] = {
        "model": model,
        "messages": wired,
        "max_tokens": output,
        **sent,
    }
    temperature_sent, top_p_sent = _sample(
        "temperature", temperature, enabled=sampling_supported
    ), _sample("top_p", top_p, enabled=sampling_supported)
    if temperature_sent is not None:
        payload["temperature"] = temperature_sent
    if top_p_sent is not None:
        payload["top_p"] = top_p_sent
    if tool_payload is not None:
        payload["tools"] = tool_payload
        selected = _choice(
            tool_choice, [item["function"]["name"] for item in tool_payload]
        )
        if selected is not None:
            payload["tool_choice"] = selected
    if n == 1:
        payload["n"] = 1
    if stream:
        payload["stream"] = True
        if usage_request_supported:
            payload["stream_options"] = {"include_usage": True}
    return ChatRequest(dialect, model, payload, evidence, mode, sent)


def _names(value: Sequence[str]) -> tuple[str, ...]:
    names = tuple(_seq("allowed_tool_names", value))
    if any(type(name) is not str or not name for name in names):
        _fail("invalid_request", "allowed tool names must be non-empty strings")
    if len(set(names)) != len(names):
        _fail("invalid_request", "allowed tool names must be unique")
    return names


def _model(payload: Mapping[str, Any], expected: str, aliases: Sequence[str]) -> str:
    if type(expected) is not str or not expected:
        _fail("invalid_request", "expected model id is required")
    allowed = tuple(_seq("allowed_model_aliases", aliases))
    if any(type(item) is not str or not item for item in allowed) or len(
        set(allowed)
    ) != len(allowed):
        _fail(
            "invalid_request", "allowed model aliases must be unique non-empty strings"
        )
    reported = payload.get("model")
    if (
        type(reported) is not str
        or not reported
        or (reported != expected and reported not in allowed)
    ):
        _fail(
            "model_identity_mismatch",
            "response model is not the deployed model or an explicit alias",
        )
    _utf8(reported)
    return reported


def _choice0(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    choices = payload.get("choices")
    choice = choices[0] if type(choices) is list and choices else None
    index = choice.get("index", 0) if type(choice) is dict else None
    if "choices" not in payload or type(choices) is not list or not choices:
        _fail("missing_choices", "response did not include a choice")
    if len(choices) != 1 or type(index) is not int or index != 0:
        _fail("ambiguous_terminal", "response did not contain one choice at index 0")
    assert isinstance(choice, dict)
    return choice


def _finish(choice: Mapping[str, Any], message: Mapping[str, Any]) -> str:
    finish, refusal = choice.get("finish_reason"), message.get("refusal")
    if "finish_reason" not in choice or type(finish) is not str or not finish:
        _fail("ambiguous_terminal", "response finish reason is missing")
    if finish in {"refusal", "content_filter"} or (
        "refusal" in message
        and not (refusal is None or (type(refusal) is str and not refusal.strip()))
    ):
        _fail("refusal", "response is a refusal")
    if finish in {"length", "max_tokens"}:
        _fail("truncated_response", "response was truncated")
    if finish not in {"stop", "tool_calls"}:
        _fail("ambiguous_terminal", "response finish reason is ambiguous")
    return finish


def _calls(
    raw: Any,
    *,
    allowed: Sequence[str],
    objects: bool,
    bound: int,
    depth: int,
    limit: int,
) -> tuple[dict[str, Any], ...]:
    if type(raw) is not list or len(raw) > limit:
        _fail("malformed_tool_batch", "tool_calls is not a bounded list")
    known, sealed, seen, indexes = set(allowed), [], set(), set()
    for index, call in enumerate(raw):
        function = call.get("function") if type(call) is dict else None
        name = function.get("name") if type(function) is dict else None
        slot, call_id = (
            (call.get("index"), call.get("id")) if type(call) is dict else (None, None)
        )
        if type(call) is not dict:
            _fail("malformed_tool_batch", "tool call is not an object", index=index)
        if (
            "index" in call
            and slot is not None
            and (type(slot) is not int or slot < 0 or slot in indexes)
        ):
            _fail("malformed_tool_batch", "tool call index conflicts", index=index)
        if type(slot) is int:
            indexes.add(slot)
        if (
            type(call_id) is not str
            or not call_id
            or call_id in seen
            or call.get("type") != "function"
            or type(name) is not str
            or name not in known
            or type(function) is not dict
            or "arguments" not in function
        ):
            _fail(
                "malformed_tool_batch",
                "tool call id or function is invalid",
                index=index,
            )
        seen.add(call_id)
        assert isinstance(function, dict)
        parsed, encoded = _arguments(
            function["arguments"],
            objects=objects,
            code="malformed_tool_batch",
            bound=bound,
            depth=depth,
            index=index,
        )
        sealed.append(
            {
                "id": call_id,
                "type": "function",
                "name": name,
                "arguments": parsed,
                "arguments_json": encoded,
            }
        )
    return tuple(sealed)


def _reason(message: Mapping[str, Any]) -> dict[str, str]:
    fields: dict[str, str] = {}
    for key in ("reasoning_content", "reasoning"):
        if key not in message or message.get(key) is None:
            continue
        if type(message.get(key)) is not str:
            _fail("invalid_response", "reasoning field is not a string", field=key)
        fields[key] = message[key]
    return fields


def _usage(
    payload: Mapping[str, Any],
) -> tuple[dict[str, int] | None, str, dict[str, str]]:
    unknown = {key: "unknown" for key in _USAGE}
    if "usage" not in payload or payload.get("usage") is None:
        return None, "unknown", unknown
    usage = payload.get("usage")
    if type(usage) is not dict:
        _fail("invalid_response", "usage is not an object")
    reported, fields = {}, dict(unknown)
    for key in _USAGE:
        if key not in usage or usage.get(key) is None:
            continue
        value = usage.get(key)
        if type(value) is not int or value < 0:
            _fail(
                "invalid_response",
                "usage contains a non-integer token count",
                field=key,
            )
        reported[key], fields[key] = value, "reported"
    return (reported, "reported", fields) if reported else (None, "unknown", fields)


def seal_chat_response(
    payload: Mapping[str, Any] | str,
    *,
    expected_model: str,
    allowed_tool_names: Sequence[str],
    allowed_model_aliases: Sequence[str] = (),
    allowed_tool_schemas: Sequence[Mapping[str, Any]] | None = None,
    argument_encoding: str = "json_string",
    max_arguments_bytes: int = 65536,
    max_argument_depth: int = 32,
    max_tool_calls: int = 32,
) -> SealedChat:
    """Validate one complete batch before the host executes any call.

    Pass the exact schemas sent in the request as ``allowed_tool_schemas``.
    Without them this provides structural validation only; the returned
    ``arguments_schema_validated`` remains false. Mathematical soundness is
    still established by Lean, independently of JSON schema validation.
    """
    response_depth = max(64, _int("max_argument_depth", max_argument_depth, 1) + 8)
    if type(payload) is str:
        parsed = loads_strict(
            payload, code="invalid_response", max_depth=response_depth
        )
        payload = (
            parsed
            if type(parsed) is dict
            else _fail("invalid_response", "response JSON must be an object")
        )
    elif type(payload) is not dict:
        _fail("invalid_response", "response must be an object or JSON text")
    if type(argument_encoding) is not str or argument_encoding not in {
        "json_string",
        "object",
    }:
        _fail("invalid_request", "argument_encoding is not supported")
    choice, message = _choice0(payload), None
    message = choice.get("message")
    if type(message) is not dict:
        _fail("invalid_response", "response choice has no message")
    if message.get("role") != "assistant":
        _fail("invalid_response", "response message must have assistant role")
    if payload.get("error") is not None:
        _fail("provider_error", "provider returned an error")
    finish = _finish(choice, message)
    if message.get("function_call") not in (None,):
        _fail("malformed_tool_batch", "legacy function_call is not a native tool batch")
    names = _names(allowed_tool_names)
    if "tool_calls" in message and message.get("tool_calls") is not None:
        calls = _calls(
            message.get("tool_calls"),
            allowed=names,
            objects=argument_encoding == "object",
            bound=_int("max_arguments_bytes", max_arguments_bytes, 1),
            depth=_int("max_argument_depth", max_argument_depth, 1),
            limit=_int("max_tool_calls", max_tool_calls, 1),
        )
    else:
        calls = ()
    if allowed_tool_schemas is not None:
        schema_tools, _size = (
            ([], 0)
            if allowed_tool_schemas == []
            else _tools(allowed_tool_schemas, depth=32)
        )
        schemas = {
            tool["function"]["name"]: tool["function"].get(
                "parameters",
                {"type": "object", "properties": {}, "additionalProperties": False},
            )
            for tool in schema_tools or []
        }
        if set(schemas) != set(names):
            _fail("invalid_request", "tool schema names differ from allowed tool names")
        for index, call in enumerate(calls):
            if not _matches_schema(call["arguments"], schemas[call["name"]]):
                _fail(
                    "malformed_tool_batch",
                    "tool arguments do not satisfy the supplied schema",
                    index=index,
                )
    if (finish == "tool_calls" and not calls) or (finish == "stop" and calls):
        _fail(
            "ambiguous_terminal", "finish reason does not match the native tool batch"
        )
    text, fields = _text(message.get("content"), code="invalid_response"), _reason(
        message
    )
    if finish == "stop" and not calls and not text.strip():
        _fail(
            (
                "reasoning_only"
                if any(value.strip() for value in fields.values())
                else "empty_reply"
            ),
            "response has no answer or native tool call",
        )
    usage, status, usage_fields = _usage(payload)
    _walk(payload, code="invalid_response", depth=0, limit=response_depth)
    return SealedChat(
        _model(payload, expected_model, allowed_model_aliases),
        text,
        "\n".join(value for value in fields.values() if value),
        fields,
        calls,
        finish,
        usage,
        status,
        usage_fields,
        allowed_tool_schemas is not None,
    )


class SSEAssembler:
    """Bounded SSE assembler. Seal only the dict returned by finish."""

    def __init__(
        self,
        *,
        max_bytes: int = 1048576,
        max_events: int = 4096,
        require_done: bool = True,
        max_tool_calls: int = 32,
        defer_semantic_errors: bool = False,
    ) -> None:
        self.max_bytes, self.max_events, self.max_calls = (
            _int("max_bytes", max_bytes, 1),
            _int("max_events", max_events, 1),
            _int("max_tool_calls", max_tool_calls, 1),
        )
        if type(require_done) is not bool or type(defer_semantic_errors) is not bool:
            _fail("invalid_request", "stream control flags must be boolean")
        self._defer_semantic_errors = defer_semantic_errors
        self._semantic_failure: LocalProtocolError | None = None
        self._completion_observed = False
        self.require_done, self.decoder = require_done, codecs.getincrementaldecoder(
            "utf-8"
        )("strict")
        self.mode: str | None = None
        self.model: str | None = None
        self.terminal: str | None = None
        self.usage: dict[str, Any] | None = None
        self._failure: LocalProtocolError | None = None
        self.response_id: str | None = None
        self.seen = self.events = 0
        self.pending, self.cr, self.done, self.closed = "", False, False, False
        self.content: list[str] = []
        self.reasoning: list[str] = []
        self.reasoning_content: list[str] = []
        self.tools: dict[int, dict[str, Any]] = {}

    @property
    def completion_observed(self) -> bool:
        """A rejected stream reached a terminal event and DONE at clean EOF.

        This is transport completion evidence only. The response stays rejected
        and no content or tool batch can be obtained from ``finish``.
        """
        return self._completion_observed

    def feed(self, chunk: bytes | str) -> None:
        if self._failure is not None:
            raise self._failure
        try:
            self._feed(chunk)
        except LocalProtocolError as exc:
            self._failure = exc
            raise

    def _feed(self, chunk: bytes | str) -> None:
        if self.closed:
            _fail("stream_incomplete", "SSE assembler was already finished")
        if type(chunk) is str:
            if self.mode == "bytes":
                _fail("invalid_request", "SSE chunks must not mix text and bytes")
            self.mode, size, text = "text", _utf8(chunk), chunk
        elif type(chunk) is bytes:
            if self.mode == "text":
                _fail("invalid_request", "SSE chunks must not mix text and bytes")
            self.mode, size = "bytes", len(chunk)
            try:
                text = self.decoder.decode(chunk, False)
            except UnicodeError:
                raise LocalProtocolError(
                    "stream_incomplete", "SSE stream is not valid UTF-8"
                ) from None
        else:
            _fail("invalid_request", "SSE chunk must be bytes or text")
        self.seen += size
        if self.seen > self.max_bytes or (self.done and text.strip()):
            _fail(
                (
                    "stream_overflow"
                    if self.seen > self.max_bytes
                    else "stream_incomplete"
                ),
                "SSE stream exceeded its bound or continued after [DONE]",
            )
        self._push(text)

    def finish(self) -> dict[str, Any]:
        if self._failure is not None:
            raise self._failure
        try:
            return self._finish_stream()
        except LocalProtocolError as exc:
            self._failure = exc
            raise

    def _finish_stream(self) -> dict[str, Any]:
        if self.closed:
            _fail("stream_incomplete", "SSE assembler was already finished")
        self.closed = True
        if self.mode == "bytes":
            try:
                self._push(self.decoder.decode(b"", True))
            except UnicodeError:
                raise LocalProtocolError(
                    "stream_incomplete", "SSE stream ended inside a UTF-8 character"
                ) from None
        if self.cr:
            self.pending, self.cr = self.pending + "\n", False
            self._drain()
        if (
            self.pending.strip()
            or self.terminal is None
            or (self.require_done and not self.done)
        ):
            _fail("stream_incomplete", "SSE stream ended without a finished event")
        # Framing and clean EOF establish completion before final semantic
        # checks (including tool-index continuity) can reject the response.
        self._completion_observed = (
            self._defer_semantic_errors
            and self.done
            and self.terminal
            in {"stop", "tool_calls", "length", "content_filter", "function_call"}
        )
        if self._semantic_failure is not None:
            raise self._semantic_failure
        indexes = sorted(self.tools)
        if indexes != list(range(len(indexes))):
            _fail("malformed_tool_batch", "SSE tool indexes are incomplete")
        message: dict[str, Any] = {
            "role": "assistant",
            "content": "".join(self.content),
        }
        if self.reasoning_content:
            message["reasoning_content"] = "".join(self.reasoning_content)
        if self.reasoning:
            message["reasoning"] = "".join(self.reasoning)
        if indexes:
            message["tool_calls"] = [
                {
                    "id": self.tools[i]["id"] or "",
                    "type": self.tools[i]["type"] or "",
                    "function": {
                        "name": self.tools[i]["name"] or "",
                        "arguments": "".join(self.tools[i]["arguments"]),
                    },
                }
                for i in indexes
            ]
        payload: dict[str, Any] = {
            "choices": [
                {"index": 0, "finish_reason": self.terminal, "message": message}
            ]
        }
        if self.model is not None:
            payload["model"] = self.model
        if self.usage is not None:
            payload["usage"] = self.usage
        return payload

    def _push(self, text: str) -> None:
        if self.cr:
            text, self.cr = "\r" + text, False
        if text.endswith("\r"):
            self.cr, text = True, text[:-1]
        if text:
            self.pending += text.replace("\r\n", "\n").replace("\r", "\n")
            self._drain()

    def _drain(self) -> None:
        while "\n\n" in self.pending:
            event, self.pending = self.pending.split("\n\n", 1)
            self._event(event)

    def _event(self, event: str) -> None:
        if self.done and event.strip():
            _fail("stream_incomplete", "SSE data followed [DONE]")
        data: list[str] = []
        for line in event.split("\n"):
            if not line or line.startswith(":"):
                continue
            if line.startswith("data:"):
                value = line[5:]
                data.append(value[1:] if value.startswith(" ") else value)
            elif not line.startswith(("event:", "id:", "retry:")):
                _fail("invalid_response", "SSE event contains an unsupported field")
        if not data:
            return
        self.events += 1
        if self.events > self.max_events:
            _fail("stream_overflow", "SSE stream exceeded its event limit")
        body = "\n".join(data)
        if body == "[DONE]":
            self.done = True
            return
        parsed = loads_strict(body, code="invalid_response")
        if type(parsed) is not dict:
            _fail("invalid_response", "SSE data is not a JSON object")
        self._apply(parsed)

    def _apply(self, chunk: Mapping[str, Any]) -> None:
        if chunk.get("error") is not None:
            _fail("provider_error", "provider returned an error")
        if "id" in chunk:
            response_id = chunk["id"]
            if (
                type(response_id) is not str
                or not response_id
                or self.response_id not in (None, response_id)
            ):
                _fail("invalid_response", "SSE response identity changed")
            self.response_id = response_id
        if "model" in chunk and chunk.get("model") is not None:
            model = chunk.get("model")
            if type(model) is not str or not model or self.model not in (None, model):
                _fail(
                    "model_identity_mismatch",
                    "SSE model identity is missing or changed",
                )
            self.model = model
        choices = (
            []
            if "choices" in chunk and chunk.get("choices") is None
            else chunk.get("choices", [])
        )
        if type(choices) is not list or len(choices) > 1:
            _fail("ambiguous_terminal", "SSE chunk does not contain one choice")
        if len(choices) == 1:
            self._apply_choice(choices[0])
        if "usage" in chunk and chunk.get("usage") is not None:
            _usage(chunk)
            usage = chunk.get("usage")
            if type(usage) is not dict or (
                self.usage is not None and self.usage != usage
            ):
                _fail("invalid_response", "SSE usage conflicts")
            self.usage = dict(usage)

    def _apply_choice(self, choice: Any) -> None:
        if self.terminal is not None:
            _fail("ambiguous_terminal", "SSE choice followed terminal completion")
        index = choice.get("index", 0) if type(choice) is dict else None
        if (
            type(choice) is not dict
            or type(index) is not int
            or index != 0
            or choice.get("message") not in (None,)
        ):
            _fail("ambiguous_terminal", "SSE choice is not a single index-0 delta")
        delta, finish = choice.get("delta"), choice.get("finish_reason")
        if delta is not None:
            if type(delta) is not dict:
                _fail("invalid_response", "SSE delta is not an object")
            try:
                self._delta(delta)
            except LocalProtocolError as exc:
                recoverable = exc.code == "malformed_tool_batch" or (
                    exc.code == "refusal" and type(delta.get("refusal")) is str
                )
                if not self._defer_semantic_errors or not recoverable:
                    raise
                # Preserve the first semantic rejection while still validating
                # every framing/identity/terminal event through bounded EOF.
                if self._semantic_failure is None:
                    self._semantic_failure = exc
        if finish is None:
            return
        if type(finish) is not str or not finish or self.terminal not in (None, finish):
            _fail("ambiguous_terminal", "SSE finish reason conflicts")
        self.terminal = finish

    def _delta(self, delta: Mapping[str, Any]) -> None:
        if "role" in delta and delta["role"] != "assistant":
            _fail("invalid_response", "SSE role must be assistant")
        refusal = delta.get("refusal")
        if refusal is not None and not (type(refusal) is str and not refusal.strip()):
            _fail("refusal", "response is a refusal")
        if delta.get("function_call") is not None:
            _fail(
                "malformed_tool_batch",
                "legacy function_call is not a native tool batch",
            )
        if delta.get("content") is not None:
            if type(delta.get("content")) is not str:
                _fail("invalid_response", "SSE content is not a string")
            self.content.append(delta["content"])
        for key, sink in (
            ("reasoning_content", self.reasoning_content),
            ("reasoning", self.reasoning),
        ):
            if delta.get(key) is not None:
                if type(delta.get(key)) is not str:
                    _fail("invalid_response", "SSE reasoning is not a string")
                sink.append(delta[key])
        calls = delta.get("tool_calls")
        if calls is None:
            return
        if type(calls) is not list:
            _fail("malformed_tool_batch", "SSE tool_calls is not a list")
        for call in calls:
            if (
                type(call) is not dict
                or type(call.get("index")) is not int
                or call["index"] < 0
            ):
                _fail("malformed_tool_batch", "SSE tool delta index is missing")
            index = call["index"]
            if index >= self.max_calls or (
                len(self.tools) >= self.max_calls and index not in self.tools
            ):
                _fail("malformed_tool_batch", "SSE tool batch exceeds the call limit")
            slot = self.tools.setdefault(
                index, {"id": None, "name": None, "type": None, "arguments": []}
            )
            for key in ("id", "type"):
                if call.get(key) is not None and (
                    type(call.get(key)) is not str
                    or not call.get(key)
                    or slot[key] not in (None, call.get(key))
                ):
                    _fail(
                        "malformed_tool_batch",
                        "SSE tool identity conflicts",
                        index=index,
                    )
                if type(call.get(key)) is str:
                    slot[key] = call[key]
            function = call.get("function")
            if function is None:
                continue
            if type(function) is not dict:
                _fail(
                    "malformed_tool_batch",
                    "SSE tool function is not an object",
                    index=index,
                )
            if function.get("name") is not None and (
                type(function.get("name")) is not str
                or not function.get("name")
                or slot["name"] not in (None, function.get("name"))
            ):
                _fail("malformed_tool_batch", "SSE tool name conflicts", index=index)
            if type(function.get("name")) is str:
                slot["name"] = function["name"]
            if (
                function.get("arguments") is not None
                and type(function.get("arguments")) is not str
            ):
                _fail(
                    "malformed_tool_batch",
                    "SSE tool arguments must be text fragments",
                    index=index,
                )
            if type(function.get("arguments")) is str:
                slot["arguments"].append(function["arguments"])
