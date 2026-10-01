"""Versioned, immutable operator declarations for a local chat wire protocol.

Declarations are configured evidence, not proof of server behavior. Runtime
qualification must independently establish the endpoint's capabilities.

An optional deployment ``protocol`` object uses ``schema: 1``. For example,
``reasoning_controls: {on: {chat_template_kwargs: {enable_thinking: true}}}``
selects an explicit vLLM template control. ``reasoning_efforts`` maps Mini's
effort labels to exact model values, such as ``high: {reasoning_effort: high}``.
No mapping is inferred from a model name. ``streaming.usage_request`` is
``omit`` by default or ``include_usage`` for a qualified streaming server.
"""
from __future__ import annotations

from dataclasses import dataclass
import re
from types import MappingProxyType
from typing import Any, Mapping, NoReturn

from .errors import LocalInferenceError

_MODEL = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:/-]{0,255}\Z")
_EFFORT_VALUE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}\Z")
_EFFORTS = frozenset({"none", "low", "medium", "high", "max"})
_FIELDS = {
    "generic": frozenset({"reasoning_effort"}),
    "vllm": frozenset({"reasoning_effort", "chat_template_kwargs"}),
    "ollama": frozenset({"reasoning_effort"}),
    "llamacpp": frozenset({"reasoning_effort", "chat_template_kwargs", "reasoning_format"}),
}
_HISTORY = {
    "generic": frozenset(),
    "vllm": frozenset({"reasoning", "reasoning_content"}),
    "ollama": frozenset({"reasoning", "reasoning_content"}),
    "llamacpp": frozenset({"reasoning_content"}),
}


@dataclass(frozen=True)
class ReasoningRequest:
    reasoning_effort: str | None = None
    enable_thinking: bool | None = None
    reasoning_format: str | None = None


@dataclass(frozen=True)
class StreamingPolicy:
    enabled: bool = False
    require_done: bool = True
    usage_request: str = "omit"


@dataclass(frozen=True)
class ProtocolLimits:
    max_response_bytes: int = 1048576
    max_stream_events: int = 4096
    max_arguments_bytes: int = 65536
    max_argument_depth: int = 32
    max_tool_calls: int = 32


@dataclass(frozen=True)
class ProtocolPolicy:
    schema: int
    reasoning_controls: Mapping[str, ReasoningRequest]
    reasoning_efforts: Mapping[str, ReasoningRequest]
    history_replay_fields: tuple[str, ...]
    require_history_replay: bool
    model_aliases: tuple[str, ...]
    argument_encoding: str
    template_overhead_tokens: int
    streaming: StreamingPolicy
    limits: ProtocolLimits

    @property
    def evidence_source(self) -> str:
        return "configured"


def _fail(field: str) -> NoReturn:
    raise LocalInferenceError("invalid_protocol_policy", field)


def _object(value: Any, allowed: set[str] | frozenset[str], field: str) -> dict[str, Any]:
    if type(value) is not dict or any(type(k) is not str or k not in allowed for k in value):
        _fail(field)
    return value


def _bool(value: Any, field: str) -> bool:
    if type(value) is not bool:
        _fail(field)
    return value


def _int(value: Any, low: int, high: int, field: str) -> int:
    if type(value) is not int or not low <= value <= high:
        _fail(field)
    return value


def _choice(value: Any, allowed: set[str], field: str) -> str:
    if type(value) is not str or value not in allowed:
        _fail(field)
    return value


def _strings(value: Any, field: str) -> tuple[str, ...]:
    if type(value) is not list or len(value) > 64:
        _fail(field)
    if any(type(item) is not str or _MODEL.fullmatch(item) is None for item in value):
        _fail(field)
    if len(set(value)) != len(value):
        _fail(field)
    return tuple(value)


def _request(value: Any) -> ReasoningRequest:
    item = _object(value, {"reasoning_effort", "chat_template_kwargs", "reasoning_format"}, "reasoning_controls")
    if not item:
        _fail("reasoning_controls")
    effort = item.get("reasoning_effort")
    if "reasoning_effort" in item and (type(effort) is not str or _EFFORT_VALUE.fullmatch(effort) is None):
        _fail("reasoning_effort")
    thinking = None
    if "chat_template_kwargs" in item:
        kwargs = _object(item["chat_template_kwargs"], {"enable_thinking"}, "chat_template_kwargs")
        thinking = _bool(kwargs.get("enable_thinking"), "enable_thinking")
    fmt = None
    if "reasoning_format" in item:
        fmt = _choice(item["reasoning_format"], {"none", "deepseek", "deepseek-legacy"}, "reasoning_format")
    return ReasoningRequest(effort, thinking, fmt)


def request_body(request: ReasoningRequest) -> dict[str, Any]:
    body: dict[str, Any] = {}
    if request.reasoning_effort is not None:
        body["reasoning_effort"] = request.reasoning_effort
    if request.enable_thinking is not None:
        body["chat_template_kwargs"] = {"enable_thinking": request.enable_thinking}
    if request.reasoning_format is not None:
        body["reasoning_format"] = request.reasoning_format
    return body


def parse_protocol_policy(value: Any) -> ProtocolPolicy:
    """Parse a schema-1 policy; callers supply ``{schema: 1}`` when omitted."""
    item = _object(value, {
        "schema", "reasoning_controls", "reasoning_efforts", "history_replay_fields",
        "require_history_replay", "model_aliases", "argument_encoding",
        "template_overhead_tokens", "streaming", "limits",
    }, "protocol")
    if type(item.get("schema")) is not int or item["schema"] != 1:
        _fail("schema")
    modes = _object(item.get("reasoning_controls", {}), {"on", "off"}, "reasoning_controls")
    efforts = _object(item.get("reasoning_efforts", {}), _EFFORTS, "reasoning_efforts")
    stream = _object(item.get("streaming", {}), {"enabled", "require_done", "usage_request"}, "streaming")
    streaming = StreamingPolicy(
        enabled=_bool(stream.get("enabled", False), "enabled"),
        require_done=_bool(stream.get("require_done", True), "require_done"),
        usage_request=_choice(stream.get("usage_request", "omit"), {"omit", "include_usage"}, "usage_request"),
    )
    if not streaming.enabled and streaming.usage_request != "omit":
        _fail("usage_request")
    bounds = {
        "max_response_bytes": (1, 67108864), "max_stream_events": (1, 1000000),
        "max_arguments_bytes": (1, 16777216), "max_argument_depth": (1, 128),
        "max_tool_calls": (1, 1024),
    }
    raw_limits = _object(item.get("limits", {}), set(bounds), "limits")
    defaults = ProtocolLimits()
    limits = ProtocolLimits(**{
        key: _int(raw_limits.get(key, getattr(defaults, key)), low, high, key)
        for key, (low, high) in bounds.items()
    })
    replay = _strings(item.get("history_replay_fields", []), "history_replay_fields")
    required = _bool(item.get("require_history_replay", False), "require_history_replay")
    if required and not replay:
        _fail("history_replay_fields")
    return ProtocolPolicy(
        schema=1,
        reasoning_controls=MappingProxyType({key: _request(body) for key, body in modes.items()}),
        reasoning_efforts=MappingProxyType({key: _request(body) for key, body in efforts.items()}),
        history_replay_fields=replay,
        require_history_replay=required,
        model_aliases=_strings(item.get("model_aliases", []), "model_aliases"),
        argument_encoding=_choice(item.get("argument_encoding", "json_string"), {"json_string", "object"}, "argument_encoding"),
        template_overhead_tokens=_int(item.get("template_overhead_tokens", 0), 0, 10000000, "template_overhead_tokens"),
        streaming=streaming,
        limits=limits,
    )


def reasoning_request_body(policy: ProtocolPolicy, mode: str, effort: str | None = None) -> dict[str, Any]:
    """Resolve explicit controls without guessing a wire value or overriding one."""
    if type(mode) is not str or mode not in {"provider-default", "auto", "on", "off"}:
        _fail("reasoning_mode")
    body: dict[str, Any] = {}
    if mode in {"on", "off"}:
        if mode not in policy.reasoning_controls:
            _fail("reasoning_controls")
        body = request_body(policy.reasoning_controls[mode])
    if effort is not None:
        if type(effort) is not str or mode in {"provider-default", "off"} or effort not in policy.reasoning_efforts:
            _fail("reasoning_efforts")
        for key, value in request_body(policy.reasoning_efforts[effort]).items():
            if key in body and body[key] != value:
                _fail("reasoning_efforts")
            body[key] = value
    return body


def validate_protocol_policy(policy: ProtocolPolicy, *, dialect: str, reasoning_mode: str, reasoning_effort: str | None = None) -> None:
    """Validate declarations against the dialect, before any request is admitted."""
    if type(dialect) is not str or dialect not in _FIELDS:
        _fail("dialect")
    for mapping in (policy.reasoning_controls, policy.reasoning_efforts):
        for request in mapping.values():
            if set(request_body(request)) - _FIELDS[dialect]:
                _fail("reasoning_controls")
    if set(policy.history_replay_fields) - _HISTORY[dialect]:
        _fail("history_replay_fields")
    reasoning_request_body(policy, reasoning_mode, reasoning_effort)


def protocol_body(policy: ProtocolPolicy) -> dict[str, Any]:
    """Return a detached canonical body for identity and private snapshots."""
    return {
        "schema": policy.schema,
        "reasoning_controls": {key: request_body(value) for key, value in policy.reasoning_controls.items()},
        "reasoning_efforts": {key: request_body(value) for key, value in policy.reasoning_efforts.items()},
        "history_replay_fields": list(policy.history_replay_fields),
        "require_history_replay": policy.require_history_replay,
        "model_aliases": list(policy.model_aliases),
        "argument_encoding": policy.argument_encoding,
        "template_overhead_tokens": policy.template_overhead_tokens,
        "streaming": {
            "enabled": policy.streaming.enabled, "require_done": policy.streaming.require_done,
            "usage_request": policy.streaming.usage_request,
        },
        "limits": {key: getattr(policy.limits, key) for key in ProtocolLimits.__dataclass_fields__},
    }
