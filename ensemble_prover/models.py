"""Provider clients, request translation, retries, and response normalization."""

from __future__ import annotations

import asyncio
import functools
import hashlib
import json
import logging
import math
import os
import random
import socket
import time
from dataclasses import replace
from typing import Any, Dict, List, Mapping, Optional, Tuple

import httpx

from .config import RoleConfig
from .llm_deadline import LLMRetryDeadlineContext, LLMRetryDeadlineExceeded
from .llm_error_policy import classify_llm_exception
from .llm_usage import (
    cost_for_record,
    emit_usage_callback,
    mark_provider_dispatched,
    mark_provider_pre_generation_rejection,
    notify_provider_dispatch_observer,
    provider_usage_from_payload,
)
from .pricing import (
    base_url_matches_provider,
    canonical_openrouter_model_id,
    ensure_openrouter_reasoning_capabilities_async,
    lookup_openrouter_reasoning_capabilities,
)
from .provider_health import (
    ProviderLaneHealthRegistry,
    ProviderLanePermit,
    ProviderLanePermitOwnership,
    bound_provider_lane_health_registry,
)
from .proof_dossier import (
    _prompt_safe_inline_text,
    prompt_safe_malformed_tool_arguments,
)
from .request_gate import (
    AsyncSharedExclusiveGate,
    formal_provider_exclusive_requested,
)
from .provider_tool_protocol import (
    MiniRequestEnvelopePolicy,
    MiniRequestEnvelopeReceipt,
    bind_mini_request_envelope_receipt,
    current_mini_request_envelope_receipt,
    extract_dsml_tool_calls,
    mini_openrouter_deepseek_v4_explicit_enable_model,
    mini_request_envelope_receipt_is_valid_for,
    resolve_mini_request_output_tokens,
)
from .protocols import LLMChatClientProtocol
from .sampling_controls import (
    API_DEFAULT_TEMPERATURE,
    is_api_default_temperature_override,
)
from .runtime_context import (
    detach_future_from_asyncio_run_shutdown,
    mark_runtime_owned_callback,
    register_transport_receipt_observer_task,
    register_transport_request_task,
    transport_request_descendant_scope,
)
from .utils import (
    estimate_tokens,
    extract_json_candidates,
    extract_json_object,
    format_exception,
    parse_tool_arguments,
    strip_thoughts,
)

_LOGGER = logging.getLogger(__name__)

__all__ = [
    "API_DEFAULT_TEMPERATURE",
    "REQUIRED_PROMPT_CONTEXT_KEY",
    "RequiredPromptContextOverflow",
    "is_api_default_temperature_override",
    "provider_defer_record_from_exception",
    "provider_serving_fingerprint",
]


REQUIRED_PROMPT_CONTEXT_KEY = "_required_prompt_context"


def provider_serving_fingerprint(client: Any) -> str:
    """Return a secret-safe identity for one provider capacity lane.

    Roles and sampling controls are intentionally absent: prove, refine, and
    planner calls using the same endpoint/model/credential/routing lane share
    capacity.  A credential contributes only a one-way digest, so the receipt
    is safe to checkpoint and emit in diagnostics.
    """

    explicit = str(getattr(client, "provider_defer_fingerprint", "") or "").strip()
    if explicit:
        return explicit
    cfg = getattr(client, "cfg", None)
    if cfg is None:
        cfg = client
    base_url = str(
        getattr(cfg, "base_url", "")
        or getattr(client, "base_url", "")
        or ""
    ).strip().rstrip("/").lower()
    model = str(getattr(cfg, "model", "") or "").strip().lower()
    if not base_url and not model:
        return ""

    api_key = str(getattr(cfg, "api_key", "") or "").strip()
    credential_digest = (
        hashlib.sha256(api_key.encode("utf-8", errors="replace")).hexdigest()
        if api_key
        else ""
    )
    revision_fields = {}
    for key in (
        "model_revision",
        "revision",
        "deployment_revision",
        "deployment",
        "model_version",
        "weights_hash",
        "model_hash",
    ):
        value = getattr(cfg, key, None)
        if value not in (None, ""):
            revision_fields[key] = value
    routing_fields = {}
    for key in (
        "provider",
        "providers",
        "provider_order",
        "provider_routing",
        "routing",
        "route",
        "organization",
        "project",
    ):
        value = getattr(cfg, key, None)
        if value not in (None, "", (), [], {}):
            routing_fields[key] = value
    payload = {
        "schema": 1,
        "base_url": base_url,
        "model": model,
        "credential_sha256": credential_digest,
        "revision": revision_fields,
        "routing": routing_fields,
    }
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        default=str,
    )
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def provider_defer_record_from_exception(client: Any, exc: BaseException) -> Dict[str, Any]:
    """Extract a validated scheduler cooldown receipt from an exception."""

    fingerprint = str(
        getattr(exc, "provider_defer_fingerprint", "") or ""
    ).strip()
    if not fingerprint:
        return {}
    expected = provider_serving_fingerprint(client)
    if expected and fingerprint != expected:
        return {}
    try:
        ready_at = float(getattr(exc, "provider_defer_ready_at", 0.0) or 0.0)
    except (TypeError, ValueError, OverflowError):
        ready_at = 0.0
    try:
        retry_after_s = float(
            getattr(exc, "provider_defer_retry_after_s", 0.0) or 0.0
        )
    except (TypeError, ValueError, OverflowError):
        retry_after_s = 0.0
    if not math.isfinite(ready_at) or ready_at <= 0.0:
        return {}
    if not math.isfinite(retry_after_s) or retry_after_s < 0.0:
        retry_after_s = 0.0
    return {
        "provider_defer_fingerprint": fingerprint,
        "provider_defer_ready_at": ready_at,
        "provider_defer_retry_after_s": retry_after_s,
    }


def _gated_chat_entrypoint(method):
    @functools.wraps(method)
    async def wrapped(self, *args, **kwargs):
        operation_started_at = time.time()
        operation_timeout_override_s = kwargs.get("operation_timeout_override_s")
        operation_deadline = self._operation_deadline(
            kwargs.get("deadline"),
            operation_timeout_override_s=operation_timeout_override_s,
        )
        configured_effort = _resolved_reasoning_effort(
            self.cfg,
            kwargs.get("reasoning_effort_override"),
        )
        reasoning_off_requested = bool(
            base_url_matches_provider(self.base_url, "openrouter")
            and str(configured_effort or "").strip().lower() == "none"
            and not _openrouter_reasoning_mandatory_model(
                getattr(self.cfg, "model", "")
            )
        )

        def discovery_needed() -> bool:
            return bool(
                reasoning_off_requested
                and self._reasoning_disable_supported is None
                and not self._reasoning_disable_rejected
            )

        owner_future: Optional[asyncio.Future[None]] = None
        while discovery_needed():
            pending = self._reasoning_disable_negotiation_future
            if pending is not None and not pending.done():
                remaining_s = (
                    None
                    if operation_deadline is None
                    else operation_deadline - time.time()
                )
                try:
                    if remaining_s is None:
                        await asyncio.shield(pending)
                    elif remaining_s > 0.0:
                        await asyncio.wait_for(
                            asyncio.shield(pending),
                            timeout=remaining_s,
                        )
                    else:
                        raise asyncio.TimeoutError
                except asyncio.TimeoutError:
                    raise self._retry_deadline_exception(
                        "LLM operation deadline expired while waiting for "
                        "reasoning capability negotiation",
                        reason="reasoning_capability_negotiation_wait",
                        attempt=0,
                        operation_started_at=operation_started_at,
                        deadline=operation_deadline,
                        request_timeout_s=kwargs.get("request_timeout_override_s"),
                        operation_timeout_override_s=operation_timeout_override_s,
                    ) from None
                continue
            owner_future = asyncio.get_running_loop().create_future()
            self._reasoning_disable_negotiation_future = owner_future
            break

        try:
            async with self._chat_request_gate.hold(
                exclusive=formal_provider_exclusive_requested()
            ):
                call_kwargs = dict(kwargs)
                if operation_deadline is not None:
                    call_kwargs["deadline"] = operation_deadline
                request_policy = call_kwargs.get("max_tokens_override")
                receipt = current_mini_request_envelope_receipt()
                if isinstance(request_policy, MiniRequestEnvelopePolicy):
                    resolved, receipt = await resolve_mini_request_output_tokens(
                        self,
                        request_policy,
                    )
                    call_kwargs["max_tokens_override"] = resolved
                    if (
                        receipt is not None
                        and "reasoning_effort_override" in call_kwargs
                    ):
                        call_kwargs["reasoning_effort_override"] = (
                            receipt.effective_reasoning_effort or None
                        )
                with bind_mini_request_envelope_receipt(receipt):
                    result = await method(self, *args, **call_kwargs)
            if reasoning_off_requested and not self._reasoning_disable_rejected:
                self._reasoning_disable_supported = True
            return result
        finally:
            if owner_future is not None:
                if not owner_future.done():
                    owner_future.set_result(None)
                if self._reasoning_disable_negotiation_future is owner_future:
                    self._reasoning_disable_negotiation_future = None

    return wrapped


def _stop_sequences(cfg: RoleConfig) -> Optional[List[str]]:
    """Return stop sequences appropriate for the model's prompt style."""
    return ["-- PROOF --"]


def _consume_task_exception(task: "asyncio.Future[Any]") -> None:
    """Observe a transport task that may outlive a cancelled request owner."""

    if task.cancelled():
        return
    try:
        task.exception()
    except BaseException:
        pass


class _DetachedTransportTimeout(asyncio.TimeoutError):
    """A timed-out provider request still unwinding outside its owner."""


class _DetachedProviderRequestError(RuntimeError):
    """A dispatched request remains live after its logical owner timed out."""

    # Shared classification inspects this marker without importing models.py.
    llm_detached_provider_request = True


class RequiredPromptContextOverflow(RuntimeError):
    """A lossless prompt unit cannot fit in the provider input budget.

    This is raised before dispatch whenever a message marked with
    :data:`REQUIRED_PROMPT_CONTEXT_KEY` (plus its system/pinned transport
    context) would otherwise have to be dropped or prefix-trimmed.
    """

    llm_required_prompt_context_overflow = True

    def __init__(
        self,
        *,
        required_tokens: int,
        available_tokens: int,
        required_kinds: Tuple[str, ...] = (),
    ) -> None:
        self.required_tokens = max(0, int(required_tokens))
        self.available_tokens = max(0, int(available_tokens))
        self.required_kinds = tuple(required_kinds)
        kinds = ", ".join(self.required_kinds) or "required prompt context"
        super().__init__(
            f"Required prompt context does not fit without loss: {kinds}; "
            f"required_tokens={self.required_tokens} "
            f"available_tokens={self.available_tokens}"
        )


def _error_dict(exc: httpx.HTTPStatusError) -> Optional[Dict[str, Any]]:
    try:
        data = exc.response.json()
    except Exception:
        return None
    if not isinstance(data, dict):
        return None
    err = data.get("error")
    return err if isinstance(err, dict) else None


def _error_message(exc: httpx.HTTPStatusError) -> str:
    err = _error_dict(exc)
    if not isinstance(err, dict):
        return ""
    return str(err.get("message", "")).lower()


def _error_param(exc: httpx.HTTPStatusError) -> str:
    err = _error_dict(exc)
    if not isinstance(err, dict):
        return ""
    param = err.get("param")
    return str(param).strip().lower() if isinstance(param, str) else ""


def _unsupported_parameter(exc: httpx.HTTPStatusError, param: str) -> bool:
    p = str(param or "").strip().lower()
    if not p:
        return False
    message = _error_message(exc)
    exact_param = _error_param(exc) == p
    if exact_param and not message:
        return True
    if not exact_param and p not in message:
        return False
    markers = (
        "unsupported parameter",
        "not supported",
        "invalid parameter",
        "unknown parameter",
        "unrecognized parameter",
        "incompatible with",
        "is not allowed",
    )
    return any(m in message for m in markers)


def _cacheable_unsupported_parameter(
    exc: httpx.HTTPStatusError,
    param: str,
) -> bool:
    """Whether a rejection proves an invariant provider/model capability.

    Value-specific ``invalid``/``incompatible``/``not allowed`` errors may be
    fixed by the next request and must not permanently downgrade the client.
    """

    p = str(param or "").strip().lower()
    message = _error_message(exc)
    if not p or p not in message:
        return False
    return any(
        marker in message
        for marker in (
            "unsupported parameter",
            "not supported",
            "unknown parameter",
            "unrecognized parameter",
        )
    )


def _max_tokens_unsupported(exc: httpx.HTTPStatusError) -> bool:
    """Detect OpenAI-style error for unsupported max_tokens parameter."""
    if _unsupported_parameter(exc, "max_tokens"):
        return True
    message = _error_message(exc)
    return "max_tokens" in message and "max_completion_tokens" in message


class ProviderCapabilityError(RuntimeError):
    """A provider/model cannot satisfy the requested capability combination.

    Deterministic (same payload → same rejection): callers must not retry the
    same leaf; a model chain should skip to a compatible fallback, and with no
    compatible model left the run has a setup error, not a search failure.
    """

    is_provider_capability_conflict = True


class ProviderCapabilityChainExhaustedError(ProviderCapabilityError):
    """Every usable model leaf has a deterministic capability conflict.

    Unlike a single-leaf conflict (non-terminal so a chain can try a
    compatible fallback), exhausting the whole chain on capability conflicts
    is a setup/configuration error: rescheduling the same work cannot
    succeed and must terminate instead of burning orchestration turns.
    """

    is_provider_capability_chain_exhausted = True


def _openai_chat_tools_require_reasoning_effort_none(
    base_url: str,
    model: str,
) -> bool:
    """Whether this family rejects function tools unless effort is 'none'.

    Live falsification (2026-07-29, gpt-5.6-terra): ``/v1/chat/completions``
    returns HTTP 400 "Function tools with reasoning_effort are not supported
    ... use /v1/responses or set reasoning_effort to 'none'" whenever tools
    are present and the effective effort is anything but the explicit string
    ``'none'`` — including when the parameter is omitted (the family default
    is not 'none'). Known-constrained families are pre-negotiated here;
    unknown families self-heal via ``_tools_reasoning_effort_conflict``.
    """

    if not base_url_matches_provider(base_url, "openai"):
        return False
    name = str(model or "").strip().lower()
    return name.startswith("gpt-5.6")


def _openai_chat_stop_unsupported(base_url: str, model: str) -> bool:
    """Whether this family rejects the ``stop`` parameter outright.

    Observed on gpt-5.6 (live, 2026-07-29): "Unsupported parameter: 'stop'
    is not supported with this model." Pre-negotiate instead of paying one
    deterministic 400 before the removed-stop compatibility retry heals it.
    """

    if not base_url_matches_provider(base_url, "openai"):
        return False
    name = str(model or "").strip().lower()
    return name.startswith("gpt-5.6")


def _openai_responses_tools_with_reasoning(
    base_url: str,
    model: str,
    tools: Any,
    reasoning_effort: Any,
) -> bool:
    """Whether to route a tool-enabled call through ``/v1/responses``.

    The constrained gpt-5.6 family rejects function tools with any
    ``reasoning_effort`` other than ``'none'`` on chat completions and points
    at the Responses API. When the caller actually WANTS reasoning with
    tools, Responses is the supported protocol; effort ``'none'`` (and
    unconstrained families) stay on chat completions.
    """

    if not tools:
        return False
    effort = str(reasoning_effort or "").strip().lower()
    if not effort or effort == "none":
        return False
    return _openai_chat_tools_require_reasoning_effort_none(base_url, model)


def _openai_responses_with_reasoning(
    base_url: str,
    reasoning_effort: Any,
) -> bool:
    """Use OpenAI's reasoning-native protocol whenever reasoning is enabled."""

    effort = str(reasoning_effort or "").strip().lower()
    return bool(
        base_url_matches_provider(base_url, "openai")
        and effort
        and effort != "none"
    )


def _chat_tool_to_responses_tool(tool: Any) -> Dict[str, Any]:
    """Flatten a chat-completions function tool to the Responses shape."""

    entry = dict(tool or {}) if isinstance(tool, dict) else {}
    function = (
        dict(entry.get("function") or {})
        if isinstance(entry.get("function"), dict)
        else {}
    )
    flattened: Dict[str, Any] = {
        "type": "function",
        "name": str(function.get("name") or entry.get("name") or ""),
    }
    description = function.get("description") or entry.get("description")
    if description:
        flattened["description"] = str(description)
    parameters = function.get("parameters") or entry.get("parameters")
    if parameters is not None:
        flattened["parameters"] = parameters
    return flattened


def _chat_messages_to_responses_input(
    messages: List[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Translate chat-completions messages into Responses input items.

    Assistant tool calls become ``function_call`` items and tool-role results
    become ``function_call_output`` items so multi-turn tool loops replay
    faithfully.
    """

    items: List[Dict[str, Any]] = []
    for message in messages or ():
        if not isinstance(message, dict):
            continue
        role = str(message.get("role") or "").strip() or "user"
        content = message.get("content")
        text = content if isinstance(content, str) else str(content or "")
        if role == "tool":
            items.append(
                {
                    "type": "function_call_output",
                    "call_id": str(message.get("tool_call_id") or ""),
                    "output": text,
                }
            )
            continue
        if role == "assistant":
            replay_items = [
                {
                    key: value
                    for key, value in item.items()
                    if key != "status"
                }
                for item in message.get("_responses_output_items") or ()
                if isinstance(item, dict)
            ]
            if replay_items:
                # Manual/ZDR continuation must replay the provider's complete
                # output sequence, not reconstructed visible text or private
                # reasoning. ``status`` is response-only and is rejected when
                # echoed as an input item.
                items.extend(replay_items)
                continue
            for reasoning_item in message.get("_responses_reasoning_items") or ():
                if isinstance(reasoning_item, dict):
                    items.append(
                        {
                            key: value
                            for key, value in reasoning_item.items()
                            if key != "status"
                        }
                    )
            if text.strip():
                items.append(
                    {
                        "role": "assistant",
                        "content": [{"type": "output_text", "text": text}],
                    }
                )
            for tool_call in message.get("tool_calls") or ():
                if not isinstance(tool_call, dict):
                    continue
                function = (
                    dict(tool_call.get("function") or {})
                    if isinstance(tool_call.get("function"), dict)
                    else {}
                )
                items.append(
                    {
                        "type": "function_call",
                        "call_id": str(tool_call.get("id") or ""),
                        "name": str(function.get("name") or ""),
                        "arguments": str(function.get("arguments") or "{}"),
                    }
                )
            continue
        items.append(
            {
                "role": role,
                "content": [{"type": "input_text", "text": text}],
            }
        )
    return items


def _responses_payload_to_chat_completion(data: Any) -> Dict[str, Any]:
    """Normalize a Responses API body to the chat-completions shape.

    Downstream plumbing (content extraction, ``extract_tool_calls``, usage
    accounting including reasoning tokens, truncation detection) is written
    against chat completions; normalizing here keeps one consumer path.
    """

    body = dict(data or {}) if isinstance(data, dict) else {}
    text_parts: List[str] = []
    tool_calls: List[Dict[str, Any]] = []
    reasoning_items: List[Dict[str, Any]] = []
    for item in body.get("output") or ():
        if not isinstance(item, dict):
            continue
        kind = str(item.get("type") or "")
        if kind == "message":
            for part in item.get("content") or ():
                if not isinstance(part, dict):
                    continue
                part_kind = str(part.get("type") or "")
                if part_kind in {"output_text", "text"}:
                    text_parts.append(str(part.get("text") or ""))
                elif part_kind == "refusal":
                    # Surface refusals as content so the caller sees WHY the
                    # turn produced no proof instead of an empty reply.
                    text_parts.append(
                        str(part.get("refusal") or part.get("text") or "")
                    )
        elif kind == "function_call":
            tool_calls.append(
                {
                    "id": str(item.get("call_id") or item.get("id") or ""),
                    "type": "function",
                    "function": {
                        "name": str(item.get("name") or ""),
                        "arguments": str(item.get("arguments") or "{}"),
                    },
                }
            )
        elif kind == "reasoning":
            # Opaque provider state is never promoted to visible content, but
            # OpenAI reasoning tool continuations require the item to be
            # replayed alongside the subsequent function_call_output.
            reasoning_items.append(dict(item))
    usage = body.get("usage") if isinstance(body.get("usage"), dict) else {}
    input_tokens = int(usage.get("input_tokens") or 0)
    output_tokens = int(usage.get("output_tokens") or 0)
    input_details = (
        usage.get("input_tokens_details")
        if isinstance(usage.get("input_tokens_details"), dict)
        else {}
    )
    output_details = (
        usage.get("output_tokens_details")
        if isinstance(usage.get("output_tokens_details"), dict)
        else {}
    )
    status = str(body.get("status") or "")
    incomplete_reason = ""
    if isinstance(body.get("incomplete_details"), dict):
        incomplete_reason = str(
            body["incomplete_details"].get("reason") or ""
        )
    if tool_calls:
        finish_reason = "tool_calls"
    elif status == "incomplete" and incomplete_reason == "max_output_tokens":
        finish_reason = "length"
    elif status == "incomplete" and incomplete_reason == "content_filter":
        finish_reason = "content_filter"
    else:
        finish_reason = "stop"
    message: Dict[str, Any] = {
        "role": "assistant",
        "content": "\n".join(part for part in text_parts if part),
    }
    if tool_calls:
        message["tool_calls"] = tool_calls
    if reasoning_items:
        message["_responses_reasoning_items"] = reasoning_items
    output_items = [
        dict(item)
        for item in body.get("output") or ()
        if isinstance(item, dict)
    ]
    if output_items:
        # Retain the complete opaque provider turn for manual/ZDR
        # continuation. Consumers must never promote these items to visible
        # content; they are replayed verbatim (minus response-only status).
        message["_responses_output_items"] = output_items
    return {
        "id": str(body.get("id") or ""),
        "object": "chat.completion",
        "model": str(body.get("model") or ""),
        "choices": [
            {
                "index": 0,
                "message": message,
                "finish_reason": finish_reason,
            }
        ],
        "usage": {
            "prompt_tokens": input_tokens,
            "completion_tokens": output_tokens,
            "total_tokens": int(
                usage.get("total_tokens") or (input_tokens + output_tokens)
            ),
            "prompt_tokens_details": {
                "cached_tokens": int(input_details.get("cached_tokens") or 0),
            },
            "completion_tokens_details": {
                "reasoning_tokens": int(
                    output_details.get("reasoning_tokens") or 0
                ),
            },
        },
    }


def _tools_reasoning_effort_conflict(exc: httpx.HTTPStatusError) -> bool:
    """Detect the provider's tools × reasoning-effort conflict rejection."""

    message = _error_message(exc)
    if "reasoning_effort" not in message or "tool" not in message:
        return False
    return (
        "set reasoning_effort to 'none'" in message
        or "not supported" in message
    )


def _reasoning_disable_rejected(exc: httpx.HTTPStatusError) -> bool:
    """Whether a routed endpoint says reasoning cannot be disabled."""

    if int(getattr(getattr(exc, "response", None), "status_code", 0) or 0) != 400:
        return False
    message = _error_message(exc)
    return "reasoning is mandatory" in message and "cannot be disabled" in message


def _max_completion_tokens_unsupported(exc: httpx.HTTPStatusError) -> bool:
    """Detect OpenAI-style error for unsupported max_completion_tokens parameter."""
    if _unsupported_parameter(exc, "max_completion_tokens"):
        return True
    message = _error_message(exc)
    return "max_completion_tokens" in message and "max_tokens" in message


def _payload_token_limit(payload: Dict[str, Any]) -> Tuple[str, Optional[int]]:
    for key in ("max_tokens", "max_completion_tokens"):
        if key not in payload:
            continue
        try:
            value = int(payload.get(key) or 0)
        except Exception:
            value = 0
        if value > 0:
            return key, value
    return "", None


def _openrouter_affordable_max_tokens(exc: httpx.HTTPStatusError) -> Optional[int]:
    """Return OpenRouter's affordable output cap from a 402, when present."""

    try:
        status_code = int(getattr(exc.response, "status_code", 0) or 0)
    except Exception:
        status_code = 0
    if status_code != 402:
        return None
    message = _error_message(exc)
    marker = "can only afford"
    if marker not in message:
        return None
    tail = message.split(marker, 1)[1].strip()
    digits = []
    for ch in tail:
        if ch.isdigit():
            digits.append(ch)
            continue
        if digits:
            break
    if not digits:
        return None
    try:
        affordable = int("".join(digits))
    except Exception:
        return None
    return affordable if affordable > 0 else None


def _stop_unsupported(exc: httpx.HTTPStatusError) -> bool:
    """Detect OpenAI-style error for unsupported stop parameter."""
    return _unsupported_parameter(exc, "stop")


def normalize_tool_calls(calls: Any) -> List[Dict[str, Any]]:
    """Return only well-formed tool-call dicts from a provider payload."""
    if not isinstance(calls, list):
        return []
    normalized: List[Dict[str, Any]] = []
    for call in calls:
        if not isinstance(call, dict):
            continue
        fn = call.get("function")
        if not isinstance(fn, dict):
            continue
        name = str(fn.get("name", "") or "").strip()
        if not name:
            continue
        arguments = fn.get("arguments", None) if "arguments" in fn else None
        normalized.append(
            {
                "id": str(call.get("id", "") or ""),
                "type": str(call.get("type", "function") or "function"),
                "function": {
                    "name": name,
                    "arguments": None if arguments is None else str(arguments),
                },
            }
        )
    return normalized


def _context_exceeded(exc: httpx.HTTPStatusError) -> bool:
    """Detect context/prompt length exceeded errors (llama.cpp, vLLM, etc)."""
    message = _error_message(exc)
    if not message:
        try:
            data = exc.response.json()
        except Exception:
            return False
        if isinstance(data, dict):
            message = str(data.get("message", "")).lower()
    # Common patterns: llama.cpp "context size has been exceeded"
    # vLLM "prompt is too long" / "exceeds max model length"
    return any(
        pattern in message
        for pattern in [
            "context size has been exceeded",
            "context length exceeded",
            "prompt is too long",
            "prompt tokens limit exceeded",
            "exceeds max model length",
            "exceeds the model's context",
            "maximum context length",
            "too many tokens",
            "context window",
            "reduce the length",
        ]
    )


def _json_body_parse_error(exc: httpx.HTTPStatusError) -> bool:
    """Detect provider errors that claim the JSON request body was malformed."""
    if exc.response.status_code != 400:
        return False
    message = _error_message(exc)
    return (
        "could not parse the json body of your request" in message
        or "request body was not valid json" in message
        or "request body is not valid json" in message
        or "request body must be valid json" in message
    )


def _replace_invalid_surrogates(text: str) -> tuple[str, int]:
    """Replace lone UTF-16 surrogate codepoints with U+FFFD."""
    if not text:
        return text, 0
    out: List[str] = []
    replaced = 0
    for ch in text:
        code = ord(ch)
        if 0xD800 <= code <= 0xDFFF:
            out.append("\ufffd")
            replaced += 1
        else:
            out.append(ch)
    if replaced == 0:
        return text, 0
    return "".join(out), replaced


def _normalize_request_json(value: Any, *, path: str = "$") -> tuple[Any, int]:
    """Normalize request payloads into strict JSON-compatible structures."""
    if value is None or isinstance(value, (bool, int)):
        return value, 0
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError(f"{path}: non-finite float {value!r}")
        return value, 0
    if isinstance(value, str):
        return _replace_invalid_surrogates(value)
    if isinstance(value, (list, tuple)):
        items: List[Any] = []
        replaced = 0
        for i, item in enumerate(value):
            normalized, item_replaced = _normalize_request_json(
                item, path=f"{path}[{i}]"
            )
            items.append(normalized)
            replaced += item_replaced
        return items, replaced
    if isinstance(value, dict):
        normalized_dict: Dict[str, Any] = {}
        replaced = 0
        for key, item in value.items():
            if not isinstance(key, str):
                raise TypeError(
                    f"{path}: JSON object keys must be strings, got {type(key).__name__}"
                )
            normalized, item_replaced = _normalize_request_json(
                item, path=f"{path}.{key}"
            )
            normalized_dict[key] = normalized
            replaced += item_replaced
        return normalized_dict, replaced
    raise TypeError(
        f"{path}: value of type {type(value).__name__} is not JSON serializable"
    )


_REQUEST_MESSAGE_KEYS = {
    "role",
    "content",
    "name",
    "tool_call_id",
    "tool_calls",
    "function_call",
}


def _request_safe_tool_call_id(value: Any) -> str:
    raw = str(value or "")
    if not raw:
        return ""
    digest = hashlib.sha256(raw.encode("utf-8", errors="replace")).hexdigest()[:16]
    return f"call_{digest}"


def _request_safe_tool_arguments(arguments: Any) -> str:
    raw = "" if arguments is None else str(arguments)
    parsed, parse_error = parse_tool_arguments(arguments)
    if parse_error:
        # Redact JSON string VALUES, not the whole literal set: keeping the
        # schema-derived keys is what makes a malformed call diagnosable at
        # all (a truncated payload looks nothing like a wrong-shaped one).
        safe_raw = prompt_safe_malformed_tool_arguments(raw, limit=1600)
        return json.dumps(
            {"__malformed_arguments__": safe_raw},
            ensure_ascii=False,
            allow_nan=False,
        )
    return json.dumps(
        _request_safe_tool_argument_value(parsed),
        ensure_ascii=False,
        allow_nan=False,
    )


def _request_safe_tool_argument_value(value: Any) -> Any:
    if isinstance(value, str):
        return _prompt_safe_inline_text(
            value,
            limit=1200,
            redact_solution_refs=True,
        )
    if isinstance(value, list):
        return [_request_safe_tool_argument_value(item) for item in value[:20]]
    if isinstance(value, dict):
        return {
            _prompt_safe_inline_text(
                str(key),
                limit=120,
                redact_solution_refs=True,
            ): _request_safe_tool_argument_value(item)
            for key, item in list(value.items())[:40]
        }
    return value


def _request_safe_tool_calls(calls: Any) -> List[Dict[str, Any]]:
    if not isinstance(calls, list):
        return []
    safe_calls: List[Dict[str, Any]] = []
    for call in calls:
        if not isinstance(call, dict):
            continue
        clean_call = dict(call)
        function = clean_call.get("function")
        if not isinstance(function, dict):
            continue
        name = str(function.get("name", "") or "").strip()
        raw_call_id = str(clean_call.get("id", "") or "")
        if not name or not raw_call_id:
            continue
        call_id = _request_safe_tool_call_id(raw_call_id)
        clean_function = dict(function)
        clean_function["name"] = name
        argument_value = (
            clean_function.get("arguments", "")
            if "arguments" in clean_function
            else None
        )
        clean_function["arguments"] = _request_safe_tool_arguments(
            argument_value
        )
        clean_call["id"] = call_id
        clean_call["type"] = str(clean_call.get("type", "function") or "function")
        clean_call["function"] = clean_function
        safe_calls.append(clean_call)
    return safe_calls


def _deepseek_v4_model(model: str) -> bool:
    # OpenRouter namespaces models as ``provider/model``.  Provider-specific
    # capability checks must inspect the leaf name, otherwise
    # ``deepseek/deepseek-v4-pro`` is incorrectly treated as an unrelated
    # generic OpenRouter model.
    name = str(model or "").strip().lower().rsplit("/", 1)[-1]
    return name.startswith("deepseek-v4-")


def _gpt_oss_120b_model(model: str) -> bool:
    name = str(model or "").strip().lower().rsplit("/", 1)[-1]
    return name.startswith("gpt-oss-120b")


def _openrouter_reasoning_mandatory_model(model: str) -> bool:
    """Known routed endpoints that reject explicit reasoning disablement."""

    name = str(model or "").strip().lower().rsplit("/", 1)[-1]
    # Verified live against OpenRouter: qwen3.8-max (2026-08-03) and
    # gpt-oss-120b (2026-08-16) return HTTP 400 "Reasoning is mandatory for
    # this endpoint" for reasoning.enabled=false.
    return name.startswith("qwen3.8-max") or _gpt_oss_120b_model(model)


def _resolved_reasoning_effort(
    cfg: RoleConfig,
    reasoning_effort_override: Optional[str],
) -> Optional[str]:
    """Resolve per-call effort without overriding an explicit role-level off."""

    configured = getattr(cfg, "reasoning_effort", None)
    if str(configured or "").strip().lower() == "none":
        return str(configured).strip()
    # DeepSeek V4 defaults to thinking. ``thinking_enabled=False`` is only an
    # off switch when the operator explicitly required that control; treating
    # the dataclass default as an opt-out disabled independent planner clients.
    if (
        base_url_matches_provider(getattr(cfg, "base_url", ""), "deepseek")
        and _deepseek_v4_model(getattr(cfg, "model", ""))
        and not bool(getattr(cfg, "thinking_enabled", False))
        and bool(getattr(cfg, "reasoning_control_required", False))
    ):
        return "none"
    if reasoning_effort_override is not None:
        return reasoning_effort_override
    return configured


def _append_reasoning_chunk(parts: List[str], value: str) -> None:
    """Append one chunk while deduplicating either ordering of prefix forms."""

    text = str(value or "").strip()
    if not text:
        return

    def subsumes(container: str, chunk: str) -> bool:
        return bool(
            container == chunk
            # Gateways can expose one field as a cumulative stream prefix and
            # the other as its latest full snapshot, with no newline exactly
            # at the overlap boundary (for example ``abc`` / ``abcdef``).
            or container.startswith(chunk)
            or container.endswith(chunk)
            or ("\n" + chunk + "\n") in container
        )

    for previous in parts:
        if subsumes(previous, text):
            return
    subsumed_indexes = [
        index for index, previous in enumerate(parts) if subsumes(text, previous)
    ]
    if subsumed_indexes:
        insert_at = subsumed_indexes[0]
        parts[:] = [
            previous
            for index, previous in enumerate(parts)
            if index not in set(subsumed_indexes)
        ]
        parts.insert(insert_at, text)
        return
    parts.append(text)


def _reasoning_value_chunks(value: Any) -> List[str]:
    """Normalize provider reasoning telemetry without promoting it to content."""

    parts: List[str] = []
    if isinstance(value, str):
        _append_reasoning_chunk(parts, value)
    elif isinstance(value, list):
        for item in value:
            for chunk in _reasoning_value_chunks(item):
                _append_reasoning_chunk(parts, chunk)
    elif isinstance(value, dict):
        for key in ("text", "content", "summary"):
            for chunk in _reasoning_value_chunks(value.get(key)):
                _append_reasoning_chunk(parts, chunk)
    return parts


def message_reasoning_text(message: Any) -> str:
    """Return normalized reasoning from either common response field.

    DeepSeek-compatible APIs commonly emit ``reasoning_content`` while
    OpenRouter-native responses may emit ``reasoning``.  Treat both as
    private transport telemetry; callers decide whether it is useful for
    structured recovery, and ordinary proof extraction never uses it as the
    answer.
    """

    if not isinstance(message, dict):
        return ""
    parts: List[str] = []
    for key in ("reasoning_content", "reasoning"):
        for chunk in _reasoning_value_chunks(message.get(key)):
            _append_reasoning_chunk(parts, chunk)
    return "\n".join(parts)


def response_reasoning_text(payload: Any) -> str:
    """Return normalized first-choice reasoning telemetry from an API payload."""

    if not isinstance(payload, dict):
        return ""
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices:
        return ""
    first = choices[0]
    if not isinstance(first, dict):
        return ""
    return message_reasoning_text(first.get("message"))


def response_reasoning_items(payload: Any) -> List[Dict[str, Any]]:
    """Return opaque OpenAI Responses reasoning items for continuation."""

    if not isinstance(payload, dict):
        return []
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices:
        return []
    first = choices[0]
    message = first.get("message") if isinstance(first, dict) else None
    if not isinstance(message, dict):
        return []
    return [
        dict(item)
        for item in message.get("_responses_reasoning_items") or ()
        if isinstance(item, dict)
    ]


def response_output_items(payload: Any) -> List[Dict[str, Any]]:
    """Return the complete opaque OpenAI Responses output turn for replay."""

    if not isinstance(payload, dict):
        return []
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices:
        return []
    first = choices[0]
    message = first.get("message") if isinstance(first, dict) else None
    if not isinstance(message, dict):
        return []
    return [
        dict(item)
        for item in message.get("_responses_output_items") or ()
        if isinstance(item, dict)
    ]


def _sanitize_request_messages(
    messages: List[Any],
    *,
    preserve_reasoning_content: bool = False,
    preserve_responses_reasoning_items: bool = False,
    _retain_required_receipts: bool = False,
) -> List[Any]:
    """Return request-safe chat messages.

    Provider response-only fields should not leak back into later requests
    unless the target API explicitly requires them. DeepSeek thinking-mode tool
    calls are the exception: their API requires assistant ``reasoning_content``
    to be replayed along with ``tool_calls``.
    """
    request_keys = set(_REQUEST_MESSAGE_KEYS)
    if preserve_reasoning_content:
        request_keys.add("reasoning_content")
    if preserve_responses_reasoning_items:
        request_keys.add("_responses_reasoning_items")
        request_keys.add("_responses_output_items")
    receipt_key = "_mini_required_prompt_transport_receipt"
    expected_receipts: List[int] = []
    sanitized: List[Any] = []
    for message in messages:
        if not isinstance(message, dict):
            sanitized.append(message)
            continue
        clean = {
            key: value
            for key, value in message.items()
            if key in request_keys
        }
        if _message_has_required_prompt_context(message):
            receipt = len(expected_receipts)
            expected_receipts.append(receipt)
            clean[receipt_key] = receipt
        if clean.get("role") == "tool" and "tool_call_id" in clean:
            clean["tool_call_id"] = _request_safe_tool_call_id(
                clean.get("tool_call_id", "")
            )
        if "tool_calls" in clean:
            safe_tool_calls = _request_safe_tool_calls(clean.get("tool_calls"))
            if safe_tool_calls:
                clean["tool_calls"] = safe_tool_calls
            else:
                clean.pop("tool_calls", None)
        if (
            clean.get("role") == "assistant"
            and "tool_calls" in clean
            and "content" not in clean
        ):
            clean["content"] = ""
        sanitized.append(clean)
    repaired = _repair_tool_transcript(sanitized)
    actual_receipts = [
        int(message[receipt_key])
        for message in repaired
        if isinstance(message, dict) and receipt_key in message
    ]
    if actual_receipts != expected_receipts:
        raise RequiredPromptContextOverflow(
            required_tokens=_messages_tokens(
                [
                    message
                    for message in messages
                    if _message_has_required_prompt_context(message)
                ]
            ),
            available_tokens=0,
            required_kinds=tuple(
                _required_prompt_kind(message)
                for message in messages
                if _message_has_required_prompt_context(message)
            ),
        )
    if _retain_required_receipts:
        return repaired
    for message in repaired:
        if isinstance(message, dict):
            message.pop(receipt_key, None)
    return repaired


def _tool_call_ids(message: Dict[str, Any]) -> List[str]:
    ids: List[str] = []
    for call in normalize_tool_calls(message.get("tool_calls")):
        call_id = str(call.get("id", "") or "")
        if call_id:
            ids.append(call_id)
    return ids


def _message_has_payload_without_tool_calls(message: Dict[str, Any]) -> bool:
    content = message.get("content")
    if isinstance(content, str):
        if content.strip():
            return True
    elif content is not None:
        return True
    return bool(message_reasoning_text(message).strip())


def _unique_request_tool_call_id(
    call_id: str,
    *,
    used_ids: set[str],
    fallback: str,
) -> str:
    base = str(call_id or "").strip() or fallback
    candidate = base
    suffix = 2
    while not candidate or candidate in used_ids:
        candidate = f"{base or fallback}_{suffix}"
        suffix += 1
    used_ids.add(candidate)
    return candidate


def _repair_tool_transcript(messages: List[Any]) -> List[Any]:
    """Remove incomplete tool-call exchanges from outbound chat history."""

    repaired: List[Any] = []
    i = 0
    while i < len(messages):
        message = messages[i]
        if not isinstance(message, dict):
            repaired.append(message)
            i += 1
            continue
        role = message.get("role")
        if role == "tool":
            i += 1
            continue
        if role == "assistant":
            tool_calls = normalize_tool_calls(message.get("tool_calls"))
            pending_ids = [
                str(call.get("id", "") or "")
                for call in tool_calls
                if str(call.get("id", "") or "")
            ]
            if pending_ids:
                used_ids: set[str] = set()
                remapped_ids: List[tuple[str, str]] = []
                repaired_calls: List[Dict[str, Any]] = []
                for call_index, call in enumerate(tool_calls):
                    original_id = str(call.get("id", "") or "")
                    repaired_id = _unique_request_tool_call_id(
                        original_id,
                        used_ids=used_ids,
                        fallback=f"call_{i}_{call_index + 1}",
                    )
                    clean_call = dict(call)
                    clean_call["id"] = repaired_id
                    repaired_calls.append(clean_call)
                    remapped_ids.append((original_id, repaired_id))
                tool_messages: List[Dict[str, Any]] = []
                j = i + 1
                while j < len(messages):
                    next_message = messages[j]
                    if not isinstance(next_message, dict) or next_message.get("role") != "tool":
                        break
                    tool_messages.append(next_message)
                    j += 1
                assigned_tool_ids: Dict[int, str] = {}
                consumed_tool_indices: set[int] = set()
                for original_id, repaired_id in remapped_ids:
                    for tool_index, tool_message in enumerate(tool_messages):
                        if tool_index in consumed_tool_indices:
                            continue
                        if str(tool_message.get("tool_call_id", "") or "") != original_id:
                            continue
                        consumed_tool_indices.add(tool_index)
                        assigned_tool_ids[tool_index] = repaired_id
                        break
                if len(assigned_tool_ids) == len(remapped_ids):
                    repaired_message = dict(message)
                    repaired_message["tool_calls"] = repaired_calls
                    repaired.append(repaired_message)
                    for tool_index in sorted(assigned_tool_ids):
                        tool_message = dict(tool_messages[tool_index])
                        tool_message["tool_call_id"] = assigned_tool_ids[tool_index]
                        repaired.append(tool_message)
                else:
                    stripped = dict(message)
                    stripped.pop("tool_calls", None)
                    stripped.pop("function_call", None)
                    if _message_has_payload_without_tool_calls(stripped):
                        repaired.append(stripped)
                i = j
                continue
        repaired.append(message)
        i += 1
    return repaired


def _drop_orphan_tool_results(messages: List[Any]) -> List[Any]:
    """Drop tool result messages whose assistant tool call is absent."""

    pending_counts: Dict[str, int] = {}
    repaired: List[Any] = []
    for message in messages:
        if not isinstance(message, dict):
            repaired.append(message)
            continue
        if message.get("role") == "assistant":
            for tool_call_id in _tool_call_ids(message):
                pending_counts[tool_call_id] = int(
                    pending_counts.get(tool_call_id, 0) or 0
                ) + 1
            repaired.append(message)
            continue
        if message.get("role") == "tool":
            tool_call_id = str(message.get("tool_call_id", "") or "")
            if tool_call_id and int(pending_counts.get(tool_call_id, 0) or 0) > 0:
                repaired.append(message)
                pending_counts[tool_call_id] = int(pending_counts[tool_call_id]) - 1
            continue
        repaired.append(message)
    return repaired


def _payload_summary(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Compact, non-sensitive request summary for diagnostics."""
    messages = payload.get("messages")
    roles: List[str] = []
    msg_count = 0
    if isinstance(messages, list):
        msg_count = len(messages)
        for message in messages[:8]:
            if isinstance(message, dict):
                roles.append(str(message.get("role", "")))
            else:
                roles.append(type(message).__name__)
    summary: Dict[str, Any] = {
        "model": str(payload.get("model", "")),
        "keys": sorted(str(k) for k in payload.keys()),
        "message_count": int(msg_count),
        "message_roles": roles,
    }
    for key in (
        "temperature",
        "top_p",
        "max_tokens",
        "max_completion_tokens",
        "n",
        "reasoning_effort",
        "reasoning",
        "response_format",
        "thinking",
        "stop",
    ):
        if key in payload:
            summary[key] = payload.get(key)
    return summary


def _supports_sampling_controls(
    *,
    base_url: str,
    model: str,
    reasoning_effort: Optional[str],
    thinking_enabled: bool = False,
) -> bool:
    """Whether sending temperature/top_p is safe for this target model/API.

    OpenAI GPT-5 family has model-specific constraints for sampling controls.
    DeepSeek-Reasoner ignores temperature/top_p entirely — omit them for
    API correctness.  DeepSeek thinking mode also disables sampling controls.
    """
    # DeepSeek thinking mode ignores temperature/top_p (hardcoded sampling).
    if thinking_enabled:
        return False
    if not base_url_matches_provider(base_url, "openai"):
        # DeepSeek-Reasoner (and similar reasoning models) do not support
        # sampling controls; sending them is harmless but incorrect.
        model_lower = str(model or "").strip().lower()
        if "reasoner" in model_lower:
            return False
        return True
    name = str(model or "").strip().lower()
    if not name.startswith("gpt-5"):
        return True
    # GPT-5.1 / 5.2: temperature/top_p supported when reasoning effort is "none"
    # (or omitted, where default is currently "none" for these families).
    if name.startswith("gpt-5.1") or name.startswith("gpt-5.2"):
        effort = str(reasoning_effort or "").strip().lower()
        return effort in {"", "none"}
    # Older GPT-5 families (e.g., gpt-5, gpt-5-mini, gpt-5-nano) can reject
    # these controls depending on reasoning mode; default safe behavior is omit.
    return False


_CTX_MIN_PROMPT_TOKENS = 256
_CTX_OVERFLOW_SHRINK = 0.55

# When the operation deadline is derived from the per-request ``timeout_s``
# fallback (no explicit ``operation_timeout_s``), multiply by this factor so
# the operation window can absorb one full hung attempt and still run at
# least one retry with a fresh sub-timeout. See ``_operation_deadline``.
_OPERATION_DEADLINE_RETRY_HEADROOM = 2.0

# The lease above reserves whole request windows, but the transport backoff
# sleep and the setup time before the first dispatch are overhead outside
# that reservation. Requiring a *full* window after them made a 2x lease refuse
# every retry after a full first-attempt timeout (the remainder was always
# ``window - delay``), which is precisely the zero-retry failure the headroom
# exists to prevent. A retry that keeps this fraction of one request window
# after the sleep is not doomed; anything less is.
_TRANSPORT_RETRY_MIN_WINDOW_FRACTION = 0.8
# A fixed one-second backoff can consume an entire short request window. Keep
# timeout retries below half of the admission margin so a 2x operation lease
# retains both a useful retry window and scheduling/setup headroom.
_TRANSPORT_RETRY_MAX_BACKOFF_WINDOW_FRACTION = 0.1


def _transport_retry_window_admissible(
    *,
    retry_window_after_backoff_s: Optional[float],
    configured_request_window_s: Optional[float],
) -> bool:
    """Whether a transport-timeout retry still owns a usable request window.

    ``retry_window_after_backoff_s`` is the lease remaining once the backoff
    sleep has been subtracted. The retry is admitted when that covers at least
    ``_TRANSPORT_RETRY_MIN_WINDOW_FRACTION`` of one configured request window,
    so the reservation made by ``_OPERATION_DEADLINE_RETRY_HEADROOM`` survives
    the sleep and setup jitter at any window scale, while a genuinely partial
    window is still refused before a doomed retry starts. Without a deadline
    or a configured window there is nothing to reserve and the retry is
    admitted.
    """

    if retry_window_after_backoff_s is None or configured_request_window_s is None:
        return True
    required_window_s = (
        float(configured_request_window_s) * _TRANSPORT_RETRY_MIN_WINDOW_FRACTION
    )
    return float(retry_window_after_backoff_s) >= required_window_s


def _prompt_budget_for_cfg(
    cfg: RoleConfig,
    *,
    max_tokens_override: Optional[int] = None,
) -> Optional[int]:
    ctx = getattr(cfg, "context_window", None)
    if ctx is None:
        return None
    try:
        ctx_i = int(ctx)
    except Exception:
        return None
    if ctx_i <= 0:
        return None
    max_out = max(
        0,
        int(
            max_tokens_override
            if max_tokens_override is not None
            else getattr(cfg, "max_tokens", 0) or 0
        ),
    )
    budget = ctx_i - max_out
    if budget < _CTX_MIN_PROMPT_TOKENS:
        return None
    return budget


def _messages_tokens(
    messages: List[Dict[str, Any]], *, model: Optional[str] = None
) -> int:
    total = 0
    for m in messages:
        total += _message_tokens(m, model=model)
    return total


def _structured_tokens(value: Any, *, model: Optional[str] = None) -> int:
    if value in (None, "", [], {}):
        return 0
    try:
        normalized, _replaced = _normalize_request_json(value)
        text = json.dumps(
            normalized,
            ensure_ascii=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    except Exception:
        text = str(value)
    return estimate_tokens(text, model=model)


def _message_tokens(message: Any, *, model: Optional[str] = None) -> int:
    if not isinstance(message, dict):
        return _structured_tokens(message, model=model)
    responses_output = message.get("_responses_output_items")
    complete_responses_replay = bool(
        str(message.get("role") or "") == "assistant"
        and isinstance(responses_output, list)
        and responses_output
    )
    content_total = 0
    content = message.get("content")
    if isinstance(content, str):
        content_total = estimate_tokens(content, model=model) if content.strip() else 0
    elif content is not None:
        content_total = _structured_tokens(content, model=model)
    common_extras: Dict[str, Any] = {}
    for key in ("role", "name", "tool_call_id"):
        value = message.get(key)
        if value not in (None, "", [], {}):
            common_extras[key] = value
    common_total = _structured_tokens(common_extras, model=model)
    visible_extras: Dict[str, Any] = {}
    for key in (
        "tool_calls",
        "function_call",
        "reasoning_content",
        "reasoning",
        "_responses_reasoning_items",
    ):
        value = message.get(key)
        if value not in (None, "", [], {}):
            visible_extras[key] = value
    visible_total = (
        common_total
        + content_total
        + _structured_tokens(visible_extras, model=model)
    )
    if not complete_responses_replay:
        return visible_total
    opaque_total = common_total + _structured_tokens(
        {"_responses_output_items": responses_output},
        model=model,
    )
    # Chat-compatible providers consume the visible reconstruction while the
    # Responses API gives complete output replay precedence. Budget for the
    # larger transport without counting both mutually exclusive forms.
    return max(visible_total, opaque_total)


def _tools_tokens(
    tools: Optional[List[Dict[str, Any]]], *, model: Optional[str] = None
) -> int:
    return _structured_tokens(tools, model=model)


def _message_budget_after_tools(
    budget: Optional[int],
    tools: Optional[List[Dict[str, Any]]],
    *,
    model: Optional[str] = None,
) -> Optional[int]:
    if budget is None:
        return None
    return max(0, int(budget) - _tools_tokens(tools, model=model))


def _tools_consume_prompt_budget(
    budget: Optional[int],
    tools: Optional[List[Dict[str, Any]]],
    *,
    model: Optional[str] = None,
) -> bool:
    if budget is None or not tools:
        return False
    minimum_message_budget = max(64, min(256, int(budget) // 3))
    return _tools_tokens(tools, model=model) >= max(0, int(budget) - minimum_message_budget)


def _trim_text_prefix_to_token_budget(
    text: str, budget: int, *, model: Optional[str] = None
) -> str:
    if not text or budget <= 0:
        return ""
    if estimate_tokens(text, model=model) <= budget:
        return text
    lo, hi = 0, len(text)
    while lo < hi:
        mid = (lo + hi) // 2
        if estimate_tokens(text[:mid], model=model) <= budget:
            lo = mid + 1
        else:
            hi = mid
    cut = max(0, lo - 1)
    return text[:cut].rstrip()


def _fit_text_to_token_budget(
    text: str,
    budget: int,
    *,
    model: Optional[str] = None,
) -> str:
    """Enforce a token budget after tokenizer-dependent prefix trimming."""

    if not text or budget <= 0:
        return ""
    fitted = str(text)
    while fitted and estimate_tokens(fitted, model=model) > budget:
        fitted = fitted[:-1].rstrip()
    return fitted


def _trim_text_to_token_budget(
    text: str, budget: int, *, model: Optional[str] = None
) -> str:
    trimmed = _trim_text_prefix_to_token_budget(text, budget, model=model)
    marker = "\n...(truncated)..."
    if trimmed and trimmed != text:
        candidate = trimmed + marker
        if estimate_tokens(candidate, model=model) <= budget:
            return candidate
        marker_tokens = estimate_tokens(marker, model=model)
        body_budget = max(0, int(budget) - marker_tokens)
        if body_budget <= 0:
            return _fit_text_to_token_budget(trimmed, budget, model=model)
        body = _trim_text_prefix_to_token_budget(trimmed, body_budget, model=model)
        candidate = (body + marker) if body else marker.strip()
        while body and estimate_tokens(candidate, model=model) > budget:
            body = body[:-1].rstrip()
            candidate = body + marker
        if estimate_tokens(candidate, model=model) <= budget:
            return candidate
        return _fit_text_to_token_budget(marker.strip(), budget, model=model)
    return _fit_text_to_token_budget(trimmed, budget, model=model)


def _extract_initial_anchor_core(text: str) -> str:
    """Return the most identity-bearing slice of the first user prompt."""

    raw = str(text or "").strip()
    if not raw:
        return ""
    marker = "Lean signature:"
    marker_idx = raw.find(marker)
    if marker_idx >= 0:
        tail = raw[marker_idx:]
        # The signature is followed by preamble/instructions; keep the theorem
        # contract, not imports that can crowd it out under emergency trimming.
        for boundary in (
            "\n\nLean preamble",
            "\n\nBuild the root",
            "\n\nSolve the problem",
            "\n\nImportant:",
        ):
            cut = tail.find(boundary)
            if cut > 0:
                tail = tail[:cut]
                break
        problem_prefix = raw[:marker_idx].strip()
        if problem_prefix:
            problem_prefix = _trim_text_to_token_budget(
                problem_prefix,
                96,
                model=None,
            ).strip()
            return f"{problem_prefix}\n\n{tail.strip()}".strip()
        return tail.strip()
    theorem_idx = raw.find("theorem ")
    if theorem_idx < 0:
        theorem_idx = raw.find("THEOREM ")
    if theorem_idx >= 0:
        prefix = raw[:theorem_idx].strip()
        theorem_tail = raw[theorem_idx:].strip()
        first_block = theorem_tail.split("\n\n", 1)[0].strip()
        if prefix:
            prefix = _trim_text_to_token_budget(prefix, 48, model=None).strip()
            return f"{prefix}\n\n{first_block}".strip()
        return first_block
    return raw


def _trim_initial_user_anchor_to_budget(
    text: str, budget: int, *, model: Optional[str] = None
) -> str:
    """Trim the initial user prompt without erasing theorem identity."""

    raw = str(text or "")
    core = _extract_initial_anchor_core(raw)
    source = core or raw.strip()
    if not source:
        return ""
    if budget <= 0:
        budget = 1
    if estimate_tokens(source, model=model) <= budget:
        return source
    marker_idx = source.find("Lean signature:")
    if marker_idx > 0:
        signature_source = source[marker_idx:].strip()
        if estimate_tokens(signature_source, model=model) <= budget:
            return signature_source
        signature_trimmed = _trim_text_to_token_budget(
            signature_source,
            budget,
            model=model,
        ).strip()
        if signature_trimmed:
            return signature_trimmed
    trimmed = _trim_text_to_token_budget(source, budget, model=model).strip()
    if trimmed:
        # A tokenizer-sized budget can be smaller than the theorem marker
        # itself once role framing is counted. Preserve a recognizable
        # identity atom rather than a meaningless prefix such as ``THEOR``;
        # this is the documented pathological-budget exception below.
        if source.startswith("THEOREM") and "THEOREM" not in trimmed:
            return "THEOREM"
        if source.startswith("theorem ") and "theorem" not in trimmed:
            return "theorem"
        return trimmed
    # Last-resort nonempty anchor. This can exceed a pathological budget of
    # zero/one token, but preserving the theorem identity is more valuable than
    # returning an empty first user message after overflow recovery.
    for line in source.splitlines():
        stripped = line.strip()
        if stripped:
            return stripped[:240]
    return source[:240].strip()


def _reserve_initial_user_anchor(
    messages: List[Dict[str, str]],
    budget: int,
    *,
    model: Optional[str] = None,
) -> List[Dict[str, str]]:
    """Reserve prompt budget for a nonempty theorem/signature anchor."""

    first_user = _initial_user_index(messages)
    if first_user is None or budget <= 0:
        return messages
    trimmed = [dict(m) if isinstance(m, dict) else m for m in messages]
    anchor_content = str(trimmed[first_user].get("content", "") or "")
    if not anchor_content.strip():
        return trimmed
    anchor_budget = max(1, min(256, max(32, int(budget) // 3)))
    if int(budget) < 32:
        anchor_budget = max(1, int(budget) // 2 or 1)
    latest_user = _latest_user_index(trimmed)
    if latest_user is not None and latest_user != first_user:
        latest_content = str(trimmed[latest_user].get("content", "") or "")
        latest_tokens = estimate_tokens(latest_content, model=model)
        if 0 < latest_tokens < int(budget):
            anchor_budget = min(anchor_budget, max(1, int(budget) - latest_tokens))
    anchor = _trim_initial_user_anchor_to_budget(
        anchor_content,
        anchor_budget,
        model=model,
    )
    anchor_msg = dict(trimmed[first_user])
    anchor_msg["content"] = anchor
    trimmed[first_user] = anchor_msg

    # Account for role/name/tool framing too; content-only accounting can
    # produce a message list that exceeds the very budget it claims to fit.
    anchor_tokens = _message_tokens(trimmed[first_user], model=model)
    remaining = max(0, int(budget) - anchor_tokens)
    other_indices = [i for i in range(len(trimmed)) if i != first_user]
    other_tokens = _messages_tokens(
        [trimmed[i] for i in other_indices],
        model=model,
    )
    if other_tokens <= remaining:
        return trimmed
    trim_order = [i for i in other_indices if i != latest_user]
    if latest_user in other_indices:
        trim_order.append(latest_user)
    for i in trim_order:
        if other_tokens <= remaining:
            break
        if not isinstance(trimmed[i], dict):
            continue
        content = str(trimmed[i].get("content", "") or "")
        if not content:
            continue
        before = estimate_tokens(content, model=model)
        allowed = max(0, remaining - (other_tokens - before))
        new_msg = dict(trimmed[i])
        new_msg["content"] = _trim_text_to_token_budget(
            content,
            allowed,
            model=model,
        )
        trimmed[i] = new_msg
        other_tokens = _messages_tokens(
            [trimmed[j] for j in other_indices],
            model=model,
        )
    return trimmed


def _message_is_explicitly_pinned(message: Dict[str, str]) -> bool:
    return bool(
        message.get("pinned")
        or message.get("pin")
        or message.get("preserve_context")
        or _message_has_required_prompt_context(message)
    )


def _message_has_required_prompt_context(message: Any) -> bool:
    """Whether *message* carries lossless transport semantics.

    The mapping form is deliberately extensible so callers can record the
    semantic units conserved by the message (for example
    ``executable_target`` or ``current_residual``).  The metadata is internal
    and is removed by :func:`_sanitize_request_messages`.
    """

    if not isinstance(message, dict):
        return False
    marker = message.get(REQUIRED_PROMPT_CONTEXT_KEY)
    if isinstance(marker, dict):
        return bool(marker.get("required", True))
    return marker is True


def _required_prompt_kind(message: Any) -> str:
    if not isinstance(message, dict):
        return "required_prompt_context"
    marker = message.get(REQUIRED_PROMPT_CONTEXT_KEY)
    if not isinstance(marker, dict):
        return "required_prompt_context"
    kind = str(marker.get("kind") or "").strip()
    units = marker.get("units")
    unit_names = [
        str(unit).strip()
        for unit in (units if isinstance(units, (list, tuple)) else ())
        if str(unit).strip()
    ]
    if kind and unit_names:
        return f"{kind}({','.join(unit_names)})"
    return kind or ",".join(unit_names) or "required_prompt_context"


_PROVIDER_SEMANTIC_MESSAGE_KEYS = (
    "role",
    "content",
    "name",
    "tool_call_id",
    "tool_calls",
    "function_call",
    "reasoning_content",
    "reasoning",
    "_responses_reasoning_items",
    "_responses_output_items",
)

_REQUIRED_INTERNAL_IDENTITY_KEYS = (
    REQUIRED_PROMPT_CONTEXT_KEY,
    "_selected_proof_idea_packet",
    "pinned",
    "pin",
    "preserve_context",
)


def _required_prompt_snapshots(messages: List[Any]) -> List[Tuple[Any, str]]:
    """Return ordered, complete identities for required transport units.

    Visible content alone is not a provider request identity: function-call
    arguments, call ids and opaque reasoning continuation items can change the
    request while role/content remain byte-identical.  Internal atomicity and
    proof-idea receipts are included for internal transformations, then
    deliberately removed only at request serialization.
    """

    snapshots: List[Tuple[Any, str]] = []
    for message in messages:
        if not _message_has_required_prompt_context(message):
            continue
        assert isinstance(message, dict)
        identity = {
            key: message[key]
            for key in (*_PROVIDER_SEMANTIC_MESSAGE_KEYS, *_REQUIRED_INTERNAL_IDENTITY_KEYS)
            if key in message
        }
        normalized, _replaced = _normalize_request_json(identity)
        digest = hashlib.sha256(
            json.dumps(
                normalized,
                ensure_ascii=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("ascii")
        ).hexdigest()
        snapshots.append((normalized, digest))
    return snapshots


def _assert_required_prompt_context_preserved(
    original_messages: List[Any],
    candidate_messages: List[Any],
) -> None:
    """Reject any internal transform that loses or changes a required unit."""

    expected = _required_prompt_snapshots(original_messages)
    if not expected:
        return
    actual = _required_prompt_snapshots(candidate_messages)
    if actual == expected:
        return
    required_tokens = _messages_tokens(
        [
            message
            for message in original_messages
            if _message_has_required_prompt_context(message)
        ]
    )
    raise RequiredPromptContextOverflow(
        required_tokens=required_tokens,
        available_tokens=0,
        required_kinds=tuple(
            _required_prompt_kind(message)
            for message in original_messages
            if _message_has_required_prompt_context(message)
        ),
    )


def _assert_serialized_required_prompt_context(
    internal_messages: List[Any],
    serialized_messages: List[Any],
    *,
    preserve_reasoning_content: bool = False,
    preserve_responses_reasoning_items: bool = False,
) -> None:
    """Verify every required provider-semantic message is serialized exactly."""

    required_count = sum(
        1 for message in internal_messages if _message_has_required_prompt_context(message)
    )
    if not required_count:
        return
    receipt_key = "_mini_required_prompt_transport_receipt"
    expected_with_receipts = _sanitize_request_messages(
        internal_messages,
        preserve_reasoning_content=preserve_reasoning_content,
        preserve_responses_reasoning_items=preserve_responses_reasoning_items,
        _retain_required_receipts=True,
    )
    expected_required: List[Dict[str, Any]] = []
    for message in expected_with_receipts:
        if not isinstance(message, dict) or receipt_key not in message:
            continue
        clean = dict(message)
        clean.pop(receipt_key, None)
        expected_required.append(clean)
    cursor = 0
    for expected_message in expected_required:
        for index in range(cursor, len(serialized_messages)):
            if serialized_messages[index] == expected_message:
                cursor = index + 1
                break
        else:
            raise RequiredPromptContextOverflow(
                required_tokens=_messages_tokens(
                    [
                        message
                        for message in internal_messages
                        if _message_has_required_prompt_context(message)
                    ]
                ),
                available_tokens=0,
                required_kinds=tuple(
                    _required_prompt_kind(message)
                    for message in internal_messages
                    if _message_has_required_prompt_context(message)
                ),
            )


def _initial_user_index(messages: List[Dict[str, str]]) -> Optional[int]:
    for i, message in enumerate(messages):
        if not isinstance(message, dict):
            continue
        if message.get("role") == "user":
            return i
    return None


def _latest_user_index(messages: List[Dict[str, str]]) -> Optional[int]:
    for i in range(len(messages) - 1, -1, -1):
        message = messages[i]
        if isinstance(message, dict) and message.get("role") == "user":
            return i
    return None


def _pinned_message_indices(messages: List[Dict[str, str]]) -> set[int]:
    pinned: set[int] = set()
    if messages and isinstance(messages[0], dict) and messages[0].get("role") == "system":
        pinned.add(0)
    first_user = _initial_user_index(messages)
    if first_user is not None:
        pinned.add(first_user)
    latest_user = _latest_user_index(messages)
    if latest_user is not None:
        pinned.add(latest_user)
    for i, message in enumerate(messages):
        if isinstance(message, dict) and _message_is_explicitly_pinned(message):
            pinned.add(i)
    return pinned


def _oldest_droppable_message_index(messages: List[Dict[str, str]]) -> Optional[int]:
    pinned = _pinned_message_indices(messages)
    for i, message in enumerate(messages):
        if i in pinned:
            continue
        if isinstance(message, dict) and message.get("role") == "system":
            continue
        return i
    return None


def _emergency_trim_order(messages: List[Dict[str, str]]) -> List[int]:
    """Trim stale context before theorem identity and newest repair text."""

    pinned = _pinned_message_indices(messages)
    first_user = _initial_user_index(messages)
    latest_user = _latest_user_index(messages)
    order: List[int] = []
    for i in range(len(messages) - 1, -1, -1):
        if i in pinned or i == latest_user:
            continue
        if isinstance(messages[i], dict) and messages[i].get("role") != "system":
            order.append(i)
    for i, message in enumerate(messages):
        if i == latest_user:
            continue
        if isinstance(message, dict) and message.get("role") == "system":
            order.append(i)
    if first_user is not None and first_user != latest_user:
        order.append(first_user)
    for i in range(len(messages) - 1, -1, -1):
        if i in order or i == latest_user:
            continue
        if isinstance(messages[i], dict) and messages[i].get("role") != "system":
            order.append(i)
    if latest_user is not None:
        order.append(latest_user)
    return list(dict.fromkeys(order))


def _trim_messages_with_required_context(
    messages: List[Dict[str, Any]],
    budget: int,
    *,
    model: Optional[str] = None,
) -> List[Dict[str, Any]]:
    """Fit an atomic prompt by dropping optional messages as whole units.

    Once any message opts into required-context semantics, system messages and
    explicitly pinned messages form the same lossless transport envelope.  No
    content in that envelope is shortened.  Other messages remain optional
    atomic units and are removed oldest-first, with ordinary initial/latest
    user anchors retained until stale middle history has been exhausted.
    """

    original = list(messages)
    trimmed = _drop_orphan_tool_results(list(messages))
    _assert_required_prompt_context_preserved(original, trimmed)

    protected = _required_prompt_envelope_indices(trimmed)

    protected_messages = [
        message for index, message in enumerate(trimmed) if index in protected
    ]
    protected_tokens = _messages_tokens(protected_messages, model=model)
    if protected_tokens > max(0, int(budget)):
        raise RequiredPromptContextOverflow(
            required_tokens=protected_tokens,
            available_tokens=max(0, int(budget)),
            required_kinds=tuple(
                _required_prompt_kind(message)
                for message in trimmed
                if _message_has_required_prompt_context(message)
            ),
        )
    if _messages_tokens(trimmed, model=model) <= int(budget):
        return trimmed  # type: ignore[return-value]

    first_user = _initial_user_index(trimmed)
    latest_user = _latest_user_index(trimmed)
    optional_indices = [
        index
        for index, message in enumerate(trimmed)
        if index not in protected
        and not (isinstance(message, dict) and message.get("role") == "system")
    ]
    drop_order = [
        index
        for index in optional_indices
        if index not in {first_user, latest_user}
    ]
    if first_user in optional_indices:
        drop_order.append(first_user)  # type: ignore[arg-type]
    if latest_user in optional_indices and latest_user != first_user:
        drop_order.append(latest_user)  # type: ignore[arg-type]

    retained = list(trimmed)
    dropped_indices: set[int] = set()
    for original_index in drop_order:
        if _messages_tokens(retained, model=model) <= int(budget):
            break
        dropped_indices.add(original_index)
        repaired = _repair_tool_transcript(
            [
                message
                for index, message in enumerate(trimmed)
                if index not in dropped_indices
            ]
        )
        _assert_required_prompt_context_preserved(original, repaired)
        retained = repaired

    if _messages_tokens(retained, model=model) > int(budget):
        # Only the lossless envelope remains.  There is no legal prefix trim.
        raise RequiredPromptContextOverflow(
            required_tokens=_messages_tokens(retained, model=model),
            available_tokens=max(0, int(budget)),
            required_kinds=tuple(
                _required_prompt_kind(message)
                for message in retained
                if _message_has_required_prompt_context(message)
            ),
        )
    _assert_required_prompt_context_preserved(original, retained)
    return retained  # type: ignore[return-value]


def _required_prompt_envelope_indices(messages: List[Any]) -> set[int]:
    """Indices that form the indivisible provider transport envelope."""

    protected: set[int] = set()
    required_tool_call_ids: set[str] = set()
    for index, message in enumerate(messages):
        if not isinstance(message, dict):
            continue
        if (
            message.get("role") == "system"
            or _message_has_required_prompt_context(message)
            or bool(
                message.get("pinned")
                or message.get("pin")
                or message.get("preserve_context")
            )
        ):
            protected.add(index)
        if _message_has_required_prompt_context(message):
            if message.get("role") == "tool":
                tool_call_id = str(message.get("tool_call_id") or "")
                if tool_call_id:
                    required_tool_call_ids.add(tool_call_id)
            elif message.get("role") == "assistant":
                required_tool_call_ids.update(_tool_call_ids(message))
    if required_tool_call_ids:
        # A tool-call assistant message is one protocol transaction. If one
        # result is required, retain every sibling call/result needed for the
        # provider to accept that assistant message rather than letting
        # transcript repair erase the marked evidence as an orphan.
        expanded = True
        while expanded:
            expanded = False
            for index, message in enumerate(messages):
                if not isinstance(message, dict) or message.get("role") != "assistant":
                    continue
                assistant_ids = set(_tool_call_ids(message))
                if not required_tool_call_ids.intersection(assistant_ids):
                    continue
                protected.add(index)
                new_ids = assistant_ids - required_tool_call_ids
                if new_ids:
                    required_tool_call_ids.update(new_ids)
                    expanded = True
        for index, message in enumerate(messages):
            if not isinstance(message, dict):
                continue
            if message.get("role") == "assistant" and required_tool_call_ids.intersection(
                _tool_call_ids(message)
            ):
                protected.add(index)
            if (
                message.get("role") == "tool"
                and str(message.get("tool_call_id") or "") in required_tool_call_ids
            ):
                protected.add(index)
    return protected


def _required_prompt_envelope(messages: List[Any]) -> List[Any]:
    """Drop all optional context while preserving required transcript closure."""

    original = list(messages)
    repaired = _drop_orphan_tool_results(original)
    _assert_required_prompt_context_preserved(original, repaired)
    protected = _required_prompt_envelope_indices(repaired)
    envelope = _repair_tool_transcript(
        [message for index, message in enumerate(repaired) if index in protected]
    )
    _assert_required_prompt_context_preserved(original, envelope)
    return envelope


def _required_prompt_overflow(
    messages: List[Any],
    *,
    available_tokens: Optional[int],
    model: Optional[str],
) -> RequiredPromptContextOverflow:
    envelope = _required_prompt_envelope(messages)
    required_tokens = _messages_tokens(envelope, model=model)
    configured_available = (
        required_tokens - 1
        if available_tokens is None
        else max(0, int(available_tokens))
    )
    # Once the provider rejects the envelope itself, it has established a
    # strict upper bound even when it did not disclose its exact context size.
    provider_proven_available = max(
        0,
        min(configured_available, max(0, required_tokens - 1)),
    )
    return RequiredPromptContextOverflow(
        required_tokens=required_tokens,
        available_tokens=provider_proven_available,
        required_kinds=tuple(
            _required_prompt_kind(message)
            for message in messages
            if _message_has_required_prompt_context(message)
        ),
    )


def _trim_messages_to_budget(
    messages: List[Dict[str, str]],
    budget: Optional[int],
    *,
    model: Optional[str] = None,
) -> List[Dict[str, str]]:
    required_context = any(
        _message_has_required_prompt_context(message) for message in messages
    )
    if required_context and budget is not None:
        return _trim_messages_with_required_context(
            messages, int(budget), model=model
        )  # type: ignore[return-value]
    if not messages or not budget or budget <= 0:
        return _drop_orphan_tool_results(list(messages))  # type: ignore[return-value]
    trimmed = _drop_orphan_tool_results(list(messages))
    total = _messages_tokens(trimmed, model=model)
    if total <= budget:
        return trimmed  # type: ignore[return-value]
    # Drop oldest non-system, non-anchor messages first. The initial user
    # message usually carries the problem/theorem statement; losing it during
    # overflow repair leaves later turns optimizing against stale fragments.
    while len(trimmed) > 1 and total > budget:
        idx = _oldest_droppable_message_index(trimmed)
        if idx is None:
            break
        trimmed.pop(idx)
        trimmed = _repair_tool_transcript(trimmed)
        total = _messages_tokens(trimmed, model=model)
    if total <= budget:
        return trimmed  # type: ignore[return-value]
    trimmed = _reserve_initial_user_anchor(trimmed, int(budget), model=model)
    trimmed = _repair_tool_transcript(trimmed)
    total = _messages_tokens(trimmed, model=model)
    if total <= budget:
        return trimmed  # type: ignore[return-value]
    first_user = _initial_user_index(trimmed)
    for idx in _emergency_trim_order(trimmed):
        if total <= budget:
            break
        if idx < 0 or idx >= len(trimmed) or not isinstance(trimmed[idx], dict):
            continue
        content = str(trimmed[idx].get("content", "") or "")
        if not content:
            continue
        other_tokens = _messages_tokens(
            [m for j, m in enumerate(trimmed) if j != idx], model=model
        )
        fixed_message_tokens = _message_tokens(
            {**trimmed[idx], "content": ""},
            model=model,
        )
        allow = max(0, int(budget) - other_tokens - fixed_message_tokens)
        if first_user is not None and idx == first_user:
            new_content = _trim_initial_user_anchor_to_budget(
                content,
                allow,
                model=model,
            )
        else:
            new_content = _trim_text_to_token_budget(content, allow, model=model)
        if new_content == content:
            continue
        new_msg = dict(trimmed[idx])
        new_msg["content"] = new_content
        trimmed[idx] = new_msg
        trimmed = _repair_tool_transcript(trimmed)
        total = _messages_tokens(trimmed, model=model)
    return trimmed  # type: ignore[return-value]


def _truncate_messages(
    messages: List[Dict[str, str]], keep_last_n: int = 2
) -> Optional[List[Dict[str, str]]]:
    """Truncate conversation history, keeping anchors + last N turns.

    Returns None if no truncation possible (already minimal).
    """
    if len(messages) <= keep_last_n + 1:
        return None  # Already minimal
    keep: set[int] = _pinned_message_indices(messages)
    if keep_last_n > 0:
        keep.update(range(max(0, len(messages) - keep_last_n), len(messages)))
    elif messages:
        keep.add(len(messages) - 1)
    result = _repair_tool_transcript(
        [message for i, message in enumerate(messages) if i in keep]
    )
    return result if len(result) < len(messages) else None


class OpenAICompatClient:
    # Maximum concurrent requests for chat_n fallback path
    _MAX_CONCURRENT_REQUESTS = 5
    _MAX_TRANSPORT_ATTEMPTS = 8
    supports_transport_dispatch_marker = True
    supports_transport_dispatch_authorization = True

    def reservation_attempt_multiplier(self, call_kind: str) -> int:
        # Reserve the first concrete provider dispatch only. ``metered_call``
        # installs an awaited transport observer that extends the hold before
        # every retry crosses the HTTP boundary. Pre-reserving all eight
        # possible attempts made a 384K-capability DeepSeek worker appear to
        # cost about $0.87 even though one dispatch costs about $0.11, while
        # the planner used this same incremental path already. Missing usage
        # for any authorized dispatch remains charged fail-closed at settle.
        del call_kind
        return 1

    def reservation_prompt_multipliers(
        self,
        candidate_count: int,
        target_count: int,
        call_kind: str,
    ) -> List[int]:
        del target_count
        count = max(1, int(candidate_count or 1))
        if "chat_n" not in str(call_kind or "") or count <= 1:
            # ``chat_n(n=1)`` takes the dedicated ``_chat_unlocked`` branch:
            # there is no native-batch probe followed by per-choice fallback.
            # This distinction matters when a pool allocates a singleton to a
            # nested chain leaf (or zero to its siblings).
            return [1]
        # chat_n first attempts one native batched request; if it returns no
        # choices, it can then issue one single request per requested choice.
        return [count + 1]

    def reservation_output_multipliers(
        self,
        candidate_count: int,
        target_count: int,
        call_kind: str,
    ) -> List[int]:
        del target_count
        count = max(1, int(candidate_count or 1))
        if "chat_n" not in str(call_kind or "") or count <= 1:
            return [1]
        return [2 * count]

    def __init__(
        self,
        cfg: RoleConfig,
        *,
        provider_lane_health_registry: Optional[ProviderLaneHealthRegistry] = None,
    ):
        if base_url_matches_provider(cfg.base_url, "openrouter"):
            # Normalize supported user aliases at the transport boundary too,
            # covering programmatic clients that bypass Mini's CLI builder.
            cfg.model = canonical_openrouter_model_id(cfg.model)
        self.cfg = cfg
        self.base_url = cfg.base_url.rstrip("/")
        self.provider_defer_fingerprint = provider_serving_fingerprint(cfg)
        self._configured_provider_lane_health_registry = (
            provider_lane_health_registry
            if isinstance(
                provider_lane_health_registry,
                ProviderLaneHealthRegistry,
            )
            else None
        )
        self._provider_lane_health_registry = (
            self._configured_provider_lane_health_registry
            or ProviderLaneHealthRegistry()
        )
        self.headers = {}
        if cfg.api_key:
            self.headers["Authorization"] = f"Bearer {cfg.api_key.strip()}"
        self.client = httpx.AsyncClient(
            timeout=self._httpx_timeout(),
            **self._keepalive_transport_kwargs(),
        )
        self._pending_http_tasks: set[asyncio.Task[Any]] = set()
        self._pending_http_observer_tasks: set[asyncio.Task[Any]] = set()
        self._pending_http_lane_ownership: Dict[
            asyncio.Task[Any], ProviderLanePermitOwnership
        ] = {}
        self._late_receipt_observer_barrier = False
        self._stop = _stop_sequences(cfg)
        # Provider-discovered constraint cache: the chat-completions endpoint
        # for this model rejects function tools unless reasoning_effort is the
        # explicit string 'none'. Seeded statically for known families and set
        # at runtime when the provider's conflict rejection is observed.
        self._chat_tools_require_reasoning_effort_none = (
            _openai_chat_tools_require_reasoning_effort_none(
                self.base_url,
                cfg.model,
            )
        )
        # Some routes omit mandatory-reasoning metadata from OpenRouter's
        # catalog but reject ``reasoning.enabled=false`` at request time.
        self._reasoning_disable_rejected = False
        self._reasoning_disable_supported: Optional[bool] = None

        self._reasoning_disable_negotiation_future: Optional[
            asyncio.Future[None]
        ] = None
        # Responses-API parameters discovered unsupported for this model.
        # Deliberately narrow (see _responses_tools_request): only parameters
        # whose omission cannot change reasoning semantics or uncap billing.
        self._responses_unsupported_parameters: set[str] = set()
        self._request_sem = asyncio.Semaphore(self._MAX_CONCURRENT_REQUESTS)
        self._chat_request_gate = AsyncSharedExclusiveGate()
        # Observability: last successfully used model/base_url (useful when wrapped).
        self.last_used_model: str = cfg.model
        self.last_used_base_url: str = self.base_url
        # Token usage accumulators (populated from API response `usage` field).
        self._usage_input_tokens: int = 0
        self._usage_output_tokens: int = 0
        self._usage_cached_input_tokens: int = 0
        self._usage_cache_write_tokens: int = 0
        self._usage_prompt_cache_miss_tokens: int = 0
        self._usage_cost_usd: float = 0.0
        self._usage_cost_usd_authoritative: bool = True
        self._usage_unpriced_input_tokens: int = 0
        self._usage_unpriced_output_tokens: int = 0
        self._usage_unpriced_cached_input_tokens: int = 0
        self._usage_unpriced_cache_write_tokens: int = 0
        self._usage_missing_responses: int = 0
        self._suppressed_unsafe_late_usage_callbacks: int = 0
        # Runtime cap learned from context-overflow errors (tokens).
        self._runtime_prompt_budget_cap_tokens: Optional[int] = None
        # Truncation detection: set after each API call by _process_response().
        # last_truncated is True when the most recent response hit max_tokens.
        # last_truncated_flags is a per-choice list for chat_n() results.
        self.last_truncated: bool = False
        self.last_truncated_flags: List[bool] = []
        # Full normalized response from the latest tool call. DeepSeek needs
        # its assistant reasoning_content replayed with subsequent tool turns.
        self.last_raw_response_data: Dict[str, Any] = {}
        self._truncation_count: int = 0
        self.last_request_body_sha256: str = ""
        self.last_request_body_bytes: int = 0
        self.last_request_payload_summary: Dict[str, Any] = {}
        self.last_request_surrogate_replacements: int = 0
        self._tools_capability: Optional[bool] = None
        self._unsupported_payload_parameters: set[str] = set()
        self.last_tool_request_effective: bool = False
        self.last_tool_request_downgraded: bool = False
        self.last_tool_request_skipped: bool = False
        self.last_temperature_requested: Optional[float] = None
        self.last_temperature_sent: Optional[float] = None
        self.last_temperature_provider_dropped: bool = False
        self.last_temperature_provider_drop_reason: str = ""
        self.last_reasoning_control_requested: str = ""
        self.last_reasoning_control_decision: str = ""
        self.last_reasoning_control_sent: Dict[str, Any] = {}
        self.last_reasoning_control_required: bool = False
        self.last_reasoning_capability_record: Dict[str, Any] = {}

    def _provider_lane_health_registry_for_dispatch(
        self,
    ) -> ProviderLaneHealthRegistry:
        """Resolve one request's run registry without mutating the client.

        Explicit operator configuration always wins.  Otherwise a public run
        binding coordinates every role in that invocation, while calls made
        outside a run retain this client's private fallback.
        """

        if self._configured_provider_lane_health_registry is not None:
            return self._configured_provider_lane_health_registry
        return (
            bound_provider_lane_health_registry()
            or self._provider_lane_health_registry
        )

    def _positive_finite_timeout(self, value: Any) -> Optional[float]:
        try:
            out = float(value)
        except Exception:
            return None
        if math.isfinite(out) and out > 0.0:
            return out
        return None

    def _configured_request_timeout_s(
        self,
        request_timeout_override_s: Optional[float] = None,
    ) -> Optional[float]:
        """Return the HTTP request timeout, or None for unbounded reads."""

        try:
            if math.isinf(float(request_timeout_override_s)):
                return None
        except (TypeError, ValueError):
            pass
        override_timeout = self._positive_finite_timeout(
            request_timeout_override_s
        )
        if override_timeout is not None:
            return override_timeout
        if bool(getattr(self.cfg, "request_timeout_disabled", False)):
            return None
        override = getattr(self.cfg, "request_timeout_s", None)
        if override is not None:
            return self._positive_finite_timeout(override)
        policy = (
            str(getattr(self.cfg, "llm_deadline_policy", "hard") or "hard")
            .strip()
            .lower()
        )
        if policy == "soft":
            return None
        return self._positive_finite_timeout(getattr(self.cfg, "timeout_s", None))

    def _connect_timeout_s(
        self,
        request_timeout_override_s: Optional[float] = None,
    ) -> float:
        for raw in (
            request_timeout_override_s,
            getattr(self.cfg, "request_timeout_s", None),
            getattr(self.cfg, "timeout_s", None),
        ):
            timeout = self._positive_finite_timeout(raw)
            if timeout is not None:
                return max(0.001, min(15.0, timeout))
        return 15.0

    @classmethod
    def _keepalive_transport_kwargs(cls) -> Dict[str, Any]:
        """AsyncClient kwargs adding keepalive without dropping env proxies.

        httpx computes ``allow_env_proxies = trust_env and transport is None``,
        so supplying *any* explicit transport silently disables
        ``HTTP_PROXY``/``HTTPS_PROXY``/``ALL_PROXY``/``NO_PROXY``.  On a host
        that reaches the provider only through a corporate proxy or a local
        gateway that means total loss of LLM connectivity -- or a silent
        direct egress on a host that is meant to be restricted.

        Connectivity outranks the keepalive diagnostic, so when the
        environment configures a proxy we leave httpx's own transport
        construction untouched and simply go without keepalive.
        """

        for env_name in (
            "HTTP_PROXY",
            "HTTPS_PROXY",
            "ALL_PROXY",
            "http_proxy",
            "https_proxy",
            "all_proxy",
        ):
            if str(os.environ.get(env_name, "") or "").strip():
                return {}
        return {
            "transport": httpx.AsyncHTTPTransport(
                socket_options=cls._keepalive_socket_options(),
            )
        }

    @staticmethod
    def _keepalive_socket_options() -> list[tuple[int, int, int]]:
        """TCP keepalive probes so a dead peer is distinguishable from a slow one.

        Chat completions are non-streaming, so httpx ``read`` is
        time-to-first-byte: a provider that dies mid-generation looks exactly
        like one still thinking, and the socket sits idle for the whole
        generation until the (deliberately large) read timeout expires -- or
        forever on the unbounded branch.

        A probe is answered by the peer's *kernel*, not its application, so a
        provider that is alive and computing for 30 minutes ACKs every probe
        and the connection survives.  Keepalive cannot kill a busy-but-alive
        server.  What it does kill is a connection whose *path* is gone, and
        that is the budget being spent here: with no data in flight an idle
        socket is otherwise immune to transient loss, so the probe tail must
        outlast any credible blip -- a WiFi roam, VPN rekey, suspend, or route
        flap -- or it destroys valid in-flight completions that would have
        arrived. 60s idle + 20 probes at 30s = ~11 minutes before teardown:
        still ~13x faster than the Linux default (~2h28m) at spotting a truly
        dead peer, without cutting live work.

        Expiry surfaces as ETIMEDOUT (``TimeoutError`` / ``httpx.ReadError``),
        which ``classify_llm_exception`` already treats as retryable
        transport.  Never shorten the probe tail to bound real work -- these
        exist to detect a peer that is gone, not to cap a peer that is slow.
        """

        options: list[tuple[int, int, int]] = [
            (socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1),
        ]
        # Platform-conditional.  macOS spells idle-time TCP_KEEPALIVE and has
        # no TCP_KEEPIDLE, so it keeps the OS default idle (2h) while still
        # taking the probe tail below; Linux takes all three.
        for name, value in (
            ("TCP_KEEPIDLE", 60),
            ("TCP_KEEPALIVE", 60),
            ("TCP_KEEPINTVL", 30),
            ("TCP_KEEPCNT", 20),
        ):
            option = getattr(socket, name, None)
            if option is not None:
                options.append((socket.IPPROTO_TCP, option, value))
        return options

    def _httpx_timeout(
        self,
        request_timeout_override_s: Optional[float] = None,
    ) -> httpx.Timeout:
        request_timeout = self._configured_request_timeout_s(
            request_timeout_override_s
        )
        connect_timeout = self._connect_timeout_s(request_timeout_override_s)
        if request_timeout is None:
            # Non-streaming chat completions keep the socket silent until
            # the full JSON body is ready. httpx ``read`` is therefore
            # time-to-first-byte, not inter-token idle. A finite read here
            # would kill the 26-minute 1977 planner POST. Connect stays
            # bounded so a wedged handshake still fails.
            #
            # ``pool`` deliberately stays unbounded too: it times how long a
            # request waits for a free connection slot, and ``chat_n`` fans
            # out many concurrent calls on one client. A finite pool wall
            # would fail a legitimately queued candidate that would have
            # succeeded. Socket liveness is handled by TCP keepalive
            # (see ``_keepalive_socket_options``), which cannot cut live work.
            return httpx.Timeout(None, connect=connect_timeout)
        return httpx.Timeout(
            request_timeout,
            connect=min(connect_timeout, request_timeout),
        )

    @staticmethod
    def _usage_int(value: Any) -> int:
        """Best-effort integer coercion for provider usage payloads."""
        try:
            if value is None:
                return 0
            return int(value)
        except Exception:
            return 0

    def _effective_prompt_budget(
        self,
        max_tokens_override: Optional[int] = None,
    ) -> Optional[int]:
        # A configured output maximum is a model capability. Phase-local
        # output caps must govern prompt headroom for the same request, just
        # as they govern the provider payload and cost reservation.
        base_budget = _prompt_budget_for_cfg(
            self.cfg,
            max_tokens_override=max_tokens_override,
        )
        cap = self._runtime_prompt_budget_cap_tokens
        if cap is None:
            return base_budget
        cap_i = max(_CTX_MIN_PROMPT_TOKENS, int(cap))
        if base_budget is None:
            return cap_i
        return max(_CTX_MIN_PROMPT_TOKENS, min(int(base_budget), cap_i))

    def _tighten_prompt_budget(
        self,
        messages: List[Dict[str, str]],
        budget: Optional[int],
        *,
        truncation_attempt: int,
    ) -> int:
        est_tokens = _messages_tokens(messages, model=self.cfg.model)
        dynamic_cap = max(_CTX_MIN_PROMPT_TOKENS, int(est_tokens * 0.75))
        if budget is not None:
            decay = min(
                _CTX_OVERFLOW_SHRINK, _CTX_OVERFLOW_SHRINK ** (truncation_attempt + 1)
            )
            budget_cap = max(_CTX_MIN_PROMPT_TOKENS, int(float(budget) * decay))
            target = min(dynamic_cap, budget_cap)
        else:
            target = dynamic_cap
        if self._runtime_prompt_budget_cap_tokens is None:
            self._runtime_prompt_budget_cap_tokens = int(target)
        else:
            self._runtime_prompt_budget_cap_tokens = int(
                max(
                    _CTX_MIN_PROMPT_TOKENS,
                    min(self._runtime_prompt_budget_cap_tokens, target),
                )
            )
        return int(self._runtime_prompt_budget_cap_tokens)

    def supports_tool_calls(self) -> bool:
        """Return whether tool-call requests should still be attempted."""
        return self._tools_capability is not False

    def _operation_deadline(
        self,
        deadline: Optional[float],
        *,
        operation_timeout_override_s: Optional[float] = None,
    ) -> Optional[float]:
        """Return the hard deadline for one logical chat operation, if any.

        ``timeout_s`` is always the HTTP request timeout configured on the
        underlying client. In hard deadline mode, older configs also use it as
        the total operation cap unless ``operation_timeout_s`` is set. In soft
        mode, provider generations are allowed to finish and caller/phase
        deadlines are not converted into local aborts for this request.
        """

        try:
            if math.isinf(float(operation_timeout_override_s)):
                return deadline
        except (TypeError, ValueError):
            pass
        override_timeout = self._positive_finite_timeout(
            operation_timeout_override_s
        )
        deadlines: List[float] = []
        if deadline is not None and float(deadline) > 0.0:
            deadlines.append(float(deadline))
        if override_timeout is not None:
            deadlines.append(time.time() + override_timeout)
            return min(deadlines)
        policy = (
            str(getattr(self.cfg, "llm_deadline_policy", "hard") or "hard")
            .strip()
            .lower()
        )
        if policy == "soft":
            return None
        operation_timeout = getattr(self.cfg, "operation_timeout_s", None)
        try:
            if operation_timeout is not None:
                timeout_s = float(operation_timeout)
            else:
                # ``timeout_s`` bounds ONE request attempt. Sizing the whole
                # operation window to a single attempt makes retries
                # structurally impossible: a first attempt that hangs for the
                # full request window (hung provider, empty-body 200 at the
                # timeout edge) leaves zero room, so every retry dies with
                # "LLM retry would exceed deadline (attempt=1)". Reserve one
                # extra request window so at least one retry can run with a
                # fresh sub-timeout.
                timeout_s = (
                    float(getattr(self.cfg, "timeout_s", 0.0) or 0.0)
                    * _OPERATION_DEADLINE_RETRY_HEADROOM
                )
        except Exception:
            timeout_s = 0.0
        if timeout_s > 0.0:
            deadlines.append(time.time() + timeout_s)
        if not deadlines:
            return None
        return min(deadlines)

    def _configured_operation_timeout_s(
        self,
        operation_timeout_override_s: Optional[float] = None,
    ) -> Optional[float]:
        override_timeout = self._positive_finite_timeout(
            operation_timeout_override_s
        )
        if override_timeout is not None:
            return override_timeout
        policy = (
            str(getattr(self.cfg, "llm_deadline_policy", "hard") or "hard")
            .strip()
            .lower()
        )
        if policy == "soft":
            return None
        operation_timeout = getattr(self.cfg, "operation_timeout_s", None)
        try:
            if operation_timeout is not None:
                timeout_s = float(operation_timeout)
            else:
                # Keep the reported value in lockstep with the window
                # _operation_deadline actually enforces for this fallback.
                timeout_s = (
                    float(getattr(self.cfg, "timeout_s", 0.0) or 0.0)
                    * _OPERATION_DEADLINE_RETRY_HEADROOM
                )
        except Exception:
            return None
        if timeout_s > 0.0:
            return timeout_s
        return None

    def _retry_deadline_exception(
        self,
        message: str,
        *,
        reason: str,
        attempt: int,
        operation_started_at: float,
        attempt_started_at: Optional[float] = None,
        retry_delay_s: Optional[float] = None,
        retry_after_s: Optional[float] = None,
        deadline: Optional[float] = None,
        request_timeout_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        original_exc: Optional[BaseException] = None,
    ) -> LLMRetryDeadlineExceeded:
        now = time.time()
        status_code = 0
        if isinstance(original_exc, httpx.HTTPStatusError):
            try:
                status_code = int(original_exc.response.status_code or 0)
            except Exception:
                status_code = 0
        deadline_remaining_s = None
        if deadline is not None:
            try:
                deadline_remaining_s = float(deadline) - now
            except Exception:
                deadline_remaining_s = None
        request_elapsed_s = None
        if attempt_started_at is not None:
            try:
                request_elapsed_s = max(0.0, now - float(attempt_started_at))
            except Exception:
                request_elapsed_s = None
        configured_timeout_s = None
        try:
            configured_timeout_s = self._configured_request_timeout_s()
        except Exception:
            configured_timeout_s = None
        deadline_policy = str(
            getattr(self.cfg, "llm_deadline_policy", "hard") or "hard"
        )
        context = LLMRetryDeadlineContext(
            reason=str(reason or ""),
            attempt=max(0, int(attempt or 0)),
            model=str(getattr(self.cfg, "model", "") or ""),
            base_url=str(getattr(self, "base_url", "") or ""),
            deadline_policy=deadline_policy,
            status_code=status_code,
            retry_after_s=retry_after_s,
            retry_delay_s=retry_delay_s,
            deadline_remaining_s=deadline_remaining_s,
            request_timeout_s=request_timeout_s,
            request_elapsed_s=request_elapsed_s,
            operation_elapsed_s=max(0.0, now - float(operation_started_at)),
            configured_timeout_s=configured_timeout_s,
            operation_timeout_s=self._configured_operation_timeout_s(
                operation_timeout_override_s
            ),
            original_exception_type=(
                type(original_exc).__name__ if original_exc is not None else ""
            ),
            original_error=(
                format_exception(original_exc) if original_exc is not None else ""
            ),
        )
        return LLMRetryDeadlineExceeded(message, context=context)

    def _accumulate_usage(self, data: Dict[str, Any]) -> None:
        record = provider_usage_from_payload(
            data,
            model=self.cfg.model,
            base_url=self.base_url,
        )
        if record is None:
            self._usage_cost_usd_authoritative = False
            self._usage_missing_responses += 1
            return
        self._usage_input_tokens += int(record.input_tokens)
        self._usage_output_tokens += int(record.output_tokens)
        self._usage_cached_input_tokens += int(record.cached_input_tokens)
        self._usage_cache_write_tokens += int(record.cache_write_tokens)
        self._usage_prompt_cache_miss_tokens += int(record.prompt_cache_miss_tokens)
        record_cost, pricing_known = cost_for_record(record)
        if pricing_known:
            self._usage_cost_usd += float(record_cost)
        else:
            self._usage_cost_usd_authoritative = False
            self._usage_unpriced_input_tokens += int(record.input_tokens)
            self._usage_unpriced_output_tokens += int(record.output_tokens)
            self._usage_unpriced_cached_input_tokens += int(
                record.cached_input_tokens
            )
            self._usage_unpriced_cache_write_tokens += int(
                record.cache_write_tokens
            )

    def _publish_response_usage_once(
        self,
        response: "httpx.Response",
        data: Dict[str, Any],
        usage_callback: Optional[Any],
    ) -> bool:
        """Claim and publish one provider receipt exactly once.

        A transport response can be observed by its normal owner or by the
        detached-receipt observer after owner cancellation.  The extension is
        the response-local ownership ledger shared by every consumption path,
        including ``chat_n`` paths that do not use ``_process_response``.
        There is no await between the claim and publication, so the claim is
        atomic with respect to other tasks on the event loop.
        """

        if bool(response.extensions.get("ensemble_transport_usage_observed")):
            return False
        response.extensions["ensemble_transport_usage_observed"] = True
        sampling_metadata = dict(
            response.extensions.get("ensemble_sampling_controls") or {}
        )
        self._accumulate_usage(data)
        record = provider_usage_from_payload(
                data,
                model=self.cfg.model,
                base_url=self.base_url,
                temperature_requested=sampling_metadata.get(
                    "temperature_requested"
                ),
                temperature_sent=sampling_metadata.get("temperature_sent"),
                temperature_provider_dropped=bool(
                    sampling_metadata.get("temperature_provider_dropped")
                ),
                temperature_provider_drop_reason=str(
                    sampling_metadata.get("temperature_provider_drop_reason") or ""
                ),
            )
        authority = dict(
            response.extensions.get("ensemble_dispatch_authority") or {}
        )
        if record is not None and authority:
            record = replace(
                record,
                reservation_target_id=str(authority.get("target_id") or ""),
                reservation_dispatch_ordinal=max(
                    0, int(authority.get("dispatch_ordinal", 0) or 0)
                ),
            )
        emit_usage_callback(usage_callback, record)
        return True

    def token_usage(self) -> Dict[str, Any]:
        return {
            "input_tokens": self._usage_input_tokens,
            "output_tokens": self._usage_output_tokens,
            "cached_input_tokens": self._usage_cached_input_tokens,
            "cache_write_tokens": self._usage_cache_write_tokens,
            "prompt_cache_miss_tokens": self._usage_prompt_cache_miss_tokens,
            "cost_usd": self._usage_cost_usd,
            "cost_usd_authoritative": self._usage_cost_usd_authoritative,
            "unpriced_input_tokens": self._usage_unpriced_input_tokens,
            "unpriced_output_tokens": self._usage_unpriced_output_tokens,
            "unpriced_cached_input_tokens": self._usage_unpriced_cached_input_tokens,
            "unpriced_cache_write_tokens": self._usage_unpriced_cache_write_tokens,
            "usage_missing_responses": self._usage_missing_responses,
            "suppressed_unsafe_late_usage_callbacks": (
                self._suppressed_unsafe_late_usage_callbacks
            ),
        }

    def reset_token_usage(self) -> None:
        self._usage_input_tokens = 0
        self._usage_output_tokens = 0
        self._usage_cached_input_tokens = 0
        self._usage_cache_write_tokens = 0
        self._usage_prompt_cache_miss_tokens = 0
        self._usage_cost_usd = 0.0
        self._usage_cost_usd_authoritative = True
        self._usage_unpriced_input_tokens = 0
        self._usage_unpriced_output_tokens = 0
        self._usage_unpriced_cached_input_tokens = 0
        self._usage_unpriced_cache_write_tokens = 0
        self._usage_missing_responses = 0
        self._suppressed_unsafe_late_usage_callbacks = 0

    def reset_prompt_budget(self) -> None:
        """Reset the runtime prompt budget cap learned from context-overflow errors.

        Call at problem boundaries so that budget shrinkage from one problem
        does not starve subsequent problems.
        """
        self._runtime_prompt_budget_cap_tokens = None

    def _chat_url(self) -> str:
        return f"{self.base_url}/chat/completions"

    def _safe_json(self, resp: httpx.Response) -> Dict[str, Any]:
        try:
            body_text = (resp.text or "").strip()
        except Exception:
            body_text = ""
        if not body_text:
            request_url = getattr(getattr(resp, "request", None), "url", "<unknown>")
            raise RuntimeError(
                f"LLM response body empty: model={self.cfg.model} url={request_url} "
                f"status={resp.status_code}"
            )
        try:
            return resp.json()
        except Exception as exc:
            body = body_text
            if body and len(body) > 500:
                body = body[:500] + "...(truncated)"
            raise RuntimeError(
                f"LLM response JSON decode failed: model={self.cfg.model} url={resp.request.url} "
                f"status={resp.status_code} body={body}"
            ) from exc

    def _encode_request_body(
        self,
        payload: Dict[str, Any],
        *,
        url: str,
    ) -> Tuple[bytes, Dict[str, Any]]:
        """Validate and encode the outbound request body exactly once."""
        self.last_request_body_sha256 = ""
        self.last_request_body_bytes = 0
        self.last_request_payload_summary = {}
        self.last_request_surrogate_replacements = 0
        try:
            normalized, replaced = _normalize_request_json(payload)
            if not isinstance(normalized, dict):
                raise TypeError("top-level JSON payload must be an object")
            body = json.dumps(
                normalized,
                ensure_ascii=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("ascii")
        except (TypeError, ValueError, UnicodeError) as exc:
            raise RuntimeError(
                f"LLM request JSON encode failed: model={self.cfg.model} url={url} "
                f"reason={exc}"
            ) from exc
        meta = {
            "sha256": hashlib.sha256(body).hexdigest()[:16],
            "bytes": len(body),
            "surrogate_replacements": int(replaced),
            "summary": _payload_summary(normalized),
        }
        self.last_request_body_sha256 = str(meta["sha256"])
        self.last_request_body_bytes = int(meta["bytes"])  # type: ignore[call-overload]
        self.last_request_payload_summary = dict(meta["summary"])  # type: ignore[call-overload]
        self.last_request_surrogate_replacements = int(meta["surrogate_replacements"])  # type: ignore[call-overload]
        return body, meta

    def _swap_token_limit(
        self, payload: Dict[str, Any], from_key: str, to_key: str
    ) -> Optional[Dict[str, Any]]:
        """Return a copy of payload swapping token limit parameter names."""
        if from_key not in payload or to_key in payload:
            return None
        updated = dict(payload)
        updated[to_key] = updated.pop(from_key)
        return updated

    def _apply_token_limit(
        self,
        payload: Dict[str, Any],
        *,
        max_tokens_override: Optional[int] = None,
    ) -> None:
        """Apply the correct token limit parameter for the target API."""
        token_limit = (
            int(max_tokens_override)
            if max_tokens_override is not None
            else int(self.cfg.max_tokens)
        )
        if base_url_matches_provider(self.base_url, "openai"):
            payload["max_completion_tokens"] = token_limit
        else:
            payload["max_tokens"] = token_limit

    async def _resolve_request_output_envelope(
        self,
        max_tokens_override: Any,
        reasoning_effort_override: Any,
    ) -> tuple[Any, Any]:
        resolved, receipt = await resolve_mini_request_output_tokens(
            self, max_tokens_override
        )
        if receipt is None:
            receipt = current_mini_request_envelope_receipt()
        if receipt is not None:
            if not mini_request_envelope_receipt_is_valid_for(
                receipt,
                self,
                resolved,
            ):
                raise RuntimeError(
                    "Mini request envelope receipt does not match concrete leaf"
            )
            self.last_request_envelope_receipt = receipt.to_record()
            reasoning_effort_override = (
                receipt.effective_reasoning_effort or None
            )
        return resolved, reasoning_effort_override

    def _apply_request_envelope_reasoning_control(
        self,
        payload: Dict[str, Any],
    ) -> bool:
        """Apply the frozen OpenRouter control without catalog re-resolution."""

        receipt = current_mini_request_envelope_receipt()
        if not isinstance(receipt, MiniRequestEnvelopeReceipt):
            return False
        if not base_url_matches_provider(self.base_url, "openrouter"):
            return False
        control = dict(receipt.reasoning_transport_control or {})
        runtime_mandatory_override = bool(
            self._reasoning_disable_rejected
            and control.get("reasoning") == {"enabled": False}
        )
        if runtime_mandatory_override:
            control["reasoning"] = {"effort": "high"}
        for key, value in control.items():
            payload[str(key)] = dict(value) if isinstance(value, Mapping) else value
        self.last_reasoning_control_requested = (
            "high"
            if runtime_mandatory_override
            else str(receipt.effective_reasoning_effort or "")
        )
        reasoning = control.get("reasoning")
        self.last_reasoning_control_sent = (
            dict(reasoning) if isinstance(reasoning, Mapping) else dict(control)
        )
        self.last_reasoning_control_decision = (
            "request_envelope_provider_mandatory_override"
            if runtime_mandatory_override
            else "request_envelope_frozen_control"
        )
        self.last_reasoning_control_required = True
        self.last_reasoning_capability_record = (
            {
                "supports_reasoning": True,
                "supports_max_tokens": False,
                "supports_disable": False,
                "supported_efforts": ["high"],
                "default_enabled": True,
                "mandatory": True,
                "source": "provider_rejection",
            }
            if runtime_mandatory_override
            else dict(receipt.reasoning_capability or {})
        )
        return True

    def _apply_reasoning_effort(
        self,
        payload: Dict[str, Any],
        *,
        reasoning_effort_override: Optional[str] = None,
        max_tokens_override: Optional[int] = None,
        reasoning_control_required: bool = False,
    ) -> None:
        """Attach optional reasoning control for providers that support it."""
        effort = _resolved_reasoning_effort(
            self.cfg,
            reasoning_effort_override,
        )
        if effort is None:
            return
        text = str(effort).strip()
        if not text:
            return
        normalized = text.lower()
        self.last_reasoning_control_requested = normalized
        self.last_reasoning_control_required = bool(reasoning_control_required)
        if base_url_matches_provider(self.base_url, "openrouter"):
            if _deepseek_v4_model(getattr(self.cfg, "model", "")):
                capabilities = lookup_openrouter_reasoning_capabilities(
                    self.base_url,
                    getattr(self.cfg, "model", ""),
                )
                capability_record = (
                    capabilities.to_record() if capabilities is not None else {}
                )
                self.last_reasoning_capability_record = dict(capability_record)
                supports_budget = bool(
                    capabilities is not None
                    and capabilities.supports_max_tokens
                )
                supports_disable = bool(
                    capabilities is not None and capabilities.supports_disable
                )
                if normalized == "none":
                    if supports_disable:
                        control = {"enabled": False}
                        payload["reasoning"] = control
                        self.last_reasoning_control_sent = dict(control)
                        self.last_reasoning_control_decision = (
                            "catalog_advertised_disabled"
                        )
                        return
                    if (
                        mini_openrouter_deepseek_v4_explicit_enable_model(
                            getattr(self.cfg, "model", "")
                        )
                        or _deepseek_v4_model(getattr(self.cfg, "model", ""))
                    ):
                        # Static DeepSeek v4 contract omits supports_disable.
                        # Visibility recovery still has to send enabled=false
                        # or a discarded receipt (int cap + effort none)
                        # raises before HTTP, as on Putnam 1978 A2 215944.
                        # Match the leaf family, not only the alias allowlist:
                        # OpenRouter may rewrite ~flash-latest to a dated id.
                        control = {"enabled": False}
                        payload["reasoning"] = control
                        self.last_reasoning_control_sent = dict(control)
                        self.last_reasoning_control_decision = (
                            "static_deepseek_v4_explicit_disabled"
                        )
                        return
                    self.last_reasoning_control_decision = (
                        "required_disable_not_advertised"
                    )
                    if reasoning_control_required:
                        raise RuntimeError(
                            "required disabled reasoning control is not advertised "
                            f"for OpenRouter model={self.cfg.model}"
                        )
                    return
                # OpenRouter currently advertises only high/xhigh effort for
                # some DeepSeek V4 routes. Sending Mini's low/medium labels
                # does not establish a bound, and max_tokens is legal only
                # when the live catalog explicitly advertises it.
                output_limit = max(
                    1,
                    int(
                        max_tokens_override
                        if max_tokens_override is not None
                        else getattr(self.cfg, "max_tokens", 1) or 1
                    ),
                )
                if output_limit <= 1:
                    if (
                        str(
                            getattr(
                                self.cfg,
                                "reasoning_requested_mode",
                                "",
                            )
                            or ""
                        ).strip().lower()
                        == "on"
                    ):
                        raise RuntimeError(
                            "explicit reasoning-on request needs at least two "
                            "total output tokens for OpenRouter "
                            f"model={self.cfg.model}"
                        )
                    if supports_disable:
                        control = {"enabled": False}
                        payload["reasoning"] = control
                        self.last_reasoning_control_sent = dict(control)
                        self.last_reasoning_control_decision = (
                            "catalog_disabled_for_visible_output_reserve"
                        )
                        return
                    self.last_reasoning_control_decision = (
                        "one_token_disable_not_advertised"
                    )
                    if reasoning_control_required:
                        raise RuntimeError(
                            "required bounded reasoning cannot preserve visible "
                            "output and disabled reasoning is not advertised for "
                            f"OpenRouter model={self.cfg.model}"
                        )
                    return
                if supports_budget:
                    effort_fraction, absolute_ceiling = {
                        "minimal": (0.10, 512),
                        "low": (0.20, 1024),
                        "medium": (0.50, 4096),
                        "high": (0.80, 8192),
                        "max": (0.95, 16384),
                        "xhigh": (0.95, 16384),
                    }.get(normalized, (0.50, 4096))
                    reasoning_limit = max(
                        1,
                        min(
                            absolute_ceiling,
                            int(output_limit * effort_fraction),
                        ),
                    )
                    reasoning_limit = min(reasoning_limit, output_limit - 1)
                    control = {"max_tokens": reasoning_limit}
                    payload["reasoning"] = control
                    self.last_reasoning_control_sent = dict(control)
                    self.last_reasoning_control_decision = (
                        "catalog_advertised_token_budget"
                    )
                    return
                if (
                    str(
                        getattr(self.cfg, "reasoning_requested_mode", "") or ""
                    ).strip().lower()
                    == "on"
                ):
                    from .provider_tool_protocol import (
                        _advertised_reasoning_effort_resolution,
                    )

                    selected, relation = _advertised_reasoning_effort_resolution(
                        normalized,
                        capabilities,
                    )
                    if selected:
                        control = {"effort": selected}
                        payload["reasoning"] = control
                        self.last_reasoning_control_sent = dict(control)
                        self.last_reasoning_control_decision = (
                            "catalog_advertised_effort_" + relation
                        )
                        return
                    if capabilities is not None and (
                        capabilities.default_enabled is True
                        or capabilities.mandatory is True
                    ):
                        control = {"enabled": True}
                        payload["reasoning"] = control
                        self.last_reasoning_control_sent = dict(control)
                        self.last_reasoning_control_decision = (
                            "catalog_explicit_enabled_unbounded"
                        )
                        return
                    if (
                        capabilities is None
                        or capabilities.supports_reasoning is True
                    ) and mini_openrouter_deepseek_v4_explicit_enable_model(
                        getattr(self.cfg, "model", "")
                    ):
                        control = {"enabled": True}
                        payload["reasoning"] = control
                        self.last_reasoning_control_sent = dict(control)
                        self.last_reasoning_control_decision = (
                            "static_deepseek_v4_explicit_enabled"
                        )
                        return
                    self.last_reasoning_control_decision = (
                        "required_reasoning_on_not_advertised"
                    )
                    raise RuntimeError(
                        "explicit reasoning-on has no advertised enabling "
                        f"transport for OpenRouter model={self.cfg.model}"
                    )
                if supports_disable:
                    control = {"enabled": False}
                    payload["reasoning"] = control
                    self.last_reasoning_control_sent = dict(control)
                    self.last_reasoning_control_decision = (
                        "catalog_disabled_without_token_budget"
                    )
                    return
                self.last_reasoning_control_decision = (
                    "required_bound_not_advertised"
                )
                if reasoning_control_required:
                    raise RuntimeError(
                        "required bounded reasoning control is not advertised "
                        f"for OpenRouter model={self.cfg.model}"
                    )
                return
            capabilities = lookup_openrouter_reasoning_capabilities(
                self.base_url,
                getattr(self.cfg, "model", ""),
            )
            if capabilities is not None:
                self.last_reasoning_capability_record = capabilities.to_record()
            mandatory = bool(
                (capabilities is not None and capabilities.mandatory is True)
                or _openrouter_reasoning_mandatory_model(
                    getattr(self.cfg, "model", "")
                )
                or self._reasoning_disable_rejected
            )
            if (
                normalized != "none"
                and str(
                    getattr(self.cfg, "reasoning_requested_mode", "") or ""
                ).strip().lower()
                == "on"
            ):
                if _gpt_oss_120b_model(getattr(self.cfg, "model", "")):
                    selected = "max" if normalized in {"max", "xhigh"} else "high"
                    relation = "static_gpt_oss_contract"
                    self.last_reasoning_capability_record = {
                        "supports_reasoning": True,
                        "supports_max_tokens": False,
                        "supports_disable": False,
                        "supported_efforts": ["high", "max"],
                        "default_enabled": True,
                        "mandatory": True,
                        "source": "static_gpt_oss_contract",
                    }
                else:
                    from .provider_tool_protocol import (
                        _advertised_reasoning_effort_resolution,
                    )

                    selected, relation = _advertised_reasoning_effort_resolution(
                        normalized,
                        capabilities,
                    )
                if not selected:
                    raise RuntimeError(
                        "explicit reasoning-on has no advertised effort "
                        f"transport for OpenRouter model={self.cfg.model}"
                    )
                control = {"effort": selected}
                payload["reasoning"] = control
                self.last_reasoning_control_sent = dict(control)
                self.last_reasoning_control_decision = (
                    "catalog_advertised_effort_" + relation
                )
                return
            if normalized == "none" and mandatory:
                advertised = tuple(
                    effort
                    for effort in (
                        capabilities.supported_efforts
                        if capabilities is not None
                        else ()
                    )
                    if effort != "none"
                )
                gpt_oss_high_required = bool(
                    self._reasoning_disable_rejected
                    or _gpt_oss_120b_model(getattr(self.cfg, "model", ""))
                )
                selected_effort = next(
                    (
                        effort
                        for effort in (
                            ("high", "max", "xhigh", "medium", "low", "minimal")
                            if gpt_oss_high_required
                            else (
                                "minimal",
                                "low",
                                "medium",
                                "high",
                                "max",
                                "xhigh",
                            )
                        )
                        if effort in advertised
                    ),
                    "high" if gpt_oss_high_required else "low",
                )
                if gpt_oss_high_required:
                    selected_effort = "high"
                control = {"effort": selected_effort}
                payload["reasoning"] = control
                self.last_reasoning_control_sent = dict(control)
                self.last_reasoning_control_decision = (
                    "mandatory_openrouter_minimum_effort"
                )
                return
            if normalized == "none":
                control = {"enabled": False}
                payload["reasoning"] = control
            else:
                control = {"effort": normalized}
                payload["reasoning"] = control
            self.last_reasoning_control_sent = dict(control)
            self.last_reasoning_control_decision = "generic_openrouter_control"
            return
        if base_url_matches_provider(self.base_url, "deepseek"):
            if normalized == "none":
                control = {"type": "disabled"}
                payload["thinking"] = control
                self.last_reasoning_control_sent = {"thinking": dict(control)}
                self.last_reasoning_control_decision = (
                    "direct_deepseek_thinking_disabled"
                )
                return
            payload["reasoning_effort"] = text
            self.last_reasoning_control_sent = {"reasoning_effort": text}
            self.last_reasoning_control_decision = (
                "direct_provider_reasoning_effort"
            )
            return
        if not base_url_matches_provider(self.base_url, "openai"):
            return
        payload["reasoning_effort"] = text
        self.last_reasoning_control_sent = {"reasoning_effort": text}
        self.last_reasoning_control_decision = "direct_provider_reasoning_effort"

    def _apply_thinking_mode(self, payload: Dict[str, Any]) -> None:
        """Attach DeepSeek thinking mode when configured.

        DeepSeek v4 defaults to thinking mode. For API compatibility, a config
        value of ``thinking_enabled: false`` must therefore be sent explicitly
        as ``thinking={"type":"disabled"}``; otherwise tool-call conversations
        require reasoning-content replay and sampling controls are ignored.
        """
        if not base_url_matches_provider(self.base_url, "deepseek"):
            return
        if payload.get("thinking") == {"type": "disabled"}:
            return
        thinking = bool(getattr(self.cfg, "thinking_enabled", False))
        is_v4 = _deepseek_v4_model(getattr(self.cfg, "model", ""))
        if not thinking and not is_v4:
            return
        if not thinking and not bool(
            getattr(self.cfg, "reasoning_control_required", False)
        ):
            thinking = True
        payload["thinking"] = {"type": "enabled" if thinking else "disabled"}

    def _record_reasoning_disable_success(self, payload: Mapping[str, Any]) -> None:
        """Cache one successful OpenRouter reasoning-off negotiation."""

        if (
            base_url_matches_provider(self.base_url, "openrouter")
            and payload.get("reasoning") == {"enabled": False}
            and not self._reasoning_disable_rejected
        ):
            self._reasoning_disable_supported = True

    def _build_payload(
        self,
        *,
        messages: List[Dict[str, Any]],
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        max_tokens_override: Optional[int] = None,
        reasoning_effort_override: Optional[str] = None,
        n: Optional[int] = None,
        tools: Optional[List[Dict[str, Any]]] = None,
        tool_choice: Optional[str] = None,
    ) -> Dict[str, Any]:
        effective_reasoning_effort = _resolved_reasoning_effort(
            self.cfg,
            reasoning_effort_override,
        )
        explicit_reasoning_off = (
            str(effective_reasoning_effort or "").strip().lower() == "none"
        )
        preserve_reasoning_content = (
            base_url_matches_provider(self.base_url, "deepseek")
            and (
                bool(getattr(self.cfg, "thinking_enabled", False))
                or (
                    _deepseek_v4_model(getattr(self.cfg, "model", ""))
                    and not bool(
                        getattr(
                            self.cfg,
                            "reasoning_control_required",
                            False,
                        )
                    )
                )
            )
            and not explicit_reasoning_off
        )
        request_messages = _sanitize_request_messages(
            messages,
            preserve_reasoning_content=preserve_reasoning_content,
        )
        _assert_serialized_required_prompt_context(
            messages,
            request_messages,
            preserve_reasoning_content=preserve_reasoning_content,
        )
        payload: Dict[str, Any] = {
            "model": self.cfg.model,
            "messages": request_messages,
        }
        api_default_temperature = is_api_default_temperature_override(
            temperature_override
        )
        requested_temperature = (
            None
            if api_default_temperature
            else (
                float(temperature_override)
                if temperature_override is not None
                else float(self.cfg.temperature)
            )
        )
        self.last_temperature_requested = requested_temperature
        self.last_temperature_sent = None
        self.last_temperature_provider_dropped = False
        self.last_temperature_provider_drop_reason = ""
        self.last_reasoning_control_requested = ""
        self.last_reasoning_control_decision = ""
        self.last_reasoning_control_sent = {}
        self.last_reasoning_control_required = bool(
            reasoning_effort_override is not None
            or getattr(self.cfg, "reasoning_control_required", False)
            or str(getattr(self.cfg, "reasoning_effort", "") or "")
            .strip()
            .lower()
            == "none"
        )
        self.last_reasoning_capability_record = {}
        if api_default_temperature:
            pass
        elif _supports_sampling_controls(
            base_url=self.base_url,
            model=self.cfg.model,
            reasoning_effort=(
                _resolved_reasoning_effort(
                    self.cfg,
                    reasoning_effort_override,
                )
            ),
            thinking_enabled=(
                bool(getattr(self.cfg, "thinking_enabled", False))
                and not explicit_reasoning_off
            ),
        ):
            payload["temperature"] = requested_temperature
            payload["top_p"] = (
                float(top_p_override) if top_p_override is not None else self.cfg.top_p
            )
            self.last_temperature_sent = requested_temperature
        else:
            self.last_temperature_provider_dropped = True
            self.last_temperature_provider_drop_reason = "unsupported_sampling_controls"
        if not self._apply_request_envelope_reasoning_control(payload):
            self._apply_reasoning_effort(
                payload,
                reasoning_effort_override=reasoning_effort_override,
                max_tokens_override=max_tokens_override,
                reasoning_control_required=self.last_reasoning_control_required,
            )
        self._apply_thinking_mode(payload)
        self._apply_token_limit(payload, max_tokens_override=max_tokens_override)
        if self._stop and not _openai_chat_stop_unsupported(
            self.base_url,
            self.cfg.model,
        ):
            payload["stop"] = self._stop
        if n is not None:
            payload["n"] = int(n)
        if tools:
            payload["tools"] = tools
            if tool_choice is not None:
                payload["tool_choice"] = tool_choice
            if (
                self._chat_tools_require_reasoning_effort_none
                and str(payload.get("reasoning_effort") or "").strip().lower()
                != "none"
            ):
                if bool(
                    getattr(self.cfg, "reasoning_control_required", False)
                ):
                    # Sol audit 2026-07-29 F5: an explicitly REQUIRED
                    # reasoning level must never be silently reinterpreted as
                    # 'none'. Internal tool-phase effort requests downgrade
                    # below; a configuration-level requirement fails closed
                    # before dispatch so the operator sees a setup error, not
                    # a quietly weaker model.
                    raise ProviderCapabilityError(
                        "model family requires reasoning_effort='none' with "
                        "function tools on chat completions, but the "
                        "configuration marks reasoning control as required "
                        f"(model={self.cfg.model}); use a family that "
                        "supports tools with reasoning, or drop the "
                        "requirement"
                    )
                # Pre-negotiate the provider constraint instead of paying a
                # deterministic 400: this family accepts tools on chat
                # completions only with the explicit effort string 'none'
                # (omitting the parameter also fails — the default is not
                # 'none').
                payload["reasoning_effort"] = "none"
                payload.pop("reasoning", None)
                self.last_reasoning_control_sent = {"reasoning_effort": "none"}
                self.last_reasoning_control_decision = (
                    "openai_chat_tools_reasoning_effort_forced_none"
                )
        return payload

    def _sampling_metadata_for_payload(
        self,
        payload: Dict[str, Any],
        *,
        temperature_override: Any = None,
    ) -> Dict[str, Any]:
        api_default_temperature = is_api_default_temperature_override(
            temperature_override
        )
        requested_temperature = (
            None
            if api_default_temperature
            else (
                float(temperature_override)
                if temperature_override is not None
                else float(self.cfg.temperature)
            )
        )
        unsupported_drop = "temperature" not in payload
        return {
            "temperature_requested": requested_temperature,
            "temperature_provider_drop_reason": (
                "unsupported_sampling_controls"
                if unsupported_drop and not api_default_temperature
                else ""
            ),
            "reasoning_control_requested": self.last_reasoning_control_requested,
            "reasoning_control_decision": self.last_reasoning_control_decision,
            "reasoning_control_sent": dict(self.last_reasoning_control_sent),
            "reasoning_control_required": bool(
                self.last_reasoning_control_required
            ),
            "reasoning_capability_record": dict(
                self.last_reasoning_capability_record
            ),
        }

    async def _post_with_token_fallback(
        self,
        url: str,
        payload: Dict[str, Any],
        *,
        deadline: Optional[float] = None,
        sampling_metadata: Optional[Dict[str, Any]] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        late_usage_callback: Optional[Any] = None,
        reasoning_control_required_override: bool = False,
    ) -> httpx.Response:
        """POST with fallback for unsupported params (tokens/stop)."""
        current = dict(payload)
        reasoning_control_required = bool(
            reasoning_control_required_override
            or getattr(self.cfg, "reasoning_control_required", False)
        )
        cached_token_limit_swap = ""
        if (
            "max_tokens" in self._unsupported_payload_parameters
            and "max_tokens" in current
            and "max_completion_tokens"
            not in self._unsupported_payload_parameters
        ):
            current["max_completion_tokens"] = current.pop("max_tokens")
            cached_token_limit_swap = "max_tokens->max_completion_tokens"
        elif (
            "max_completion_tokens" in self._unsupported_payload_parameters
            and "max_completion_tokens" in current
            and "max_tokens" not in self._unsupported_payload_parameters
        ):
            current["max_tokens"] = current.pop("max_completion_tokens")
            cached_token_limit_swap = "max_completion_tokens->max_tokens"
        cached_compatibility_drops = sorted(
            key
            for key in self._unsupported_payload_parameters
            if key in current
            and key not in {"max_tokens", "max_completion_tokens"}
        )
        if reasoning_control_required and any(
            key in {"reasoning", "reasoning_effort", "thinking"}
            for key in cached_compatibility_drops
        ):
            raise RuntimeError(
                "required per-call reasoning control is cached as unsupported "
                f"for model={self.cfg.model}"
            )
        for key in cached_compatibility_drops:
            current.pop(key, None)
        removed_stop = False
        removed_temp = False
        removed_top_p = False
        forced_tools_effort_none = False
        enabled_mandatory_reasoning = False
        removed_reasoning_effort = False
        removed_reasoning = False
        removed_thinking = False
        removed_tools = False
        removed_tool_choice = False
        swapped_max = False
        swapped_back = False
        reduced_openrouter_affordability = False
        affordability_metadata: Dict[str, Any] = {}
        for _ in range(8):
            try:
                resp = await self._post_with_retry(
                    url,
                    current,
                    deadline=deadline,
                    request_timeout_override_s=request_timeout_override_s,
                    operation_timeout_override_s=operation_timeout_override_s,
                    late_usage_callback=late_usage_callback,
                )
                metadata = dict(sampling_metadata or {})
                if "temperature_requested" not in metadata:
                    metadata["temperature_requested"] = payload.get("temperature")
                metadata.update(affordability_metadata)
                metadata["provider_compatibility_cached_drops"] = list(
                    cached_compatibility_drops
                )
                metadata["provider_compatibility_cached_token_limit_swap"] = (
                    cached_token_limit_swap
                )
                metadata["provider_compatibility_fallbacks"] = sorted(
                    key
                    for key, removed in (
                        ("stop", removed_stop),
                        ("temperature", removed_temp),
                        ("top_p", removed_top_p),
                        ("reasoning_effort", removed_reasoning_effort),
                        (
                            "tools_reasoning_effort_forced_none",
                            forced_tools_effort_none,
                        ),
                        ("reasoning", removed_reasoning),
                        ("thinking", removed_thinking),
                        ("tools", removed_tools),
                        ("tool_choice", removed_tool_choice),
                    )
                    if removed
                )
                initial_temperature_present = "temperature" in payload
                final_temperature_present = "temperature" in current
                metadata["temperature_sent"] = (
                    current.get("temperature") if final_temperature_present else None
                )
                dropped = bool(
                    removed_temp or "temperature" in cached_compatibility_drops
                )
                reason = (
                    "provider_400_retry"
                    if removed_temp
                    else "provider_capability_cache"
                    if "temperature" in cached_compatibility_drops
                    else ""
                )
                if (
                    not initial_temperature_present
                    and metadata.get("temperature_requested") is not None
                ):
                    dropped = True
                    reason = (
                        str(metadata.get("temperature_provider_drop_reason") or "")
                        or "unsupported_sampling_controls"
                    )
                metadata["temperature_provider_dropped"] = dropped
                metadata["temperature_provider_drop_reason"] = reason
                resp.extensions["ensemble_sampling_controls"] = metadata
                return resp
            except httpx.HTTPStatusError as exc:
                affordable_max_tokens = _openrouter_affordable_max_tokens(exc)
                limit_key, current_limit = _payload_token_limit(current)
                if (
                    not reduced_openrouter_affordability
                    and affordable_max_tokens is not None
                    and limit_key
                    and current_limit is not None
                    and affordable_max_tokens < current_limit
                ):
                    current = dict(current)
                    current[limit_key] = max(1, int(affordable_max_tokens))
                    reduced_openrouter_affordability = True
                    affordability_metadata = {
                        "openrouter_affordability_retry": True,
                        "openrouter_affordability_limit_key": limit_key,
                        "openrouter_affordability_original_max_tokens": int(
                            current_limit
                        ),
                        "openrouter_affordability_retry_max_tokens": int(
                            current[limit_key]
                        ),
                    }
                    continue
                if not removed_stop and _stop_unsupported(exc) and "stop" in current:
                    current = dict(current)
                    current.pop("stop", None)
                    removed_stop = True
                    if _cacheable_unsupported_parameter(exc, "stop"):
                        self._unsupported_payload_parameters.add("stop")
                    continue
                if (
                    not removed_temp
                    and _unsupported_parameter(exc, "temperature")
                    and "temperature" in current
                ):
                    current = dict(current)
                    current.pop("temperature", None)
                    removed_temp = True
                    if _cacheable_unsupported_parameter(exc, "temperature"):
                        self._unsupported_payload_parameters.add("temperature")
                    self.last_temperature_sent = None
                    self.last_temperature_provider_dropped = True
                    self.last_temperature_provider_drop_reason = "provider_400_retry"
                    continue
                if (
                    not removed_top_p
                    and _unsupported_parameter(exc, "top_p")
                    and "top_p" in current
                ):
                    current = dict(current)
                    current.pop("top_p", None)
                    removed_top_p = True
                    if _cacheable_unsupported_parameter(exc, "top_p"):
                        self._unsupported_payload_parameters.add("top_p")
                    continue
                if (
                    not forced_tools_effort_none
                    and "tools" in current
                    and _tools_reasoning_effort_conflict(exc)
                    and str(current.get("reasoning_effort") or "")
                    .strip()
                    .lower()
                    != "none"
                ):
                    if bool(
                        getattr(self.cfg, "reasoning_control_required", False)
                    ):
                        # Sol audit 2026-07-29 F5/R1: never silently downgrade
                        # an explicitly required reasoning level to 'none'.
                        # CACHE the discovered constraint first, so the next
                        # call on this client fails closed BEFORE dispatch
                        # (typed, zero provider requests) instead of paying
                        # the deterministic 400 again.
                        self._chat_tools_require_reasoning_effort_none = True
                        raise ProviderCapabilityError(
                            "model family requires reasoning_effort='none' "
                            "with function tools on chat completions, but "
                            "the configuration marks reasoning control as "
                            f"required (model={self.cfg.model})"
                        ) from exc
                    # The provider's own suggested resolution: keep the tools,
                    # send the explicit effort string 'none'. Dropping the
                    # parameter does NOT help (the family default is not
                    # 'none'), and dropping tools would silently blind the
                    # tool loop. Cache the constraint so subsequent payloads
                    # are pre-negotiated. Internal tool-phase effort requests
                    # (per-call overrides) are downgradable; a configuration-
                    # level requirement is not.
                    current = dict(current)
                    current["reasoning_effort"] = "none"
                    current.pop("reasoning", None)
                    forced_tools_effort_none = True
                    self._chat_tools_require_reasoning_effort_none = True
                    self.last_reasoning_control_sent = {
                        "reasoning_effort": "none"
                    }
                    self.last_reasoning_control_decision = (
                        "openai_chat_tools_reasoning_effort_forced_none"
                    )
                    continue
                if (
                    not enabled_mandatory_reasoning
                    and current.get("reasoning") == {"enabled": False}
                    and _reasoning_disable_rejected(exc)
                ):
                    # Correct only the rejected value and preserve every other
                    # request field, including response_format. Generic JSON
                    # compatibility retry is unrelated to this provider-owned
                    # reasoning constraint.
                    current = dict(current)
                    current["reasoning"] = {"effort": "high"}
                    enabled_mandatory_reasoning = True
                    self._reasoning_disable_rejected = True
                    self.last_reasoning_control_sent = {"effort": "high"}
                    self.last_reasoning_control_decision = (
                        "mandatory_openrouter_minimum_effort"
                    )
                    self.last_reasoning_capability_record = {
                        "supports_reasoning": True,
                        "supports_max_tokens": False,
                        "supports_disable": False,
                        "supported_efforts": ["high"],
                        "default_enabled": True,
                        "mandatory": True,
                        "source": "provider_rejection",
                    }
                    continue
                if (
                    not removed_reasoning_effort
                    and _unsupported_parameter(exc, "reasoning_effort")
                    and "reasoning_effort" in current
                ):
                    if reasoning_control_required:
                        raise
                    current = dict(current)
                    current.pop("reasoning_effort", None)
                    removed_reasoning_effort = True
                    if _cacheable_unsupported_parameter(exc, "reasoning_effort"):
                        self._unsupported_payload_parameters.add("reasoning_effort")
                    continue
                if (
                    not removed_reasoning
                    and _unsupported_parameter(exc, "reasoning")
                    and "reasoning" in current
                ):
                    if reasoning_control_required:
                        raise
                    current = dict(current)
                    current.pop("reasoning", None)
                    removed_reasoning = True
                    if _cacheable_unsupported_parameter(exc, "reasoning"):
                        self._unsupported_payload_parameters.add("reasoning")
                    continue
                if (
                    not removed_thinking
                    and _unsupported_parameter(exc, "thinking")
                    and "thinking" in current
                ):
                    if reasoning_control_required:
                        raise
                    current = dict(current)
                    current.pop("thinking", None)
                    removed_thinking = True
                    if _cacheable_unsupported_parameter(exc, "thinking"):
                        self._unsupported_payload_parameters.add("thinking")
                    continue
                if (
                    not removed_tool_choice
                    and _unsupported_parameter(exc, "tool_choice")
                    and "tool_choice" in current
                ):
                    current = dict(current)
                    current.pop("tool_choice", None)
                    removed_tool_choice = True
                    if _cacheable_unsupported_parameter(exc, "tool_choice"):
                        self._unsupported_payload_parameters.add("tool_choice")
                    continue
                if (
                    not removed_tools
                    and _unsupported_parameter(exc, "tools")
                    and "tools" in current
                ):
                    current = dict(current)
                    current.pop("tools", None)
                    current.pop("tool_choice", None)
                    removed_tools = True
                    removed_tool_choice = True
                    if _cacheable_unsupported_parameter(exc, "tools"):
                        self._unsupported_payload_parameters.update(
                            {"tools", "tool_choice"}
                        )
                        self._tools_capability = False
                    self.last_tool_request_downgraded = True
                    self.last_tool_request_effective = False
                    continue
                if not swapped_max and _max_tokens_unsupported(exc):
                    alt_payload = self._swap_token_limit(
                        current, "max_tokens", "max_completion_tokens"
                    )
                    if alt_payload is not None:
                        current = alt_payload
                        swapped_max = True
                        if _cacheable_unsupported_parameter(exc, "max_tokens"):
                            self._unsupported_payload_parameters.add("max_tokens")
                        continue
                if not swapped_back and _max_completion_tokens_unsupported(exc):
                    alt_payload = self._swap_token_limit(
                        current, "max_completion_tokens", "max_tokens"
                    )
                    if alt_payload is not None:
                        current = alt_payload
                        swapped_back = True
                        if _cacheable_unsupported_parameter(
                            exc,
                            "max_completion_tokens",
                        ):
                            self._unsupported_payload_parameters.add(
                                "max_completion_tokens"
                            )
                        continue
                raise
        return await self._post_with_retry(
            url,
            current,
            deadline=deadline,
            request_timeout_override_s=request_timeout_override_s,
            operation_timeout_override_s=operation_timeout_override_s,
            late_usage_callback=late_usage_callback,
        )

    async def _post_with_retry(
        self,
        url: str,
        payload: Dict[str, Any],
        *,
        deadline: Optional[float] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        late_usage_callback: Optional[Any] = None,
    ) -> httpx.Response:
        """POST with retry/backoff for transient errors (429/5xx/timeouts).

        When *deadline* (a ``time.time()`` value) is set, retries abort early
        if the deadline has passed, preventing retry storms from consuming the
        entire phase budget.
        """
        lane_health_registry = self._provider_lane_health_registry_for_dispatch()
        retryable = {408, 409, 425, 429, 500, 502, 503, 504}
        max_http_retries = 5
        max_json_body_retries = 2
        # Keep long-backoff HTTP status retries at 5, but allow a few extra
        # attempts for transport-level disconnects (e.g., incomplete chunked
        # reads) that are usually short-lived and recover quickly.
        max_transport_retries = self._MAX_TRANSPORT_ATTEMPTS
        backoff = 1.0
        json_body_retries = 0
        operation_started_at = time.time()
        for attempt in range(max(max_http_retries, max_transport_retries)):
            attempt_started_at = time.time()
            dispatch_authority: Dict[str, Any] = {}
            lane_permit: Optional[ProviderLanePermit] = None
            lane_permit_ownership: Optional[ProviderLanePermitOwnership] = None
            post_task: Optional[asyncio.Task[httpx.Response]] = None
            owner_transport_receipt_claimed = False
            try:
                body, meta = self._encode_request_body(payload, url=url)
                headers = dict(self.headers)
                headers.setdefault("Content-Type", "application/json")
                request_timeout: float | None = self._configured_request_timeout_s(
                    request_timeout_override_s
                )
                if deadline:
                    remaining = float(deadline) - time.time()
                    if remaining <= 0.0:
                        raise self._retry_deadline_exception(
                            "LLM request deadline expired before dispatch "
                            f"(attempt={attempt+1}, model={self.cfg.model})",
                            reason="deadline_expired_before_dispatch",
                            attempt=attempt + 1,
                            operation_started_at=operation_started_at,
                            attempt_started_at=attempt_started_at,
                            deadline=deadline,
                            operation_timeout_override_s=operation_timeout_override_s,
                        )
                    cfg_timeout = self._configured_request_timeout_s(
                        request_timeout_override_s
                    )
                    bounded_timeout = (
                        remaining if cfg_timeout is None else min(cfg_timeout, remaining)
                    )
                    if bounded_timeout <= 1e-3:
                        raise self._retry_deadline_exception(
                            "LLM request deadline too close to dispatch safely "
                            f"(attempt={attempt+1}, model={self.cfg.model})",
                            reason="deadline_too_close_before_dispatch",
                            attempt=attempt + 1,
                            operation_started_at=operation_started_at,
                            attempt_started_at=attempt_started_at,
                            deadline=deadline,
                            request_timeout_s=bounded_timeout,
                            operation_timeout_override_s=operation_timeout_override_s,
                        )
                    request_timeout = bounded_timeout
                # This admission check does not cancel or time-box an admitted
                # request.  It only prevents sibling role/client objects from
                # re-probing a serving lane whose authenticated 429 lease is
                # still open.
                lane_permit = lane_health_registry.acquire(
                    self.provider_defer_fingerprint
                )
                lane_permit_ownership = ProviderLanePermitOwnership(
                    lane_health_registry,
                    lane_permit,
                )

                async def _observe_transport_receipt_impl(
                    completed: "asyncio.Task[httpx.Response]",
                    authority: Mapping[str, Any],
                    permit: ProviderLanePermit,
                ) -> None:
                    # This lifecycle task is registered synchronously with the
                    # transport, rather than spawned by its done callback. That
                    # gives close() a durable handshake to await even when task
                    # completion and callback delivery straddle a loop turn.
                    try:
                        response = await asyncio.shield(completed)
                    except BaseException:
                        return
                    response.extensions.setdefault(
                        "ensemble_dispatch_authority", dict(authority)
                    )
                    status_code = int(response.status_code)
                    if 200 <= status_code < 300:
                        lane_health_registry.record_success(permit)
                    await asyncio.sleep(0.01)
                    if self._late_receipt_observer_barrier:
                        return
                    if bool(
                        response.extensions.get(
                            "ensemble_transport_usage_observed"
                        )
                    ):
                        return
                    if 200 <= status_code < 300:
                        try:
                            data = response.json()
                        except Exception:
                            return
                        if (
                            late_usage_callback is not None
                            and not bool(
                                response.extensions.get(
                                    "ensemble_transport_usage_observed"
                                )
                            )
                        ):
                            self._suppressed_unsafe_late_usage_callbacks += 1
                        self._publish_response_usage_once(
                            response,
                            data,
                            None,
                        )
                        return
                    if bool(
                        response.extensions.get(
                            "ensemble_transport_owner_received"
                        )
                    ):
                        # The owner handles 4xx/5xx synchronously through
                        # ``raise_for_status`` and the surrounding error
                        # classifier. Unlike 2xx usage parsing, there is no
                        # later await gap that can lose this rejection.
                        return
                    late_exc = httpx.HTTPStatusError(
                        f"late provider HTTP {status_code}",
                        request=response.request,
                        response=response,
                    )
                    late_classification = classify_llm_exception(late_exc)
                    if (
                        status_code == 429
                        and late_classification.retryable
                        and not late_classification.terminal
                    ):
                        try:
                            provider_retry_after_s = float(
                                response.headers.get("retry-after", "0") or 0.0
                            )
                        except (TypeError, ValueError, OverflowError):
                            provider_retry_after_s = 0.0
                        lane_health_registry.record_rate_limit(
                            permit,
                            provider_retry_after_s=provider_retry_after_s,
                        )
                    affordability = _openrouter_affordable_max_tokens(late_exc)
                    if status_code in {
                        400,
                        401,
                        402,
                        403,
                        404,
                        413,
                        422,
                        429,
                    }:
                        mark_provider_pre_generation_rejection(
                            status_code=status_code,
                            reason=(
                                "openrouter_affordability_retry"
                                if status_code == 402
                                and affordability is not None
                                else "late_provider_rejected_before_generation"
                            ),
                            dispatch_receipt=authority,
                        )

                async def _observe_transport_receipt(
                    completed: "asyncio.Task[httpx.Response]",
                    authority: Mapping[str, Any],
                    permit: ProviderLanePermit,
                    ownership: ProviderLanePermitOwnership,
                ) -> None:
                    try:
                        await _observe_transport_receipt_impl(
                            completed,
                            authority,
                            permit,
                        )
                    finally:
                        # This observer is the authenticated owner of the
                        # detached transport lifecycle.  Keep its lane-map
                        # cleanup here instead of a done-callback lambda that
                        # closes over the whole client and therefore cannot
                        # cross a MiniSession action boundary safely.
                        try:
                            ownership.settle_observer()
                        finally:
                            self._pending_http_lane_ownership.pop(completed, None)

                def _track_post_task(
                    task: "asyncio.Task[httpx.Response]",
                    authority: Mapping[str, Any],
                    permit: ProviderLanePermit,
                    ownership: ProviderLanePermitOwnership,
                ) -> None:
                    self._pending_http_tasks.add(task)
                    self._pending_http_lane_ownership[task] = ownership
                    try:
                        register_transport_request_task(task)
                    except PermissionError:
                        # Registration is an exemption from mutation-boundary
                        # accounting. It must never fail the mathematical call.
                        pass
                    task.add_done_callback(
                        mark_runtime_owned_callback(self._pending_http_tasks.discard)
                    )
                    # An outer search deadline may detach this request owner
                    # while httpx is still unwinding cancellation. Own and
                    # observe the concrete transport task independently.
                    task.add_done_callback(
                        mark_runtime_owned_callback(_consume_task_exception)
                    )
                    observer = asyncio.create_task(
                        _observe_transport_receipt(
                            task,
                            dict(authority),
                            permit,
                            ownership,
                        ),
                        name="openai-transport-receipt-observer",
                    )
                    try:
                        register_transport_receipt_observer_task(observer)
                    except PermissionError:
                        pass
                    self._pending_http_observer_tasks = {
                        pending
                        for pending in self._pending_http_observer_tasks
                        if not pending.done()
                    }
                    self._pending_http_observer_tasks.add(observer)
                    observer.add_done_callback(
                        mark_runtime_owned_callback(_consume_task_exception)
                    )

                if request_timeout is not None:
                    dispatch_authority = await notify_provider_dispatch_observer(
                        candidate_count=max(1, int(payload.get("n", 1) or 1))
                    )
                    mark_provider_dispatched(**dispatch_authority)
                    with transport_request_descendant_scope():
                        post_task = asyncio.create_task(
                            self.client.post(
                                url,
                                content=body,
                                headers=headers,
                                timeout=request_timeout,
                            )
                        )
                    _track_post_task(
                        post_task,
                        dispatch_authority,
                        lane_permit,
                        lane_permit_ownership,
                    )
                    done, _pending = await asyncio.wait(
                        {post_task},
                        timeout=request_timeout,
                    )
                    if post_task not in done:
                        post_task.cancel()
                        cancel_grace = min(
                            0.25,
                            max(0.01, float(request_timeout) * 0.01),
                        )
                        done, _pending = await asyncio.wait(
                            {post_task},
                            timeout=cancel_grace,
                        )
                        if post_task not in done:
                            # Retrying while this request may still generate
                            # would create concurrent duplicate billing.
                            lane_permit_ownership.transfer_to_observer()
                            raise _DetachedTransportTimeout(
                                "provider request detached after hard timeout"
                            )
                        try:
                            resp = post_task.result()
                        except asyncio.CancelledError as exc:
                            raise asyncio.TimeoutError from exc
                    else:
                        resp = post_task.result()
                    resp.extensions["ensemble_transport_owner_received"] = True
                    owner_transport_receipt_claimed = True
                else:
                    dispatch_authority = await notify_provider_dispatch_observer(
                        candidate_count=max(1, int(payload.get("n", 1) or 1))
                    )
                    mark_provider_dispatched(**dispatch_authority)
                    with transport_request_descendant_scope():
                        post_task = asyncio.create_task(
                            self.client.post(
                                url,
                                content=body,
                                headers=headers,
                                # ``request_timeout is None`` can be the result of
                                # an explicit infinite per-call override. Omitting
                                # this argument would re-enable the AsyncClient's
                                # finite construction-time default under a hard
                                # role policy. Pass the resolved unbounded timeout
                                # explicitly while retaining the bounded connect
                                # timeout produced by ``_httpx_timeout``.
                                timeout=self._httpx_timeout(
                                    request_timeout_override_s
                                ),
                            )
                        )
                    _track_post_task(
                        post_task,
                        dispatch_authority,
                        lane_permit,
                        lane_permit_ownership,
                    )
                    resp = await post_task
                    resp.extensions["ensemble_transport_owner_received"] = True
                    owner_transport_receipt_claimed = True
                resp.extensions["ensemble_dispatch_authority"] = dict(
                    dispatch_authority
                )
                resp.raise_for_status()
                lane_health_registry.record_success(lane_permit)
                return resp
            except httpx.HTTPStatusError as exc:
                if bool(
                    getattr(exc, "provider_lane_predispatch_defer", False)
                ):
                    # No transport boundary was crossed.  Preserve the typed
                    # scheduler wait without fabricating a provider dispatch
                    # or multiplying the lane's rejection count.
                    raise
                status = exc.response.status_code
                if status in {400, 401, 402, 403, 404, 413, 422, 429}:
                    mark_provider_pre_generation_rejection(
                        status_code=status,
                        reason=(
                            "unsupported_parameter"
                            if status in {400, 422}
                            else "provider_rejected_before_generation"
                        ),
                        dispatch_receipt=dispatch_authority,
                    )
                classification = classify_llm_exception(exc)
                if classification.terminal:
                    raise
                # Context exceeded is NOT transient - re-raise immediately so caller can truncate
                if _context_exceeded(exc):
                    raise
                if _json_body_parse_error(exc):
                    if json_body_retries < max_json_body_retries:
                        json_body_retries += 1
                        delay = min(
                            2.0, 0.25 * json_body_retries + random.random() * 0.15
                        )
                        if deadline and time.time() + delay >= deadline:
                            raise self._retry_deadline_exception(
                                "LLM retry would exceed deadline after OpenAI "
                                f"JSON-body parse error (attempt={json_body_retries}, "
                                f"model={self.cfg.model})",
                                reason="json_body_parse_error",
                                attempt=json_body_retries,
                                operation_started_at=operation_started_at,
                                attempt_started_at=attempt_started_at,
                                retry_delay_s=delay,
                                deadline=deadline,
                                request_timeout_s=request_timeout,
                                operation_timeout_override_s=operation_timeout_override_s,
                                original_exc=exc,
                            ) from exc
                        await asyncio.sleep(delay)
                        continue
                    raise RuntimeError(
                        "OpenAI rejected a syntactically encoded request body as invalid JSON: "
                        f"model={self.cfg.model} url={url} body_sha256={meta['sha256']} "
                        f"bytes={meta['bytes']} surrogate_replacements="
                        f"{meta['surrogate_replacements']} summary={meta['summary']}"
                    ) from exc
                if status in retryable and classification.retryable:
                    retry_after = exc.response.headers.get("retry-after")
                    if retry_after:
                        try:
                            delay = float(retry_after)
                            retry_after_s: Optional[float] = delay
                        except ValueError:
                            delay = backoff
                            retry_after_s = None
                    else:
                        delay = backoff
                        retry_after_s = None
                    if status == 429:
                        # No generation occurred. Let the scheduler rotate
                        # mathematical work. The run-owned registry compounds
                        # evidence across every role/client on this exact lane,
                        # rather than resetting the ladder at each target.
                        assert lane_permit is not None
                        receipt = (
                            lane_health_registry.record_rate_limit(
                                lane_permit,
                                provider_retry_after_s=(
                                    retry_after_s
                                    if retry_after_s is not None
                                    else 0.0
                                ),
                            )
                        )
                        setattr(
                            exc,
                            "provider_defer_fingerprint",
                            receipt.fingerprint,
                        )
                        setattr(
                            exc,
                            "provider_defer_retry_after_s",
                            receipt.retry_after_s,
                        )
                        setattr(exc, "provider_defer_ready_at", receipt.ready_at)
                        raise
                    if attempt >= max_http_retries - 1:
                        raise
                    # jitter for statuses still retried inside this logical
                    # operation; 429 is deliberately yielded to the scheduler.
                    delay = min(30.0, delay + random.random() * 0.2)
                    if deadline and time.time() + delay >= deadline:
                        raise self._retry_deadline_exception(
                            f"LLM retry would exceed deadline "
                            f"(attempt={attempt+1}, model={self.cfg.model})",
                            reason="http_retry_after"
                            if retry_after_s is not None
                            else "http_retry_backoff",
                            attempt=attempt + 1,
                            operation_started_at=operation_started_at,
                            attempt_started_at=attempt_started_at,
                            retry_delay_s=delay,
                            retry_after_s=retry_after_s,
                            deadline=deadline,
                            request_timeout_s=request_timeout,
                            operation_timeout_override_s=operation_timeout_override_s,
                            original_exc=exc,
                        ) from exc
                    await asyncio.sleep(delay)
                    backoff = min(backoff * 2.0, 30.0)
                    continue
                raise
            except _DetachedTransportTimeout:
                raise _DetachedProviderRequestError(
                    f"LLM chat request detached after hard timeout "
                    f"model={self.cfg.model} url={url} timeout_s={request_timeout}"
                ) from None
            except (
                asyncio.TimeoutError,
                httpx.TimeoutException,
                httpx.RequestError,
            ) as exc:
                if attempt < max_transport_retries - 1:
                    # RemoteProtocolError/incomplete chunked reads are often
                    # brief upstream disconnects: retry quickly first.
                    if isinstance(exc, httpx.RemoteProtocolError):
                        delay = min(2.0, 0.25 * (attempt + 1) + random.random() * 0.25)
                    else:
                        delay = min(30.0, backoff + random.random() * 0.2)
                        backoff = min(backoff * 2.0, 30.0)
                    configured_request_window = self._configured_request_timeout_s(
                        request_timeout_override_s
                    )
                    if (
                        isinstance(
                            exc,
                            (asyncio.TimeoutError, httpx.TimeoutException),
                        )
                        and configured_request_window is not None
                    ):
                        delay = min(
                            delay,
                            configured_request_window
                            * _TRANSPORT_RETRY_MAX_BACKOFF_WINDOW_FRACTION,
                        )
                    retry_window_after_backoff = (
                        float(deadline) - (time.time() + delay)
                        if deadline
                        else None
                    )
                    if (
                        deadline
                        and isinstance(
                            exc,
                            (asyncio.TimeoutError, httpx.TimeoutException),
                        )
                        and configured_request_window is not None
                        and retry_window_after_backoff is not None
                        and not _transport_retry_window_admissible(
                            retry_window_after_backoff_s=retry_window_after_backoff,
                            configured_request_window_s=configured_request_window,
                        )
                    ):
                        raise self._retry_deadline_exception(
                            "LLM deadline cannot admit a timed-request retry "
                            "with only a partial request window "
                            f"(attempt={attempt+1}, model={self.cfg.model})",
                            reason=(
                                "transport_retry_insufficient_request_window"
                            ),
                            attempt=attempt + 1,
                            operation_started_at=operation_started_at,
                            attempt_started_at=attempt_started_at,
                            retry_delay_s=delay,
                            deadline=deadline,
                            request_timeout_s=request_timeout,
                            operation_timeout_override_s=(
                                operation_timeout_override_s
                            ),
                            original_exc=exc,
                        ) from exc
                    if deadline and time.time() + delay >= deadline:
                        raise self._retry_deadline_exception(
                            f"LLM retry would exceed deadline "
                            f"(attempt={attempt+1}, model={self.cfg.model})",
                            reason="transport_retry_backoff",
                            attempt=attempt + 1,
                            operation_started_at=operation_started_at,
                            attempt_started_at=attempt_started_at,
                            retry_delay_s=delay,
                            deadline=deadline,
                            request_timeout_s=request_timeout,
                            operation_timeout_override_s=operation_timeout_override_s,
                            original_exc=exc,
                        ) from exc
                    # Make the ladder visible. Under soft policy the
                    # operation deadline is None, so this can legally repeat
                    # up to _MAX_TRANSPORT_ATTEMPTS times with a full request
                    # window each -- ~8 x 600s for one logical call. Silent,
                    # that is indistinguishable from a hang, and it cost real
                    # diagnosis time.
                    _LOGGER.warning(
                        "llm transport retry %d/%d after %s: model=%s "
                        "request_timeout_s=%s backoff_s=%.2f "
                        "(a full request window restarts on each attempt)",
                        attempt + 1,
                        max_transport_retries,
                        format_exception(exc),
                        self.cfg.model,
                        request_timeout,
                        delay,
                    )
                    await asyncio.sleep(delay)
                    continue
                raise RuntimeError(
                    f"LLM chat request failed ({format_exception(exc)}) "
                    f"model={self.cfg.model} url={url} timeout_s={self.cfg.timeout_s}"
                ) from exc
            finally:
                if lane_permit_ownership is not None:
                    if (
                        lane_permit is not None
                        and lane_permit.half_open_probe
                        and post_task is not None
                        and not owner_transport_receipt_claimed
                    ):
                        # Cancellation can unwind the owner while it awaits
                        # asyncio.wait without consuming a response, including
                        # the race where the concrete task completed in the
                        # same loop turn. Keep the half-open lane reserved
                        # until the independently registered observer claims
                        # and classifies that exact receipt.
                        lane_permit_ownership.transfer_to_observer()
                    lane_permit_ownership.settle_owner()
        raise RuntimeError(
            f"LLM chat request failed after retries: model={self.cfg.model} url={url}"
        )

    async def _chat_request(
        self,
        messages: List[Dict[str, str]],
        response_format: Optional[str] = None,
        *,
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        max_tokens_override: Optional[int] = None,
        reasoning_effort_override: Optional[str] = None,
        deadline: Optional[float] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        tools: Optional[List[Dict[str, Any]]] = None,
        tool_choice: Optional[str] = None,
        usage_callback: Optional[Any] = None,
    ) -> "httpx.Response":
        """Execute the HTTP request for a chat completion (shared by chat/chat_raw)."""
        effective_reasoning_effort = _resolved_reasoning_effort(
            self.cfg,
            reasoning_effort_override,
        )
        if (
            effective_reasoning_effort is not None
            and str(effective_reasoning_effort).strip()
            and base_url_matches_provider(self.base_url, "openrouter")
            and (
                _deepseek_v4_model(getattr(self.cfg, "model", ""))
                or _openrouter_reasoning_mandatory_model(
                    getattr(self.cfg, "model", "")
                )
            )
            and not _gpt_oss_120b_model(getattr(self.cfg, "model", ""))
        ):
            # Capability discovery is an explicit preflight for every routed
            # DeepSeek V4 reasoning request. It does not depend on whether a
            # dollar-budget path happened to refresh pricing first.
            await ensure_openrouter_reasoning_capabilities_async(
                self.base_url,
                getattr(self.cfg, "model", ""),
                deadline=deadline,
            )
        budget = self._effective_prompt_budget(max_tokens_override)
        url = self._chat_url()
        requested_tools = bool(tools)
        self.last_tool_request_effective = False
        self.last_tool_request_downgraded = False
        self.last_tool_request_skipped = bool(
            requested_tools and self._tools_capability is False
        )
        effective_tools = tools
        effective_tool_choice = tool_choice
        if self.last_tool_request_skipped:
            effective_tools = None
            effective_tool_choice = None
        elif _tools_consume_prompt_budget(
            budget,
            effective_tools,
            model=self.cfg.model,
        ):
            effective_tools = None
            effective_tool_choice = None
            self.last_tool_request_skipped = True
            self.last_tool_request_downgraded = True
        current_messages = _trim_messages_to_budget(
            list(messages),
            _message_budget_after_tools(
                budget,
                effective_tools,
                model=self.cfg.model,
            ),
            model=self.cfg.model,
        )

        def _handle_context_overflow(truncation_attempt: int) -> None:
            nonlocal budget, current_messages, effective_tools, effective_tool_choice
            if any(
                _message_has_required_prompt_context(message)
                for message in current_messages
            ):
                envelope = _required_prompt_envelope(current_messages)
                if envelope != current_messages:
                    current_messages = envelope
                    return
                if effective_tools:
                    # Tool availability is useful but is not part of a marked
                    # prompt unit. Preserve the exact selected work and retry
                    # the provider's ordinary no-tools capability once.
                    effective_tools = None
                    effective_tool_choice = None
                    self.last_tool_request_downgraded = True
                    self.last_tool_request_skipped = True
                    return
                raise _required_prompt_overflow(
                    current_messages,
                    available_tokens=budget,
                    model=self.cfg.model,
                )
            truncated = _truncate_messages(
                current_messages,
                keep_last_n=max(1, 4 - truncation_attempt),
            )
            candidate_messages = truncated if truncated is not None else current_messages
            budget = self._tighten_prompt_budget(
                candidate_messages,
                budget,
                truncation_attempt=truncation_attempt,
            )
            next_messages = _trim_messages_to_budget(
                candidate_messages,
                _message_budget_after_tools(
                    budget,
                    effective_tools,
                    model=self.cfg.model,
                ),
                model=self.cfg.model,
            )
            if effective_tools and next_messages == current_messages:
                effective_tools = None
                effective_tool_choice = None
                self.last_tool_request_downgraded = True
                self.last_tool_request_skipped = True
                next_messages = _trim_messages_to_budget(
                    current_messages,
                    budget,
                    model=self.cfg.model,
                )
            current_messages = next_messages

        # Allow up to 3 truncation attempts for context overflow
        for truncation_attempt in range(4):
            payload: Dict[str, Any] = self._build_payload(
                messages=current_messages,
                temperature_override=temperature_override,
                top_p_override=top_p_override,
                max_tokens_override=max_tokens_override,
                reasoning_effort_override=reasoning_effort_override,
                tools=effective_tools,
                tool_choice=effective_tool_choice,
            )
            if response_format == "json":
                payload["response_format"] = {"type": "json_object"}
            sampling_metadata = self._sampling_metadata_for_payload(
                payload,
                temperature_override=temperature_override,
            )
            try:
                resp = await self._post_with_token_fallback(
                    url,
                    payload,
                    deadline=deadline,
                    sampling_metadata=sampling_metadata,
                    request_timeout_override_s=request_timeout_override_s,
                    operation_timeout_override_s=operation_timeout_override_s,
                    late_usage_callback=usage_callback,
                    reasoning_control_required_override=(
                        self.last_reasoning_control_required
                    ),
                )
                if requested_tools and effective_tools:
                    self.last_tool_request_effective = (
                        not self.last_tool_request_downgraded
                    )
                    if self.last_tool_request_effective:
                        self._tools_capability = True
                self._record_reasoning_disable_success(payload)
                return resp
            except httpx.HTTPStatusError as exc:
                if _context_exceeded(exc):
                    # Context overflow: tighten runtime budget aggressively and retry.
                    _handle_context_overflow(truncation_attempt)
                    continue
                if response_format and _unsupported_parameter(
                    exc, "response_format"
                ):
                    if classify_llm_exception(exc).terminal:
                        raise
                    payload.pop("response_format", None)
                    try:
                        resp = await self._post_with_token_fallback(
                            url,
                            payload,
                            deadline=deadline,
                            sampling_metadata=sampling_metadata,
                            request_timeout_override_s=request_timeout_override_s,
                            operation_timeout_override_s=operation_timeout_override_s,
                            late_usage_callback=usage_callback,
                            reasoning_control_required_override=(
                                self.last_reasoning_control_required
                            ),
                        )
                        self._record_reasoning_disable_success(payload)
                        return resp
                    except httpx.HTTPStatusError as inner_exc:
                        if _context_exceeded(inner_exc):
                            _handle_context_overflow(truncation_attempt)
                            continue
                        raise
                    except (httpx.TimeoutException, httpx.RequestError) as inner_exc:
                        raise RuntimeError(
                            f"LLM chat retry failed ({format_exception(inner_exc)}) "
                            f"model={self.cfg.model} url={url} timeout_s={self.cfg.timeout_s}"
                        ) from inner_exc
                raise
        if any(
            _message_has_required_prompt_context(message)
            for message in current_messages
        ):
            raise _required_prompt_overflow(
                current_messages,
                available_tokens=_message_budget_after_tools(
                    budget,
                    effective_tools,
                    model=self.cfg.model,
                ),
                model=self.cfg.model,
            )
        raise RuntimeError(
            f"LLM context exceeded after all truncation attempts: "
            f"model={self.cfg.model} original_messages={len(messages)}"
        )

    def _process_response(
        self,
        resp: "httpx.Response",
        *,
        json_mode: bool = False,
        usage_callback: Optional[Any] = None,
    ) -> tuple:
        """Parse API response into (content_string, raw_data_dict)."""
        data = self._safe_json(resp)
        self._publish_response_usage_once(resp, data, usage_callback)
        self.last_used_model = self.cfg.model
        self.last_used_base_url = self.base_url
        # Detect max_tokens truncation via finish_reason.
        finish_reason = extract_finish_reason(data)
        self.last_truncated = finish_reason == "length"
        self.last_truncated_flags = [self.last_truncated]
        if self.last_truncated:
            self._truncation_count += 1
        content = extract_message_content(data, json_mode=json_mode)
        # Some models occasionally return only <analysis> / <reasoning> blocks (or other
        # non-user-visible formats). If stripping yields empty but raw content is non-empty,
        # fall back to the raw text so higher layers can decide how to handle it.
        stripped = strip_thoughts(content).strip()
        if not stripped and isinstance(content, str) and content.strip():
            return content.strip(), data
        return stripped, data

    @_gated_chat_entrypoint
    async def chat(
        self,
        messages: List[Dict[str, str]],
        response_format: Optional[str] = None,
        *,
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        max_tokens_override: Optional[int] = None,
        reasoning_effort_override: Optional[str] = None,
        deadline: Optional[float] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        usage_callback: Optional[Any] = None,
    ) -> str:
        return await self._chat_unlocked(
            messages,
            response_format,
            temperature_override=temperature_override,
            top_p_override=top_p_override,
            max_tokens_override=max_tokens_override,
            reasoning_effort_override=reasoning_effort_override,
            deadline=deadline,
            request_timeout_override_s=request_timeout_override_s,
            operation_timeout_override_s=operation_timeout_override_s,
            usage_callback=usage_callback,
        )

    async def _chat_unlocked(
        self,
        messages: List[Dict[str, str]],
        response_format: Optional[str] = None,
        *,
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        max_tokens_override: Optional[int] = None,
        reasoning_effort_override: Optional[str] = None,
        deadline: Optional[float] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        usage_callback: Optional[Any] = None,
    ) -> str:
        (
            max_tokens_override,
            reasoning_effort_override,
        ) = await self._resolve_request_output_envelope(
            max_tokens_override,
            reasoning_effort_override,
        )
        deadline = self._operation_deadline(
            deadline,
            operation_timeout_override_s=operation_timeout_override_s,
        )
        resp = await self._chat_request(
            messages,
            response_format,
            temperature_override=temperature_override,
            top_p_override=top_p_override,
            max_tokens_override=max_tokens_override,
            reasoning_effort_override=reasoning_effort_override,
            deadline=deadline,
            request_timeout_override_s=request_timeout_override_s,
            operation_timeout_override_s=operation_timeout_override_s,
            usage_callback=usage_callback,
        )
        text, _data = self._process_response(
            resp,
            json_mode=(response_format == "json"),
            usage_callback=usage_callback,
        )
        return text

    @_gated_chat_entrypoint
    async def chat_raw(
        self,
        messages: List[Dict[str, str]],
        response_format: Optional[str] = None,
        *,
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        max_tokens_override: Optional[int] = None,
        reasoning_effort_override: Optional[str] = None,
        deadline: Optional[float] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        usage_callback: Optional[Any] = None,
    ) -> tuple:
        """Like chat() but returns ``(content_str, raw_data_dict)`` tuple.

        The raw data dict is the full parsed API response, allowing callers
        to inspect ``reasoning_content`` separately from ``content``.
        """
        (
            max_tokens_override,
            reasoning_effort_override,
        ) = await self._resolve_request_output_envelope(
            max_tokens_override,
            reasoning_effort_override,
        )
        deadline = self._operation_deadline(
            deadline,
            operation_timeout_override_s=operation_timeout_override_s,
        )
        effective_reasoning_effort = _resolved_reasoning_effort(
            self.cfg, reasoning_effort_override
        )
        if _openai_responses_with_reasoning(
            self.base_url, effective_reasoning_effort
        ):
            resp = await self._responses_reasoning_request(
                messages,
                response_format=response_format,
                reasoning_effort=str(effective_reasoning_effort),
                max_tokens_override=max_tokens_override,
                deadline=deadline,
                request_timeout_override_s=request_timeout_override_s,
                operation_timeout_override_s=operation_timeout_override_s,
                usage_callback=usage_callback,
            )
        else:
            resp = await self._chat_request(
                messages,
                response_format,
                temperature_override=temperature_override,
                top_p_override=top_p_override,
                max_tokens_override=max_tokens_override,
                reasoning_effort_override=reasoning_effort_override,
                deadline=deadline,
                request_timeout_override_s=request_timeout_override_s,
                operation_timeout_override_s=operation_timeout_override_s,
                usage_callback=usage_callback,
            )
        return self._process_response(
            resp,
            json_mode=(response_format == "json"),
            usage_callback=usage_callback,
        )

    async def _responses_reasoning_request(
        self,
        messages: List[Dict[str, Any]],
        *,
        response_format: Optional[str],
        reasoning_effort: str,
        max_tokens_override: Optional[int],
        deadline: Optional[float],
        request_timeout_override_s: Optional[float],
        operation_timeout_override_s: Optional[float],
        usage_callback: Optional[Any],
    ) -> "httpx.Response":
        """Execute a non-tool reasoning call through OpenAI Responses."""

        token_limit = int(
            max_tokens_override
            if max_tokens_override is not None
            else self.cfg.max_tokens
        )
        current_messages = list(messages)
        if any(
            _message_has_required_prompt_context(message)
            for message in current_messages
        ):
            current_messages = _trim_messages_to_budget(
                current_messages,
                self._effective_prompt_budget(max_tokens_override),
                model=self.cfg.model,
            )
        self.last_reasoning_control_requested = reasoning_effort
        self.last_reasoning_control_decision = "openai_responses_reasoning"
        self.last_reasoning_control_sent = {
            "reasoning": {"effort": reasoning_effort, "summary": "auto"}
        }
        self.last_temperature_sent = None
        self.last_temperature_provider_dropped = True
        self.last_temperature_provider_drop_reason = "responses_api_reasoning"
        resp: Optional[httpx.Response] = None
        for _context_attempt in range(2):
            request_messages = _sanitize_request_messages(
                current_messages,
                preserve_responses_reasoning_items=True,
            )
            _assert_serialized_required_prompt_context(
                current_messages,
                request_messages,
                preserve_responses_reasoning_items=True,
            )
            payload: Dict[str, Any] = {
                "model": self.cfg.model,
                "input": _chat_messages_to_responses_input(request_messages),
                "max_output_tokens": max(1, token_limit),
                "reasoning": {"effort": reasoning_effort, "summary": "auto"},
                # Required for stateless/manual continuation: opaque reasoning
                # state is provider-authored and must be replayed exactly.
                "include": ["reasoning.encrypted_content"],
                "truncation": "disabled",
            }
            if response_format == "json":
                payload["text"] = {"format": {"type": "json_object"}}
            opaque_continuation_required = any(
                isinstance(message, dict)
                and (
                    message.get("_responses_output_items")
                    or message.get("_responses_reasoning_items")
                )
                for message in current_messages
            )
            current = dict(payload)
            if "include" in self._responses_unsupported_parameters:
                if opaque_continuation_required:
                    raise RuntimeError(
                        "provider does not support encrypted reasoning output "
                        "required for opaque Responses continuation"
                    )
                current.pop("include", None)
            retry_with_envelope = False
            for _parameter_attempt in range(2):
                try:
                    resp = await self._post_with_retry(
                        f"{self.base_url}/responses",
                        current,
                        deadline=deadline,
                        request_timeout_override_s=request_timeout_override_s,
                        operation_timeout_override_s=operation_timeout_override_s,
                        late_usage_callback=usage_callback,
                    )
                    break
                except httpx.HTTPStatusError as exc:
                    if (
                        "include" in current
                        and not opaque_continuation_required
                        and _unsupported_parameter(exc, "include")
                    ):
                        current = dict(current)
                        current.pop("include", None)
                        self._responses_unsupported_parameters.add("include")
                        continue
                    if not _context_exceeded(exc) or not any(
                        _message_has_required_prompt_context(message)
                        for message in current_messages
                    ):
                        raise
                    envelope = _required_prompt_envelope(current_messages)
                    if envelope == current_messages:
                        raise _required_prompt_overflow(
                            current_messages,
                            available_tokens=self._effective_prompt_budget(
                                max_tokens_override
                            ),
                            model=self.cfg.model,
                        ) from exc
                    current_messages = envelope
                    retry_with_envelope = True
                    break
            if resp is not None:
                break
            if retry_with_envelope:
                continue
        assert resp is not None
        raw_data = self._safe_json(resp)
        self._publish_response_usage_once(resp, raw_data, usage_callback)
        converted = _responses_payload_to_chat_completion(raw_data)
        normalized = httpx.Response(
            resp.status_code,
            json=converted,
            request=getattr(resp, "request", None),
        )
        normalized.extensions.update(dict(resp.extensions or {}))
        return normalized

    @_gated_chat_entrypoint
    async def chat_with_tools(
        self,
        messages: List[Dict[str, Any]],
        tools: List[Dict[str, Any]],
        *,
        tool_choice: Optional[str] = None,
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        max_tokens_override: Optional[int] = None,
        reasoning_effort_override: Optional[str] = None,
        deadline: Optional[float] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        usage_callback: Optional[Any] = None,
    ) -> tuple:
        """Chat with tool-use support.

        Returns ``(content_str, tool_calls_list)`` where *tool_calls_list*
        is a list of tool-call dicts from the API response (empty when the
        model produces text instead of calling a tool).
        """
        (
            max_tokens_override,
            reasoning_effort_override,
        ) = await self._resolve_request_output_envelope(
            max_tokens_override,
            reasoning_effort_override,
        )
        deadline = self._operation_deadline(
            deadline,
            operation_timeout_override_s=operation_timeout_override_s,
        )
        effective_reasoning_effort = _resolved_reasoning_effort(
            self.cfg,
            reasoning_effort_override,
        )
        if _openai_responses_tools_with_reasoning(
            self.base_url,
            self.cfg.model,
            tools,
            effective_reasoning_effort,
        ):
            resp = await self._responses_tools_request(
                messages,
                tools=tools,
                tool_choice=tool_choice,
                reasoning_effort=str(effective_reasoning_effort or ""),
                max_tokens_override=max_tokens_override,
                deadline=deadline,
                request_timeout_override_s=request_timeout_override_s,
                operation_timeout_override_s=operation_timeout_override_s,
                usage_callback=usage_callback,
            )
        else:
            resp = await self._chat_request(
                messages,
                temperature_override=temperature_override,
                top_p_override=top_p_override,
                max_tokens_override=max_tokens_override,
                reasoning_effort_override=reasoning_effort_override,
                deadline=deadline,
                request_timeout_override_s=request_timeout_override_s,
                operation_timeout_override_s=operation_timeout_override_s,
                tools=tools,
                tool_choice=tool_choice,
                usage_callback=usage_callback,
            )
        content, data = self._process_response(resp, usage_callback=usage_callback)
        self.last_raw_response_data = dict(data) if isinstance(data, dict) else {}
        tool_calls = extract_tool_calls(data)
        return content, tool_calls

    async def _responses_tools_request(
        self,
        messages: List[Dict[str, Any]],
        *,
        tools: List[Dict[str, Any]],
        tool_choice: Optional[str],
        reasoning_effort: str,
        max_tokens_override: Optional[int],
        deadline: Optional[float],
        request_timeout_override_s: Optional[float],
        operation_timeout_override_s: Optional[float],
        usage_callback: Optional[Any],
    ) -> "httpx.Response":
        """Execute a tools-with-reasoning call via the Responses API.

        The response is normalized to the chat-completions shape so the
        shared ``_process_response`` / ``extract_tool_calls`` / usage
        plumbing consumes it unchanged (ModelChain and cost accounting see
        the familiar contract).
        """

        token_limit = (
            int(max_tokens_override)
            if max_tokens_override is not None
            else int(self.cfg.max_tokens)
        )
        current_messages = list(messages)
        if any(
            _message_has_required_prompt_context(message)
            for message in current_messages
        ):
            current_messages = _trim_messages_to_budget(
                current_messages,
                _message_budget_after_tools(
                    self._effective_prompt_budget(max_tokens_override),
                    tools,
                    model=self.cfg.model,
                ),
                model=self.cfg.model,
            )
        self.last_reasoning_control_requested = str(reasoning_effort)
        self.last_reasoning_control_decision = (
            "openai_responses_tools_with_reasoning"
        )
        self.last_reasoning_control_sent = {
            "reasoning": {"effort": str(reasoning_effort)}
        }
        self.last_temperature_sent = None
        self.last_temperature_provider_dropped = True
        self.last_temperature_provider_drop_reason = (
            "responses_api_reasoning"
        )
        # Bounded self-heal for provider parameter drift (audit residual R-C):
        # ``tool_choice`` and the optional encrypted-reasoning include may be
        # dropped on an explicit unsupported-parameter 400.
        # ``reasoning`` is the point of this path (silently dropping it would
        # reintroduce the F5 downgrade), and dropping ``max_output_tokens``
        # would uncap billing — both surface instead, with the provider error
        # message preserved in artifacts.
        resp: Optional[httpx.Response] = None
        for _context_attempt in range(2):
            request_messages = _sanitize_request_messages(
                current_messages,
                preserve_responses_reasoning_items=True,
            )
            _assert_serialized_required_prompt_context(
                current_messages,
                request_messages,
                preserve_responses_reasoning_items=True,
            )
            payload: Dict[str, Any] = {
                "model": self.cfg.model,
                "input": _chat_messages_to_responses_input(request_messages),
                "max_output_tokens": max(1, token_limit),
                "reasoning": {"effort": str(reasoning_effort)},
                "include": ["reasoning.encrypted_content"],
                "tools": [_chat_tool_to_responses_tool(tool) for tool in tools],
            }
            if tool_choice is not None:
                payload["tool_choice"] = tool_choice
            current = dict(payload)
            opaque_continuation_required = any(
                isinstance(message, dict)
                and (
                    message.get("_responses_output_items")
                    or message.get("_responses_reasoning_items")
                )
                for message in current_messages
            )
            for cached_drop in self._responses_unsupported_parameters:
                if cached_drop == "include" and opaque_continuation_required:
                    raise RuntimeError(
                        "provider does not support encrypted reasoning output "
                        "required for opaque Responses continuation"
                    )
                current.pop(cached_drop, None)
            retry_with_envelope = False
            for _parameter_attempt in range(2):
                try:
                    resp = await self._post_with_retry(
                        f"{self.base_url}/responses",
                        current,
                        deadline=deadline,
                        request_timeout_override_s=request_timeout_override_s,
                        operation_timeout_override_s=operation_timeout_override_s,
                        late_usage_callback=usage_callback,
                    )
                    break
                except httpx.HTTPStatusError as exc:
                    if _context_exceeded(exc) and any(
                        _message_has_required_prompt_context(message)
                        for message in current_messages
                    ):
                        envelope = _required_prompt_envelope(current_messages)
                        if envelope == current_messages:
                            raise _required_prompt_overflow(
                                current_messages,
                                available_tokens=_message_budget_after_tools(
                                    self._effective_prompt_budget(max_tokens_override),
                                    tools,
                                    model=self.cfg.model,
                                ),
                                model=self.cfg.model,
                            ) from exc
                        current_messages = envelope
                        retry_with_envelope = True
                        break
                    if (
                        "include" in current
                        and not opaque_continuation_required
                        and _unsupported_parameter(exc, "include")
                    ):
                        current = dict(current)
                        current.pop("include", None)
                        self._responses_unsupported_parameters.add("include")
                        continue
                    if (
                        "tool_choice" in current
                        and "tool_choice" not in self._responses_unsupported_parameters
                        and _unsupported_parameter(exc, "tool_choice")
                    ):
                        current = dict(current)
                        current.pop("tool_choice", None)
                        self._responses_unsupported_parameters.add("tool_choice")
                        continue
                    raise
            if resp is not None:
                break
            if retry_with_envelope:
                continue
        assert resp is not None
        raw_data = self._safe_json(resp)
        # Claim usage on the original transport response before wrapping it.
        # Publishing only from the chat-normalized copy loses Responses-only
        # cache details and leaves the original looking unclaimed to the
        # detached transport observer, which then invents a second dispatch
        # and publishes duplicate late usage.
        self._publish_response_usage_once(resp, raw_data, usage_callback)
        converted = _responses_payload_to_chat_completion(raw_data)
        normalized = httpx.Response(
            resp.status_code,
            json=converted,
            request=getattr(resp, "request", None),
        )
        normalized.extensions.update(dict(resp.extensions or {}))
        return normalized

    @_gated_chat_entrypoint
    async def chat_n(
        self,
        messages: List[Dict[str, str]],
        n: int = 1,
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        *,
        max_tokens_override: Optional[int] = None,
        deadline: Optional[float] = None,
        usage_callback: Optional[Any] = None,
    ) -> List[str]:
        """Generate *n* completions for the same prompt.

        Tries the OpenAI ``n`` parameter first (single request). Falls back
        to sequential single requests if the server rejects it or returns
        fewer than *n* choices.
        """
        max_tokens_override, _unused_reasoning_effort = (
            await self._resolve_request_output_envelope(
                max_tokens_override,
                None,
            )
        )
        deadline = self._operation_deadline(deadline)
        if n <= 1:
            return [
                await self._chat_unlocked(
                    messages,
                    temperature_override=temperature_override,
                    top_p_override=top_p_override,
                    max_tokens_override=max_tokens_override,
                    deadline=deadline,
                    usage_callback=usage_callback,
                )
            ]

        budget = self._effective_prompt_budget(max_tokens_override)
        current_messages = _trim_messages_to_budget(
            list(messages), budget, model=self.cfg.model
        )
        url = self._chat_url()

        # Allow up to 3 truncation attempts for context overflow
        for truncation_attempt in range(4):
            payload: Dict[str, Any] = self._build_payload(
                messages=current_messages,
                temperature_override=temperature_override,
                top_p_override=top_p_override,
                max_tokens_override=max_tokens_override,
            )

            collected: List[str] = []
            trunc_flags: List[bool] = []
            errors: List[BaseException] = []
            context_exceeded_seen = False

            # Attempt 1: use OpenAI-style `n` if the backend supports it.
            payload_with_n = self._build_payload(
                messages=current_messages,
                temperature_override=temperature_override,
                top_p_override=top_p_override,
                max_tokens_override=max_tokens_override,
                n=n,
            )
            sampling_metadata_n = self._sampling_metadata_for_payload(
                payload_with_n,
                temperature_override=temperature_override,
            )
            try:
                resp = await self._post_with_token_fallback(
                    url,
                    payload_with_n,
                    deadline=deadline,
                    sampling_metadata=sampling_metadata_n,
                    late_usage_callback=usage_callback,
                )
                data = self._safe_json(resp)
                self._publish_response_usage_once(resp, data, usage_callback)
                choices = data.get("choices", [])
                if isinstance(choices, list) and choices:
                    for c in choices:
                        fr = str(c.get("finish_reason", "") or "")
                        is_trunc = fr == "length"
                        content = extract_message_content({"choices": [c]})
                        if content:
                            stripped = strip_thoughts(content).strip()
                            collected.append(stripped if stripped else content.strip())
                            trunc_flags.append(is_trunc)
                            if is_trunc:
                                self._truncation_count += 1
            except httpx.HTTPStatusError as exc:
                if _context_exceeded(exc):
                    context_exceeded_seen = True
                elif classify_llm_exception(exc).terminal:
                    raise
                errors.append(exc)
            except Exception as exc:
                if classify_llm_exception(exc).terminal:
                    raise
                errors.append(exc)

            # If context exceeded on attempt 1, try truncation before fallback
            if context_exceeded_seen and not collected:
                if any(
                    _message_has_required_prompt_context(message)
                    for message in current_messages
                ):
                    envelope = _required_prompt_envelope(current_messages)
                    if envelope == current_messages:
                        raise _required_prompt_overflow(
                            current_messages,
                            available_tokens=budget,
                            model=self.cfg.model,
                        )
                    current_messages = envelope
                    continue
                truncated = _truncate_messages(
                    current_messages,
                    keep_last_n=max(1, 4 - truncation_attempt),
                )
                candidate_messages = (
                    truncated if truncated is not None else current_messages
                )
                budget = self._tighten_prompt_budget(
                    candidate_messages,
                    budget,
                    truncation_attempt=truncation_attempt,
                )
                current_messages = _trim_messages_to_budget(
                    candidate_messages,
                    budget,
                    model=self.cfg.model,
                )
                continue

            # Attempt 2: parallel single requests for remaining completions (rate limited).
            remaining = max(0, int(n) - len(collected))
            if remaining:
                single_payload = dict(payload)
                sampling_metadata_single = self._sampling_metadata_for_payload(
                    single_payload,
                    temperature_override=temperature_override,
                )
                is_openai = base_url_matches_provider(self.base_url, "openai")

                async def _single_request() -> Optional[tuple]:
                    async with self._request_sem:
                        resp = await self._post_with_token_fallback(
                            url,
                            single_payload,
                            deadline=deadline,
                            sampling_metadata=sampling_metadata_single,
                            late_usage_callback=usage_callback,
                        )
                        sr_data = self._safe_json(resp)
                        self._publish_response_usage_once(
                            resp,
                            sr_data,
                            usage_callback,
                        )
                        fr = extract_finish_reason(sr_data)
                        is_trunc = fr == "length"
                        content = extract_message_content(sr_data)
                        if not content:
                            return None
                        stripped = strip_thoughts(content).strip()
                        text = stripped if stripped else content.strip()
                        return (text, is_trunc)

                results: list[tuple[Any, ...] | BaseException | None] = []
                if is_openai:
                    # Sequential requests are less likely to hit rate limits.
                    for _ in range(remaining):
                        try:
                            results.append(await _single_request())
                        except httpx.HTTPStatusError as exc:
                            if _context_exceeded(exc):
                                context_exceeded_seen = True
                            elif classify_llm_exception(exc).terminal:
                                raise
                            results.append(exc)
                        except Exception as exc:
                            if classify_llm_exception(exc).terminal:
                                raise
                            results.append(exc)
                else:
                    results = await asyncio.gather(
                        *(_single_request() for _ in range(remaining)),
                        return_exceptions=True,
                    )
                for r in results:
                    if isinstance(r, BaseException):
                        if isinstance(r, httpx.HTTPStatusError) and _context_exceeded(
                            r
                        ):
                            context_exceeded_seen = True
                        elif classify_llm_exception(r).terminal:
                            raise r
                        errors.append(r)
                    elif r:
                        text, is_trunc = r
                        collected.append(text)
                        trunc_flags.append(is_trunc)
                        if is_trunc:
                            self._truncation_count += 1

            if collected:
                self.last_used_model = self.cfg.model
                self.last_used_base_url = self.base_url
                self.last_truncated_flags = trunc_flags[:n]
                self.last_truncated = any(self.last_truncated_flags)
                return collected[:n]

            # All failed - if context exceeded, try truncation
            if context_exceeded_seen:
                if any(
                    _message_has_required_prompt_context(message)
                    for message in current_messages
                ):
                    envelope = _required_prompt_envelope(current_messages)
                    if envelope == current_messages:
                        raise _required_prompt_overflow(
                            current_messages,
                            available_tokens=budget,
                            model=self.cfg.model,
                        )
                    current_messages = envelope
                    continue
                truncated = _truncate_messages(
                    current_messages,
                    keep_last_n=max(1, 4 - truncation_attempt),
                )
                candidate_messages = (
                    truncated if truncated is not None else current_messages
                )
                budget = self._tighten_prompt_budget(
                    candidate_messages,
                    budget,
                    truncation_attempt=truncation_attempt,
                )
                current_messages = _trim_messages_to_budget(
                    candidate_messages,
                    budget,
                    model=self.cfg.model,
                )
                continue

            # Non-context errors - raise
            tail = (
                ", ".join(format_exception(e) for e in errors[-3:])
                if errors
                else "unknown error"
            )
            raise RuntimeError(
                f"LLM chat_n failed: model={self.cfg.model} url={url} timeout_s={self.cfg.timeout_s} "
                f"errors=[{tail}]"
            ) from (errors[-1] if errors else None)

        # Exhausted truncation attempts
        if any(
            _message_has_required_prompt_context(message)
            for message in current_messages
        ):
            raise _required_prompt_overflow(
                current_messages,
                available_tokens=budget,
                model=self.cfg.model,
            )
        raise RuntimeError(
            f"LLM chat_n context exceeded after all truncation attempts: "
            f"model={self.cfg.model} original_messages={len(messages)}"
        )

    async def close(self) -> None:
        def _fence_unresolved_half_open_lanes(
            unresolved: set[asyncio.Task[Any]],
        ) -> None:
            try:
                lease_s = float(
                    getattr(
                        self.cfg,
                        "provider_lane_abandonment_lease_s",
                        300.0,
                    )
                    or 300.0
                )
            except (TypeError, ValueError, OverflowError):
                lease_s = 300.0
            for transport_task in unresolved:
                ownership = self._pending_http_lane_ownership.pop(
                    transport_task,
                    None,
                )
                if ownership is None or not ownership.permit.half_open_probe:
                    continue
                ownership.registry.record_unresolved_abandonment(
                    ownership.permit,
                    lease_s=lease_s,
                )

        async def _quiesce() -> tuple[
            Optional[BaseException],
            int,
            Optional[BaseException],
        ]:
            underlying_close_error: Optional[BaseException] = None
            try:
                try:
                    await self.client.aclose()
                except BaseException as exc:
                    # An HTTP-pool close error cannot bypass ownership cleanup.
                    underlying_close_error = exc
                # Outer proof-search deadlines may have detached a request
                # while its transport was unwinding cancellation. Never leave
                # those tasks for asyncio.run shutdown to reap.
                for _ in range(8):
                    await asyncio.sleep(0)
                    pending = {
                        task
                        for task in self._pending_http_tasks
                        if not task.done()
                    }
                    if not pending:
                        break
                    for task in pending:
                        task.cancel()
                    done, _still_pending = await asyncio.wait(
                        pending,
                        timeout=0.25,
                    )
                    for task in done:
                        _consume_task_exception(task)
                # Every transport pre-registers its receipt lifecycle at
                # dispatch, so quiescence is a structural two-part handshake.
                unresolved = {
                    task
                    for task in self._pending_http_tasks
                    if not task.done()
                }
                if unresolved:
                    # Failed close is a hard accounting boundary. The owning
                    # CostBudgetController retains conservative exposure. A
                    # run-local lane retirement must precede observer
                    # cancellation or its finally hook would release a live
                    # half-open task. A later theorem gets a fresh registry.
                    _fence_unresolved_half_open_lanes(unresolved)
                    self._late_receipt_observer_barrier = True
                    observers = {
                        task
                        for task in self._pending_http_observer_tasks
                        if not task.done()
                    }
                    for observer in observers:
                        observer.cancel()
                    if observers:
                        await asyncio.gather(*observers, return_exceptions=True)
                    return underlying_close_error, len(unresolved), None
                # Publish every definitive receipt before final accounting.
                observers = {
                    task
                    for task in self._pending_http_observer_tasks
                    if not task.done()
                }
                if observers:
                    await asyncio.gather(*observers, return_exceptions=True)
                self._late_receipt_observer_barrier = True
                return underlying_close_error, 0, None
            except BaseException as cleanup_error:
                # No exceptional cleanup path may leave callbacks live behind
                # a caller that is proceeding to freeze final accounting.
                self._late_receipt_observer_barrier = True
                for task in self._pending_http_tasks:
                    if not task.done():
                        task.cancel()
                unresolved = {
                    task
                    for task in self._pending_http_tasks
                    if not task.done()
                }
                _fence_unresolved_half_open_lanes(unresolved)
                observers = {
                    task
                    for task in self._pending_http_observer_tasks
                    if not task.done()
                }
                for observer in observers:
                    observer.cancel()
                if observers:
                    await asyncio.gather(*observers, return_exceptions=True)
                unresolved_count = len(unresolved)
                return underlying_close_error, unresolved_count, cleanup_error

        # Caller cancellation must be preserved, but it cannot interrupt the
        # ownership transition that makes post-summary callbacks impossible.
        quiescence_task = asyncio.create_task(_quiesce())
        caller_cancellation: Optional[asyncio.CancelledError] = None
        while True:
            try:
                result = await asyncio.shield(quiescence_task)
                break
            except asyncio.CancelledError as exc:
                if caller_cancellation is None:
                    caller_cancellation = exc
                continue
        underlying_close_error, unresolved_count, cleanup_error = result
        self._pending_http_tasks = {
            task for task in self._pending_http_tasks if not task.done()
        }
        self._pending_http_observer_tasks = {
            task
            for task in self._pending_http_observer_tasks
            if not task.done()
        }
        self._pending_http_lane_ownership = {
            task: ownership
            for task, ownership in self._pending_http_lane_ownership.items()
            if not task.done()
        }
        if caller_cancellation is not None:
            raise caller_cancellation
        if cleanup_error is not None:
            if not isinstance(cleanup_error, Exception):
                raise cleanup_error
            raise RuntimeError(
                "provider transport cleanup failed behind accounting barrier"
            ) from cleanup_error
        if unresolved_count:
            for task in tuple(self._pending_http_tasks):
                detach_future_from_asyncio_run_shutdown(task)
            error = RuntimeError(
                "provider transport close left "
                f"{unresolved_count} unresolved request task(s)"
            )
            if underlying_close_error is not None:
                raise error from underlying_close_error
            raise error
        if underlying_close_error is not None:
            if not isinstance(underlying_close_error, Exception):
                raise underlying_close_error
            raise RuntimeError(
                "provider HTTP client close failed after transport cleanup"
            ) from underlying_close_error


async def get_json(
    client: LLMChatClientProtocol,
    messages: List[Dict[str, str]],
    *,
    temperature_override: Any = None,
    top_p_override: Optional[float] = None,
    max_tokens_override: Optional[int] = None,
    deadline: Optional[float] = None,
    usage_callback: Optional[Any] = None,
) -> Dict[str, Any]:
    def _mark_truncated(result: Dict[str, Any]) -> Dict[str, Any]:
        if not was_truncated:
            return result
        tagged = dict(result)
        tagged["_truncated"] = True
        return tagged

    def _non_object_result(raw_text: str) -> Dict[str, Any]:
        obj_text = extract_json_object(raw_text)
        if obj_text:
            try:
                parsed_obj = json.loads(obj_text)
            except json.JSONDecodeError:
                parsed_obj = None
            if isinstance(parsed_obj, dict):
                return _mark_truncated(parsed_obj)
        return _mark_truncated({"_raw": raw_text, "_error": "json_not_object"})

    chat_kwargs: Dict[str, Any] = {
        "response_format": "json",
        "temperature_override": temperature_override,
        "top_p_override": top_p_override,
        "max_tokens_override": max_tokens_override,
        "deadline": deadline,
    }
    if usage_callback is not None:
        chat_kwargs["usage_callback"] = usage_callback
    try:
        raw = await client.chat(messages, **chat_kwargs)
    except TypeError as exc:
        text = str(exc)
        unexpected_usage_callback = (
            "unexpected keyword argument 'usage_callback'" in text
            or "got an unexpected keyword argument 'usage_callback'" in text
        )
        if "usage_callback" not in chat_kwargs or not unexpected_usage_callback:
            raise
        chat_kwargs.pop("usage_callback", None)
        raw = await client.chat(
            messages,
            **chat_kwargs,
        )
    was_truncated = getattr(client, "last_truncated", False)
    try:
        result = json.loads(raw)
        if isinstance(result, dict):
            return _mark_truncated(result)
        return _non_object_result(raw)
    except json.JSONDecodeError:
        candidates = extract_json_candidates(raw)
        if not candidates:
            return _mark_truncated({"_raw": raw, "_error": "json_parse_failed"})
        for cand in candidates:
            try:
                result = json.loads(cand)
                if isinstance(result, dict):
                    return _mark_truncated(result)
            except json.JSONDecodeError:
                continue
        return _mark_truncated({"_raw": raw, "_error": "json_parse_failed"})


def extract_message_content(payload: Dict[str, Any], *, json_mode: bool = False) -> str:
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices:
        return ""
    choice = choices[0]
    msg = choice.get("message") or {}
    content = msg.get("content")
    if isinstance(content, str) and content.strip():
        return content
    if isinstance(content, list):
        parts: List[str] = []
        for part in content:
            if not isinstance(part, dict):
                continue
            ptype = part.get("type")
            if ptype in {"text", "output_text"}:
                text = part.get("text")
                if isinstance(text, str):
                    parts.append(text)
        if parts:
            return "".join(parts)
    # DeepSeek-Reasoner puts chain-of-thought in reasoning_content.
    # Do NOT fall back to it here — reasoning_content is informal NL that
    # poisons proof candidates when returned for prover/refiner calls.
    # Planner reasoning is extracted separately via _get_reasoning_content()
    # in orchestrator.py which reads the raw API payload directly.
    # Return empty content string for backward compatibility.
    if isinstance(content, str):
        return content
    # OpenAI-style refusals can populate a separate field.
    refusal = msg.get("refusal")
    if isinstance(refusal, str) and refusal.strip():
        return refusal
    text = msg.get("text")
    if isinstance(text, str):
        return text
    if isinstance(choice.get("text"), str):
        return choice["text"]
    return ""


def extract_finish_reason(payload: Dict[str, Any]) -> str:
    """Extract finish_reason from the first choice in an API response.

    Returns ``"length"`` when the LLM hit ``max_tokens`` and truncated,
    ``"stop"`` on normal completion, or ``""`` if unavailable.
    """
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices:
        return ""
    return str(choices[0].get("finish_reason", "") or "")


def extract_tool_calls(payload: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Extract tool_calls from the first choice in an API response.

    Returns a list of tool-call dicts (each with ``id``, ``type``,
    ``function.name``, ``function.arguments``), or an empty list when
    the model produced text content instead of calling a tool.
    """
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices:
        return []
    msg = choices[0].get("message")
    if not isinstance(msg, dict):
        return []
    structured = normalize_tool_calls(msg.get("tool_calls"))
    if structured:
        return structured
    return extract_dsml_tool_calls(msg.get("content"))
