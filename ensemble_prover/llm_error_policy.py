"""Shared LLM error classification for retry and terminal-failure policy."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from typing import Any, Iterable, Mapping, Optional

from .dispatch_exception_projection import (
    dispatch_exception_projection,
    dispatch_exception_projection_is_canonical,
)
from .llm_usage import CostBudgetExceeded, ProviderDispatchAttemptLimitExceeded


_TRANSIENT_HTTP_STATUSES = {408, 409, 425, 429, 500, 502, 503, 504}
_FATAL_QUOTA_MARKERS = {
    "insufficient_quota",
    "quota_exceeded",
    "billing_hard_limit_reached",
}
_FATAL_AUTH_MARKERS = {
    "invalid_api_key",
    "incorrect_api_key",
    "expired_api_key",
    "missing_api_key",
}
_FATAL_BILLING_MARKERS = {
    "billing_not_active",
    "billing_hard_limit_reached",
    "account_deactivated",
}
_FATAL_QUOTA_PHRASES = (
    "exceeded your current quota",
    "exceeded current quota",
    "exceeded your quota",
    "quota exhausted",
    "quota has been exhausted",
    "insufficient quota",
    "out of quota",
    "insufficient credits",
    "insufficient balance",
    "requires more credits",
    "require more credits",
    "add credits",
    "can only afford",
)
_FATAL_BILLING_PHRASES = (
    "billing is not active",
    "billing not active",
    "billing has not been activated",
    "billing is disabled",
    "set up billing",
    "activate billing",
)
_TERMINAL_LLM_FAILURE_REASONS = {
    "llm_auth_error",
    "llm_billing_error",
    "llm_cost_budget_exhausted",
    "llm_cost_budget_unknown_pricing",
    "llm_insufficient_quota",
    "provider_capability_conflict",
    "llm_required_prompt_context_overflow",
}
_SCOPED_LLM_FAILURE_REASONS = {
    "llm_network_error",
    "llm_retry_deadline_exhausted",
    "provider_dispatch_attempt_limit_exhausted",
    "provider_lane_run_closed",
    "selected_proof_idea_context_invalidated",
}
_SCOPED_CONTROLLER_FAILURE_REASONS = {
    # A poisoned MiniSession remains terminal and non-reusable.  When that
    # session belongs to one isolated recursive child, however, its authority
    # does not extend to sibling claims or the parent controller.  Preserve
    # the diagnostic while letting the parent continue independent work.
    "mini_dispatch_mutation_boundary_violation",
    "mini_dispatch_primary_failure",
}
_TERMINAL_SESSION_FAILURE_REASONS = {
    "falsification_trust_boundary_conflict",
    "mini_recursive_planner_prompt_error",
    "mini_session_action_exception",
    "root_disproved_by_audited_lean_certificate",
}
_HTTP_TRANSPORT_TIMEOUT_NAMES = {
    "ConnectTimeout",
    "PoolTimeout",
    "ReadTimeout",
    "WriteTimeout",
    "TimeoutException",
}
_RUNTIME_TRANSPORT_OWNERSHIP_MARKERS = (
    "runtime request ownership requires",
    "runtime receipt ownership requires",
)
_TOOL_TRANSCRIPT_STRONG_MARKERS = (
    "tool transcript",
    "tool message",
    "tool messages",
    "tool response",
    "tool responses",
    "tool result",
    "tool results",
    "messages with role 'tool'",
    "messages with role tool",
)
_TOOL_TRANSCRIPT_GENERIC_MARKERS = (
    "tool calls",
    "tool_calls",
)
_TOOL_TRANSCRIPT_REQUEST_ERROR_PHRASES = (
    "bad request",
    "invalid",
    "malformed",
    "must be followed by tool messages",
    "messages with role 'tool'",
    "messages with role tool",
)
_TOOL_REQUEST_PARAMETER_ERROR_PHRASES = (
    "unknown parameter",
    "unsupported parameter",
    "unrecognized parameter",
    "unrecognised parameter",
    "invalid parameter",
    "unexpected parameter",
    "unknown field",
    "unrecognized field",
    "unrecognised field",
    "not a valid parameter",
    "request option",
    "unknown option",
    "unrecognized option",
    "unrecognised option",
    "invalid option",
    "request argument",
    "unknown argument",
    "unrecognized argument",
    "unrecognised argument",
)
_TOOL_CAPABILITY_UNSUPPORTED_PHRASES = (
    "not supported",
    "unsupported",
    "does not support",
    "do not support",
    "don't support",
    "no support for",
    "disabled",
    "not enabled",
    "unavailable",
    "not allowed",
    "disallowed",
    "not permitted",
    "forbidden",
)


@dataclass(frozen=True)
class LLMErrorClassification:
    """Normalized retry/terminal decision for one provider failure."""

    kind: str
    retryable: bool
    terminal: bool
    failure_reason: str = ""
    status_code: int = 0
    provider_error_type: str = ""
    provider_error_code: str = ""
    message: str = ""


def _lower_text(value: Any) -> str:
    return str(value or "").strip().lower()


def _runtime_transport_ownership_classification(
    message: str,
) -> Optional[LLMErrorClassification]:
    text = _lower_text(message)
    if not any(marker in text for marker in _RUNTIME_TRANSPORT_OWNERSHIP_MARKERS):
        return None
    return LLMErrorClassification(
        kind="transport",
        retryable=True,
        terminal=False,
        failure_reason="llm_network_error",
        message=str(message or ""),
    )


def _error_mapping_from_json(data: Any) -> Mapping[str, Any]:
    if not isinstance(data, Mapping):
        return {}
    err = data.get("error")
    if isinstance(err, Mapping):
        return err
    return data


def _response_error_mapping(exc: BaseException) -> Mapping[str, Any]:
    response = getattr(exc, "response", None)
    if response is None:
        return {}
    try:
        return _error_mapping_from_json(response.json())
    except Exception:
        pass
    try:
        text = str(getattr(response, "text", "") or "").strip()
    except Exception:
        text = ""
    if not text:
        return {}
    try:
        return _error_mapping_from_json(json.loads(text))
    except Exception:
        return {"message": text}


def _response_status(exc: BaseException) -> int:
    try:
        return int(getattr(getattr(exc, "response", None), "status_code", 0) or 0)
    except Exception:
        return 0


def _is_tool_request_parameter_error(message: str) -> bool:
    msg = _lower_text(message)
    has_tool_call_collection = "tool_calls" in msg or "tool calls" in msg
    has_tool_call_key = "tool_call_id" in msg or "tool call id" in msg
    has_tool_response_id = bool(
        re.search(r"\btool\s+(?:message|response|result)\s+id\b", msg)
    )
    if not (has_tool_call_collection or has_tool_call_key or has_tool_response_id):
        return False
    if "parallel_tool_calls" in msg:
        return True
    if any(phrase in msg for phrase in _TOOL_REQUEST_PARAMETER_ERROR_PHRASES):
        return True
    has_schema_shape_error = bool(
        re.search(
            r"\b(?:invalid|wrong|unsupported|unexpected)\s+type\b"
            r"|\btype\s+(?:is\s+)?(?:invalid|wrong|unsupported|unexpected)\b",
            msg,
        )
        or re.search(
            r"\bmust\s+be\s+(?:an?\s+)?(?:array|object|string|boolean|integer|number|null)\b",
            msg,
        )
        or re.search(
            r"\b(?:expected|expects)\s+(?:an?\s+)?(?:array|object|string|boolean|integer|number|null)\b",
            msg,
        )
        or re.search(
            r"\bnot\s+(?:an?\s+)?(?:array|object|string|boolean|integer|number|null)\b",
            msg,
        )
    )
    if has_schema_shape_error:
        return True
    has_field_value_error = bool(
        re.search(
            r"\b(?:invalid|malformed|bad|unsupported|unexpected)\s+(?:characters?|format|pattern|value)\b",
            msg,
        )
        or re.search(
            r"\b(?:contains|has)\s+(?:invalid|malformed|bad|unsupported|unexpected)\b",
            msg,
        )
        or re.search(
            r"\b(?:format|pattern|value|characters?)\s+(?:is\s+)?(?:invalid|malformed|bad|unsupported|unexpected)\b",
            msg,
        )
    )
    if has_field_value_error:
        return True
    has_key_requirement_error = bool(
        re.search(r"\b(missing|required|provided)\b", msg)
        or "not provided" in msg
        or "is required" in msg
    )
    if (
        has_tool_call_collection or has_tool_call_key or has_tool_response_id
    ) and has_key_requirement_error:
        return True
    has_request_noun = bool(
        re.search(r"\b(parameter|option|argument|field|property|key|value)\b", msg)
    )
    has_request_error = bool(
        re.search(
            r"\b(invalid|unknown|unrecognized|unrecognised|unsupported|unexpected|supplied|malformed|missing|required|provided)\b",
            msg,
        )
        or "not a valid" in msg
        or "bad request" in msg
    )
    return bool(has_request_noun and has_request_error)


def _is_tool_transcript_request_error(message: str, *, status_code: int = 0) -> bool:
    msg = _lower_text(message)
    has_strong_marker = any(
        phrase in msg for phrase in _TOOL_TRANSCRIPT_STRONG_MARKERS
    )
    has_tool_id_marker = "tool_call_id" in msg or "tool call id" in msg
    has_tool_response_id = bool(
        re.search(r"\btool\s+(?:message|response|result)\s+id\b", msg)
    )
    if (has_tool_id_marker or has_tool_response_id) and re.search(
        r"\b(?:does not|did not|doesn't|didn't)\s+match\s+"
        r"(?:the\s+)?(?:expected\s+)?(?:format|pattern|regex|schema)\b",
        msg,
    ):
        return False
    has_transcript_order_context = any(
        phrase in msg
        for phrase in (
            "must be followed",
            "must be a response",
            "must have response",
            "must have responses",
            "preceding message",
            "response message",
            "response messages",
            "did not have response",
            "does not have response",
            "did not match",
            "does not match",
            "mismatch",
            "no matching",
            "missing tool response",
            "missing tool result",
            "missing tool message",
            "no tool response",
            "no tool result",
            "no tool message",
            "previous assistant message",
        )
    )
    if (
        any(phrase in msg for phrase in _TOOL_CAPABILITY_UNSUPPORTED_PHRASES)
        and not has_transcript_order_context
    ):
        return False
    if (
        _is_tool_request_parameter_error(msg)
        and not has_transcript_order_context
    ):
        return False
    has_generic_marker = any(
        phrase in msg for phrase in _TOOL_TRANSCRIPT_GENERIC_MARKERS
    )
    has_http_400_shape = bool(
        status_code == 400 or re.search(r"\b400\b", msg) or "bad request" in msg
    )
    has_transcript_request_shape = any(
        phrase in msg
        for phrase in _TOOL_TRANSCRIPT_REQUEST_ERROR_PHRASES
        if phrase != "bad request"
    )
    has_status_order_shape = has_http_400_shape and has_transcript_order_context
    if not has_strong_marker and not (
        has_generic_marker
        and (has_transcript_request_shape or has_status_order_shape)
        or has_tool_id_marker
        and has_status_order_shape
    ):
        return False
    if has_status_order_shape:
        return True
    if status_code == 400 and has_strong_marker:
        return bool(has_transcript_request_shape)
    if status_code == 400 and has_generic_marker:
        return bool(has_transcript_request_shape)
    return bool(has_transcript_request_shape)


def _classify_provider_fields(
    *,
    status_code: int = 0,
    error_type: str = "",
    error_code: str = "",
    message: str = "",
    default_retryable: bool = False,
) -> Optional[LLMErrorClassification]:
    tokens = {
        _lower_text(error_type),
        _lower_text(error_code),
    }
    msg = _lower_text(message)
    if _is_tool_transcript_request_error(msg, status_code=status_code):
        return LLMErrorClassification(
            kind="http_400_tool_transcript",
            retryable=True,
            terminal=False,
            failure_reason="llm_network_error",
            status_code=status_code,
            provider_error_type=_lower_text(error_type),
            provider_error_code=_lower_text(error_code),
            message=msg,
        )
    if (
        status_code == 400
        and "reasoning is mandatory" in msg
        and "cannot be disabled" in msg
    ):
        return LLMErrorClassification(
            kind="provider_capability_conflict",
            retryable=False,
            terminal=False,
            failure_reason="",
            status_code=status_code,
            provider_error_type=_lower_text(error_type),
            provider_error_code=_lower_text(error_code),
            message=msg,
        )
    if any(
        marker in tokens or marker in msg for marker in _FATAL_QUOTA_MARKERS
    ) or any(phrase in msg for phrase in _FATAL_QUOTA_PHRASES):
        return LLMErrorClassification(
            kind="insufficient_quota",
            retryable=False,
            terminal=True,
            failure_reason="llm_insufficient_quota",
            status_code=status_code,
            provider_error_type=_lower_text(error_type),
            provider_error_code=_lower_text(error_code),
            message=msg,
        )
    if any(
        marker in tokens or marker in msg for marker in _FATAL_BILLING_MARKERS
    ) or any(phrase in msg for phrase in _FATAL_BILLING_PHRASES):
        return LLMErrorClassification(
            kind="billing_error",
            retryable=False,
            terminal=True,
            failure_reason="llm_billing_error",
            status_code=status_code,
            provider_error_type=_lower_text(error_type),
            provider_error_code=_lower_text(error_code),
            message=msg,
        )
    if (
        status_code in {401, 403}
        or any(marker in tokens or marker in msg for marker in _FATAL_AUTH_MARKERS)
    ):
        return LLMErrorClassification(
            kind="auth_error",
            retryable=False,
            terminal=True,
            failure_reason="llm_auth_error",
            status_code=status_code,
            provider_error_type=_lower_text(error_type),
            provider_error_code=_lower_text(error_code),
            message=msg,
        )
    if status_code:
        retryable = bool(default_retryable)
        return LLMErrorClassification(
            kind=f"http_{status_code}",
            retryable=retryable,
            terminal=False,
            failure_reason="llm_network_error" if retryable else "",
            status_code=status_code,
            provider_error_type=_lower_text(error_type),
            provider_error_code=_lower_text(error_code),
            message=msg,
        )
    return None


def _exception_chain(exc: BaseException) -> Iterable[BaseException]:
    """Yield chained exceptions once, preferring explicit causes."""

    seen: set[int] = {id(exc)}
    current: Optional[BaseException] = exc
    for _depth in range(8):
        if current is None:
            return
        next_exc = getattr(current, "__cause__", None)
        if next_exc is None:
            next_exc = getattr(current, "__context__", None)
        if next_exc is None or id(next_exc) in seen:
            return
        seen.add(id(next_exc))
        yield next_exc
        current = next_exc


def classify_llm_exception(
    exc: BaseException,
    _seen: Optional[set[int]] = None,
) -> LLMErrorClassification:
    """Classify one exception for mini-prover retry and termination policy."""

    seen = _seen if _seen is not None else set()
    if id(exc) in seen:
        return LLMErrorClassification(kind="unknown", retryable=False, terminal=False)
    seen.add(id(exc))

    if bool(getattr(exc, "mini_selected_proof_idea_context_error", False)):
        return LLMErrorClassification(
            kind="mini_selected_proof_idea_context_error",
            retryable=False,
            terminal=False,
            failure_reason="selected_proof_idea_context_invalidated",
            message=str(exc),
        )

    if bool(getattr(exc, "llm_required_prompt_context_overflow", False)):
        # The application declared this context indivisible. Replaying the
        # same leaf cannot help and silently shortening it is forbidden. A
        # ModelChain handles this terminal-at-the-leaf condition specially by
        # trying its next (potentially larger-context) backend; if the chain
        # exhausts, callers receive this terminal classification.
        return LLMErrorClassification(
            kind="llm_required_prompt_context_overflow",
            retryable=False,
            terminal=True,
            failure_reason="llm_required_prompt_context_overflow",
            message=str(exc),
        )

    if bool(getattr(exc, "provider_lane_run_closed", False)):
        # A cancellation-resistant request outlived its client's hard close.
        # This run-local serving fingerprint is permanently retired so no
        # sibling can overlap unknown provider work. A new theorem gets a
        # fresh provider-health registry at its run boundary.
        return LLMErrorClassification(
            kind="provider_lane_run_closed",
            retryable=False,
            terminal=False,
            failure_reason="provider_lane_run_closed",
            message=str(exc),
        )

    if bool(getattr(exc, "is_provider_capability_chain_exhausted", False)):
        # Every usable model leaf deterministically conflicts: setup error.
        return LLMErrorClassification(
            kind="provider_capability_conflict",
            retryable=False,
            terminal=True,
            failure_reason="provider_capability_conflict",
            message=str(exc),
        )

    if bool(getattr(exc, "is_provider_capability_conflict", False)):
        # Deterministic setup/capability conflict (e.g. tools require
        # reasoning_effort='none' but configuration marks reasoning as
        # required). Never retryable on the same leaf; NOT terminal so a
        # model chain can skip to a compatible fallback model.
        return LLMErrorClassification(
            kind="provider_capability_conflict",
            retryable=False,
            terminal=False,
            failure_reason="",
            message=str(exc),
        )

    cls = type(exc)
    projection = dispatch_exception_projection(exc)
    trusted_projection = bool(
        projection is not None
        and dispatch_exception_projection_is_canonical(projection)
    )
    name = str(
        (projection.original_name if trusted_projection else "")
        or cls.__name__
    )
    module = str(
        (projection.original_module if trusted_projection else "")
        or cls.__module__
    )

    if isinstance(exc, CostBudgetExceeded) or (
        module == CostBudgetExceeded.__module__
        and name == CostBudgetExceeded.__name__
    ):
        raw_reason = str(
            getattr(exc, "reason", None) or "llm_cost_budget_exhausted"
        )
        reason = (
            "llm_cost_budget_exhausted"
            if raw_reason == "cost_budget_exhausted"
            else raw_reason
        )
        terminal = reason in {
            "llm_cost_budget_exhausted",
            "llm_cost_budget_unknown_pricing",
        }
        return LLMErrorClassification(
            kind=reason,
            retryable=False,
            terminal=terminal,
            failure_reason=reason if terminal else "",
            message=str(exc),
        )

    if isinstance(exc, ProviderDispatchAttemptLimitExceeded) or (
        module == ProviderDispatchAttemptLimitExceeded.__module__
        and name == ProviderDispatchAttemptLimitExceeded.__name__
    ):
        # A concrete transport was refused before exposure because the caller's
        # per-logical-call ceiling was spent.  Durable callers may resume with
        # a fresh, explicitly-accounted attempt; this is neither a provider
        # fatal error nor an unclassified action crash.
        return LLMErrorClassification(
            kind="provider_dispatch_attempt_limit_exhausted",
            retryable=True,
            terminal=False,
            failure_reason="provider_dispatch_attempt_limit_exhausted",
            message=str(exc),
        )

    if bool(getattr(exc, "llm_detached_provider_request", False)):
        return LLMErrorClassification(
            kind="detached_provider_request",
            retryable=False,
            terminal=False,
            failure_reason="llm_network_error",
            message=str(exc),
        )

    ownership_classification = _runtime_transport_ownership_classification(str(exc))
    if ownership_classification is not None:
        return ownership_classification

    if isinstance(exc, (TimeoutError, ConnectionError)):
        return LLMErrorClassification(
            kind="transient",
            retryable=True,
            terminal=False,
            failure_reason="llm_network_error",
            message=str(exc),
        )
    if isinstance(exc, json.JSONDecodeError) or (
        module == json.JSONDecodeError.__module__
        and name == json.JSONDecodeError.__name__
    ):
        return LLMErrorClassification(
            kind="transient",
            retryable=True,
            terminal=False,
            failure_reason="llm_network_error",
        )

    status = _response_status(exc)
    mapping = _response_error_mapping(exc)
    provider_type = _lower_text(mapping.get("type"))
    provider_code = _lower_text(mapping.get("code"))
    message = _lower_text(mapping.get("message") or str(exc))

    if module.startswith("httpx") and name == "HTTPStatusError":
        field_classification = _classify_provider_fields(
            status_code=status,
            error_type=provider_type,
            error_code=provider_code,
            message=message,
            default_retryable=status in _TRANSIENT_HTTP_STATUSES,
        )
        if field_classification is not None:
            return field_classification
    if module.startswith("httpx") and (
        name.endswith("Error")
        or name.endswith("Timeout")
        or name in _HTTP_TRANSPORT_TIMEOUT_NAMES
    ):
        return LLMErrorClassification(
            kind="transport",
            retryable=True,
            terminal=False,
            failure_reason="llm_network_error",
            message=message,
        )
    if module.startswith("httpcore") and (
        name.endswith("Error")
        or name.endswith("Timeout")
        or name in _HTTP_TRANSPORT_TIMEOUT_NAMES
    ):
        return LLMErrorClassification(
            kind="transport",
            retryable=True,
            terminal=False,
            failure_reason="llm_network_error",
            message=message,
        )
    if module.startswith("openai"):
        field_classification = _classify_provider_fields(
            status_code=status,
            error_type=provider_type or name,
            error_code=provider_code,
            message=message,
            default_retryable=name
            in {
                "APIConnectionError",
                "APITimeoutError",
                "APIError",
                "RateLimitError",
                "InternalServerError",
            },
        )
        if field_classification is not None:
            return field_classification
        if name in {
            "APIConnectionError",
            "APITimeoutError",
        }:
            return LLMErrorClassification(
                kind="transport",
                retryable=True,
                terminal=False,
                failure_reason="llm_network_error",
                message=message,
            )

    text_classification = classify_llm_error_text(str(exc))
    if (
        text_classification.terminal
        or text_classification.retryable
        or text_classification.kind not in {"empty", "text"}
    ):
        return text_classification
    for chained in _exception_chain(exc):
        chained_classification = classify_llm_exception(chained, seen)
        if (
            chained_classification.terminal
            or chained_classification.retryable
            or chained_classification.kind != "unknown"
        ):
            return chained_classification
    return LLMErrorClassification(kind="unknown", retryable=False, terminal=False)


def classify_llm_error_text(error_text: str) -> LLMErrorClassification:
    """Classify a rendered LLM error after the original exception is gone."""

    text = _lower_text(error_text)
    if not text:
        return LLMErrorClassification(kind="empty", retryable=False, terminal=False)
    ownership_classification = _runtime_transport_ownership_classification(error_text)
    if ownership_classification is not None:
        return ownership_classification
    if "provider_lane_run_closed" in text:
        return LLMErrorClassification(
            kind="provider_lane_run_closed",
            retryable=False,
            terminal=False,
            failure_reason="provider_lane_run_closed",
            message=text,
        )
    if (
        text == "provider_capability_conflict"
        or "providercapabilitychainexhaustederror" in text
        or (
            "every usable model" in text
            and "deterministic provider capability conflict" in text
        )
    ):
        return LLMErrorClassification(
            kind="provider_capability_conflict",
            retryable=False,
            terminal=True,
            failure_reason="provider_capability_conflict",
            message=text,
        )
    if "llm response body empty" in text:
        return LLMErrorClassification(
            kind="transient",
            retryable=True,
            terminal=False,
            failure_reason="llm_network_error",
            message=text,
        )
    for capacity_reason in (
        "llm_cost_budget_reserved_capacity",
        "llm_cost_budget_request_capacity",
        "llm_cost_budget_retry_capacity",
    ):
        if capacity_reason not in text:
            continue
        return LLMErrorClassification(
            kind=capacity_reason,
            retryable=False,
            terminal=False,
            message=text,
        )
    if (
        "llm retry would exceed deadline" in text
        or "llm deadline cannot admit a timed-request retry" in text
        or "llm request deadline expired before dispatch" in text
        or "llm request deadline too close to dispatch safely" in text
    ):
        return LLMErrorClassification(
            kind="llm_retry_deadline_exhausted",
            retryable=False,
            terminal=False,
            failure_reason="llm_retry_deadline_exhausted",
            message=text,
        )
    for reason in (
        "llm_cost_budget_unknown_pricing",
        "llm_cost_budget_exhausted",
        "cost_budget_exhausted",
    ):
        if reason in text:
            canonical = (
                "llm_cost_budget_exhausted"
                if reason == "cost_budget_exhausted"
                else reason
            )
            return LLMErrorClassification(
                kind=canonical,
                retryable=False,
                terminal=True,
                failure_reason=canonical,
                message=text,
            )
    status_code = 0
    if _is_tool_transcript_request_error(text):
        status_code = 400
    elif re.search(r"\b400\b", text) and "bad request" in text:
        status_code = 400
    if re.search(r"\b401\b", text) and (
        "unauthorized" in text or "unauthorised" in text
    ):
        status_code = 401
    elif re.search(r"\b403\b", text) and "forbidden" in text:
        status_code = 403
    field_classification = _classify_provider_fields(
        status_code=status_code,
        message=text,
    )
    if field_classification is not None and (
        field_classification.terminal
        or field_classification.retryable
        or field_classification.status_code > 0
    ):
        return field_classification
    if "too many requests" in text and "insufficient_quota" not in text:
        return LLMErrorClassification(
            kind="rate_limit",
            retryable=True,
            terminal=False,
            failure_reason="llm_network_error",
        )
    return LLMErrorClassification(kind="text", retryable=False, terminal=False)


def is_retryable_llm_exception(exc: BaseException) -> bool:
    classification = classify_llm_exception(exc)
    return bool(classification.retryable and not classification.terminal)


def terminal_llm_failure_reason_from_error(error_text: str) -> str:
    classification = classify_llm_error_text(error_text)
    return classification.failure_reason if classification.terminal else ""


def terminal_llm_failure_reason_from_exception(exc: BaseException) -> str:
    classification = classify_llm_exception(exc)
    return classification.failure_reason if classification.terminal else ""


def is_terminal_llm_failure_reason(reason: str) -> bool:
    """Return true for canonical run-stopping LLM failure reasons."""

    text = str(reason or "").strip()
    if not text:
        return False
    if text in _TERMINAL_LLM_FAILURE_REASONS:
        return True
    classification = classify_llm_error_text(text)
    return bool(classification.terminal)


def is_terminal_session_failure_reason(reason: str) -> bool:
    """Return true for durable run-terminal LLM or controller verdicts."""

    text = str(reason or "").strip()
    return bool(
        text
        and (
            text in _TERMINAL_SESSION_FAILURE_REASONS
            or is_terminal_llm_failure_reason(text)
        )
    )


def is_scoped_llm_failure_reason(reason: str) -> bool:
    """Return true for failures local to one request or isolated work item."""

    text = str(reason or "").strip()
    if not text:
        return False
    if text in (
        _SCOPED_LLM_FAILURE_REASONS | _SCOPED_CONTROLLER_FAILURE_REASONS
    ):
        return True
    classification = classify_llm_error_text(text)
    return str(classification.kind or "") in _SCOPED_LLM_FAILURE_REASONS


def llm_failure_scope(reason: str) -> str:
    """Classify an LLM failure reason as ``global``, ``scoped``, or unknown."""

    text = str(reason or "").strip()
    if not text:
        return ""
    if is_terminal_llm_failure_reason(text):
        return "global"
    if is_scoped_llm_failure_reason(text):
        return "scoped"
    return ""


_PLANNER_TRANSPORT_EMPTY_REASONS = frozenset(
    {
        "llm_network_error",
        "llm_retry_deadline_exhausted",
        "provider_dispatch_attempt_limit_exhausted",
    }
)


def planner_failure_is_transport_empty(
    reason: str,
    *,
    metadata: Optional[Mapping[str, Any]] = None,
) -> bool:
    """Return whether a planner miss is transport, not a mathematical miss.

    A 0-completion deadline/network/dispatch failure produced no plan. Treating
    that as "try a smaller decomposition" burned remaining passes while
    ``empty_planner_streak`` stayed 0. Completions that still failed to parse
    remain ordinary empty-plan degeneracy.
    """

    text = str(reason or "").strip()
    if text not in _PLANNER_TRANSPORT_EMPTY_REASONS:
        return False
    if not isinstance(metadata, Mapping):
        return True
    if "zero_provider_failure" not in metadata:
        return True
    return bool(metadata.get("zero_provider_failure"))


def projected_scoped_llm_failure_is_retryable(
    *,
    reason: str,
    kind: str = "",
    metadata: Optional[Mapping[str, Any]] = None,
) -> bool:
    """Recover retryability after a nested LLM result crosses an action boundary.

    Nested recursive actions persist the normalized reason/kind instead of the
    original exception.  Prefer the classifier's explicit boolean when it was
    checkpointed; otherwise infer only the canonical transient scoped shapes.
    Permanent/global failures are never reopened here.
    """

    normalized_reason = str(reason or "").strip()
    if llm_failure_scope(normalized_reason) != "scoped":
        return False
    if normalized_reason in {
        "llm_retry_deadline_exhausted",
        "provider_dispatch_attempt_limit_exhausted",
    }:
        # The classifier boolean describes retrying inside the composite call.
        # These two reasons specifically mean that in-call authority is spent;
        # their recovery is a later, durably scheduled quantum.
        return True
    if isinstance(metadata, Mapping):
        explicit = metadata.get("llm_retryable")
        if isinstance(explicit, bool):
            return explicit
    normalized_kind = str(kind or "").strip().lower()
    if normalized_reason != "llm_network_error":
        return False
    return bool(
        normalized_kind in {
            "transient",
            "transport",
            "rate_limit",
            "timeout",
        }
        or normalized_kind.startswith("http_")
    )
