"""Inert planner failure receipts that preserve policy across process restarts.

The original exception is classified while it is live. Disk restore creates
one known value exception, never an SDK exception, response, or traceback.
"""

from __future__ import annotations

from dataclasses import asdict, fields
import math
from typing import Any, Mapping

from ensemble_prover.llm_deadline import (
    LLMRetryDeadlineContext,
    llm_retry_deadline_record_from_exception,
)
from ensemble_prover.llm_error_policy import (
    LLMErrorClassification,
    classify_llm_exception,
    transport_failure_record_from_exception,
)
from ensemble_prover.state_data import clone_json_value


_CLASSIFICATION_FIELDS = {item.name for item in fields(LLMErrorClassification)} - {"message"}
_DISPATCH_COUNTS = {"provider_dispatches_started", "dispatch_attempt_limit", "next_dispatch_ordinal"}
_TRANSPORT_FIELDS = {
    "llm_transport_failure_type", "llm_transport_failure_attempt",
    "llm_transport_failure_request_timeout_s",
}
_DEADLINE_NAMES = {
    "reason": "reason", "attempt": "attempt", "model": "model",
    "status_code": "status_code", "retry_after_s": "retry_after_s",
    "retry_delay_s": "retry_delay_s", "deadline_remaining_s": "remaining_s",
    "request_timeout_s": "request_timeout_s", "request_elapsed_s": "request_elapsed_s",
    "operation_elapsed_s": "operation_elapsed_s", "configured_timeout_s": "configured_timeout_s",
    "operation_timeout_s": "operation_timeout_s", "deadline_policy": "policy",
    "original_exception_type": "original_exception_type",
}


class RestoredPlannerJobError(RuntimeError):
    """Known failure value with no original request or provider capabilities."""

    def __init__(self, classification: LLMErrorClassification) -> None:
        self.classification = classification
        super().__init__(classification.message)

    def __copy__(self) -> RestoredPlannerJobError:
        # A consumer raises its own exception. Reusing this receipt would
        # retain action stack frames and their live provider/proof objects.
        return decode_planner_error(encode_planner_error(self))


def restored_planner_error_classification(error: BaseException) -> LLMErrorClassification | None:
    """Return saved policy only for the exact codec-owned exception type."""

    if type(error) is RestoredPlannerJobError:
        return error.classification
    return None


def _object(value: Any, *, label: str) -> dict[str, Any]:
    if type(value) is not dict or any(type(key) is not str for key in value):
        raise ValueError(f"{label} must be a string-keyed object")
    return value


def _count(value: Any, *, label: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{label} must be a nonnegative integer")
    return value


def _classification(value: Any) -> LLMErrorClassification:
    data = _object(value, label="planner error classification")
    if set(data) != _CLASSIFICATION_FIELDS:
        raise ValueError("planner error classification fields do not match the schema")
    for key in ("retryable", "terminal"):
        if type(data[key]) is not bool:
            raise ValueError("planner error classification flags must be booleans")
    _count(data["status_code"], label="planner error HTTP status")
    for key in ("kind", "failure_reason", "provider_error_type", "provider_error_code"):
        if type(data[key]) is not str:
            raise ValueError("planner error classification identities must be strings")
    if data["terminal"] and data["retryable"]:
        raise ValueError("a terminal planner error cannot also request retry")
    return LLMErrorClassification(**data, message=(
        f"saved planner failure: {data['kind']} ({data['failure_reason']})"
    ))


def _deadline_context(value: Any) -> LLMRetryDeadlineContext | None:
    if value is None:
        return None
    data = _object(value, label="planner retry deadline")
    if set(data) != {item.name for item in fields(LLMRetryDeadlineContext)}:
        raise ValueError("planner retry deadline fields do not match the schema")
    for key, item in data.items():
        if key in {"attempt", "status_code"}:
            _count(item, label=key)
        elif key.endswith("_s"):
            if item is not None and (type(item) not in {int, float} or not math.isfinite(item)):
                raise ValueError("planner deadline durations must be finite numbers or null")
        elif type(item) is not str:
            raise ValueError("planner deadline identifiers must be strings")
    # Provider text and URLs can contain request material or credentials.
    if data["base_url"] or data["original_error"]:
        raise ValueError("planner error receipts cannot restore raw provider diagnostics")
    return LLMRetryDeadlineContext(**data)


def encode_planner_error(error: BaseException) -> dict[str, Any]:
    """Project only policy, transport diagnostics and logical dispatch counts."""

    policy = asdict(classify_llm_exception(error))
    policy.pop("message")
    deadline = llm_retry_deadline_record_from_exception(error)
    context = None
    if deadline:
        values = {
            name: deadline["llm_retry_deadline_" + suffix]
            for name, suffix in _DEADLINE_NAMES.items()
            if "llm_retry_deadline_" + suffix in deadline
        }
        context = asdict(LLMRetryDeadlineContext(
            **{"reason": "", "attempt": 0, "model": "", **values},
        ))
    record = {
        "schema_version": 1, "classification": policy,
        "transport": transport_failure_record_from_exception(error),
        "deadline_context": context,
        "dispatch_counts": {
            name: getattr(error, name) for name in _DISPATCH_COUNTS if hasattr(error, name)
        },
    }
    clean = clone_json_value(record, label="planner failure receipt")
    decode_planner_error(clean)
    return clean


def decode_planner_error(record: Mapping[str, Any]) -> RestoredPlannerJobError:
    """Validate inert receipt data and restore its original policy decision."""

    data = _object(clone_json_value(record, label="planner failure receipt"), label="planner failure receipt")
    if (set(data) != {"schema_version", "classification", "transport", "deadline_context", "dispatch_counts"}
            or type(data["schema_version"]) is not int or data["schema_version"] != 1):
        raise ValueError("unsupported planner failure receipt schema")
    error = RestoredPlannerJobError(_classification(data["classification"]))
    transport = _object(data["transport"], label="planner transport diagnostics")
    if transport:
        if not {"llm_transport_failure_type", "llm_transport_failure_attempt"} <= set(transport) <= _TRANSPORT_FIELDS:
            raise ValueError("planner transport diagnostic fields do not match the schema")
        if type(transport["llm_transport_failure_type"]) is not str or not transport["llm_transport_failure_type"]:
            raise ValueError("planner transport type must be a nonempty string")
        if not _count(transport["llm_transport_failure_attempt"], label="transport attempt"):
            raise ValueError("planner transport attempt must be positive")
        timeout = transport.get("llm_transport_failure_request_timeout_s")
        if timeout is not None and (type(timeout) not in {int, float} or not math.isfinite(timeout) or timeout <= 0):
            raise ValueError("planner transport timeout must be positive and finite")
        for name, value in transport.items():
            setattr(error, name, value)
    counts = _object(data["dispatch_counts"], label="planner dispatch counts")
    if not set(counts) <= _DISPATCH_COUNTS:
        raise ValueError("planner dispatch count fields do not match the schema")
    for name, value in counts.items():
        setattr(error, name, _count(value, label=name))
    context = _deadline_context(data["deadline_context"])
    if context is not None:
        error.context = context
    return error
