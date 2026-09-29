"""Structured metadata for local LLM deadline guard exits."""

from __future__ import annotations

import math
import re
from dataclasses import dataclass
from typing import Any, Dict, Optional


_ATTEMPT_RE = re.compile(r"\battempt=(\d+)")
_MODEL_RE = re.compile(r"\bmodel=([^) ,]+)")


def _finite_float(value: Any) -> Optional[float]:
    try:
        out = float(value)
    except Exception:
        return None
    if not math.isfinite(out):
        return None
    return out


def _rounded(value: Any) -> Optional[float]:
    out = _finite_float(value)
    if out is None:
        return None
    return round(out, 3)


def _positive_int(value: Any) -> int:
    try:
        return max(0, int(value or 0))
    except Exception:
        return 0


@dataclass(frozen=True)
class LLMRetryDeadlineContext:
    """Facts captured where a provider retry is suppressed by a deadline."""

    reason: str
    attempt: int
    model: str
    base_url: str = ""
    status_code: int = 0
    retry_after_s: Optional[float] = None
    retry_delay_s: Optional[float] = None
    deadline_remaining_s: Optional[float] = None
    request_timeout_s: Optional[float] = None
    request_elapsed_s: Optional[float] = None
    operation_elapsed_s: Optional[float] = None
    configured_timeout_s: Optional[float] = None
    operation_timeout_s: Optional[float] = None
    deadline_policy: str = ""
    original_exception_type: str = ""
    original_error: str = ""

    @property
    def original_exception_family(self) -> str:
        reason = str(self.reason or "").strip()
        original_type = str(self.original_exception_type or "").strip()
        if reason in {
            "deadline_expired_before_dispatch",
            "deadline_too_close_before_dispatch",
        }:
            return "deadline_guard"
        if str(original_type).endswith("HTTPStatusError") or self.status_code > 0:
            return "http_status"
        if "timeout" in original_type.lower():
            return "timeout"
        if original_type:
            return "transport"
        return ""

    def as_record(self) -> Dict[str, Any]:
        """Return flattened JSON-safe fields for recorder events."""

        out: Dict[str, Any] = {
            "llm_retry_deadline_exhausted": True,
            "llm_retry_deadline_reason": str(self.reason or ""),
            "llm_retry_deadline_attempt": int(self.attempt or 0),
            "llm_retry_deadline_model": str(self.model or ""),
            "llm_retry_deadline_base_url": str(self.base_url or ""),
            "llm_retry_deadline_policy": str(self.deadline_policy or ""),
            "llm_retry_deadline_status_code": int(self.status_code or 0),
            "llm_retry_deadline_original_exception_type": str(
                self.original_exception_type or ""
            ),
            "llm_retry_deadline_original_exception_family": (
                self.original_exception_family
            ),
            "llm_retry_deadline_original_error": str(self.original_error or "")[:300],
        }
        optional = {
            "llm_retry_deadline_retry_after_s": self.retry_after_s,
            "llm_retry_deadline_retry_delay_s": self.retry_delay_s,
            "llm_retry_deadline_remaining_s": self.deadline_remaining_s,
            "llm_retry_deadline_request_timeout_s": self.request_timeout_s,
            "llm_retry_deadline_request_elapsed_s": self.request_elapsed_s,
            "llm_retry_deadline_operation_elapsed_s": self.operation_elapsed_s,
            "llm_retry_deadline_configured_timeout_s": self.configured_timeout_s,
            "llm_retry_deadline_operation_timeout_s": self.operation_timeout_s,
        }
        for key, value in optional.items():
            rounded = _rounded(value)
            if rounded is not None:
                out[key] = rounded
        return out


class LLMRetryDeadlineExceeded(RuntimeError):
    """Raised when retrying or dispatching would overrun an LLM deadline."""

    def __init__(self, message: str, *, context: LLMRetryDeadlineContext) -> None:
        self.context = context
        super().__init__(message)


def llm_retry_deadline_record_from_exception(exc: BaseException) -> Dict[str, Any]:
    """Extract retry-deadline metadata from a live exception if available."""

    current: Optional[BaseException] = exc
    seen: set[int] = set()
    for _depth in range(8):
        if current is None or id(current) in seen:
            break
        seen.add(id(current))
        context = getattr(current, "context", None)
        if isinstance(context, LLMRetryDeadlineContext):
            return context.as_record()
        text_record = llm_retry_deadline_record_from_text(str(current or ""))
        if text_record:
            return text_record
        cause = getattr(current, "__cause__", None)
        current = cause if isinstance(cause, BaseException) else None
    return {}


def llm_retry_deadline_record_from_text(error_text: str) -> Dict[str, Any]:
    """Best-effort parse for historical retry-deadline text-only records."""

    text = str(error_text or "")
    lowered = text.lower()
    if (
        "llm retry would exceed deadline" not in lowered
        and "llm deadline cannot admit a timed-request retry" not in lowered
        and "llm request deadline expired before dispatch" not in lowered
        and "llm request deadline too close to dispatch safely" not in lowered
    ):
        return {}
    if "expired before dispatch" in lowered:
        reason = "deadline_expired_before_dispatch"
    elif "too close to dispatch safely" in lowered:
        reason = "deadline_too_close_before_dispatch"
    elif "cannot admit a timed-request retry" in lowered:
        reason = "transport_retry_insufficient_request_window"
    elif "json-body parse error" in lowered:
        reason = "json_body_parse_error"
    else:
        reason = "retry_would_exceed_deadline"
    attempt_match = _ATTEMPT_RE.search(text)
    model_match = _MODEL_RE.search(text)
    return {
        "llm_retry_deadline_exhausted": True,
        "llm_retry_deadline_reason": reason,
        "llm_retry_deadline_attempt": _positive_int(
            attempt_match.group(1) if attempt_match else 0
        ),
        "llm_retry_deadline_model": model_match.group(1) if model_match else "",
    }


def llm_retry_deadline_fields(record: Dict[str, Any]) -> Dict[str, Any]:
    """Return retry-deadline keys already present on a recorder event."""

    return {
        str(key): value
        for key, value in dict(record or {}).items()
        if str(key).startswith("llm_retry_deadline_")
    }
