"""Bounded, non-billing provider telemetry for synchronous live recorders."""

from __future__ import annotations

import asyncio
import inspect
import math
import time
from typing import Any, Mapping


PROGRESS_KEY = "llm_provider_progress"
_STATUSES = {
    "initialized", "requesting", "thinking", "compacting", "idle",
    "retrying", "responding", "finished", "failed", "cancelled", "timed_out",
}
_COUNTERS = {
    "event_count", "thinking_event_count", "retry_event_count",
    "assistant_event_count", "current_block_estimated_tokens",
    "retry_attempt", "max_retries", "retry_delay_ms", "error_status",
}


def progress_snapshot(value: Any) -> dict[str, Any] | None:
    """Allow only known telemetry fields; never copy provider text or usage."""
    if not isinstance(value, Mapping):
        return None
    if value.get("backend") != "claude_code_subscription":
        return None
    status = value.get("status")
    if not isinstance(status, str) or status not in _STATUSES:
        return None
    clean: dict[str, Any] = {
        "backend": "claude_code_subscription", "status": status,
        "usage_authoritative": False,
    }
    for key in _COUNTERS:
        number = value.get(key)
        if type(number) is int and 0 <= number <= 2**63 - 1:
            clean[key] = number
    elapsed = value.get("elapsed_s")
    if (isinstance(elapsed, (int, float)) and not isinstance(elapsed, bool)
            and 0 <= elapsed <= 10**12 and math.isfinite(elapsed)):
        clean["elapsed_s"] = round(elapsed, 3)
    return clean


class ProviderProgressForwarder:
    """Best-effort sync sink delivery, with no tasks or accounting transitions.

    Async sinks remain supported for authoritative accounting events, but are
    deliberately skipped here: progress must not extend the provider deadline
    or leave background tasks behind. The production recorder is synchronous.
    """

    def __init__(self, sink: Any, identity: Mapping[str, Any]) -> None:
        self.sink = sink
        self.identity = dict(identity)
        self.active = True
        self.last_time: float | None = None
        self.last_status = ""
        self.last_retry_count = 0

    def publish(self, snapshot: dict[str, Any]) -> None:
        if not self.active or self.sink is None:
            return
        now = time.monotonic()
        retry_count = snapshot.get("retry_event_count", 0)
        status = snapshot["status"]
        if (self.last_time is not None and now - self.last_time < 30.0
                and status == self.last_status and retry_count == self.last_retry_count):
            return
        self.last_time, self.last_status, self.last_retry_count = now, status, retry_count
        verdict = f"provider_{status}"
        if "current_block_estimated_tokens" in snapshot:
            verdict += f" thinking_block_estimate={snapshot['current_block_estimated_tokens']} (not billed)"
        record = {
            **self.identity, "phase": "llm_provider_progress", "verdict": verdict,
            PROGRESS_KEY: dict(snapshot),
        }
        try:
            if inspect.iscoroutinefunction(self.sink):
                return
            result = self.sink(record)
            if inspect.iscoroutine(result):
                result.close()
            elif isinstance(result, asyncio.Future):
                # A synchronous wrapper can still schedule asynchronous work.
                # Cancel it before it can publish after this request retires,
                # and consume failures from tasks that already completed.
                result.cancel()
                result.add_done_callback(_consume_sink_future)
        except Exception:
            # Telemetry cannot change a request's success/failure or liability.
            pass


def _consume_sink_future(future: asyncio.Future[Any]) -> None:
    if not future.cancelled():
        future.exception()
