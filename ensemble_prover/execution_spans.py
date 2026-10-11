"""Bounded execution diagnostics; timings never confer proof authority."""
from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
import time
import uuid
from typing import Any, Iterator

_SINK: ContextVar[dict[str, Any] | None] = ContextVar("execution_span_sink", default=None)
_PARENT: ContextVar[str | None] = ContextVar("execution_span_parent", default=None)


@contextmanager
def collect_execution_spans(sink: dict[str, Any]) -> Iterator[None]:
    sink.setdefault("spans", [])
    sink.setdefault("open_operations", [])
    sink.setdefault("open_parent_operations", {})
    sink["time_accounting"] = "nested inclusive wall; exclusive wall subtracts union of completed direct children"
    token = _SINK.set(sink)
    try:
        yield
    finally:
        _SINK.reset(token)


@contextmanager
def execution_span(stage: str) -> Iterator[dict[str, Any]]:
    sink = _SINK.get()
    if sink is None:
        yield {}
        return
    operation = uuid.uuid4().hex
    record = {"operation_id": operation, "parent_operation_id": _PARENT.get(), "stage": stage,
              "started_monotonic": time.monotonic(), "disposition": "completed"}
    cpu = time.process_time()
    sink["open_operations"].append(operation)
    sink["open_parent_operations"][operation] = record["parent_operation_id"]
    token = _PARENT.set(operation)
    try:
        yield record
    except BaseException as exc:
        record.update(disposition="cancelled" if type(exc).__name__ == "CancelledError" else "failed",
                      exception_type=type(exc).__name__)
        raise
    finally:
        ended = time.monotonic()
        record.update(ended_monotonic=ended, wall_s=max(0.0, ended-record["started_monotonic"]),
                      process_cpu_delta_s=max(0.0, time.process_time()-cpu))
        intervals = sorted((max(record["started_monotonic"], child["started_monotonic"]),
                            min(ended, child["ended_monotonic"]))
                           for child in sink["spans"] if child.get("parent_operation_id") == operation)
        union = 0.0
        end = record["started_monotonic"]
        for left, right in intervals:
            union += max(0.0, right-max(left,end))
            end = max(end,right)
        record["exclusive_wall_s"] = max(0.0, record["wall_s"]-union)
        record["exclusive_complete"] = not sink.get("dropped_spans") and operation not in sink["open_parent_operations"].values()
        record["cpu_accounting"] = "shared_process_delta_not_exclusive"
        sink["open_operations"].remove(operation)
        sink["open_parent_operations"].pop(operation, None)
        if len(sink["spans"]) < 128:
            sink["spans"].append(record)
        else:
            sink["dropped_spans"] = sink.get("dropped_spans", 0) + 1
        _PARENT.reset(token)


def record_lean_result(result: Any) -> None:
    sink = _SINK.get()
    if sink is None:
        return
    timings = getattr(result, "stage_timings", {})
    metadata = getattr(result, "execution_metadata", {})
    records = sink.setdefault("lean_results", [])
    if len(records) < 16:
        records.append({"operation_id": _PARENT.get(), "accepted": bool(getattr(result, "ok", False)),
                        "stage_timings": dict(timings) if isinstance(timings, dict) else {},
                        "execution_metadata": {key: metadata[key] for key in (
                            "backend", "context_key", "context_family_key", "audit_policy", "execution_stages",
                            "generation", "generation_id") if isinstance(metadata, dict) and key in metadata}})
