"""Shared shutdown deadlines and structural cleanup diagnostics."""

from __future__ import annotations

import asyncio
import contextvars
import json
import math
import os
import stat
import time
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, TypeGuard


class ShutdownIncomplete(TimeoutError):
    """Owned tasks remain alive and require their process owner's backstop."""


def _finite_lease_number(value: Any) -> TypeGuard[int | float]:
    if type(value) not in (int, float):
        return False
    try:
        return math.isfinite(value)
    except OverflowError:
        return False


@dataclass
class ShutdownState:
    nonce: str = field(default_factory=lambda: uuid.uuid4().hex)
    deadline: float = 0.0
    stop_requested: bool = False
    output_dir: Path | None = None
    unfinished: dict[str, list[dict[str, Any]]] = field(default_factory=dict)
    created_monotonic_s: float = field(default_factory=time.monotonic)

    def adopt_supervisor_stop(self) -> int | None:
        """Reuse the supervisor's already-written stop lease for this process."""
        if self.output_dir is None:
            return None
        try:
            descriptor = os.open(self.output_dir / "shutdown.jsonl",
                                 os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            with os.fdopen(descriptor, "rb") as stream:
                info = os.fstat(stream.fileno())
                if not stat.S_ISREG(info.st_mode):
                    return None
                stream.seek(max(0, info.st_size - 65536))
                rows = stream.read(65536).splitlines()
            for raw in reversed(rows):
                try:
                    row = json.loads(raw)
                except (ValueError, RecursionError):
                    continue
                if not isinstance(row, dict) or row.get("stage") != "supervisor_stop_requested":
                    continue
                started, deadline = row.get("monotonic_s"), row.get("deadline_monotonic_s")
                if (row.get("worker_pid") != os.getpid()
                        or not _finite_lease_number(started)
                        or started < self.created_monotonic_s
                        or not _finite_lease_number(deadline)
                        or deadline < started
                        or not isinstance(row.get("owner_nonce"), str)):
                    continue
                self.nonce = row["owner_nonce"]
                self.deadline = min(self.deadline, deadline) if self.deadline > 0 else deadline
                original = row.get("original_signal")
                return original if type(original) is int and original in (2, 15) else None
        except (OSError, ValueError):
            pass
        return None

    def begin(self, seconds: float, *, stop_work: bool = True, reason: str = "shutdown") -> float:
        seconds = float(seconds)
        if not math.isfinite(seconds) or seconds <= 0:
            seconds = 120.0
        if self.deadline <= 0:
            self.deadline = time.monotonic() + seconds
        self.stop_requested |= stop_work
        self.record("stop_requested" if stop_work else "cleanup_started", reason=reason)
        return self.deadline

    def record(self, stage: str, **details: Any) -> None:
        if self.output_dir is None:
            return
        row = {"stage": stage, "owner_nonce": self.nonce,
               "monotonic_s": time.monotonic(), "deadline_monotonic_s": self.deadline,
               **details}
        try:
            with (self.output_dir / "shutdown.jsonl").open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(row, sort_keys=True, allow_nan=False) + "\n")
        except (OSError, ValueError, TypeError):
            pass


_CURRENT: contextvars.ContextVar[ShutdownState | None] = contextvars.ContextVar(
    "ensemble_shutdown_state", default=None)


def current_shutdown() -> ShutdownState | None:
    return _CURRENT.get()


def install_shutdown_state() -> tuple[ShutdownState, contextvars.Token]:
    state = ShutdownState()
    return state, _CURRENT.set(state)


def reset_shutdown_state(token: contextvars.Token) -> None:
    _CURRENT.reset(token)


def cleanup_deadline(default_seconds: float = 10.0) -> float:
    state = current_shutdown()
    if state is not None and state.deadline > 0:
        return state.deadline
    return time.monotonic() + max(0.001, default_seconds)


def remaining_cleanup_seconds(limit: float) -> float:
    state = current_shutdown()
    if state is None or state.deadline <= 0:
        return max(0.0, limit)
    return max(0.0, min(limit, state.deadline - time.monotonic()))


def require_work_admission() -> None:
    state = current_shutdown()
    if state is not None and state.stop_requested:
        raise asyncio.CancelledError("run is stopping")


async def join_owned_tasks(tasks: Iterable[asyncio.Task], *, deadline: float,
                           label: str) -> None:
    owned = set(tasks)
    if not owned:
        return
    state = current_shutdown()
    if state is not None:
        state.record("join_started", owner=label, task_count=len(owned))
    _, pending = await asyncio.wait(owned, timeout=max(0.0, deadline - time.monotonic()))
    if pending:
        details = [{"name": task.get_name(), "frames": [
            {"file": Path(frame.f_code.co_filename).name,
             "function": frame.f_code.co_name, "line": frame.f_lineno}
            for frame in task.get_stack(limit=3)
        ]} for task in pending]
        if state is not None:
            state.unfinished[label] = details
            state.record("join_unfinished", owner=label, tasks=details)
        raise ShutdownIncomplete(f"{label}: {len(pending)} owned tasks remain")
    if state is not None:
        state.unfinished.pop(label, None)
        state.record("join_finished", owner=label)


async def enforce_process_backstop() -> None:
    """Do not finalize over a live writer in an isolated supervised worker."""
    from .mini_session.process_watchdog import is_watchdog_worker
    if is_watchdog_worker():
        while True:
            try:
                await asyncio.Future()
            except asyncio.CancelledError:
                continue
