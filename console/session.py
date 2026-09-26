"""An attached run: tailer plus reducer plus periodic summary and liveness reads."""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from pathlib import Path

from .reducer import RunState, reduce
from .runs import ProcessObservation, RunInfo, inspect_run_dir, observe_processes
from .summary import SummaryView, load_summary
from .tailer import JsonlTailer, TailEvent

MAX_SLICES_PER_POLL = 8
SUMMARY_REFRESH_S = 5.0
LIVENESS_REFRESH_S = 5.0
MAX_TAIL_EVENTS = 200


@dataclass
class AttachedRun:
    run_dir: Path
    info: RunInfo
    tailer: JsonlTailer
    state: RunState = field(default_factory=RunState)
    summary: SummaryView = field(default_factory=SummaryView)
    liveness: ProcessObservation = field(default_factory=lambda: ProcessObservation("unknown", [], "not yet observed"))
    tail_events: list[TailEvent] = field(default_factory=list)
    backlog: bool = False
    trace_size: int = 0
    last_summary_read: float = 0.0
    last_liveness_read: float = 0.0
    polls: int = 0

    @classmethod
    def attach(cls, run_dir: Path) -> "AttachedRun":
        run_dir = Path(run_dir)
        return cls(run_dir=run_dir, info=inspect_run_dir(run_dir), tailer=JsonlTailer(run_dir / "turns.jsonl"))

    def poll(self, *, now: float | None = None, proc_root: str = "/proc") -> int:
        """Ingest up to MAX_SLICES_PER_POLL slices. Returns new record count."""
        now = time.time() if now is None else now
        self.polls += 1
        new_records = 0
        for _ in range(MAX_SLICES_PER_POLL):
            tail = self.tailer.poll()
            for event in tail.events:
                if event.kind == "generation_reset":
                    self.state = RunState()
                self.tail_events.append(event)
            del self.tail_events[:-MAX_TAIL_EVENTS]
            for rec in tail.records:
                reduce(self.state, rec)
            new_records += len(tail.records)
            self.trace_size = tail.size
            self.backlog = tail.has_more
            if not tail.has_more:
                break
        if now - self.last_summary_read >= SUMMARY_REFRESH_S or self.polls == 1:
            self.summary = load_summary(self.run_dir)
            self.info = inspect_run_dir(self.run_dir, kind=self.info.kind, sweep=self.info.sweep)
            self.last_summary_read = now
        if now - self.last_liveness_read >= LIVENESS_REFRESH_S or self.polls == 1:
            self.liveness = observe_processes(self.run_dir, proc_root=proc_root)
            self.last_liveness_read = now
        return new_records

    def catch_up(self, *, max_polls: int = 10_000) -> int:
        """Read the whole existing trace (bounded by poll count)."""
        total = 0
        for _ in range(max_polls):
            total += self.poll()
            if not self.backlog:
                break
        return total
