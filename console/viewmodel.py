"""Plain-text projections of an attached run for the status bar and views."""

from __future__ import annotations

import time
from typing import Iterable

from .reducer import Line, RunState
from .runs import ProcessObservation, RunInfo, age_seconds
from .session import AttachedRun
from .summary import SummaryView

_KIND_MARK = {"info": "·", "good": "✓", "bad": "✗", "warn": "!", "milestone": "◆"}


def fmt_elapsed(seconds: float | None) -> str:
    if seconds is None:
        return "?"
    seconds = int(seconds)
    hours, rem = divmod(seconds, 3600)
    minutes, secs = divmod(rem, 60)
    return f"{hours}:{minutes:02d}:{secs:02d}"


def fmt_age(seconds: float | None) -> str:
    if seconds is None:
        return "unknown"
    if seconds < 90:
        return f"{int(seconds)}s ago"
    if seconds < 5400:
        return f"{int(seconds // 60)}m ago"
    return f"{seconds / 3600:.1f}h ago"


def root_status_text(state: RunState, summary: SummaryView) -> str:
    if summary.export_state == "verified":
        return "VERIFIED EXPORT (canonical policy)"
    if summary.export_state == "policy_unavailable":
        badge = "policy unavailable; verified badge withheld"
    elif summary.export_state == "pending" and summary.internal_solved:
        badge = "solved internally; export pending"
    elif summary.export_state == "failed":
        badge = f"export failed: {summary.export_reason}"
    else:
        badge = ""
    trace = {
        "unresolved": "root unresolved",
        "root_finalization_accepted": "root finalization accepted (internal)",
        "root_solved_internal": "root solved internally",
    }.get(state.root_status, state.root_status)
    return f"{trace}; {badge}" if badge else trace


def process_text(info: RunInfo, liveness: ProcessObservation, summary: SummaryView) -> str:
    age = fmt_age(age_seconds(info.last_write_ts))
    if liveness.status == "referenced":
        proc = f"process referenced by pid {', '.join(str(p) for p in liveness.pids)} (observation only)"
    elif liveness.status == "none_found":
        proc = "no referencing process found"
    else:
        proc = f"process liveness unknown ({liveness.detail})"
    if summary.present and summary.valid:
        terminal = "summary present"
        if summary.failure_reason:
            terminal += f" (failure_reason={summary.failure_reason})"
    elif summary.present:
        terminal = f"summary invalid ({summary.error})"
    else:
        terminal = "no summary"
    if info.has_maintenance_receipt:
        terminal += "; theory maintenance receipt present"
    return f"{proc}; last artifact write {age}; {terminal}"


def cost_text(state: RunState, summary: SummaryView) -> str:
    if state.cost_calls_priced == 0 and state.cost_calls_unpriced == 0:
        if summary.cost_usd is not None and summary.cost_available:
            return f"${summary.cost_usd:.2f} (summary)"
        return "spend unknown"
    text = f"${state.cost_accounted_usd:.2f} across {state.cost_calls_priced} priced calls"
    if state.cost_calls_unpriced:
        text += f"; {state.cost_calls_unpriced} calls unpriced (subscription or unknown pricing)"
    return text


def lanes_text(state: RunState) -> list[str]:
    lines = []
    for lane in state.lanes.values():
        if lane.count == 0:
            lines.append(f"{lane.name:8s} no activity recorded")
        else:
            lines.append(f"{lane.name:8s} {lane.count:5d} rows · last at {fmt_elapsed(lane.last_elapsed_s)} · {lane.last_text}")
    if state.deferred:
        for (activation, action), entry in list(state.deferred.items())[:20]:
            lines.append(f"deferred  {action} [{entry['scope']} {activation[:8]}] since {fmt_elapsed(entry['elapsed_s'])}: {entry['reason'] or entry['verdict']}")
        if len(state.deferred) > 20:
            lines.append(f"… {len(state.deferred) - 20} more deferrals")
    if state.releases_unmatched:
        lines.append(f"unmatched releases kept as history: {state.releases_unmatched}")
    return lines


def status_lines(run: AttachedRun) -> list[str]:
    state, summary = run.state, run.summary
    snap = state.snapshot
    theorem = summary.problem or run.info.label
    l1 = f"{theorem} · {root_status_text(state, summary)}"
    counts = []
    if snap:
        node = snap.get("node_count")
        openn = snap.get("open_nodes")
        proved = snap.get("proved_nodes")
        counts.append(f"graph nodes {node if node is not None else '?'} (open {openn if openn is not None else '?'}, proved {proved if proved is not None else '?'})")
        if snap.get("work_frontier_status") == "not_materialized_in_live_snapshot":
            counts.append("frontier not materialized (unknown, not zero)")
    counts.append(f"helpers accepted {len(state.helpers_accepted)}")
    if state.child_root_finalizations:
        counts.append(f"child roots finalized {state.child_root_finalizations}")
    l2 = f"elapsed {fmt_elapsed(state.last_elapsed_s)} · rows {state.rows} (recorder rows, not turns) · {' · '.join(counts)} · {cost_text(state, summary)}"
    lane_bits = []
    for lane in state.lanes.values():
        if lane.count:
            lane_bits.append(f"{lane.name}@{fmt_elapsed(lane.last_elapsed_s)}")
    deferred = f" · deferred {len(state.deferred)}" if state.deferred else ""
    backlog = " · BACKLOG" if run.backlog else ""
    boundary = " · resumed generation" if state.generation_boundary else ""
    l3 = f"{process_text(run.info, run.liveness, summary)} · lanes {' '.join(lane_bits) or 'none'}{deferred}{backlog}{boundary}"
    return [l1, l2, l3]


def config_lines(state: RunState) -> list[str]:
    lines = []
    for role, cfg in state.config.items():
        lines.append(f"{role:8s} {cfg['provider']} {cfg['model']} · reasoning mode {cfg['mode'] or 'unspecified'} effort {cfg['effort'] or cfg['effective_effort'] or 'unspecified'} · backend {cfg['base_url'] or 'api'}")
    for key, value in state.governors.items():
        lines.append(f"{key} = {value}")
    if state.answer_visibility:
        lines.append(f"answer visibility: {state.answer_visibility}")
    return lines or ["no run_config row observed yet"]


def transcript_lines(lines: Iterable[Line]) -> list[str]:
    out = []
    for line in lines:
        mark = _KIND_MARK.get(line.kind, "·")
        scope = f"[{line.scope}]" if line.scope else ""
        out.append(f"{fmt_elapsed(line.elapsed_s)} {mark} {scope} {line.text}".rstrip())
    return out


def milestone_lines(state: RunState, limit: int = 60) -> list[str]:
    items = list(state.milestones)[-limit:]
    return transcript_lines(items) or ["no milestones recorded"]


def helper_lines(state: RunState, limit: int = 100) -> list[str]:
    if not state.helpers_accepted:
        return ["no accepted helpers recorded"]
    items = sorted(state.helpers_accepted.items(), key=lambda kv: kv[1])[-limit:]
    lines = [f"{fmt_elapsed(elapsed)}  {name}" for name, elapsed in items]
    if state.helpers_overflow:
        lines.append(f"… {state.helpers_overflow} more helpers not retained")
    return lines


def live_graph_lines(state: RunState, *, limit: int = 80) -> list[str]:
    """Text projection of recorded search evidence; partial, not a kernel graph."""
    lines = ["proof structure from recorded search evidence (partial projection; a text view, not a kernel dependency graph)"]
    lines.append(f"◉ root: {state.root_status.replace('_', ' ')}")
    if state.root_helper_names:
        lines.append(f"  helpers named by the problem-scope root finalization ({len(state.root_helper_names)}):")
        for name in state.root_helper_names[:limit]:
            dep = " (dependency)" if name in state.root_dependency_helper_names else ""
            lines.append(f"    • {name}{dep}")
    snap = state.snapshot
    if snap:
        lines.append(f"  proof-state snapshot: nodes {snap.get('node_count', '?')} open {snap.get('open_nodes', '?')} proved {snap.get('proved_nodes', '?')} · frontier {snap.get('work_frontier_status', 'unknown')}")
    lines.append(f"accepted helpers ({len(state.helpers_accepted)}{'+' if state.helpers_overflow else ''}):")
    for name, elapsed in sorted(state.helpers_accepted.items(), key=lambda kv: kv[1])[-limit:]:
        supports = state.helper_supports.get(name) or []
        arrow = f" ← {', '.join(supports)}" if supports else ""
        lines.append(f"  • {fmt_elapsed(elapsed)} {name}{arrow}")
    if state.child_root_finalizations:
        lines.append(f"child roots finalized in subgoal scope: {state.child_root_finalizations} (scoped evidence, not problem completion)")
    if state.deferred:
        lines.append(f"deferred lanes: {len(state.deferred)}")
    return lines


def summary_lines(summary: SummaryView) -> list[str]:
    if not summary.present:
        return ["summary.json absent (run may be live, interrupted or lost)"]
    if not summary.valid:
        return [f"summary.json invalid: {summary.error}"]
    lines = [
        f"problem {summary.problem or '?'} · answer visibility {summary.answer_visibility or '?'}",
        f"internal solved: {summary.internal_solved if summary.internal_solved is not None else 'unknown'} · export {summary.export_state}: {summary.export_reason}",
        f"recorded rows {summary.recorded_rows if summary.recorded_rows is not None else '?'} (not logical turns) · wall {fmt_elapsed(summary.wall_clock_s)}",
    ]
    if summary.export_path:
        lines.append(f"export path {summary.export_path}")
    if summary.failure_reason:
        lines.append(f"failure reason {summary.failure_reason}")
    if summary.cost_usd is not None:
        lines.append(f"summary cost ${summary.cost_usd:.2f} (cost_available={summary.cost_available})")
    return lines


def run_listing_lines(listing: list[RunInfo], *, now: float | None = None) -> list[str]:
    now = time.time() if now is None else now
    lines = []
    for index, info in enumerate(listing, start=1):
        flags = []
        flags.append("summary" if info.has_summary else "no-summary")
        if info.has_checkpoints:
            flags.append("checkpoints")
        if info.attempt_id:
            flags.append(f"attempt {info.attempt_id[:8]}")
        lines.append(f"{index:3d}. {info.label:60s} {fmt_age(age_seconds(info.last_write_ts, now=now)):>10s}  {info.turns_bytes / 1e6:7.1f} MB  {' '.join(flags)}")
    return lines or ["no run directories found"]
