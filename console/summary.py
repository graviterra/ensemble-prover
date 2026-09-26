"""Read ``summary.json`` and classify it with the canonical solved policy.

The policy functions are imported from ``ensemble_prover.solved_export_policy``
at call time. If that import fails the console fails closed: the export
state becomes ``policy_unavailable`` and no verified badge can be shown.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

_MAX_SUMMARY_BYTES = 64 * 1024 * 1024


@dataclass
class SummaryView:
    present: bool = False
    valid: bool = False
    error: str = ""
    policy_available: bool = False
    internal_solved: bool | None = None
    export_state: str = "unavailable"  # verified | pending | failed | unavailable | policy_unavailable
    export_reason: str = ""
    export_path: str = ""
    failure_reason: str = ""
    recorded_rows: int | None = None
    wall_clock_s: float | None = None
    problem: str = ""
    answer_visibility: str = ""
    cost_usd: float | None = None
    cost_available: bool | None = None
    raw_keys: int = 0
    extra: dict[str, Any] = field(default_factory=dict)


def _load_policy() -> dict[str, Callable[[Any], Any]] | None:
    try:
        from ensemble_prover.solved_export_policy import (  # type: ignore
            effective_solved,
            export_boundary_present,
            solved_export_failure_reason,
            solved_export_verified_payload,
        )
    except Exception:  # noqa: BLE001 - fail closed on any import problem
        return None
    return {
        "effective_solved": effective_solved,
        "export_boundary_present": export_boundary_present,
        "solved_export_verified_payload": solved_export_verified_payload,
        "solved_export_failure_reason": solved_export_failure_reason,
    }


def classify_summary(summary: dict[str, Any], policy: dict[str, Callable[[Any], Any]] | None) -> SummaryView:
    view = SummaryView(present=True, valid=True, raw_keys=len(summary))
    view.problem = str(summary.get("problem") or summary.get("theorem_name") or "")
    view.answer_visibility = str(summary.get("answer_visibility") or "")
    rows = summary.get("total_turns")
    view.recorded_rows = rows if isinstance(rows, int) and not isinstance(rows, bool) else None
    wall = summary.get("wall_clock_s")
    view.wall_clock_s = float(wall) if isinstance(wall, (int, float)) and not isinstance(wall, bool) else None
    failure = summary.get("failure_reason")
    view.failure_reason = str(failure) if failure else ""
    cost = summary.get("cost_usd")
    view.cost_usd = float(cost) if isinstance(cost, (int, float)) and not isinstance(cost, bool) else None
    available = summary.get("cost_available")
    view.cost_available = available if isinstance(available, bool) else None
    path = summary.get("mini_solved_export_path")
    view.export_path = str(path) if isinstance(path, str) else ""
    if policy is None:
        view.policy_available = False
        view.export_state = "policy_unavailable"
        view.export_reason = "solved policy import failed; verified badges withheld"
        return view
    view.policy_available = True
    try:
        solved = bool(policy["effective_solved"](summary))
        # Mini clears the final solved bit while the supervisor verifies an
        # internally completed root, and keeps it false after export failure.
        view.internal_solved = any(
            summary.get(key) is True
            for key in ("solved", "pre_export_solved", "session_root_finalized")
        )
        if not policy["export_boundary_present"](summary):
            view.export_state = "pending" if view.internal_solved else "unavailable"
            view.export_reason = (
                "internal solve claim; export boundary absent" if view.internal_solved
                else "not solved by the canonical policy"
            )
            return view
        if solved and policy["solved_export_verified_payload"](summary):
            view.export_state = "verified"
            view.export_reason = "export boundary present and verified payload"
            return view
        reason = str(policy["solved_export_failure_reason"](summary) or "export not verified")
        if reason in {"not_attempted", "pending_supervisor_verification"}:
            view.export_state = "pending" if view.internal_solved else "unavailable"
            view.export_reason = reason
            return view
        view.export_state = "failed"
        view.export_reason = reason if reason != "verified" else "not solved by the canonical policy"
    except Exception as exc:  # noqa: BLE001 - policy evaluation must fail closed
        view.policy_available = False
        view.internal_solved = None
        view.export_state = "policy_unavailable"
        view.export_reason = f"policy evaluation failed: {exc.__class__.__name__}"
    return view


def load_summary(run_dir: Path, *, policy_loader: Callable[[], dict[str, Callable[[Any], Any]] | None] = _load_policy) -> SummaryView:
    path = run_dir / "summary.json"
    try:
        if path.is_symlink() or not path.is_file():
            return SummaryView(present=False, export_state="unavailable", export_reason="summary.json absent")
        if path.stat().st_size > _MAX_SUMMARY_BYTES:
            return SummaryView(present=True, valid=False, error="summary.json exceeds size limit")
        with path.open("rb") as handle:
            payload = json.loads(handle.read().decode("utf-8"))
    except OSError as exc:
        return SummaryView(present=True, valid=False, error=f"unreadable: {exc.__class__.__name__}")
    except ValueError as exc:
        return SummaryView(present=True, valid=False, error=f"invalid JSON: {exc}")
    if not isinstance(payload, dict):
        return SummaryView(present=True, valid=False, error="summary.json is not an object")
    return classify_summary(payload, policy_loader())
