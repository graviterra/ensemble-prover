"""Confined, read-only discovery of Mini Prover run directories.

A run directory is any directory under the trusted root that holds at least
one of the recorder's marker files. Registry, checkpoint, scratch and export
directories are excluded by name. Sweep attempts nested under
``sweeps/<id>/attempts/<problem>/attempt_*`` are discovered and tagged with
their sweep. Symlinked directories are never followed.

Process liveness is tri-state: ``referenced`` (a ``/proc`` command line
mentions the run directory), ``none_found`` (``/proc`` was readable and no
command line matched) or ``unknown`` (``/proc`` unavailable or denied). A
match is an observation, never ownership or proof that the run is healthy.
"""

from __future__ import annotations

import json
import os
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

EXCLUDED_DIR_NAMES = frozenset(
    {".mini_attempts", "checkpoints", ".lean_tmp", "solved", "__pycache__", "sweeps"}
)
RUN_MARKERS = ("turns.jsonl", "run.log", "summary.json", "attempt_checkpoint.json")
_MAX_SMALL_JSON = 1024 * 1024
_MAX_CMDLINE = 64 * 1024


@dataclass
class RunInfo:
    path: Path
    name: str
    kind: str = "run"  # run | sweep_attempt
    sweep: str = ""
    has_turns: bool = False
    has_summary: bool = False
    has_attempt_checkpoint: bool = False
    has_checkpoints: bool = False
    has_answer_discovery: bool = False
    has_maintenance_receipt: bool = False
    turns_bytes: int = 0
    last_write_ts: float | None = None
    attempt_id: str = ""

    @property
    def label(self) -> str:
        if self.kind == "sweep_attempt":
            return f"{self.sweep}/{self.name}"
        return self.name


@dataclass
class ProcessObservation:
    status: str  # referenced | none_found | unknown
    pids: list[int] = field(default_factory=list)
    detail: str = ""


def _is_real_dir(path: Path) -> bool:
    try:
        return not path.is_symlink() and path.is_dir()
    except OSError:
        return False


def _read_small_json(path: Path) -> Any:
    try:
        if path.is_symlink() or not path.is_file():
            return None
        if path.stat().st_size > _MAX_SMALL_JSON:
            return None
        with path.open("rb") as handle:
            return json.loads(handle.read().decode("utf-8"))
    except (OSError, ValueError):
        return None


def inspect_run_dir(path: Path, *, kind: str = "run", sweep: str = "") -> RunInfo:
    info = RunInfo(path=path, name=path.name, kind=kind, sweep=sweep)
    latest: float | None = None
    for name in (
        "turns.jsonl",
        "run.log",
        "summary.json",
        "attempt_checkpoint.json",
        "answer_discovery.json",
        "theory_promotion_maintenance.json",
    ):
        candidate = path / name
        try:
            if candidate.is_symlink() or not candidate.is_file():
                continue
            st = candidate.stat()
        except OSError:
            continue
        latest = st.st_mtime if latest is None else max(latest, st.st_mtime)
        if name == "turns.jsonl":
            info.has_turns = True
            info.turns_bytes = st.st_size
        elif name == "summary.json":
            info.has_summary = True
        elif name == "attempt_checkpoint.json":
            info.has_attempt_checkpoint = True
            payload = _read_small_json(candidate)
            if isinstance(payload, dict) and isinstance(payload.get("attempt_id"), str):
                info.attempt_id = payload["attempt_id"]
        elif name == "answer_discovery.json":
            info.has_answer_discovery = True
        elif name == "theory_promotion_maintenance.json":
            info.has_maintenance_receipt = True
    info.has_checkpoints = _is_real_dir(path / "checkpoints")
    info.last_write_ts = latest
    return info


def is_run_dir(path: Path) -> bool:
    if not _is_real_dir(path):
        return False
    for marker in RUN_MARKERS:
        candidate = path / marker
        try:
            if candidate.is_file() and not candidate.is_symlink():
                return True
        except OSError:
            continue
    return False


def _safe_children(path: Path) -> list[Path]:
    try:
        return sorted(child for child in path.iterdir())
    except OSError:
        return []


def discover_runs(root: str | os.PathLike[str], *, limit: int = 500) -> list[RunInfo]:
    root_path = Path(root)
    if not _is_real_dir(root_path):
        return []
    found: list[RunInfo] = []
    for child in _safe_children(root_path):
        if child.name in EXCLUDED_DIR_NAMES or child.name.startswith("."):
            continue
        if is_run_dir(child):
            found.append(inspect_run_dir(child))
    sweeps = root_path / "sweeps"
    if _is_real_dir(sweeps):
        for sweep in _safe_children(sweeps):
            attempts = sweep / "attempts"
            if not _is_real_dir(sweep) or not _is_real_dir(attempts):
                continue
            for problem in _safe_children(attempts):
                if not _is_real_dir(problem):
                    continue
                for attempt in _safe_children(problem):
                    if attempt.name.startswith("attempt_") and is_run_dir(attempt):
                        found.append(
                            inspect_run_dir(
                                attempt,
                                kind="sweep_attempt",
                                sweep=f"{sweep.name}/{problem.name}",
                            )
                        )
    found.sort(key=lambda info: (info.last_write_ts or 0.0, info.name), reverse=True)
    return found[: max(0, int(limit))]


def resolve_contained_directory(root: Path, selector: str) -> Path | None:
    """Select existing, non-symlink children of a trusted root for the browser.

    Request components are compared with directory entries, never used to build
    a filesystem path. This differs deliberately from the CLI's explicit paths.
    """
    selector = selector.strip()
    relative = Path(selector)
    if not selector or "\0" in selector or relative.is_absolute() or ".." in relative.parts:
        return None
    if not relative.parts:
        return None
    descriptor: int | None = None
    try:
        current = root.resolve(strict=True)
        flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        descriptor = os.open(current, flags)
        for component in relative.parts:
            with os.scandir(descriptor) as children:
                match = next((child for child in children if child.name == component), None)
                if match is None:
                    return None
                child = os.open(match.name, flags, dir_fd=descriptor)
                os.close(descriptor)
                descriptor = child
                current = current / match.name
        return current
    except (OSError, RuntimeError, ValueError):
        return None
    finally:
        if descriptor is not None:
            os.close(descriptor)


def resolve_run_dir(root: Path, selector: str, listing: list[RunInfo] | None = None) -> Path | None:
    """Resolve an explicitly requested CLI index, run name, or local path."""
    selector = selector.strip()
    if not selector:
        return None
    if listing is not None and selector.isdigit():
        index = int(selector)
        if 1 <= index <= len(listing):
            return listing[index - 1].path
        return None
    candidates = [Path(selector), root / selector]
    for candidate in candidates:
        if is_run_dir(candidate):
            return candidate.resolve()
    return None


def observe_processes(run_dir: Path, *, proc_root: str | os.PathLike[str] = "/proc") -> ProcessObservation:
    proc = Path(proc_root)
    try:
        entries = os.listdir(proc)
    except OSError as exc:
        return ProcessObservation("unknown", [], f"/proc unavailable: {exc.__class__.__name__}")
    needle = os.fsencode(str(run_dir))
    pids: list[int] = []
    denied = 0
    for entry in entries:
        if not entry.isdigit():
            continue
        try:
            with open(proc / entry / "cmdline", "rb") as handle:
                cmdline = handle.read(_MAX_CMDLINE)
        except OSError:
            denied += 1
            continue
        if needle in cmdline:
            pids.append(int(entry))
    if pids:
        return ProcessObservation("referenced", sorted(pids), "command line references the run directory")
    if denied:
        return ProcessObservation("unknown", [], f"{denied} process command lines unreadable")
    return ProcessObservation("none_found", [], "no command line references the run directory")


def age_seconds(ts: float | None, *, now: float | None = None) -> float | None:
    if ts is None:
        return None
    return max(0.0, (time.time() if now is None else now) - ts)
