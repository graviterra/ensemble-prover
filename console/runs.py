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
_MAX_INPUT_BATCH_JSON = 32 * 1024 * 1024
_MAX_CMDLINE = 64 * 1024
_INPUT_GENERATION_MARKER = ".ensemble-input-generation"


@dataclass
class RunInfo:
    path: Path
    name: str
    kind: str = "run"  # run | sweep_attempt | input_batch | input_attempt
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
    batch_root: str = ""
    batch_state: str = ""
    batch_counts: dict[str, int] = field(default_factory=dict)
    target_name: str = ""
    target_status: str = ""

    @property
    def label(self) -> str:
        if self.kind == "sweep_attempt":
            return f"{self.sweep}/{self.name}"
        if self.kind == "input_attempt":
            return f"{Path(self.batch_root).name}/{self.target_name}"
        if self.kind == "input_batch":
            return f"{self.name} [input batch]"
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


def _read_small_json(path: Path, *, max_bytes: int = _MAX_SMALL_JSON) -> Any:
    try:
        if path.is_symlink() or not path.is_file():
            return None
        if path.stat().st_size > max_bytes:
            return None
        with path.open("rb") as handle:
            raw = handle.read(max_bytes + 1)
        return json.loads(raw.decode("utf-8")) if len(raw) <= max_bytes else None
    except (OSError, ValueError):
        return None


def _input_batch_manifest(path: Path) -> dict[str, Any] | None:
    data = _read_small_json(path / "batch_manifest.json", max_bytes=_MAX_INPUT_BATCH_JSON)
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        return None
    if data.get("kind") == "lean_input_batch":
        rows = data.get("queue")
    elif data.get("status") == "checked" and isinstance(data.get("metadata"), dict):
        rows = data.get("targets")
    else:
        return None
    return data if isinstance(rows, list) and all(isinstance(row, dict) for row in rows) else None


def is_input_batch_dir(path: Path) -> bool:
    """Recognize preparation and batch manifests without inventing run telemetry."""
    if not _is_real_dir(path):
        return False
    marker = path / _INPUT_GENERATION_MARKER
    return (not marker.is_symlink() and marker.is_file()) or _input_batch_manifest(path) is not None


def _input_batch_children(path: Path) -> list[tuple[Path, dict[str, Any]]]:
    manifest = _input_batch_manifest(path)
    if manifest is None or manifest.get("kind") != "lean_input_batch":
        return []
    children = []
    for row in manifest["queue"]:
        output = row.get("output_dir")
        if not isinstance(output, str):
            continue
        try:
            relative = Path(output).relative_to(path.absolute())
        except ValueError:
            continue
        # Only the producer's fixed layout is meaningful. Recorded paths may
        # not select another run, an external directory, or a symlink target.
        if len(relative.parts) != 3 or relative.parts[0] != "attempts" or relative.parts[2] != "run":
            continue
        child = resolve_contained_directory(path, str(relative))
        if child is None:
            continue
        proof = resolve_contained_directory(path, str(relative / "proof"))
        if proof is not None and is_run_dir(proof):
            child = proof
        if is_run_dir(child):
            children.append((child, row))
    return children


def active_input_batch_run(path: Path) -> Path | None:
    """Select only the currently running target; completed batches show totals."""
    manifest = _input_batch_manifest(path)
    if manifest is None or "exit_code" in manifest:
        return None
    return next((child for child, row in _input_batch_children(path)
                 if row.get("status") == "running"), None)


def _input_batch_membership(path: Path) -> tuple[Path, dict[str, Any]] | None:
    path = path.absolute()
    if path.name == "proof" and path.parent.name == "run" and len(path.parents) >= 4:
        batch = path.parents[3]
    elif path.name == "run" and len(path.parents) >= 3:
        batch = path.parents[2]
    else:
        return None
    if not is_input_batch_dir(batch):
        return None
    return next(((batch, row) for child, row in _input_batch_children(batch)
                 if child == path or (child.name == "proof" and child.parent == path)), None)


def input_batch_for_run(path: Path) -> Path | None:
    """Bind a child to its batch only through a confined, matching manifest row."""
    binding = _input_batch_membership(path)
    return binding[0] if binding is not None else None


def inspect_run_dir(
    path: Path, *, kind: str = "run", sweep: str = "",
    batch_target: tuple[Path, dict[str, Any]] | None = None,
) -> RunInfo:
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
    if is_input_batch_dir(path):
        manifest = _input_batch_manifest(path)
        info.kind, info.batch_root = "input_batch", str(path)
        info.batch_state = "preparing"
        if manifest is not None:
            rows = manifest.get("queue", manifest.get("targets", []))
            for row in rows:
                status = str(row.get("status") or ("blocked" if row.get("error") else "ready"))
                info.batch_counts[status] = info.batch_counts.get(status, 0) + 1
            info.batch_state = ("checked" if manifest.get("status") == "checked" else
                                f"complete (exit {manifest['exit_code']})" if "exit_code" in manifest else
                                "running" if info.batch_counts.get("running") else "ready")
        elif (path / "batch_manifest.json").exists():
            info.batch_state = "manifest unavailable"
        for name in ("batch_manifest.json", _INPUT_GENERATION_MARKER):
            candidate = path / name
            try:
                if not candidate.is_symlink() and candidate.is_file():
                    info.last_write_ts = max(info.last_write_ts or 0, candidate.stat().st_mtime)
            except OSError:
                pass
    else:
        binding = batch_target or _input_batch_membership(path)
        if binding is not None:
            batch, row = binding
            info.kind, info.batch_root = "input_attempt", str(batch)
            info.target_name = str(row.get("theorem_name") or row.get("name") or path.parent.name)
            info.target_status = str(row.get("status") or "unknown")
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
        if is_input_batch_dir(child):
            if not is_run_dir(child):
                found.append(inspect_run_dir(child))
            found.extend(inspect_run_dir(path, batch_target=(child, row))
                         for path, row in _input_batch_children(child))
    inputs = root_path / "inputs"
    if _is_real_dir(inputs):
        for batch in _safe_children(inputs):
            if is_input_batch_dir(batch):
                found.append(inspect_run_dir(batch))
                found.extend(inspect_run_dir(path, batch_target=(batch, row))
                             for path, row in _input_batch_children(batch))
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
        if is_run_dir(candidate) or is_input_batch_dir(candidate):
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
