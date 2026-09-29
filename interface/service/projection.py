"""Bounded, public projections of run and launch state."""

from __future__ import annotations

import json
import math
import stat
import threading
from collections import OrderedDict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, TypeVar

from console.launcher import read_boot_id, read_launches, read_proc_identity
from console.runs import RunInfo
from console.session import AttachedRun
from console.summary import SummaryView, load_summary
from .mathematics import node_mathematics

_MAX_TEXT_BYTES = 256 * 1024
_MAX_LEAN_BYTES = 2 * 1024 * 1024
_MAX_FORMALIZATION_BYTES = 16 * 1024 * 1024
_MAX_MILESTONES = 200
_ARTIFACT_NAMES = ("Problem.lean", "formalization.json", "problem.txt")
_RUNNING_LAUNCH_STATES = frozenset({"running", "launch_pending"})
_T = TypeVar("_T")
_FileStamp = tuple[int, int, int, int, int]


@dataclass(frozen=True)
class FormalizationMetadata:
    status: str = ""
    problem: str = ""
    last_write_ts: float | None = None


class FormalizationCache:
    """Cache compact library fields, invalidating on artifact file changes."""

    def __init__(self, *, max_entries: int = 512) -> None:
        self.max_entries = max(1, int(max_entries))
        self._entries: OrderedDict[
            Path, tuple[tuple[_FileStamp | None, ...], FormalizationMetadata]
        ] = OrderedDict()
        self._lock = threading.Lock()

    def read(self, state_root: Path, record: Any | None) -> FormalizationMetadata:
        """Read status and problem once per file version without loading Lean source."""

        if record is None or _launch_field(record, "kind") != "nl":
            return FormalizationMetadata(status="unavailable")
        fallback = "starting" if _launch_field(record, "status") in _RUNNING_LAUNCH_STATES else "unavailable"
        directory = _formalization_directory(state_root, _launch_field(record, "launch_id"))
        if directory is None:
            return FormalizationMetadata(status=fallback)
        with self._lock:
            signature = _artifact_signature(directory)
            entry = self._entries.get(directory)
            if entry is not None and entry[0] == signature:
                self._entries.move_to_end(directory)
                metadata = entry[1]
            else:
                payload = _read_json_object(directory / "formalization.json", _MAX_FORMALIZATION_BYTES) or {}
                problem = _read_text(directory / "problem.txt", _MAX_TEXT_BYTES)
                metadata = FormalizationMetadata(
                    status=_bounded_line(payload.get("status"), 64),
                    problem=problem or _bounded_text(payload.get("statement"), _MAX_TEXT_BYTES),
                    last_write_ts=_signature_time(signature),
                )
                self._entries[directory] = (signature, metadata)
                self._entries.move_to_end(directory)
                if len(self._entries) > self.max_entries:
                    self._entries.popitem(last=False)
        return FormalizationMetadata(metadata.status or fallback, metadata.problem, metadata.last_write_ts)


class FormalizationDetailCache:
    """Keep a small cache of allowlisted detail fields, never provider transcripts."""

    def __init__(self, *, max_entries: int = 16) -> None:
        self.max_entries = max(1, int(max_entries))
        self._entries: OrderedDict[
            Path,
            tuple[tuple[_FileStamp | None, ...], str, tuple[dict[str, Any], str, float | None]],
        ] = OrderedDict()
        self._lock = threading.Lock()

    def read(self, state_root: Path, record: Any | None) -> tuple[dict[str, Any], str, float | None]:
        """Reuse a sanitized artifact projection while files and launch status match."""

        if record is None or _launch_field(record, "kind") != "nl":
            return _formalization_or_empty(state_root, record)
        directory = _formalization_directory(state_root, _launch_field(record, "launch_id"))
        if directory is None:
            return _formalization_or_empty(state_root, record)
        status = _launch_field(record, "status")
        with self._lock:
            signature = _artifact_signature(directory)
            entry = self._entries.get(directory)
            if entry is not None and entry[0] == signature and entry[1] == status:
                self._entries.move_to_end(directory)
                result = entry[2]
            else:
                result = public_formalization(state_root, record)
                self._entries[directory] = (signature, status, result)
                self._entries.move_to_end(directory)
                if len(self._entries) > self.max_entries:
                    self._entries.popitem(last=False)
        body, problem, latest = result
        return {**body, "artifactFiles": list(body["artifactFiles"])}, problem, latest


@dataclass
class _SessionEntry:
    attached: AttachedRun
    lock: threading.Lock


class SessionCache:
    """Keep a small LRU of incremental reducers and serialize each poll."""

    def __init__(self, *, max_entries: int = 16) -> None:
        self.max_entries = max(1, int(max_entries))
        self._entries: OrderedDict[Path, _SessionEntry] = OrderedDict()
        self._lock = threading.Lock()

    def project(self, run_dir: Path, projector: Callable[[AttachedRun], _T]) -> _T:
        """Poll and copy a public projection while holding the session lock."""

        key = Path(run_dir).resolve()
        with self._lock:
            entry = self._entries.get(key)
            if entry is None:
                if len(self._entries) >= self.max_entries:
                    oldest_key, oldest = next(iter(self._entries.items()))
                    oldest.lock.acquire()
                    try:
                        del self._entries[oldest_key]
                    finally:
                        oldest.lock.release()
                entry = _SessionEntry(AttachedRun.attach(key), threading.Lock())
                self._entries[key] = entry
            else:
                self._entries.move_to_end(key)
            entry.lock.acquire()
        try:
            entry.attached.poll()
            return projector(entry.attached)
        finally:
            entry.lock.release()


def launches_for_request(state_root: Path, registry: Any) -> list[Any]:
    """Observe live registry state when available, otherwise read it purely."""

    listing = getattr(registry, "list", None)
    if callable(listing):
        try:
            records = listing()
        except Exception:  # noqa: BLE001 - an unavailable registry must not break browsing
            pass
        else:
            if isinstance(records, list):
                return records
    records = read_launches(state_root)
    for record in records:
        if record.status == "launch_pending":
            record.status = "unknown"
        elif record.status == "running" and not _persisted_identity_matches(record):
            record.status = "unknown"
    return records


def launch_output(record: Any, run_root: Path) -> Path | None:
    raw = str(getattr(record, "output_dir", "") or "")
    if not raw:
        return None
    root = Path(run_root).resolve()
    candidate = Path(raw)
    try:
        resolved = candidate.resolve()
        resolved.relative_to(root)
    except (OSError, ValueError):
        return None
    try:
        if candidate.is_symlink() or not resolved.is_dir():
            return None
    except OSError:
        return None
    return resolved


def launch_by_path(launches: list[Any], run_root: Path) -> dict[Path, Any]:
    result: dict[Path, Any] = {}
    for record in launches:
        path = launch_output(record, run_root)
        if path is not None:
            result.setdefault(path, record)
    return result


def public_formalization(state_root: Path, record: Any) -> tuple[dict[str, Any], str, float | None]:
    """Return allowlisted formalization fields and files for one owned launch."""

    launch_id = str(getattr(record, "launch_id", "") or "")
    status = str(getattr(record, "status", "") or "")
    empty = {
        "status": "starting" if status in _RUNNING_LAUNCH_STATES else "unavailable",
        "statement": "",
        "message": "",
        "leanSource": "",
        "leanFile": "",
        "artifactFiles": [],
    }
    artifact_dir = _formalization_directory(state_root, launch_id)
    if artifact_dir is None:
        return empty, "", None

    files: list[str] = []
    latest: float | None = None
    for name in _ARTIFACT_NAMES:
        candidate = artifact_dir / name
        try:
            if candidate.is_symlink() or not candidate.is_file():
                continue
            stamp = candidate.stat().st_mtime
        except OSError:
            continue
        files.append(name)
        latest = stamp if latest is None else max(latest, stamp)

    payload = _read_json_object(artifact_dir / "formalization.json", _MAX_FORMALIZATION_BYTES)
    result_status = _bounded_line(payload.get("status"), 64) if payload else ""
    if not result_status:
        result_status = empty["status"]
    statement = _bounded_text(payload.get("statement"), _MAX_TEXT_BYTES) if payload else ""
    message = _bounded_text(payload.get("message"), 16 * 1024) if payload else ""
    problem = _read_text(artifact_dir / "problem.txt", _MAX_TEXT_BYTES)
    source = _read_text(artifact_dir / "Problem.lean", _MAX_LEAN_BYTES)
    return (
        {
            "status": result_status,
            "statement": statement,
            "message": message,
            "leanSource": source,
            "leanFile": "Problem.lean" if source else "",
            "artifactFiles": files,
        },
        problem or statement,
        latest,
    )


def library_run(
    info: RunInfo, run_root: Path, record: Any | None, state_root: Path,
    metadata_cache: FormalizationCache,
) -> dict[str, Any]:
    """Project one discovered run without replaying traces or reading processes."""

    summary = load_summary(info.path)
    formalization = metadata_cache.read(state_root, record)
    body = {
        "id": _public_id(run_root, info.path),
        "label": info.label,
        "kind": info.kind,
        "problem": summary.problem or formalization.problem,
        "exportState": summary.export_state,
        "internalSolved": summary.internal_solved,
        "rootStatus": _library_root_status(summary),
        "hasSummary": info.has_summary,
        "lastWriteTs": _latest(info.last_write_ts, formalization.last_write_ts),
        "launchId": _launch_field(record, "launch_id"),
        "launchStatus": _launch_field(record, "status"),
        "formalizationStatus": formalization.status,
    }
    return body


def library_launch(
    record: Any, run_root: Path, state_root: Path, metadata_cache: FormalizationCache,
) -> dict[str, Any] | None:
    path = launch_output(record, run_root)
    if path is None:
        return None
    formalization = metadata_cache.read(state_root, record)
    problem = formalization.problem
    created = _number(getattr(record, "created_at", None))
    return {
        "id": _public_id(run_root, path),
        "label": problem or path.name,
        "kind": "english" if _launch_field(record, "kind") == "nl" else _launch_field(record, "kind") or "run",
        "problem": problem,
        "exportState": "unavailable",
        "internalSolved": None,
        "rootStatus": launch_root_status(record, formalization.status),
        "hasSummary": False,
        "lastWriteTs": _latest(created, formalization.last_write_ts),
        "launchId": _launch_field(record, "launch_id"),
        "launchStatus": _launch_field(record, "status"),
        "formalizationStatus": formalization.status,
    }


def launch_updated_at(record: Any, state_root: Path, *, include_created: bool = True) -> float | None:
    """Read only artifact timestamps when selecting library candidates."""

    created = _number(getattr(record, "created_at", None)) if include_created else None
    if _launch_field(record, "kind") != "nl":
        return created
    directory = _formalization_directory(state_root, _launch_field(record, "launch_id"))
    if directory is None:
        return created
    return _latest(created, _signature_time(_artifact_signature(directory)))


def _library_root_status(summary: SummaryView) -> str:
    if summary.export_state == "verified":
        return "VERIFIED EXPORT (canonical policy)"
    if summary.export_state == "policy_unavailable":
        return "policy unavailable; verified badge withheld"
    if summary.export_state == "failed":
        return f"export failed: {summary.export_reason}"
    if summary.internal_solved:
        return "solved internally; export pending"
    return "open attempt for recorded progress"


def launch_detail(
    record: Any, run_root: Path, state_root: Path, detail_cache: FormalizationDetailCache,
) -> dict[str, Any] | None:
    path = launch_output(record, run_root)
    if path is None:
        return None
    formalization, problem, _artifact_ts = detail_cache.read(state_root, record)
    return {
        "id": _public_id(run_root, path),
        "label": problem or path.name,
        "kind": "english" if _launch_field(record, "kind") == "nl" else _launch_field(record, "kind") or "run",
        "problem": problem,
        "exportState": "unavailable",
        "exportReason": "no completed run summary is available",
        "internalSolved": None,
        "rootStatus": launch_root_status(record, formalization["status"]),
        "hasSummary": False,
        "childRootFinalizations": 0,
        "cost": "spend unknown",
        "process": launch_process(record),
        "lanes": [
            {"name": name, "count": 0, "lastText": ""}
            for name in ("prover", "refiner", "planner", "lean")
        ],
        "milestones": [],
        "graph": [{"id": "root", "label": problem or "root", "kind": "root", "status": "unresolved"}],
        "launchId": _launch_field(record, "launch_id"),
        "launchStatus": _launch_field(record, "status"),
        "formalization": formalization,
    }


def decorate_detail(
    body: dict[str, Any], attached: AttachedRun, record: Any | None, state_root: Path,
    detail_cache: FormalizationDetailCache,
) -> None:
    body["exportReason"] = attached.summary.export_reason
    body["milestones"] = [
        {"elapsedS": line.elapsed_s, "text": line.text, "kind": line.kind}
        for line in list(attached.state.milestones)[-_MAX_MILESTONES:]
    ]
    formalization, _problem, _artifact_ts = detail_cache.read(state_root, record)
    body["launchId"] = _launch_field(record, "launch_id")
    body["launchStatus"] = _launch_field(record, "status")
    body["formalization"] = formalization
    graph = body.get("graph")
    root = graph[0] if isinstance(graph, list) and graph and isinstance(graph[0], dict) else {}
    body["nodeEvidence"] = node_mathematics(attached, str(root.get("label") or ""))


def launch_root_status(record: Any, formalization_status: str) -> str:
    launch_status = _launch_field(record, "status")
    if launch_status == "launch_failed":
        return "launch failed"
    if launch_status == "launch_delivery_unknown":
        return "launch delivery unknown"
    if launch_status == "unknown":
        return "launch delivery unknown"
    if formalization_status in {"formalized", "translated", "success", "ready"}:
        return "translation ready"
    if formalization_status in {"needs_clarification", "clarification_needed"}:
        return "translation needs clarification"
    if formalization_status in {"failed", "error", "incomplete", "cancelled"}:
        return "translation failed"
    if launch_status in _RUNNING_LAUNCH_STATES:
        return "formalizing" if _launch_field(record, "kind") == "nl" else "starting"
    if launch_status == "exited":
        return "finished without run output"
    return "starting"


def launch_process(record: Any) -> dict[str, str]:
    status = _launch_field(record, "status")
    if status == "launch_failed":
        return {"status": "exited", "detail": "The launcher did not start a process."}
    if status == "running":
        return {"status": "running", "detail": "The owned launch is in progress."}
    if status == "launch_pending":
        return {"status": "starting", "detail": "The launch request is pending."}
    if status == "launch_delivery_unknown":
        return {"status": "unknown", "detail": "Launch delivery could not be confirmed."}
    if status == "exited":
        return {"status": "exited", "detail": "The owned launch exited."}
    return {"status": "unknown", "detail": "No process state is available."}


def _formalization_or_empty(state_root: Path, record: Any | None) -> tuple[dict[str, Any], str, float | None]:
    if record is None or _launch_field(record, "kind") != "nl":
        return ({"status": "unavailable", "statement": "", "message": "", "leanSource": "", "leanFile": "", "artifactFiles": []}, "", None)
    return public_formalization(state_root, record)


def _formalization_directory(state_root: Path, launch_id: str) -> Path | None:
    if not _safe_component(launch_id):
        return None
    state = Path(state_root).resolve()
    spelled_root = Path(state_root) / "nl"
    try:
        if spelled_root.is_symlink():
            return None
        root = spelled_root.resolve()
        root.relative_to(state)
        directory = root / launch_id
        if directory.is_symlink() or not directory.is_dir():
            return None
        directory.resolve().relative_to(root)
    except (OSError, ValueError):
        return None
    return directory


def _artifact_signature(directory: Path) -> tuple[_FileStamp | None, ...]:
    stamps: list[_FileStamp | None] = []
    for name in _ARTIFACT_NAMES:
        try:
            info = (directory / name).lstat()
            stamp = (
                (info.st_dev, info.st_ino, info.st_mtime_ns, info.st_ctime_ns, info.st_size)
                if stat.S_ISREG(info.st_mode) else None
            )
        except OSError:
            stamp = None
        stamps.append(stamp)
    return tuple(stamps)


def _signature_time(signature: tuple[_FileStamp | None, ...]) -> float | None:
    return _latest(*(stamp[2] / 1_000_000_000 for stamp in signature if stamp is not None))


def _read_json_object(path: Path, limit: int) -> dict[str, Any] | None:
    text = _read_text(path, limit)
    if not text:
        return None
    try:
        payload = json.loads(text)
    except (ValueError, RecursionError):
        return None
    return payload if isinstance(payload, dict) else None


def _read_text(path: Path, limit: int) -> str:
    try:
        if path.is_symlink() or not path.is_file():
            return ""
        with path.open("rb") as handle:
            raw = handle.read(limit + 1)
        if len(raw) > limit:
            return ""
        return raw.decode("utf-8")
    except (OSError, UnicodeError):
        return ""


def _bounded_text(value: Any, limit: int) -> str:
    if not isinstance(value, str):
        return ""
    encoded = value.encode("utf-8", errors="replace")
    if len(encoded) <= limit:
        return encoded.decode("utf-8")
    return encoded[:limit].decode("utf-8", errors="ignore")


def _bounded_line(value: Any, limit: int) -> str:
    text = _bounded_text(value, limit).replace("\n", " ").replace("\r", " ")
    return text.strip()


def _safe_component(value: str) -> bool:
    return bool(value) and len(value) <= 128 and all(ch.isalnum() or ch in "_-" for ch in value)


def _public_id(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.name


def _launch_field(record: Any | None, field: str) -> str:
    return str(getattr(record, field, "") or "") if record is not None else ""


def _number(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        number = float(value)
    except OverflowError:
        return None
    return number if math.isfinite(number) else None


def _latest(*values: float | None) -> float | None:
    present = [value for value in values if value is not None]
    return max(present) if present else None


def _persisted_identity_matches(record: Any) -> bool:
    pid = getattr(record, "pid", None)
    pgid = getattr(record, "pgid", None)
    start_ticks = getattr(record, "start_ticks", None)
    boot_id = getattr(record, "boot_id", "")
    if any(isinstance(value, bool) or not isinstance(value, int) for value in (pid, pgid, start_ticks)):
        return False
    if pid <= 0 or pgid <= 0 or start_ticks < 0 or not isinstance(boot_id, str) or not boot_id:
        return False
    current_boot = read_boot_id(Path("/proc"))
    if not current_boot or current_boot != boot_id:
        return False
    identity = read_proc_identity(pid, Path("/proc"))
    return identity == (pgid, start_ticks)
