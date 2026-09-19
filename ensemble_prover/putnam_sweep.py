"""Persisted, sequential Putnam sweeps with accepted-proof throughput gates.

Run ``python -m ensemble_prover.putnam_sweep --help`` from a repository checkout.
Each problem retains MiniProver's own parallel samples and process supervisor.
"""

from __future__ import annotations

import argparse
import codecs
import fcntl
import hashlib
import json
import math
import os
import random
import re
import secrets
import select
import signal
import subprocess
import sys
import time
from contextlib import contextmanager
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import Any, BinaryIO, Callable, Iterator, Mapping, Sequence

from .solved_export_policy import effective_solved, export_boundary_present
from .subprocess_environment import (
    sanitized_subprocess_environment,
    trusted_provider_worker_environment,
)


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_FIRST_ACCEPTED_BY_S = 1200.0
DEFAULT_SECOND_ACCEPTED_BY_S = 1800.0
DEFAULT_STARTUP_LIVENESS_S = 180.0
_MATHLIB_PREWARM_SOURCE = "import Mathlib\nexample : True := by trivial\n"
_PROBLEM = re.compile(r"putnam_\d{4}_[ab][1-6]")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_TERMINAL = {
    "solved",
    "failed",
    "cutoff",
    "skipped_solved",
    "answer_preparation_failed",
}
_STATUSES = _TERMINAL | {
    "pending",
    "running",
    "interrupted",
    "cleanup_unconfirmed",
    "monitor_error",
}


def _seconds(value: Any) -> float:
    if isinstance(value, bool):
        raise ValueError("deadline values must be positive finite seconds")
    try:
        number = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError("deadline values must be positive finite seconds") from exc
    if not math.isfinite(number) or number <= 0:
        raise ValueError("deadline values must be positive finite seconds")
    return number


def _acceptance_seconds(value: Any) -> float:
    """Zero disables an acceptance gate; polling/cleanup still require > 0."""
    if not isinstance(value, bool) and isinstance(value, (int, float)) and value == 0:
        return 0.0
    return _seconds(value)


@dataclass
class AcceptanceGate:
    start_monotonic: float
    first_accepted_by_s: float = DEFAULT_FIRST_ACCEPTED_BY_S
    second_accepted_by_s: float = DEFAULT_SECOND_ACCEPTED_BY_S
    accepted: dict[str, float] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self.first_accepted_by_s = _acceptance_seconds(self.first_accepted_by_s)
        self.second_accepted_by_s = _acceptance_seconds(self.second_accepted_by_s)
        if (self.first_accepted_by_s and self.second_accepted_by_s
                and self.second_accepted_by_s < self.first_accepted_by_s):
            raise ValueError("second acceptance deadline must not precede the first")

    def observe(self, record: Mapping[str, Any], *, now: float) -> bool:
        """Consume only committed proof receipts belonging to this attempt."""
        if (record.get("phase"), record.get("verdict")) != (
            "session_accepted_proof",
            "accepted_proof_committed",
        ):
            return False
        identity = record.get("acceptance_identity")
        accepted_at = record.get("acceptance_monotonic_s")
        if not isinstance(identity, str) or not _SHA256.fullmatch(identity):
            return False
        if isinstance(accepted_at, bool) or not isinstance(accepted_at, (int, float)):
            return False
        if (
            not math.isfinite(accepted_at)
            or not self.start_monotonic <= accepted_at <= now
        ):
            return False
        elapsed = float(accepted_at) - self.start_monotonic
        previous = self.accepted.get(identity)
        self.accepted[identity] = (
            elapsed if previous is None else min(previous, elapsed)
        )
        return previous is None

    def cutoff_reason(self, *, now: float) -> str | None:
        elapsed = now - self.start_monotonic
        if self.first_accepted_by_s and elapsed >= self.first_accepted_by_s and not any(
            value <= self.first_accepted_by_s for value in self.accepted.values()
        ):
            return "first_acceptance_deadline"
        if (
            self.second_accepted_by_s
            and elapsed >= self.second_accepted_by_s
            and sum(
                value <= self.second_accepted_by_s for value in self.accepted.values()
            )
            < 2
        ):
            return "second_acceptance_deadline"
        return None


class AcceptanceEventTail:
    """Read complete JSONL receipts without losing a partially written record."""

    def __init__(self, path: Path):
        self.path = Path(path)
        self.offset = 0
        self.identity: tuple[int, int] | None = None
        self.alive = False

    def read(self) -> list[dict[str, Any]]:
        try:
            handle = self.path.open("rb")
        except FileNotFoundError:
            return []
        records = []
        with handle:
            stat = os.fstat(handle.fileno())
            identity = (stat.st_dev, stat.st_ino)
            if (
                self.identity is not None and self.identity != identity
            ) or stat.st_size < self.offset:
                raise ValueError("acceptance log changed identity or was truncated")
            self.identity = identity
            handle.seek(self.offset)
            for line in handle:
                if not line.endswith(b"\n"):
                    break
                self.offset += len(line)
                try:
                    record = json.loads(line)
                except (ValueError, UnicodeError):
                    continue
                if not isinstance(record, dict):
                    continue
                self.alive = True
                if record.get("phase") == "session_accepted_proof":
                    records.append(record)
        return records


class AttemptStartupLiveness:
    """Observe preparation separately, then allow a fresh proof startup window."""

    def __init__(self, output_dir: Path, *, start: float, timeout_s: float):
        self.output_dir = output_dir
        self.start = start
        self.timeout_s = timeout_s
        self.proof_started_at: float | None = None
        self.preparation = AcceptanceEventTail(
            answer_preparation_dir(output_dir) / "capability_preflight.jsonl"
        )

    def expired(self, *, now: float, proof_alive: bool) -> bool:
        if not self.timeout_s or proof_alive:
            return False
        if self.proof_started_at is None:
            if (answer_preparation_dir(self.output_dir) / "prover_command.json").is_file():
                self.proof_started_at = now
            else:
                # Preparation readiness is liveness, never accepted proof.
                # Its own worker watchdog and the original acceptance gate
                # continue to bound this phase, including long provider calls.
                self.preparation.read()
                discovery = _load_answer_discovery(self.output_dir) or {}
                if self.preparation.alive or discovery.get("status") in {
                    "running", "candidate_ready",
                }:
                    return False
        start = self.start if self.proof_started_at is None else self.proof_started_at
        return now - start >= self.timeout_s


def default_lean_project_dir() -> Path:
    return ROOT / "lean_project"


def prewarm_shared_mathlib_runtime(
    *,
    project_dir: Path | None = None,
    timeout_s: float = 180.0,
) -> dict[str, Any]:
    """Import Mathlib once so attempt processes do not pay a cold lake start.

    Problem-specific ``proof_state_cache_seed`` still runs after attempt launch
    and counts against the acceptance clock. Missing lake/project is a skip,
    not a sweep failure.
    """
    project = Path(project_dir or default_lean_project_dir()).expanduser()
    try:
        project = project.resolve()
    except OSError:
        return {"status": "skipped", "reason": "lean_project_missing", "elapsed_s": 0.0}
    if not project.is_dir() or not any(
        (project / name).is_file() for name in ("lakefile.lean", "lakefile.toml")
    ):
        return {"status": "skipped", "reason": "lean_project_missing", "elapsed_s": 0.0}
    timeout_s = _seconds(timeout_s)
    snippet: Path | None = None
    proc: subprocess.Popen | None = None
    cleanup_confirmed = True
    status, reason = "failed", ""
    started = time.monotonic()
    try:
        with NamedTemporaryFile(
            "w",
            encoding="utf-8",
            suffix=".lean",
            prefix="sweep_mathlib_prewarm_",
            dir=project,
            delete=False,
        ) as handle:
            snippet = Path(handle.name)
            handle.write(_MATHLIB_PREWARM_SOURCE)
            handle.flush()
        proc = subprocess.Popen(
            ["lake", "env", "lean", str(snippet)],
            cwd=str(project),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            env=sanitized_subprocess_environment(),
            start_new_session=True,
        )
        returncode = proc.wait(timeout=timeout_s)
        status = "ok" if returncode == 0 else "failed"
        reason = "" if status == "ok" else "lake_env_lean_failed"
    except FileNotFoundError:
        status, reason = "skipped", "lake_not_found"
    except subprocess.TimeoutExpired:
        status, reason = "timeout", "mathlib_prewarm_timeout"
    except Exception as exc:
        status, reason = "failed", f"{type(exc).__name__}: {exc}"
    finally:
        if proc is not None:
            # Lake spawns Lean rather than exec'ing it. Keep its PGID even
            # after the leader exits, and clean the entire group on every
            # path (including cancellation and a successful leader exit).
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except OSError:
                cleanup_confirmed = False
            try:
                cleanup_confirmed = _wait_for_cleanup(
                    proc, timeout_s=5.0, poll_interval_s=.01,
                ) and cleanup_confirmed
            except Exception:
                cleanup_confirmed = False
            if not cleanup_confirmed:
                status, reason = "failed", "mathlib_prewarm_cleanup_unconfirmed"
        if snippet is not None:
            try:
                snippet.unlink(missing_ok=True)
            except OSError:
                pass
    return {
        "status": status,
        "reason": reason,
        "elapsed_s": time.monotonic() - started,
        "returncode": proc.returncode if proc is not None else None,
        "cleanup_confirmed": cleanup_confirmed,
    }


def _normalize_prewarm_report(raw: Any) -> dict[str, Any]:
    if not isinstance(raw, dict):
        return {
            "status": "failed",
            "reason": "prewarm_invalid_report",
            "elapsed_s": 0.0,
        }
    status = raw.get("status") if isinstance(raw.get("status"), str) else "failed"
    reason = raw.get("reason") if isinstance(raw.get("reason"), str) else ""
    elapsed = raw.get("elapsed_s")
    try:
        elapsed_s = float(elapsed)
    except (TypeError, ValueError):
        elapsed_s = 0.0
    if not math.isfinite(elapsed_s):
        elapsed_s = 0.0
    report = {
        "status": status or "failed",
        "reason": reason,
        "elapsed_s": elapsed_s,
    }
    error = raw.get("error")
    if isinstance(error, str) and error:
        report["error"] = error
    returncode = raw.get("returncode")
    if isinstance(returncode, int) and not isinstance(returncode, bool):
        report["returncode"] = returncode
    if type(raw.get("cleanup_confirmed")) is bool:
        report["cleanup_confirmed"] = raw["cleanup_confirmed"]
    return report


def _record_prewarm_report(directory: Path, raw: Any) -> None:
    """Persist prewarm telemetry without being able to abort the sweep."""
    report = _normalize_prewarm_report(raw)
    try:
        payload = json.dumps(report, indent=2, allow_nan=False) + "\n"
    except (TypeError, ValueError):
        report = {
            "status": "failed",
            "reason": "prewarm_unserializable_report",
            "elapsed_s": 0.0,
        }
        payload = json.dumps(report, indent=2, allow_nan=False) + "\n"
    try:
        (Path(directory) / "mathlib_prewarm.json").write_text(
            payload, encoding="utf-8"
        )
    except OSError:
        pass
    try:
        print(
            f"Mathlib prewarm: {report.get('status')}; "
            f"elapsed={float(report.get('elapsed_s') or 0):.1f}s; "
            f"reason={report.get('reason') or 'none'}",
            flush=True,
        )
    except OSError:
        pass


def _solved_policy(value: Any) -> str:
    if not isinstance(value, str) or value not in {"exported", "verified"}:
        raise ValueError("invalid solved selection policy; use exported or verified")
    return value


def _scan_solved(paths: Sequence[Path], *, policy: str) -> set[str]:
    from .putnam_solved_exports import scan_exported_problems, scan_solved_artifacts

    if _solved_policy(policy) == "exported":
        return scan_exported_problems(paths)
    return scan_solved_artifacts(paths)


def build_command(
    source_path: Path, output_dir: Path, mini_args: Sequence[str]
) -> list[str]:
    reserved = (
        "--putnam-file",
        "--lean-file",
        "--theorem-name",
        "--output-dir",
        "--help",
    )
    for argument in mini_args:
        flag = argument.split("=", 1)[0]
        if flag == "-h" or (
            flag.startswith("--") and any(item.startswith(flag) for item in reserved)
        ):
            raise ValueError(f"sweep owns target/output arguments: {flag}")
    return [
        sys.executable,
        "-m",
        "ensemble_prover.mini_prover",
        "--putnam-file",
        str(Path(source_path).resolve()),
        "--output-dir",
        str(Path(output_dir).resolve()),
        *mini_args,
    ]


def build_manifest(
    *,
    source_dir: Path,
    solved_dirs: Sequence[Path],
    seed: int,
    mini_args: Sequence[str],
    solved_policy: str = "exported",
    first_accepted_by_s: float = DEFAULT_FIRST_ACCEPTED_BY_S,
    second_accepted_by_s: float = DEFAULT_SECOND_ACCEPTED_BY_S,
    startup_liveness_s: float = DEFAULT_STARTUP_LIVENESS_S,
    prewarm_shared_mathlib: bool = True,
) -> dict[str, Any]:
    source_dir = Path(source_dir).resolve()
    solved_dirs = [Path(path).resolve() for path in solved_dirs]
    if isinstance(seed, bool) or not isinstance(seed, int):
        raise ValueError("seed must be an integer")
    gate = AcceptanceGate(0, first_accepted_by_s, second_accepted_by_s)
    startup_liveness_s = _acceptance_seconds(startup_liveness_s)
    if not isinstance(prewarm_shared_mathlib, bool):
        raise ValueError("prewarm_shared_mathlib must be a boolean")
    build_command(source_dir / "putnam_2000_a1.lean", Path("unused"), mini_args)
    solved_policy = _solved_policy(solved_policy)
    solved = _scan_solved(solved_dirs, policy=solved_policy)
    sources = sorted(
        path
        for path in source_dir.glob("putnam_*.lean")
        if _PROBLEM.fullmatch(path.stem)
    )
    if not sources:
        raise ValueError(f"no Putnam problems found in {source_dir}")
    queue = [
        {
            "problem_id": path.stem,
            "source_path": str(path.resolve()),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "status": "pending",
            "attempts": [],
        }
        for path in sources
        if path.stem not in solved
    ]
    random.Random(seed).shuffle(queue)
    return {
        "schema_version": 1,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "seed": seed,
        "source_dir": str(source_dir),
        "solved_dirs": [str(path) for path in solved_dirs],
        "solved_policy": solved_policy,
        "mini_args": list(mini_args),
        "first_accepted_by_s": gate.first_accepted_by_s,
        "second_accepted_by_s": gate.second_accepted_by_s,
        "startup_liveness_s": startup_liveness_s,
        "prewarm_shared_mathlib": prewarm_shared_mathlib,
        "corpus_count": len(sources),
        "excluded_solved_count": len(sources) - len(queue),
        "queue": queue,
    }


def save_manifest(path: Path, manifest: Mapping[str, Any]) -> None:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with NamedTemporaryFile(
            "w", encoding="utf-8", dir=path.parent, delete=False
        ) as handle:
            temporary = Path(handle.name)
            json.dump(manifest, handle, indent=2, allow_nan=False)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def load_manifest(path: Path) -> dict[str, Any]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if (
        not isinstance(data, dict)
        or type(data.get("schema_version")) is not int
        or data["schema_version"] != 1
    ):
        raise ValueError("unsupported sweep manifest version")
    if not isinstance(data.get("queue"), list) or not isinstance(
        data.get("mini_args"), list
    ):
        raise ValueError("malformed sweep manifest")
    if any(not isinstance(argument, str) for argument in data["mini_args"]):
        raise ValueError("malformed MiniProver arguments")
    # Schema-1 manifests written before inventory selection used verified mode.
    _solved_policy(data.get("solved_policy", "verified"))
    if type(data.get("seed")) is not int:
        raise ValueError("sweep seed must be an integer")
    if not isinstance(data.get("source_dir"), str) or not data["source_dir"]:
        raise ValueError("malformed sweep source directory")
    if not isinstance(data.get("solved_dirs"), list) or any(
        not isinstance(directory, str) or not directory
        for directory in data["solved_dirs"]
    ):
        raise ValueError("malformed solved-export directories")
    AcceptanceGate(
        0,
        _acceptance_seconds(data.get("first_accepted_by_s")),
        _acceptance_seconds(data.get("second_accepted_by_s")),
    )
    if "startup_liveness_s" in data:
        data["startup_liveness_s"] = _acceptance_seconds(data.get("startup_liveness_s"))
    else:
        data["startup_liveness_s"] = 0.0
    if "prewarm_shared_mathlib" in data:
        if not isinstance(data.get("prewarm_shared_mathlib"), bool):
            raise ValueError("malformed prewarm_shared_mathlib")
    else:
        data["prewarm_shared_mathlib"] = False
    if "prewarm_cleanup_unconfirmed" in data and type(data["prewarm_cleanup_unconfirmed"]) is not bool:
        raise ValueError("malformed prewarm_cleanup_unconfirmed")
    names = set()
    for row in data["queue"]:
        name = row.get("problem_id", "") if isinstance(row, dict) else ""
        if not isinstance(name, str) or not _PROBLEM.fullmatch(name) or name in names:
            raise ValueError("invalid or duplicate problem in sweep manifest")
        names.add(name)
        if not isinstance(row.get("status"), str) or row["status"] not in _STATUSES or not isinstance(
            row.get("attempts"), list
        ):
            raise ValueError("invalid sweep attempt status")
        if not isinstance(row.get("source_sha256"), str) or not _SHA256.fullmatch(
            row["source_sha256"]
        ):
            raise ValueError("invalid source digest")
        if not isinstance(row.get("source_path"), str) or not row["source_path"]:
            raise ValueError("invalid sweep source path")
        if (
            Path(row.get("source_path", "")).resolve()
            != (Path(data["source_dir"]) / f"{name}.lean").resolve()
        ):
            raise ValueError("sweep source path does not match its problem")
    return data


def _summary_solved(output_dir: Path, exit_code: int | None = None) -> bool:
    try:
        data = json.loads((output_dir / "summary.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return False
    if not isinstance(data, dict) or not effective_solved(data):
        return False
    # A pre-export solved summary can defer a cutoff while export finishes;
    # a failed/interrupted exit still needs the explicit verified boundary.
    return export_boundary_present(data) or exit_code in (None, 0)


def answer_preparation_dir(output_dir: Path) -> Path:
    resolved = Path(output_dir).resolve()
    return resolved.with_name(resolved.name + ".answer_preparation")


def _load_answer_discovery(output_dir: Path) -> dict[str, Any] | None:
    path = answer_preparation_dir(output_dir) / "answers" / "answer_discovery.json"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return data if isinstance(data, dict) else None


def _capability_outage_recorded(output_dir: Path) -> bool:
    path = answer_preparation_dir(output_dir) / "capability_preflight.jsonl"
    last: dict[str, Any] | None = None
    try:
        for line in path.read_text(encoding="utf-8").splitlines():
            try:
                record = json.loads(line)
            except ValueError:
                continue
            if isinstance(record, dict):
                last = record
    except OSError:
        return False
    return bool(last) and last.get("status") == "unavailable"


def classify_answer_preparation_reason(
    output_dir: Path, *, console_text: str = ""
) -> str:
    """Classify a pre-proof discovery failure; empty means proof search started."""
    discovery = _load_answer_discovery(output_dir)
    if discovery and discovery.get("status") == "candidate_ready":
        return ""
    if (output_dir / "summary.json").is_file() or (output_dir / "turns.jsonl").is_file():
        return ""
    if discovery and discovery.get("status") == "no_candidate":
        return "no_admissible_answer"
    if _capability_outage_recorded(output_dir):
        return "capability_outage"
    error_type = str((discovery or {}).get("error_type") or "")
    lowered = console_text.lower()
    if "CapabilityUnavailable" in error_type or "capability catalog" in lowered:
        return "capability_outage"
    if discovery and discovery.get("status") in {"error", "running", "cancelled"}:
        return "error"
    if "answer discovery input rejected" in lowered or "no supported answer slots" in lowered:
        return "no_slots"
    if "answer discovery stopped" in lowered or "answer preparation failed" in lowered:
        return "error"
    if answer_preparation_dir(output_dir).is_dir():
        return "error"
    return ""


def summarize_manifest(manifest: Mapping[str, Any]) -> dict[str, int]:
    """Count terminal outcomes without folding prep failures into proof cutoffs."""
    totals = {
        "solved": 0,
        "cutoff": 0,
        "failed": 0,
        "answer_preparation_failed": 0,
        "answer_preparation_capability_outage": 0,
        "answer_preparation_no_admissible_answer": 0,
        "interrupted": 0,
        "pending": 0,
        "skipped_solved": 0,
        "running": 0,
        "cleanup_unconfirmed": 0,
        "monitor_error": 0,
    }
    queue = manifest.get("queue")
    if not isinstance(queue, list):
        return totals
    for row in queue:
        if not isinstance(row, dict):
            continue
        status = row.get("status")
        if isinstance(status, str):
            totals[status] = totals.get(status, 0) + 1
        if status != "answer_preparation_failed":
            continue
        attempts = row.get("attempts")
        last = attempts[-1] if isinstance(attempts, list) and attempts else {}
        reason = last.get("answer_preparation_reason") if isinstance(last, dict) else ""
        if reason == "capability_outage":
            totals["answer_preparation_capability_outage"] += 1
        elif reason == "no_admissible_answer":
            totals["answer_preparation_no_admissible_answer"] += 1
    return totals


def _print_sweep_totals(manifest: Mapping[str, Any]) -> None:
    totals = summarize_manifest(manifest)
    print(
        "Sweep totals: "
        f"solved={totals['solved']} cutoff={totals['cutoff']} "
        f"answer_preparation_failed={totals['answer_preparation_failed']} "
        f"(capability_outage={totals['answer_preparation_capability_outage']} "
        f"no_admissible_answer={totals['answer_preparation_no_admissible_answer']}) "
        f"failed={totals['failed']}",
        flush=True,
    )


def _process_group_alive(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    # Linux can retain a dead process-group member briefly as a zombie. It
    # owns no running work; retain a conservative answer on unreadable /proc.
    try:
        uncertain = False
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
                if int(fields[2]) == pgid and fields[0] not in {"Z", "X"}:
                    return True
            except FileNotFoundError:
                continue
            except (OSError, ValueError, IndexError):
                uncertain = True
        return uncertain
    except OSError:
        return True


class _ConsoleRelay:
    """Echo the durable log without making the child depend on a drained pipe."""

    def __init__(self, reader: BinaryIO):
        self.reader = reader
        self.output = sys.stdout
        try:
            self.output_fd = self.output.fileno()
        except (AttributeError, OSError, ValueError):
            self.output_fd = None
        self.decoder = codecs.getincrementaldecoder("utf-8")(errors="replace")
        self.pending = b""
        self.error = ""

    def _write(self, data: bytes) -> int:
        if self.output_fd is None:
            # In-memory output streams (e.g. embedded callers/test capture).
            self.output.write(self.decoder.decode(data))
            self.output.flush()
            return len(data)
        # A terminal or pipe can stop accepting output. Preserve its original
        # mode for the caller, and leave any unwritten bytes for the next tick.
        blocking = os.get_blocking(self.output_fd)
        try:
            os.set_blocking(self.output_fd, False)
            return os.write(self.output_fd, data)
        except BlockingIOError:
            return 0
        finally:
            os.set_blocking(self.output_fd, blocking)

    def copy_available(self, *, final: bool = False) -> None:
        if self.error:
            return
        try:
            # Bound each monitoring tick, including output without a newline.
            # At shutdown, drain only the bytes already present: an unconfirmed
            # child must not keep us following an ever-growing file forever.
            remaining = (
                max(0, os.fstat(self.reader.fileno()).st_size - self.reader.tell())
                if final else 64 * 1024 - len(self.pending)
            )
            # Cleanup has already finished before the final drain. Give a
            # healthy pipe reader a brief scheduling grace, with a separate
            # hard bound so a stopped consumer cannot hold the sweep open.
            drain_deadline = time.monotonic() + .25 if final else 0
            while self.pending or remaining:
                if final and time.monotonic() >= drain_deadline:
                    return
                if not self.pending:
                    self.pending = self.reader.read(min(remaining, 64 * 1024))
                    if not self.pending:
                        break
                    remaining -= len(self.pending)
                written = self._write(self.pending)
                if not written:
                    patience = drain_deadline - time.monotonic()
                    if not final or self.output_fd is None or patience <= 0:
                        return
                    poller = select.poll()
                    poller.register(self.output_fd, select.POLLOUT)
                    poller.poll(max(1, math.ceil(patience * 1000)))
                    continue
                self.pending = self.pending[written:]
            if final and self.output_fd is None:
                self.output.write(self.decoder.decode(b"", final=True))
                self.output.flush()
        except (OSError, ValueError) as exc:
            # Let the owner stop and reap the process even if its console fails.
            self.error = f"console relay failed: {type(exc).__name__}: {exc}"


def _wait_for_cleanup(
    proc: subprocess.Popen, *, timeout_s: float, poll_interval_s: float,
    on_poll: Callable[[], None] = lambda: None,
) -> bool:
    deadline = time.monotonic() + timeout_s
    while True:
        on_poll()
        if proc.poll() is not None and not _process_group_alive(proc.pid):
            return True
        if time.monotonic() >= deadline:
            return False
        time.sleep(min(poll_interval_s, max(0, deadline - time.monotonic())))


def console_log_path(output_dir: Path) -> Path:
    """Keep sweep-owned output outside MiniProver's fresh generation directory."""
    directory = Path(output_dir).resolve()
    return directory.with_name(directory.name + ".sweep_console.log")


def run_attempt(
    command: Sequence[str],
    output_dir: Path,
    *,
    first_accepted_by_s: float = DEFAULT_FIRST_ACCEPTED_BY_S,
    second_accepted_by_s: float = DEFAULT_SECOND_ACCEPTED_BY_S,
    startup_liveness_s: float = 0,
    poll_interval_s: float = 1,
    cleanup_timeout_s: float = 130,
    should_stop: Callable[[], bool] = lambda: False,
    on_started: Callable[[int], None] = lambda _pid: None,
) -> dict[str, Any]:
    """Own one CLI process group; never advance before its supervisor settles."""
    poll_interval_s, cleanup_timeout_s = (
        _seconds(poll_interval_s),
        _seconds(cleanup_timeout_s),
    )
    startup_liveness_s = _acceptance_seconds(startup_liveness_s)
    output_dir = Path(output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    if any(
        (output_dir / name).exists()
        for name in ("summary.json", "turns.jsonl", "sweep_console.log")
    ):
        raise ValueError("attempt output directory already contains run artifacts")
    start = time.monotonic()
    gate = AcceptanceGate(start, first_accepted_by_s, second_accepted_by_s)
    tail = AcceptanceEventTail(output_dir / "turns.jsonl")
    startup = AttemptStartupLiveness(output_dir, start=start, timeout_s=startup_liveness_s)
    cutoff = ""
    interrupted = False
    monitor_error = ""
    console_path = console_log_path(output_dir)
    worker_env = trusted_provider_worker_environment()
    worker_env["PYTHONUNBUFFERED"] = "1"
    # Exclusive creation also rejects existing or dangling symlink destinations.
    with console_path.open("xb") as console, console_path.open("rb") as reader:
        relay = _ConsoleRelay(reader)
        proc = subprocess.Popen(
            list(command),
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=console,
            stderr=subprocess.STDOUT,
            start_new_session=True,
            env=worker_env,
        )
        try:
            on_started(proc.pid)
            while proc.poll() is None:
                relay.copy_available()
                if relay.error:
                    monitor_error = relay.error
                    break
                records = tail.read()
                now = time.monotonic()
                for record in records:
                    gate.observe(record, now=now)
                interrupted = bool(should_stop())
                if startup.expired(now=now, proof_alive=tail.alive):
                    cutoff = "startup_liveness_deadline"
                else:
                    cutoff = gate.cutoff_reason(now=now) or ""
                if interrupted or (cutoff and not _summary_solved(output_dir)):
                    break
                cutoff = ""
                time.sleep(poll_interval_s)
        except BaseException as exc:
            monitor_error = f"{type(exc).__name__}: {exc}"
            interrupted = isinstance(exc, KeyboardInterrupt)
        needs_stop = proc.poll() is None or _process_group_alive(proc.pid)
        if needs_stop:
            stop_reason = "sweep_interrupted" if interrupted else (
                cutoff or ("sweep_monitor_error" if monitor_error else "child_cleanup")
            )
            try:
                console.write(
                    f"\n[sweep] stop requested: {stop_reason}; sending SIGINT to this attempt\n".encode()
                )
                console.flush()
                relay.copy_available()
            except OSError as exc:
                monitor_error = monitor_error or f"could not record stop reason: {exc}"
            try:
                # One SIGINT reaches CLI + supervisor. Keep the supervisor
                # alive to reap worker/Lean children in their own sessions.
                os.killpg(proc.pid, signal.SIGINT)
            except ProcessLookupError:
                pass
            except OSError as exc:
                monitor_error = f"could not signal CLI supervisor: {exc}"
        cleaned = _wait_for_cleanup(
            proc, timeout_s=cleanup_timeout_s, poll_interval_s=poll_interval_s,
            on_poll=relay.copy_available,
        )
        if proc.returncode is not None and (
            proc.returncode < 0
            or proc.returncode == 125
            or 192 <= proc.returncode <= 255
        ):
            # A vanished supervisor group cannot attest that detached workers
            # were reaped. Negative supervisor statuses are wrapped modulo 256
            # by the outer Python CLI; 125 means the supervisor itself failed.
            cleaned = False
        if cleaned:
            try:
                records = tail.read()
                now = time.monotonic()
                for record in records:
                    gate.observe(record, now=now)
            except (OSError, ValueError) as exc:
                monitor_error = f"{type(exc).__name__}: {exc}"
        monitor_error = monitor_error or relay.error
        if not cleaned:
            status = "cleanup_unconfirmed"
        elif _summary_solved(output_dir, proc.returncode):
            status, cutoff = "solved", ""
        elif interrupted:
            status, cutoff = "interrupted", ""
        elif monitor_error:
            status = "monitor_error"
        else:
            status = "cutoff" if cutoff else "failed"
        prep_reason = ""
        if status in {"failed", "cutoff"}:
            try:
                console_text = console_path.read_text(
                    encoding="utf-8", errors="replace"
                )
            except OSError:
                console_text = ""
            prep_reason = classify_answer_preparation_reason(
                output_dir, console_text=console_text
            )
            # Preparation diagnostics describe the phase, while a supervisor
            # cutoff records why the process was stopped. Keep that cause and
            # its terminal status even if cancellation writes a prep error.
            if prep_reason and status == "failed":
                status = "answer_preparation_failed"
        def record_result() -> None:
            console.write(
                f"\n[sweep] result={status}; cutoff_reason={cutoff or 'none'}; "
                f"answer_preparation_reason={prep_reason or 'none'}; "
                f"accepted={len(gate.accepted)}; cleanup_confirmed={cleaned}\n".encode()
            )
            console.flush()

        if needs_stop:
            try:
                record_result()
            except OSError as exc:
                monitor_error = monitor_error or f"could not record result: {exc}"
        relay.copy_available(final=True)
        monitor_error = monitor_error or relay.error
        if monitor_error and status not in {"cleanup_unconfirmed", "solved", "interrupted", "monitor_error"}:
            status = "monitor_error"
            # The result notice itself can discover a broken output pipe.
            # Keep the durable final result aligned with the manifest even
            # when the terminal can no longer receive the correction.
            if needs_stop:
                try:
                    record_result()
                except OSError:
                    pass  # The original write/relay failure remains recorded.
    return {
        "status": status,
        "console_log": str(console_path),
        "exit_code": proc.returncode,
        "cutoff_reason": cutoff,
        "answer_preparation_reason": prep_reason,
        "accepted_identities": sorted(gate.accepted),
        "accepted_elapsed_s": gate.accepted,
        "cleanup_confirmed": cleaned,
        "wall_s": time.monotonic() - start,
        "monitor_error": monitor_error,
    }


@contextmanager
def _manifest_lock(path: Path) -> Iterator[None]:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.with_suffix(".lock").open("a") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError("this sweep already has an active owner") from exc
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def run_sweep(
    manifest_path: Path,
    *,
    poll_interval_s: float = 1,
    cleanup_timeout_s: float = 130,
    should_stop: Callable[[], bool] = lambda: False,
) -> int:
    manifest_path = Path(manifest_path).resolve()
    with _manifest_lock(manifest_path):
        manifest = load_manifest(manifest_path)
        if manifest.get("prewarm_cleanup_unconfirmed"):
            raise ValueError(
                "previous Mathlib prewarm cleanup is unconfirmed; refusing to start new work"
            )
        if any(
            row["status"] in {"running", "cleanup_unconfirmed", "monitor_error"}
            for row in manifest["queue"]
        ):
            raise ValueError(
                "previous attempt cleanup is unconfirmed; refusing to start new work"
            )
        if manifest.get("prewarm_shared_mathlib"):
            try:
                raw = prewarm_shared_mathlib_runtime()
            except Exception as exc:
                raw = {
                    "status": "failed",
                    "reason": "prewarm_exception",
                    "error": f"{type(exc).__name__}: {exc}",
                    "elapsed_s": 0.0,
                }
            if isinstance(raw, dict) and raw.get("cleanup_confirmed") is False:
                # Preserve the cleanup failure across --resume, even if the
                # optional telemetry sidecar cannot be written.
                manifest["prewarm_cleanup_unconfirmed"] = True
                save_manifest(manifest_path, manifest)
            try:
                _record_prewarm_report(manifest_path.parent, raw)
            except Exception:
                pass
            if isinstance(raw, dict) and raw.get("cleanup_confirmed") is False:
                # Optional warmup failure is harmless only once it owns no
                # running work. Do not overlap a sweep with a leaked compiler.
                return 1
        exit_code = 0
        for index, row in enumerate(manifest["queue"]):
            if should_stop():
                exit_code = 130
                break
            if row["status"] in _TERMINAL:
                continue
            if row["problem_id"] in _scan_solved(
                [Path(path) for path in manifest["solved_dirs"]],
                policy=manifest.get("solved_policy", "verified"),
            ):
                row["status"] = "skipped_solved"
                save_manifest(manifest_path, manifest)
                continue
            source = Path(row["source_path"])
            if (
                not source.exists()
                or hashlib.sha256(source.read_bytes()).hexdigest()
                != row["source_sha256"]
            ):
                raise ValueError(f"source changed after sweep planning: {source}")
            output_dir = (
                manifest_path.parent
                / "attempts"
                / f"{index + 1:04d}_{row['problem_id']}"
                / f"attempt_{len(row['attempts']) + 1:03d}"
            )
            output_dir.mkdir(parents=True, exist_ok=False)
            command = build_command(source, output_dir, manifest["mini_args"])
            attempt = {
                "output_dir": str(output_dir),
                "console_log": str(console_log_path(output_dir)),
                "command": command,
                "started_at": datetime.now(timezone.utc).isoformat(),
                "status": "running",
            }
            row["attempts"].append(attempt)
            row["status"] = "running"
            save_manifest(manifest_path, manifest)

            def started(pid: int) -> None:
                attempt["cli_pid"] = pid
                save_manifest(manifest_path, manifest)

            print(
                f"[{index + 1}/{len(manifest['queue'])}] {row['problem_id']} -> {output_dir}",
                flush=True,
            )
            result = run_attempt(
                command,
                output_dir,
                first_accepted_by_s=manifest["first_accepted_by_s"],
                second_accepted_by_s=manifest["second_accepted_by_s"],
                startup_liveness_s=manifest.get("startup_liveness_s", 0),
                poll_interval_s=poll_interval_s,
                cleanup_timeout_s=cleanup_timeout_s,
                should_stop=should_stop,
                on_started=started,
            )
            attempt.update(result)
            row["status"] = result["status"]
            save_manifest(manifest_path, manifest)
            print(
                f"  {result['status']}; accepted={len(result.get('accepted_identities', []))}; "
                f"cutoff_reason={result.get('cutoff_reason') or 'none'}; "
                f"answer_preparation_reason={result.get('answer_preparation_reason') or 'none'}",
                flush=True,
            )
            if row["status"] in {"cleanup_unconfirmed", "monitor_error"}:
                exit_code = 2
                break
            if row["status"] == "interrupted":
                exit_code = 130
                break
        _print_sweep_totals(manifest)
        return exit_code


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--sweep-dir", "--output-dir", type=Path)
    parser.add_argument(
        "--resume", type=Path, help="Resume a sweep directory or manifest.json"
    )
    parser.add_argument("--putnam-dir", type=Path)
    parser.add_argument("--solved-dir", type=Path, action="append")
    parser.add_argument(
        "--solved-policy", choices=("exported", "verified"),
        help="Skip existing exported filenames (default), or only verified manifest entries",
    )
    parser.add_argument("--seed", type=int)
    parser.add_argument(
        "--first-accepted-by-s",
        type=float,
        help=(
            "First acceptance deadline from launch, including startup "
            f"(default: {DEFAULT_FIRST_ACCEPTED_BY_S:g}; 0 disables)"
        ),
    )
    parser.add_argument(
        "--second-accepted-by-s",
        type=float,
        help=(
            "Second acceptance deadline from launch, including startup "
            f"(default: {DEFAULT_SECOND_ACCEPTED_BY_S:g}; 0 disables)"
        ),
    )
    parser.add_argument("--no-acceptance-cutoffs", action="store_true", help="Disable both sweep acceptance cutoffs; retain MiniProver's own limits")
    parser.add_argument(
        "--startup-liveness-s",
        type=float,
        help=(
            "Cut a silent launch with no turns.jsonl events "
            f"(default: {DEFAULT_STARTUP_LIVENESS_S:g}; 0 disables). "
            "Does not subtract Mathlib/runtime boot from the acceptance clock."
        ),
    )
    parser.add_argument(
        "--no-prewarm",
        action="store_true",
        help="Skip the shared Mathlib lake-env import before the first attempt",
    )
    parser.add_argument("--poll-interval-s", type=float, default=1)
    parser.add_argument("--cleanup-timeout-s", type=float, default=130)
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Persist and print the queue without starting MiniProver",
    )
    parser.add_argument(
        "mini_args", nargs=argparse.REMAINDER, help="MiniProver arguments after --"
    )
    args = parser.parse_args(argv)
    mini_args = args.mini_args[1:] if args.mini_args[:1] == ["--"] else args.mini_args
    try:
        _seconds(args.poll_interval_s)
        _seconds(args.cleanup_timeout_s)
        if args.resume:
            if (
                any(
                    value is not None
                    for value in (
                        args.sweep_dir,
                        args.putnam_dir,
                        args.solved_dir,
                        args.solved_policy,
                        args.seed,
                        args.first_accepted_by_s,
                        args.second_accepted_by_s,
                        args.startup_liveness_s,
                    )
                )
                or mini_args or args.no_acceptance_cutoffs or args.no_prewarm
            ):
                raise ValueError(
                    "resume uses persisted queue/settings; do not override them"
                )
            manifest_path = (
                args.resume
                if args.resume.name == "manifest.json"
                else args.resume / "manifest.json"
            )
            manifest = load_manifest(manifest_path)
        else:
            if args.no_acceptance_cutoffs and (
                args.first_accepted_by_s is not None or args.second_accepted_by_s is not None
            ):
                raise ValueError("choose --no-acceptance-cutoffs or individual deadlines, not both")
            directory = args.sweep_dir or ROOT / "runs" / "mini_prover" / "sweeps" / (
                datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + secrets.token_hex(3)
            )
            manifest_path = directory.resolve() / "manifest.json"
            with _manifest_lock(manifest_path):
                if manifest_path.exists():
                    raise ValueError("sweep manifest already exists; use --resume")
                manifest = build_manifest(
                    source_dir=args.putnam_dir
                    or ROOT / "external/PutnamBench/lean4/src",
                    solved_dirs=args.solved_dir
                    or [ROOT / "runs/mini_prover/solved", ROOT / "runs/solved"],
                    seed=args.seed if args.seed is not None else secrets.randbits(64),
                    mini_args=mini_args,
                    solved_policy=args.solved_policy or "exported",
                    first_accepted_by_s=0 if args.no_acceptance_cutoffs else args.first_accepted_by_s
                    if args.first_accepted_by_s is not None
                    else DEFAULT_FIRST_ACCEPTED_BY_S,
                    second_accepted_by_s=0 if args.no_acceptance_cutoffs else args.second_accepted_by_s
                    if args.second_accepted_by_s is not None
                    else DEFAULT_SECOND_ACCEPTED_BY_S,
                    startup_liveness_s=(
                        args.startup_liveness_s
                        if args.startup_liveness_s is not None
                        else DEFAULT_STARTUP_LIVENESS_S
                    ),
                    prewarm_shared_mathlib=not args.no_prewarm,
                )
                save_manifest(manifest_path, manifest)
        print(
            f"Sweep: {manifest_path.resolve()}\nSeed: {manifest['seed']}\n"
            f"Corpus: {manifest['corpus_count']}; excluded: {manifest['excluded_solved_count']}; "
            f"selection policy: {manifest.get('solved_policy', 'verified')}\n"
            f"Unsolved queue: {len(manifest['queue'])}"
        )
        first, second = manifest["first_accepted_by_s"], manifest["second_accepted_by_s"]
        policy = "disabled" if not first and not second else (
            f"first={str(first) + 's' if first else 'disabled'}, "
            f"second={str(second) + 's' if second else 'disabled'} from attempt launch (includes startup)"
        )
        startup = manifest.get("startup_liveness_s", 0)
        startup_text = f"{startup:g}s" if startup else "disabled"
        print(
            f"Acceptance cutoffs: {policy}; startup_liveness={startup_text}; "
            f"prewarm_shared_mathlib={bool(manifest.get('prewarm_shared_mathlib'))}",
            flush=True,
        )
        if args.dry_run:
            for row in manifest["queue"]:
                print(f"  {row['problem_id']} [{row['status']}]")
            return 0
        stopped = False

        def request_stop(_signum: int, _frame: Any) -> None:
            nonlocal stopped
            stopped = True

        previous = {
            signum: signal.signal(signum, request_stop)
            for signum in (signal.SIGINT, signal.SIGTERM)
        }
        try:
            return run_sweep(
                manifest_path,
                poll_interval_s=args.poll_interval_s,
                cleanup_timeout_s=args.cleanup_timeout_s,
                should_stop=lambda: stopped,
            )
        finally:
            for signum, handler in previous.items():
                signal.signal(signum, handler)
    except (ValueError, OSError) as exc:
        print(f"putnam sweep: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
