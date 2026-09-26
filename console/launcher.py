"""Owned launches, durable registry and at-most-once cooperative stop.

Process and persistence guarantees:

* Every launch reserves its output directory with ``mkdir(exist_ok=False)``
  and persists a ``launch_pending`` tombstone before ``Popen``. A record
  left pending with no process identity becomes ``launch_delivery_unknown``
  and is never respawned for the same idempotency key.
* The child is started with ``start_new_session=True`` so the CLI parent and
  its watchdog supervisor share one process group that the console owns.
* Stop is at most once per launch lifetime: ``stop_requested`` is persisted
  before one ``killpg(SIGINT)``. Duplicate requests return the stored
  status. Identity (pid, pgid, process start ticks, boot id) is re-verified
  under the lock before signalling; any mismatch refuses.
* Return codes come from ``Popen.wait``/``poll`` on the owned handle. A
  restarted console cannot reap a non-child and reports the code unknown.
* Console logs live in the console state root, never inside a run.
"""

from __future__ import annotations

import fcntl
import json
import math
import os
import secrets
import signal
import stat
import subprocess
import sys
import time
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field, fields
from pathlib import Path
from typing import Any, Iterator

STATE_SCHEMA = 1
MAX_LAUNCH_STATE_BYTES = 16 * 1024 * 1024
DEFAULT_INTERPRETER = ".venv/bin/python3"
MINI_MODULE = "ensemble_prover.mini_prover"
NL_MODULE = "ensemble_prover.nl_input"
_FORBIDDEN_USER_FLAGS = {"--output-dir", "--resume-from", "--resume-accept-source-hash"}
_VALIDATE_SCRIPT = r"""
import json, sys
argv = json.load(sys.stdin)
from ensemble_prover.mini_prover import _build_argparser
parser = _build_argparser()
try:
    ns = parser.parse_args(argv)
except SystemExit as exc:
    print(json.dumps({"ok": False, "error": "parser rejected arguments", "code": exc.code}))
    raise SystemExit(0)
keys = ("putnam_file", "lean_file", "theorem_name", "prover", "prover_model", "refiner", "refiner_model",
        "planner_escalation", "reasoning_mode", "opaque_mode", "allow_official_answer_visibility",
        "mini_recursive_passes", "mini_recursive_claims", "mini_recursive_turns_per_claim",
        "max_prove_turns", "max_refine_turns", "cost_budget_usd", "llm_deadline_policy", "answer_attempts")
print(json.dumps({"ok": True, "parsed": {k: getattr(ns, k, None) for k in keys}}, default=str))
"""


@dataclass
class ValidationResult:
    ok: bool
    error: str = ""
    parsed: dict[str, Any] = field(default_factory=dict)


@dataclass
class StopRecord:
    requested_at: float = 0.0
    request_id: str = ""
    delivered: bool | None = None
    detail: str = ""


@dataclass
class Launch:
    launch_id: str
    idempotency_key: str
    kind: str  # run | resume | nl
    argv: list[str]
    cwd: str
    output_dir: str
    console_log: str
    created_at: float
    status: str = "launch_pending"  # launch_pending | running | exited | launch_failed | launch_delivery_unknown
    pid: int | None = None
    pgid: int | None = None
    start_ticks: int | None = None
    boot_id: str = ""
    returncode: int | None = None
    exited_at: float | None = None
    exit_source: str = ""  # owned_wait | proc_gone | unknown
    spawn_error: str = ""
    stop: StopRecord | None = None
    note: str = ""

    def to_json(self) -> dict[str, Any]:
        data = asdict(self)
        return data

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> "Launch":
        stop = data.get("stop")
        record = cls(**{k: v for k, v in data.items() if k != "stop"})
        record.stop = StopRecord(**stop) if isinstance(stop, dict) else None
        return record


@dataclass
class StopResult:
    outcome: str  # signalled | already_requested | refused | delivery_unknown
    detail: str
    launch: Launch | None = None


class RegistryStateError(RuntimeError):
    """Saved launch state cannot safely authorize a launch or signal."""


def _registry_number(value: Any) -> bool:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return False
    try:
        return value >= 0 and math.isfinite(value)
    except OverflowError:
        return False


def _identity_integer(value: Any, *, minimum: int = 1) -> bool:
    return type(value) is int and value >= minimum


def _strict_launch(raw: Any) -> Launch:
    if not isinstance(raw, dict) or "stop" not in raw:
        raise ValueError("launch record must include its stop receipt field")
    stop = raw.get("stop")
    if stop is not None:
        if not isinstance(stop, dict) or set(stop) != {item.name for item in fields(StopRecord)}:
            raise ValueError("stop receipt must have its complete schema")
        if (not _registry_number(stop["requested_at"])
                or not _valid_persisted_text(stop["request_id"], 200) or not stop["request_id"].strip()
                or (stop["delivered"] is not None and type(stop["delivered"]) is not bool)
                or not _valid_persisted_text(stop["detail"], 64 * 1024)):
            raise ValueError("invalid stop receipt")
    record = Launch.from_json(raw)
    if not _valid_persisted_launch(record) or not _registry_number(record.created_at):
        raise ValueError("invalid launch record")
    for value in (record.launch_id, record.idempotency_key, record.cwd, record.output_dir, record.console_log):
        if not value.strip() or "\0" in value:
            raise ValueError("invalid launch identity or path")
    if record.kind not in {"run", "resume", "nl"} or record.status not in {
        "launch_pending", "running", "exited", "launch_failed", "launch_delivery_unknown",
    }:
        raise ValueError("unsupported launch kind or state")
    for value, minimum in ((record.pid, 1), (record.pgid, 1), (record.start_ticks, 0)):
        if value is not None and not _identity_integer(value, minimum=minimum):
            raise ValueError("invalid process identity")
    if (not _valid_persisted_text(record.boot_id, 128)
            or not _valid_persisted_text(record.exit_source, 64)
            or not _valid_persisted_text(record.spawn_error, 64 * 1024)
            or not _valid_persisted_text(record.note, 64 * 1024)
            or (record.returncode is not None and type(record.returncode) is not int)
            or (record.exited_at is not None and not _registry_number(record.exited_at))):
        raise ValueError("invalid launch receipt")
    return record


def _registry_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def _parse_registry(data: bytes) -> dict[str, Launch]:
    try:
        payload = json.loads(data, object_pairs_hook=_registry_object)
        if (not isinstance(payload, dict) or set(payload) != {"schema_version", "launches"}
                or type(payload["schema_version"]) is not int or payload["schema_version"] != STATE_SCHEMA
                or not isinstance(payload["launches"], list)):
            raise ValueError("unsupported registry schema")
        launches: dict[str, Launch] = {}
        keys: set[str] = set()
        for raw in payload["launches"]:
            record = _strict_launch(raw)
            if record.launch_id in launches or record.idempotency_key in keys:
                raise ValueError("duplicate launch identity")
            launches[record.launch_id] = record
            keys.add(record.idempotency_key)
        return launches
    except (TypeError, ValueError, UnicodeError, RecursionError) as exc:
        raise RegistryStateError("Saved launch state is invalid or unsupported; preserve it and restore a valid copy.") from exc


def read_launches(state_root: Path) -> list[Launch]:
    """Read persisted launches without reconciling processes or writing state."""

    path = Path(state_root) / "launches.json"
    try:
        if path.is_symlink() or not path.is_file():
            return []
        with path.open("rb") as handle:
            raw_payload = handle.read(MAX_LAUNCH_STATE_BYTES + 1)
        if len(raw_payload) > MAX_LAUNCH_STATE_BYTES:
            return []
        payload = json.loads(raw_payload)
    except (OSError, UnicodeError, ValueError, RecursionError):
        return []
    if not isinstance(payload, dict) or payload.get("schema_version") != STATE_SCHEMA:
        return []
    launches: list[Launch] = []
    raw_launches = payload.get("launches")
    if not isinstance(raw_launches, list):
        return []
    for raw in raw_launches[:10_000]:
        if not isinstance(raw, dict):
            continue
        try:
            record = Launch.from_json(raw)
        except (TypeError, ValueError):
            continue
        if not _valid_persisted_launch(record):
            continue
        launches.append(record)
    return sorted(launches, key=lambda record: record.created_at, reverse=True)


def _valid_persisted_launch(record: Launch) -> bool:
    strings = (
        (record.launch_id, 128),
        (record.idempotency_key, 200),
        (record.kind, 32),
        (record.cwd, 4096),
        (record.output_dir, 4096),
        (record.console_log, 4096),
        (record.status, 64),
    )
    if not all(_valid_persisted_text(value, limit) for value, limit in strings):
        return False
    if not isinstance(record.argv, list) or len(record.argv) > 4096:
        return False
    if not all(_valid_persisted_text(value, 64 * 1024) for value in record.argv):
        return False
    if isinstance(record.created_at, bool) or not isinstance(record.created_at, (int, float)):
        return False
    try:
        return math.isfinite(float(record.created_at))
    except OverflowError:
        return False


def _valid_persisted_text(value: Any, limit: int) -> bool:
    if not isinstance(value, str) or len(value) > limit:
        return False
    try:
        value.encode("utf-8")
    except UnicodeError:
        return False
    return True


def read_boot_id(proc_root: Path) -> str:
    try:
        return (proc_root / "sys" / "kernel" / "random" / "boot_id").read_text(encoding="utf-8").strip()
    except (OSError, UnicodeError):
        return ""


def read_proc_identity(pid: int, proc_root: Path) -> tuple[int, int] | None:
    """Return (pgid, start_ticks) from /proc/<pid>/stat, or None if unavailable."""
    try:
        raw = (proc_root / str(pid) / "stat").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    end = raw.rfind(")")
    if end < 0:
        return None
    fields = raw[end + 1 :].split()
    # fields[0] is state (overall field 3); pgrp is overall 5, starttime overall 22.
    try:
        if fields[0] in ("Z", "X"):
            return None  # zombie or dead: not a signalling target and not alive
        return int(fields[2]), int(fields[19])
    except (IndexError, ValueError):
        return None


def _atomic_write(path: Path, payload: bytes) -> None:
    tmp = path.with_name(path.name + f".{os.getpid()}.{secrets.token_hex(4)}.tmp")
    with tmp.open("wb") as handle:
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(tmp, path)
    try:
        dir_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)
    except OSError:
        pass


class LaunchRegistry:
    def __init__(
        self,
        state_root: Path,
        *,
        repo_root: Path,
        run_root: Path,
        command_prefix: list[str] | None = None,
        nl_command_prefix: list[str] | None = None,
        proc_root: str | os.PathLike[str] = "/proc",
        validate: bool = True,
    ) -> None:
        self.state_root = Path(state_root)
        self.repo_root = Path(repo_root).resolve()
        self.run_root = Path(run_root)
        self.proc_root = Path(proc_root)
        self.validate_enabled = validate
        self.state_root.mkdir(parents=True, exist_ok=True)
        try:
            os.chmod(self.state_root, 0o700)
        except OSError:
            pass
        (self.state_root / "logs").mkdir(exist_ok=True)
        self.path = self.state_root / "launches.json"
        self.lock_path = self.state_root / "launches.lock"
        interpreter = str(self.repo_root / DEFAULT_INTERPRETER)
        self.command_prefix = list(command_prefix) if command_prefix is not None else [interpreter, "-m", MINI_MODULE]
        self.nl_command_prefix = list(nl_command_prefix) if nl_command_prefix is not None else [interpreter, "-m", NL_MODULE]
        self._procs: dict[str, subprocess.Popen[Any]] = {}

    # -- persistence -----------------------------------------------------------

    @contextmanager
    def _locked(self) -> Iterator[None]:
        with self.lock_path.open("a+b") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

    def _load(self) -> dict[str, Launch]:
        try:
            descriptor = os.open(self.path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        except FileNotFoundError:
            return {}
        except OSError as exc:
            raise RegistryStateError("Saved launch state cannot be opened safely.") from exc
        try:
            with os.fdopen(descriptor, "rb") as handle:
                metadata = os.fstat(handle.fileno())
                if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > MAX_LAUNCH_STATE_BYTES:
                    raise RegistryStateError("Saved launch state must be a bounded regular file.")
                data = handle.read(MAX_LAUNCH_STATE_BYTES + 1)
        except OSError as exc:
            raise RegistryStateError("Saved launch state cannot be read safely.") from exc
        if len(data) > MAX_LAUNCH_STATE_BYTES:
            raise RegistryStateError("Saved launch state exceeds its size limit.")
        return self._reconcile(_parse_registry(data))

    def validate_state(self) -> None:
        """Check control availability without rewriting or reserving any state."""
        with self._locked():
            self._load()

    def _save(self, launches: dict[str, Launch]) -> None:
        try:
            payload = {"schema_version": STATE_SCHEMA, "launches": [r.to_json() for r in launches.values()]}
            encoded = json.dumps(payload, indent=1, sort_keys=True, allow_nan=False).encode("utf-8")
        except (TypeError, ValueError, RecursionError) as exc:
            raise RegistryStateError("Launch state cannot be serialized safely; previous state was preserved.") from exc
        if len(encoded) > MAX_LAUNCH_STATE_BYTES:
            raise RegistryStateError("Launch state exceeds its size limit; previous state was preserved.")
        # Never install bytes the reader would reject. This also preserves the
        # pending tombstone when a later process or signal receipt cannot fit.
        _parse_registry(encoded)
        _atomic_write(self.path, encoded)

    def _reconcile(self, launches: dict[str, Launch]) -> dict[str, Launch]:
        """Crash-window tombstones: never spawn or signal again on recovery."""
        for record in launches.values():
            if record.status == "launch_pending" and record.launch_id not in self._procs:
                record.status = "launch_delivery_unknown"
                record.note = "console did not persist a spawn receipt; the original process may exist"
            if record.stop is not None and record.stop.delivered is None and record.launch_id not in self._procs:
                record.stop.delivered = None
                record.stop.detail = record.stop.detail or "stop_delivery_unknown: console stopped between persisting the request and signalling"
        return launches

    # -- helpers ---------------------------------------------------------------

    def reserve_output_dir(self, slug: str) -> Path:
        self.run_root.mkdir(parents=True, exist_ok=True)
        stem = f"{(slug or 'run').strip() or 'run'}_{time.strftime('%Y%m%d_%H%M%S')}"
        primary = self.run_root / stem
        try:
            primary.mkdir(exist_ok=False)
            return primary.resolve()
        except FileExistsError:
            pass
        for _ in range(64):
            candidate = self.run_root / f"{stem}_{os.getpid()}_{secrets.token_hex(6)}"
            try:
                candidate.mkdir(exist_ok=False)
                return candidate.resolve()
            except FileExistsError:
                continue
        raise RuntimeError("could not reserve a unique output directory")

    @staticmethod
    def check_user_args(args: list[str]) -> str:
        for token in args:
            if not isinstance(token, str) or "\0" in token or "\n" in token:
                return "argument contains an invalid character"
            name = token.split("=", 1)[0]
            if name in _FORBIDDEN_USER_FLAGS:
                return f"{name} is managed by the console; do not pass it"
        return ""

    def validate_args(self, args: list[str], *, timeout_s: float = 90.0) -> ValidationResult:
        problem = self.check_user_args(args)
        if problem:
            return ValidationResult(False, problem)
        if not self.validate_enabled:
            return ValidationResult(True, "validation disabled")
        interpreter = self.command_prefix[0] if self.command_prefix else sys.executable
        try:
            completed = subprocess.run(
                [interpreter, "-c", _VALIDATE_SCRIPT],
                input=json.dumps(args),
                capture_output=True,
                text=True,
                cwd=self.repo_root,
                timeout=timeout_s,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return ValidationResult(False, f"validator could not run: {exc.__class__.__name__}")
        line = completed.stdout.strip().splitlines()[-1] if completed.stdout.strip() else ""
        try:
            payload = json.loads(line)
        except ValueError:
            return ValidationResult(False, f"validator produced no verdict (exit {completed.returncode}): {completed.stderr.strip()[-400:]}")
        if not payload.get("ok"):
            return ValidationResult(False, f"{payload.get('error', 'rejected')}: {completed.stderr.strip()[-400:]}")
        parsed = payload.get("parsed") if isinstance(payload.get("parsed"), dict) else {}
        return ValidationResult(True, "", parsed)

    # -- launch ----------------------------------------------------------------

    def _spawn(self, launches: dict[str, Launch], record: Launch) -> Launch:
        launches[record.launch_id] = record
        self._save(launches)  # launch_pending tombstone persisted before Popen
        log_path = Path(record.console_log)
        try:
            with log_path.open("ab") as log:
                proc = subprocess.Popen(  # noqa: S603 - argv list, no shell
                    record.argv,
                    cwd=record.cwd,
                    stdin=subprocess.DEVNULL,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    start_new_session=True,
                    close_fds=True,
                )
        except OSError as exc:
            record.status = "launch_failed"
            record.spawn_error = f"{exc.__class__.__name__}: {exc}"
            self._save(launches)
            return record
        self._procs[record.launch_id] = proc
        record.pid = proc.pid
        identity = read_proc_identity(proc.pid, self.proc_root)
        if identity is not None:
            record.pgid, record.start_ticks = identity
        else:
            try:
                record.pgid = os.getpgid(proc.pid)
            except OSError:
                record.pgid = None
        record.boot_id = read_boot_id(self.proc_root)
        record.status = "running"
        self._save(launches)
        return record

    def launch(self, user_args: list[str], *, slug: str, idempotency_key: str, kind: str = "run", validate: bool = True) -> tuple[Launch | None, str]:
        with self._locked():
            launches = self._load()
            for record in launches.values():
                if record.idempotency_key == idempotency_key:
                    return record, "existing launch returned for this idempotency key; nothing spawned"
            if validate:
                verdict = self.validate_args(user_args)
                if not verdict.ok:
                    return None, verdict.error
            else:
                problem = self.check_user_args(user_args)
                if problem:
                    return None, problem
            output_dir = self.reserve_output_dir(slug)
            launch_id = secrets.token_hex(8)
            record = Launch(
                launch_id=launch_id,
                idempotency_key=idempotency_key,
                kind=kind,
                argv=[*self.command_prefix, *user_args, "--output-dir", str(output_dir)],
                cwd=str(self.repo_root),
                output_dir=str(output_dir),
                console_log=str(self.state_root / "logs" / f"{launch_id}.log"),
                created_at=time.time(),
            )
            return self._spawn(launches, record), "launched"

    def resume(self, run_dir: Path, *, accept_source_hash: str = "", idempotency_key: str) -> tuple[Launch | None, str]:
        run_dir = Path(run_dir).resolve()
        if not (run_dir / "attempt_checkpoint.json").is_file():
            return None, "run directory has no attempt_checkpoint.json; nothing to resume"
        args = ["--resume-from", str(run_dir)]
        if accept_source_hash:
            args += ["--resume-accept-source-hash", accept_source_hash]
        with self._locked():
            launches = self._load()
            for record in launches.values():
                if record.idempotency_key == idempotency_key:
                    return record, "existing launch returned for this idempotency key; nothing spawned"
            output_dir = self.reserve_output_dir(f"{run_dir.name}_resume")
            launch_id = secrets.token_hex(8)
            record = Launch(
                launch_id=launch_id,
                idempotency_key=idempotency_key,
                kind="resume",
                argv=[*self.command_prefix, *args, "--output-dir", str(output_dir)],
                cwd=str(self.repo_root),
                output_dir=str(output_dir),
                console_log=str(self.state_root / "logs" / f"{launch_id}.log"),
                created_at=time.time(),
                note=f"resumes {run_dir}",
            )
            return self._spawn(launches, record), "launched (paid resume of a durable attempt)"

    def launch_nl(
        self,
        text: str,
        *,
        project_path: Path,
        user_args: list[str],
        idempotency_key: str,
        slug: str = "nl",
        formalize_only: bool = False,
    ) -> tuple[Launch | None, str]:
        if not text.strip():
            return None, "empty theorem text"
        project_path = Path(project_path).expanduser().resolve()
        if not any((project_path / f).is_file() for f in ("lakefile.toml", "lakefile.lean")):
            return None, "project path must contain a Lake project (lakefile.toml or lakefile.lean)"
        if formalize_only and user_args:
            return None, "translate-only does not accept prover arguments"
        problem = self.check_user_args(user_args)
        if problem:
            return None, problem
        with self._locked():
            launches = self._load()
            for record in launches.values():
                if record.idempotency_key == idempotency_key:
                    return record, "existing launch returned for this idempotency key; nothing spawned"
            output_dir = self.reserve_output_dir(slug)
            launch_id = secrets.token_hex(8)
            nl_dir = self.state_root / "nl" / launch_id  # must not exist; nl_input creates it
            record = Launch(
                launch_id=launch_id,
                idempotency_key=idempotency_key,
                kind="nl",
                argv=(
                    [*self.nl_command_prefix, "--text", text, "--project-path", str(project_path), "--output-dir", str(nl_dir), "--formalize-only"]
                    if formalize_only
                    else [*self.nl_command_prefix, "--text", text, "--project-path", str(project_path), "--output-dir", str(nl_dir), "--", *user_args, "--output-dir", str(output_dir)]
                ),
                cwd=str(self.repo_root),
                output_dir=str(output_dir),
                console_log=str(self.state_root / "logs" / f"{launch_id}.log"),
                created_at=time.time(),
                note=f"natural-language input; formalization artifacts in {nl_dir}",
            )
            return self._spawn(launches, record), "launched (formalization then proof search; the run directory fills once formalization succeeds)"

    # -- observation -----------------------------------------------------------

    def _identity_matches(self, record: Launch) -> tuple[bool, str]:
        if (not _identity_integer(record.pid) or not _identity_integer(record.pgid)
                or not _identity_integer(record.start_ticks, minimum=0)
                or not isinstance(record.boot_id, str) or not record.boot_id.strip()):
            return False, "complete process identity was not recorded"
        boot = read_boot_id(self.proc_root)
        if not isinstance(boot, str) or not boot.strip():
            return False, "current boot identity is unavailable"
        if record.boot_id != boot:
            return False, "boot id changed since launch"
        identity = read_proc_identity(record.pid, self.proc_root)
        if identity is None:
            return False, "process not found in /proc"
        pgid, start_ticks = identity
        if not _identity_integer(pgid) or not _identity_integer(start_ticks, minimum=0):
            return False, "current process identity is invalid"
        if start_ticks != record.start_ticks:
            return False, "pid reused by a different process (start time differs)"
        if pgid != record.pgid:
            return False, "process group differs from the owned launch group"
        return True, "identity verified"

    def refresh(self, record: Launch, launches: dict[str, Launch] | None = None) -> Launch:
        proc = self._procs.get(record.launch_id)
        if proc is not None:
            code = proc.poll()
            if code is not None and record.status == "running":
                record.status = "exited"
                record.returncode = code
                record.exited_at = time.time()
                record.exit_source = "owned_wait"
                if record.stop is not None and record.stop.delivered is None:
                    record.stop.detail = record.stop.detail or "process exited; delivery receipt was never recorded"
            return record
        if record.status == "running":
            ok, detail = self._identity_matches(record)
            if not ok:
                record.status = "exited"
                record.returncode = None
                record.exited_at = time.time()
                record.exit_source = "proc_gone"
                record.note = f"not a child of this console; return code unknown ({detail})"
        return record

    def list(self) -> list[Launch]:
        with self._locked():
            launches = self._load()
            for record in launches.values():
                self.refresh(record)
            self._save(launches)
            return sorted(launches.values(), key=lambda r: r.created_at, reverse=True)

    def owned(self, run_dir: Path) -> Launch | None:
        target = str(Path(run_dir).resolve())
        for record in self.list():
            if record.output_dir == target:
                return record
        return None

    def wait(self, launch_id: str, timeout_s: float | None = None) -> int | None:
        proc = self._procs.get(launch_id)
        if proc is None:
            return None
        try:
            code = proc.wait(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            return None
        with self._locked():
            launches = self._load()
            record = launches.get(launch_id)
            if record is not None:
                self.refresh(record)
                self._save(launches)
        return code

    # -- stop ------------------------------------------------------------------

    def stop(self, launch_id: str, *, request_id: str | None = None) -> StopResult:
        request_id = request_id or secrets.token_hex(6)
        with self._locked():
            launches = self._load()
            record = launches.get(launch_id)
            if record is None:
                return StopResult("refused", "unknown launch")
            if record.stop is not None:
                self.refresh(record)
                self._save(launches)
                state = "delivered" if record.stop.delivered else ("delivery unknown" if record.stop.delivered is None else "delivery failed")
                return StopResult("already_requested", f"stop already requested at {time.strftime('%H:%M:%S', time.localtime(record.stop.requested_at))} ({state}); no second signal sent", record)
            self.refresh(record)
            if record.status != "running":
                self._save(launches)
                return StopResult("refused", f"launch is {record.status}; nothing to signal", record)
            ok, detail = self._identity_matches(record)
            if not ok or record.pgid is None:
                self._save(launches)
                return StopResult("refused", f"identity not verified ({detail}); refusing to signal", record)
            record.stop = StopRecord(requested_at=time.time(), request_id=request_id, delivered=None, detail="pending")
            self._save(launches)  # durable before the only signal
            try:
                os.killpg(record.pgid, signal.SIGINT)
            except OSError as exc:
                record.stop.delivered = False
                record.stop.detail = f"killpg failed: {exc.__class__.__name__}: {exc}"
                self._save(launches)
                return StopResult("delivery_unknown", record.stop.detail, record)
            record.stop.delivered = True
            record.stop.detail = "one SIGINT delivered to the owned launch group; cooperative grace is 120 s by default"
            self._save(launches)
            return StopResult("signalled", record.stop.detail, record)


def launch_lines(records: list[Launch]) -> list[str]:
    if not records:
        return ["no console launches recorded"]
    lines = []
    for record in records:
        when = time.strftime("%m-%d %H:%M:%S", time.localtime(record.created_at))
        code = "" if record.returncode is None else f" code {record.returncode}"
        unknown = " code unknown" if record.status == "exited" and record.returncode is None else ""
        stop = ""
        if record.stop is not None:
            stop = " · stop " + ("delivered" if record.stop.delivered else ("unknown" if record.stop.delivered is None else "failed"))
        lines.append(f"{when} {record.launch_id} {record.kind:6s} {record.status:24s}{code}{unknown}{stop} pid {record.pid or '-'} → {Path(record.output_dir).name}")
        if record.note:
            lines.append(f"    {record.note}")
        if record.spawn_error:
            lines.append(f"    spawn error: {record.spawn_error}")
    return lines
