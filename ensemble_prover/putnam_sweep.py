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
from .subprocess_environment import trusted_provider_worker_environment


ROOT = Path(__file__).resolve().parent.parent
_PROBLEM = re.compile(r"putnam_\d{4}_[ab][1-6]")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_TERMINAL = {"solved", "failed", "cutoff", "skipped_solved"}
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


@dataclass
class AcceptanceGate:
    start_monotonic: float
    first_accepted_by_s: float = 600.0
    second_accepted_by_s: float = 1800.0
    accepted: dict[str, float] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self.first_accepted_by_s = _seconds(self.first_accepted_by_s)
        self.second_accepted_by_s = _seconds(self.second_accepted_by_s)
        if self.second_accepted_by_s < self.first_accepted_by_s:
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
        if elapsed >= self.first_accepted_by_s and not any(
            value <= self.first_accepted_by_s for value in self.accepted.values()
        ):
            return "first_acceptance_deadline"
        if (
            elapsed >= self.second_accepted_by_s
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
                if (
                    isinstance(record, dict)
                    and record.get("phase") == "session_accepted_proof"
                ):
                    records.append(record)
        return records


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
    first_accepted_by_s: float = 600,
    second_accepted_by_s: float = 1800,
) -> dict[str, Any]:
    source_dir = Path(source_dir).resolve()
    solved_dirs = [Path(path).resolve() for path in solved_dirs]
    if isinstance(seed, bool) or not isinstance(seed, int):
        raise ValueError("seed must be an integer")
    gate = AcceptanceGate(0, first_accepted_by_s, second_accepted_by_s)
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
        _seconds(data.get("first_accepted_by_s")),
        _seconds(data.get("second_accepted_by_s")),
    )
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
    first_accepted_by_s: float = 600,
    second_accepted_by_s: float = 1800,
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
        relay.copy_available(final=True)
        monitor_error = monitor_error or relay.error
    if not cleaned:
        status = "cleanup_unconfirmed"
    elif _summary_solved(output_dir, proc.returncode):
        status, cutoff = "solved", ""
    elif interrupted:
        status = "interrupted"
    elif monitor_error:
        status = "monitor_error"
    else:
        status = "cutoff" if cutoff else "failed"
    return {
        "status": status,
        "console_log": str(console_path),
        "exit_code": proc.returncode,
        "cutoff_reason": cutoff,
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
        if any(
            row["status"] in {"running", "cleanup_unconfirmed", "monitor_error"}
            for row in manifest["queue"]
        ):
            raise ValueError(
                "previous attempt cleanup is unconfirmed; refusing to start new work"
            )
        for index, row in enumerate(manifest["queue"]):
            if should_stop():
                return 130
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
                poll_interval_s=poll_interval_s,
                cleanup_timeout_s=cleanup_timeout_s,
                should_stop=should_stop,
                on_started=started,
            )
            attempt.update(result)
            row["status"] = result["status"]
            save_manifest(manifest_path, manifest)
            print(
                f"  {result['status']}; accepted={len(result.get('accepted_identities', []))}",
                flush=True,
            )
            if row["status"] in {"cleanup_unconfirmed", "monitor_error"}:
                return 2
            if row["status"] == "interrupted":
                return 130
    return 0


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
    parser.add_argument("--first-accepted-by-s", type=float)
    parser.add_argument("--second-accepted-by-s", type=float)
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
                    )
                )
                or mini_args
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
                    first_accepted_by_s=args.first_accepted_by_s
                    if args.first_accepted_by_s is not None
                    else 600,
                    second_accepted_by_s=args.second_accepted_by_s
                    if args.second_accepted_by_s is not None
                    else 1800,
                )
                save_manifest(manifest_path, manifest)
        print(
            f"Sweep: {manifest_path.resolve()}\nSeed: {manifest['seed']}\n"
            f"Corpus: {manifest['corpus_count']}; excluded: {manifest['excluded_solved_count']}; "
            f"selection policy: {manifest.get('solved_policy', 'verified')}\n"
            f"Unsolved queue: {len(manifest['queue'])}"
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
