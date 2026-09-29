"""Launch prepared generic Lean targets through Mini's existing supervisor."""

from __future__ import annotations

import hashlib
import json
import signal
import sys
import threading
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterator, Mapping, Sequence

from .lean_input_io import read_source_bytes
from .lean_input_preparation import validate_prepared_environment
from .llm_error_policy import is_provider_infrastructure_failure
from .putnam_sweep import _manifest_lock, run_attempt, save_manifest
from .solved_export_policy import effective_solved, export_boundary_present
from .theorem_project import theorem_artifact_slug

MANIFEST_NAME = "batch_manifest.json"
_STOP_STATUSES = {
    "interrupted", "cleanup_unconfirmed", "monitor_error", "infrastructure_blocked",
}


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


@contextmanager
def _stop_requests(should_stop: Callable[[], bool]) -> Iterator[Callable[[], bool]]:
    stopped = False

    def request_stop(_signum: int, _frame: Any) -> None:
        nonlocal stopped
        stopped = True

    previous = {}
    if threading.current_thread() is threading.main_thread():
        previous = {
            signum: signal.signal(signum, request_stop)
            for signum in (signal.SIGINT, signal.SIGTERM)
        }
    try:
        yield lambda: stopped or should_stop()
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def _validate_prepared_target(row: Mapping[str, Any]) -> None:
    for prefix in ("source", "prepared"):
        raw_path = row.get(f"{prefix}_path")
        if not isinstance(raw_path, str) or not raw_path:
            raise ValueError(f"missing {prefix} path")
        path = Path(raw_path)
        if not path.is_file() or path.suffix != ".lean":
            raise ValueError(f"{prefix} input is not a Lean file: {path}")
        actual = hashlib.sha256(read_source_bytes(path)).hexdigest()
        if actual != row.get(f"{prefix}_sha256"):
            raise ValueError(f"{prefix} input changed after preparation: {path}")
    if not str(row.get("theorem_name") or row.get("name") or "").strip():
        raise ValueError("missing theorem name")
    project_path = row.get("project_path")
    if not isinstance(project_path, str) or not project_path or not Path(project_path).is_dir():
        raise ValueError("missing Lean project directory")
    validate_prepared_environment(row)


def _command(row: Mapping[str, Any], output_dir: Path, mini_args: Sequence[str]) -> list[str]:
    return [
        sys.executable, "-m", "ensemble_prover.mini_prover",
        "--lean-file", str(Path(row["prepared_path"]).resolve()),
        "--theorem-name", str(row.get("theorem_name") or row["name"]),
        "--project-path", str(Path(row["project_path"]).resolve()),
        "--output-dir", str(output_dir),
        *mini_args,
    ]


def _read_summary(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return value if isinstance(value, dict) else {}


def _record_child_result(row: dict[str, Any], child: Path, result: Mapping[str, Any]) -> None:
    # Generic answer preparation owns ``run`` and places proof work in
    # ``run/proof``; ordinary generic theorem input writes directly to ``run``.
    proof = child / "proof" if (child / "proof").is_dir() else child
    row["proof_output_dir"] = str(proof)
    if (proof / "attempt_checkpoint.json").is_file():
        row["resume_command"] = [
            sys.executable, "-m", "ensemble_prover.mini_prover",
            "--resume-from", str(proof),
        ]
    summary = _read_summary(proof / "summary.json")
    status = str(result.get("status") or "failed")
    if result.get("cleanup_confirmed") is not True:
        status = "cleanup_unconfirmed"
    elif result.get("exit_code") == 130:
        status = "interrupted"
    elif status not in _STOP_STATUSES:
        if (result.get("exit_code") == 0 and effective_solved(summary)
                and export_boundary_present(summary)):
            status = "solved"
        else:
            # A zero process exit or a pre-export ``solved`` summary is not
            # a verified solution. Never propagate the monitor's guess.
            status = "failed"
            if not summary and proof != child:
                summary = _read_summary(child / "summary.json")
            reason = str(summary.get("failure_reason") or "")
            if (summary.get("infrastructure_aborted") is True
                    and is_provider_infrastructure_failure(reason)):
                status = "infrastructure_blocked"
                row["failure_reason"] = reason
    row.update(status=status, result=dict(result), finished_at=_now())


def _validate_mini_args(mini_args: Sequence[str]) -> None:
    from .mini_prover import _build_argparser

    parser = _build_argparser()
    owned = {
        "_input_path", "_check_input", "lean_file", "putnam_file", "theorem_name",
        "lean_project_dir", "output_dir", "resume_from", "rediscover_from", "help",
    }
    index = 0
    while index < len(mini_args):
        token = mini_args[index]
        parsed = parser._parse_optional(token)
        if parsed is None:
            raise ValueError(f"unexpected positional Mini argument: {token}")
        candidates = parsed if isinstance(parsed, list) else [parsed]
        action, value = candidates[0][0], candidates[0][-1]
        if action is None or action.dest in owned:
            raise ValueError(f"batch target argument must not be forwarded: {token}")
        if action.nargs not in (None, 0):
            raise ValueError(f"unsupported Mini argument arity: {token}")
        count = 2 if action.nargs is None and value is None else 1
        if index + count > len(mini_args):
            raise ValueError(f"missing Mini argument value: {token}")
        index += count


def _run_queue(
    manifest: dict[str, Any], manifest_path: Path, *,
    should_stop: Callable[[], bool], poll_interval_s: float, cleanup_timeout_s: float,
) -> int:
    for index, row in enumerate(manifest["queue"]):
        if should_stop():
            return 130
        if row["status"] == "input_error":
            continue
        try:
            _validate_prepared_target(row)
        except (OSError, ValueError) as exc:
            row.update(status="input_error", error=str(exc))
            save_manifest(manifest_path, manifest)
            continue
        if should_stop():
            return 130
        name = str(row.get("theorem_name") or row["name"])
        attempt = manifest_path.parent / "attempts" / f"{index + 1:04d}_{theorem_artifact_slug(name)}"
        attempt.mkdir(parents=True, exist_ok=False)
        # run_attempt creates its monitor directory. Keeping the actual Mini
        # output separate lets both plain and answer-discovery CLIs allocate
        # their own fresh generation without changing their checkpoint rules.
        child = attempt / "run"
        command = _command(row, child, manifest["mini_args"])
        row.update(status="running", output_dir=str(child), command=command, started_at=_now())
        save_manifest(manifest_path, manifest)
        print(f"Lean target {index + 1}/{len(manifest['queue'])}: {name}; output: {child}", flush=True)

        def on_started(pid: int) -> None:
            row["cli_pid"] = pid
            save_manifest(manifest_path, manifest)

        try:
            result = run_attempt(
                command, attempt / "monitor",
                first_accepted_by_s=0, second_accepted_by_s=0,
                startup_liveness_s=0, startup_timeout_s=0,
                poll_interval_s=poll_interval_s, cleanup_timeout_s=cleanup_timeout_s,
                should_stop=should_stop, on_started=on_started,
                cwd=Path(manifest["working_directory"]),
            )
        except KeyboardInterrupt:
            row.update(status="interrupted", finished_at=_now())
            save_manifest(manifest_path, manifest)
            return 130
        except (OSError, ValueError) as exc:
            row.update(status="monitor_error", error=str(exc), finished_at=_now())
            save_manifest(manifest_path, manifest)
            return 2
        _record_child_result(row, child, result)
        save_manifest(manifest_path, manifest)
        print(f"Lean target {name}: {row['status']}", flush=True)
        if should_stop() or row["status"] == "interrupted" or result.get("exit_code") == 130:
            return 130
        if row["status"] in _STOP_STATUSES:
            return 2
    if any(row["status"] == "input_error" for row in manifest["queue"]) or manifest["metadata"].get("errors"):
        return 2
    return 0 if all(row["status"] == "solved" for row in manifest["queue"]) else 1


def run_prepared_batch(
    targets: Sequence[Mapping[str, Any]], output_dir: Path, mini_args: Sequence[str], *,
    metadata: Mapping[str, Any] | None = None,
    should_stop: Callable[[], bool] = lambda: False,
    poll_interval_s: float = 1, cleanup_timeout_s: float = 130,
) -> int:
    """Run fresh prepared targets sequentially, persisting each child outcome.

    Existing Mini options are passed unchanged; its supervisor owns all proof
    and startup budgets. This frontend adds no acceptance or solving deadline.
    Individual interrupted proof runs retain normal ``--resume-from`` support.
    """
    _validate_mini_args(mini_args)
    output_dir = Path(output_dir).expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = output_dir / MANIFEST_NAME
    with _manifest_lock(manifest_path):
        if manifest_path.exists():
            raise ValueError(f"batch output already has a manifest: {manifest_path}")
        manifest = {
            "schema_version": 1, "kind": "lean_input_batch", "created_at": _now(),
            "working_directory": str(Path.cwd()),
            "metadata": dict(metadata or {}), "mini_args": list(mini_args),
            "queue": [
                {**row, "status": "input_error" if row.get("error") else "pending"}
                for row in targets
            ],
        }
        save_manifest(manifest_path, manifest)
        with _stop_requests(should_stop) as stopped:
            code = _run_queue(
                manifest, manifest_path, should_stop=stopped,
                poll_interval_s=poll_interval_s, cleanup_timeout_s=cleanup_timeout_s,
            )
        manifest.update(finished_at=_now(), exit_code=code)
        save_manifest(manifest_path, manifest)
        return code
