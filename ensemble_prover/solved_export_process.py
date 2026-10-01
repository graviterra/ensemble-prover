"""Fresh-interpreter export with owned-process cleanup.

A search may outlive an update to its source checkout. Export reconstruction
therefore runs in a fresh interpreter, without the search's cached modules.
The private supervisor owns its entire descendant tree, including Lean tools
that start new process groups. Verification keeps its existing per-check
allowance; the bridge adds no overall mathematical-work deadline.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from typing import Any, Sequence

from .local_inference.network_policy import owned_worker_environment, restore_owned_worker_network_policy

_PROJECT_ROOT = Path(__file__).resolve().parent.parent
_CLEANUP_TIMEOUT_S = 10.0
_OWNERSHIP_ENV = "ENSEMBLE_SOLVED_EXPORT_NONCE"


def _export_one(output_dir: Path, project_dir: Path, solved_dir: Path | None) -> dict[str, Any]:
    try:
        from .extract_solved import SolvedExportVerificationError, export_solved_run
    except Exception as exc:
        return {"status": "import_error", "diagnostic": str(exc)}
    try:
        record = export_solved_run(
            output_dir,
            solved_dir=solved_dir,
            verify_lean=True,
            allow_pre_export_bootstrap=True,
            lean_project_dir=project_dir,
        )
    except SolvedExportVerificationError as exc:
        return {"status": str(exc.status or "lean_rejected"), "diagnostic": exc.output}
    except Exception as exc:
        return {"status": "exception", "diagnostic": f"{type(exc).__name__}: {exc}"}
    if record is None:
        return {"status": "not_reconstructable", "diagnostic": ""}
    if record.export_verified is not True or record.export_verification_status != "verified":
        return {"status": "exception", "diagnostic": "Exporter returned an unverified record"}
    return {
        "status": "verified",
        "diagnostic": record.export_verification_output,
        "record": {
            "output_path": record.output_path,
            "answer_visibility": record.answer_visibility,
            "opaque_mode": record.opaque_mode,
            "allow_official_answer_visibility": record.allow_official_answer_visibility,
            "official_answer_payload_present": record.official_answer_payload_present,
        },
    }


def _supervise(command: Sequence[str]) -> int:
    # This interpreter has no unrelated children. The existing private-worker
    # cleanup can therefore safely include adopted grandchildren and double
    # forks, without changing subreaper policy in an embedding application.
    from .mini_session.process_watchdog import (
        _enable_child_subreaper,
        _identity_alive,
        _refresh_known_tree,
        _terminate_worker_tree,
    )

    _enable_child_subreaper()

    def interrupted(_signum: int, _frame: Any) -> None:
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGHUP, interrupted)
    proc = subprocess.Popen(list(command), env=owned_worker_environment())
    known: dict[int, int] = {}
    try:
        while True:
            _refresh_known_tree(known, ownership_nonce="")
            try:
                return proc.wait(timeout=0.1)
            except subprocess.TimeoutExpired:
                continue
    except KeyboardInterrupt:
        return 130
    finally:
        _terminate_worker_tree(proc, known, ownership_nonce="")
        _refresh_known_tree(known, ownership_nonce="")
        if any(_identity_alive(pid, started) for pid, started in known.items()):
            raise RuntimeError("Export descendant cleanup could not be confirmed")


def _refresh_export_tree(known: dict[int, int]) -> None:
    """Refresh only captured export descendants, never sibling application work."""
    from .mini_session.process_watchdog import (
        _identity_alive, _proc_child_pids, _proc_identity,
    )

    pending = [pid for pid, started in tuple(known.items()) if _identity_alive(pid, started)]
    visited: set[int] = set()
    while pending:
        parent = pending.pop()
        if parent in visited:
            continue
        visited.add(parent)
        for child in _proc_child_pids(parent):
            identity = _proc_identity(child)
            if identity is not None:
                known[identity[0]] = identity[1]
                pending.append(child)


def _recover_export_orphans(known: dict[int, int], nonce: str) -> None:
    """Recover ordinary orphaned Lean children after a supervisor crash.

    The nonce survives the standard sanitized Lean environment. Previously
    captured identities also cover children that later scrub their environment;
    an unobserved, environment-scrubbed orphan cannot be recovered this way.
    """
    from .mini_session.process_watchdog import _proc_identity

    marker = (_OWNERSHIP_ENV + "=" + nonce).encode()
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        identity = _proc_identity(int(entry.name))
        if identity is None:
            continue
        try:
            environment = (entry / "environ").read_bytes()
        except OSError:
            continue
        if marker in environment.split(b"\0") and _proc_identity(identity[0]) == identity:
            known[identity[0]] = identity[1]


def _export_process_running(pid: int, started: int) -> bool:
    try:
        raw = Path(f"/proc/{pid}/stat").read_text()
        fields = raw[raw.rfind(")") + 2:].split()
        return int(fields[19]) == started and fields[0] != "Z"
    except (OSError, ValueError, IndexError):
        return False


def _cleanup_export_tree(proc: subprocess.Popen, known: dict[int, int], nonce: str) -> None:
    from .mini_session.process_watchdog import (
        _reap_known_children_nonblocking, _signal_known,
    )

    # The private subreaper normally does this work. After its crash, retain
    # exact ownership through captured identities and the per-export nonce.
    _recover_export_orphans(known, nonce)
    expires = time.monotonic() + _CLEANUP_TIMEOUT_S
    while True:
        _refresh_export_tree(known)
        _signal_known(known, signal.SIGSTOP)
        _refresh_export_tree(known)
        _signal_known(known, signal.SIGKILL)
        _reap_known_children_nonblocking(known, root_pid=proc.pid)
        proc.poll()
        if not any(_export_process_running(pid, started) for pid, started in known.items()):
            return
        if time.monotonic() >= expires:
            raise RuntimeError("Export descendant cleanup could not be confirmed")
        time.sleep(0.01)


def _run_process(command: Sequence[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    from .mini_session.process_watchdog import _proc_identity

    nonce = uuid.uuid4().hex
    # A crashed supervisor must not leave communicate() waiting on a pipe
    # still held open by an orphaned new-session Lean process.
    with tempfile.TemporaryFile() as output_file:
        proc = subprocess.Popen(
            list(command), cwd=cwd,
            env=owned_worker_environment(overrides={_OWNERSHIP_ENV: nonce}),
            stdout=output_file, stderr=subprocess.STDOUT, start_new_session=True,
        )
        identity = _proc_identity(proc.pid)
        known = {} if identity is None else {identity[0]: identity[1]}
        try:
            while True:
                _refresh_export_tree(known)
                try:
                    proc.wait(timeout=0.1)
                    break
                except subprocess.TimeoutExpired:
                    continue
            if proc.returncode != 0:
                _cleanup_export_tree(proc, known, nonce)
        except BaseException:
            # Ask the private supervisor to quiesce/reap first. Only cleanup
            # has a deadline; mathematical replay has no aggregate deadline.
            prior_mask = signal.pthread_sigmask(
                signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT, signal.SIGHUP},
            )
            try:
                try:
                    proc.send_signal(signal.SIGTERM)
                except OSError:
                    pass
                expires = time.monotonic() + _CLEANUP_TIMEOUT_S
                while proc.poll() is None and time.monotonic() < expires:
                    _refresh_export_tree(known)
                    time.sleep(0.01)
                _cleanup_export_tree(proc, known, nonce)
            finally:
                signal.pthread_sigmask(signal.SIG_SETMASK, prior_mask)
            raise
        output_file.seek(0)
        output = output_file.read().decode("utf-8", errors="replace")
        return subprocess.CompletedProcess(command, proc.returncode, output)


def export_solved_run_in_fresh_process(
    output_dir: Path,
    *,
    lean_project_dir: Path,
    solved_dir: Path | None = None,
) -> dict[str, Any]:
    """Return an export status only after fresh replay and child-tree cleanup."""
    with tempfile.TemporaryDirectory(prefix="ensemble-solved-export-") as temporary:
        result_path = Path(temporary) / "result.json"
        command = [
            sys.executable, "-m", "ensemble_prover.solved_export_process",
            "--output-dir", str(Path(output_dir).resolve()),
            "--lean-project-dir", str(Path(lean_project_dir).resolve()),
            "--result-path", str(result_path),
        ]
        if solved_dir is not None:
            command.extend(["--solved-dir", str(Path(solved_dir).resolve())])
        result = _run_process(command, cwd=_PROJECT_ROOT)
        if result.returncode != 0:
            raise RuntimeError(
                f"Export process exited with status {result.returncode}: {result.stdout[-4000:]}"
            )
        payload = json.loads(result_path.read_text(encoding="utf-8"))
        if not isinstance(payload, dict) or not isinstance(payload.get("status"), str):
            raise ValueError("Export process returned a malformed status")
        if payload["status"] == "verified":
            record = payload.get("record")
            if not isinstance(record, dict) or not isinstance(record.get("output_path"), str):
                raise ValueError("Export process returned a malformed verified record")
            if not record["output_path"]:
                raise ValueError("Export process returned an empty verified path")
        return payload


def main(argv: Sequence[str] | None = None) -> int:
    restore_owned_worker_network_policy()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--lean-project-dir", type=Path, required=True)
    parser.add_argument("--solved-dir", type=Path)
    parser.add_argument("--result-path", type=Path, required=True)
    parser.add_argument("--worker", action="store_true")
    arguments = list(sys.argv[1:] if argv is None else argv)
    args = parser.parse_args(arguments)
    if not args.worker:
        return _supervise([
            sys.executable, "-m", "ensemble_prover.solved_export_process", "--worker", *arguments,
        ])
    result = _export_one(args.output_dir, args.lean_project_dir, args.solved_dir)
    args.result_path.write_text(json.dumps(result, allow_nan=False), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
