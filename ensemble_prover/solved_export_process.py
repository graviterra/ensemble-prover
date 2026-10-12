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
from .mini_session.process_watchdog import WORKER_CLEANUP_INCOMPLETE_EXIT_CODE, _WorkerCleanupIncomplete
from .mini_session.supervisor_completion import (
    SupervisorCompletionChannel,
    _WorkerCleanupState,
    adopt_supervisor_completion,
)

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
            "verified_output_path": str(
                (Path(record.output_path) if Path(record.output_path).is_absolute()
                 else _PROJECT_ROOT / record.output_path).absolute()
            ),
            "answer_visibility": record.answer_visibility,
            "opaque_mode": record.opaque_mode,
            "allow_official_answer_visibility": record.allow_official_answer_visibility,
            "official_answer_payload_present": record.official_answer_payload_present,
            "verified_source_digest": getattr(record, "verified_source_digest", ""),
            "accepted_root_proof_hash": getattr(record, "accepted_root_proof_hash", ""),
            "export_occurrence_id": uuid.uuid4().hex,
        },
    }


def _supervise(command: Sequence[str], *, cleanup_state: _WorkerCleanupState | None = None) -> int:
    # This interpreter has no unrelated children. The existing private-worker
    # cleanup can therefore safely include adopted grandchildren and double
    # forks, without changing subreaper policy in an embedding application.
    from .mini_session.process_watchdog import (
        _WorkerCleanupIncomplete,
        _enable_child_subreaper,
        _proc_identity,
        _refresh_known_tree,
        _signal_known,
        _terminate_worker_tree,
    )

    if cleanup_state is None:
        cleanup_state = _WorkerCleanupState()
    _enable_child_subreaper()

    stop_signals: list[int] = []

    def interrupted(signum: int, _frame: Any) -> None:
        # Queue requests so a repeat cannot unwind Popen before assignment or
        # interrupt resource teardown in this private supervisor.
        if len(stop_signals) < 2:
            stop_signals.append(int(signum))

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    signal.signal(signal.SIGHUP, interrupted)
    proc = None
    known: dict[int, int] = {}
    try:
        proc = subprocess.Popen(list(command), env=owned_worker_environment())
        identity = _proc_identity(proc.pid)
        if identity is not None:
            known[identity[0]] = identity[1]
        stop_deadline = None
        while True:
            _refresh_known_tree(known, ownership_nonce="")
            if len(stop_signals) > 1:
                return 130
            if stop_signals and stop_deadline is None:
                stop_deadline = time.monotonic() + _CLEANUP_TIMEOUT_S
                _signal_known(known, signal.SIGTERM)
            try:
                rc = proc.wait(timeout=0.1)
                return 130 if stop_signals and rc != 0 else rc
            except subprocess.TimeoutExpired:
                if stop_deadline is not None and time.monotonic() >= stop_deadline:
                    return 130
    except KeyboardInterrupt:
        return 130
    finally:
        cleanup_state.complete = _terminate_worker_tree(proc, known, ownership_nonce="")
        if not cleanup_state.complete:
            raise _WorkerCleanupIncomplete("Export descendant cleanup could not be confirmed")


def _refresh_export_tree(known: dict[int, int]) -> bool:
    """Refresh only captured export descendants, never sibling application work."""
    from .mini_session.process_watchdog import _refresh_known_tree

    return _refresh_known_tree(known, ownership_nonce="", include_supervisor=False)


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


def _export_process_running(pid: int, started: int) -> bool | None:
    """Distinguish a stopped writer from an unreadable process observation."""
    from .mini_session.process_watchdog import _proc_stat_observation

    observation, absent = _proc_stat_observation(pid, include_zombies=False)
    if absent:
        return False
    if observation is None:
        return None
    return observation[:2] == (pid, started)


def _cleanup_export_tree(proc: subprocess.Popen | None, known: dict[int, int], nonce: str) -> None:
    from .mini_session.process_watchdog import _WorkerCleanupIncomplete

    prior_mask = None
    complete = False
    try:
        prior_mask = signal.pthread_sigmask(
            signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT, signal.SIGHUP},
        )
        _cleanup_export_tree_blocked(proc, known, nonce)
        complete = True
    except BaseException:
        raise _WorkerCleanupIncomplete("Export descendant cleanup could not be confirmed") from None
    finally:
        try:
            if prior_mask is not None:
                signal.pthread_sigmask(signal.SIG_SETMASK, prior_mask)
        except BaseException:
            if not complete:
                raise _WorkerCleanupIncomplete("Export descendant cleanup could not be confirmed") from None
            raise


def _cleanup_export_tree_blocked(proc: subprocess.Popen | None, known: dict[int, int], nonce: str) -> None:
    from .mini_session.process_watchdog import (
        _reap_known_children_nonblocking, _signal_known,
    )

    # The private subreaper normally does this work. After its crash, retain
    # exact ownership through captured identities and the per-export nonce.
    _recover_export_orphans(known, nonce)
    expires = time.monotonic() + _CLEANUP_TIMEOUT_S
    stable_rounds = 0
    previous: set[tuple[int, int]] = set()
    while True:
        _refresh_export_tree(known)
        _signal_known(known, signal.SIGSTOP)
        complete = _refresh_export_tree(known)
        current = set(known.items())
        stable_rounds = stable_rounds + 1 if complete and current == previous else 0
        previous = current
        # The embedding process is not a private subreaper. Preserve readable
        # parent lineage until the frozen descendant closure is captured.
        if stable_rounds >= 3:
            _signal_known(known, signal.SIGKILL)
        _reap_known_children_nonblocking(known, root_pid=proc.pid if proc is not None else -1)
        # A lost embedding Popen handle cannot establish root exit. Nonce
        # recovery still cleans safely identified children before failing.
        root_exited = proc is not None and proc.poll() is not None
        if root_exited and complete and all(
            _export_process_running(pid, started) is False for pid, started in known.items()
        ):
            return
        if time.monotonic() >= expires:
            _signal_known(known, signal.SIGKILL)
            raise RuntimeError("Export descendant cleanup could not be confirmed")
        time.sleep(0.01)


def _run_process(command: Sequence[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    from .mini_session.process_watchdog import _proc_identity, _signal_known

    handled_signals = {signal.SIGTERM, signal.SIGINT, signal.SIGHUP}
    caller_mask = signal.pthread_sigmask(signal.SIG_BLOCK, set())
    nonce = uuid.uuid4().hex
    # A crashed supervisor must not leave communicate() waiting on a pipe
    # still held open by an orphaned new-session Lean process.
    completion = SupervisorCompletionChannel()
    proc = None
    local_cleanup_complete = False
    output_file = None
    pending_error = None
    try:
        output_file = tempfile.TemporaryFile()
        known: dict[int, int] = {}
        try:
            signal.pthread_sigmask(signal.SIG_BLOCK, handled_signals)
            try:
                completion.begin_launch()
                proc = subprocess.Popen(
                    [sys.executable, '-I', '-S',
                     str(Path(__file__).with_name('_export_process_bootstrap.py').resolve()),
                     ','.join(str(int(sig)) for sig in sorted(caller_mask)), *command], cwd=cwd,
                    env=owned_worker_environment(overrides={
                        _OWNERSHIP_ENV: nonce, **completion.environment,
                    }),
                    pass_fds=completion.pass_fds,
                    stdout=output_file, stderr=subprocess.STDOUT, start_new_session=True,
                )
                completion.close_parent_writer()
                identity = _proc_identity(proc.pid)
                if identity is not None:
                    known[identity[0]] = identity[1]
            finally:
                signal.pthread_sigmask(signal.SIG_SETMASK, caller_mask)
            while True:
                _refresh_export_tree(known)
                try:
                    proc.wait(timeout=0.1)
                    break
                except subprocess.TimeoutExpired:
                    continue
        except BaseException:
            # Ask the private supervisor to quiesce/reap first. Only cleanup
            # has a deadline; mathematical replay has no aggregate deadline.
            try:
                signal.pthread_sigmask(signal.SIG_BLOCK, handled_signals)
                if proc is not None:
                    root_started = known.get(proc.pid)
                    if root_started is not None:
                        _signal_known({proc.pid: root_started}, signal.SIGTERM)
                    expires = time.monotonic() + _CLEANUP_TIMEOUT_S
                    while proc.poll() is None and time.monotonic() < expires:
                        _refresh_export_tree(known)
                        time.sleep(0.01)
            except BaseException:
                # The final sweep below decides safety. Preserve the original
                # cancellation or failure if that sweep confirms completion.
                pass
            raise
        finally:
            # Keep handled signals blocked through the entire teardown and
            # output close. Unmasking between guards can lose cleanup failure
            # or leak the temporary descriptor on a repeat interruption.
            try:
                signal.pthread_sigmask(signal.SIG_BLOCK, handled_signals)
            finally:
                _cleanup_export_tree(proc, known, nonce)
                local_cleanup_complete = True
        output_file.seek(0)
        output = output_file.read().decode("utf-8", errors="replace")
        return subprocess.CompletedProcess(command, proc.returncode, output)
    except BaseException as exc:
        pending_error = exc
        raise
    finally:
        try:
            try:
                if output_file is not None:
                    output_file.close()
            except BaseException as exc:
                if pending_error is None:
                    pending_error = exc
            try:
                signal.pthread_sigmask(signal.SIG_SETMASK, caller_mask)
            except BaseException as exc:
                if pending_error is None:
                    pending_error = exc
        finally:
            # Completion authority is checked after every fallible output and
            # resource operation. An exit code alone never authorizes handoff.
            completion.finalize(
                proc, local_cleanup_complete=local_cleanup_complete, pending_error=pending_error,
            )


def export_solved_run_in_fresh_process(
    output_dir: Path,
    *,
    lean_project_dir: Path,
    solved_dir: Path | None = None,
) -> dict[str, Any]:
    """Return an export status only after fresh replay and child-tree cleanup."""
    temporary = tempfile.TemporaryDirectory(prefix="ensemble-solved-export-")
    cleanup_failure = None
    try:
        result_path = Path(temporary.name) / "result.json"
        command = [
            sys.executable, "-m", "ensemble_prover.solved_export_process",
            "--output-dir", str(Path(output_dir).resolve()),
            "--lean-project-dir", str(Path(lean_project_dir).resolve()),
            "--result-path", str(result_path),
        ]
        if solved_dir is not None:
            command.extend(["--solved-dir", str(Path(solved_dir).resolve())])
        result = _run_process(command, cwd=_PROJECT_ROOT)
        if result.returncode == WORKER_CLEANUP_INCOMPLETE_EXIT_CODE:
            raise _WorkerCleanupIncomplete("Export supervisor could not confirm descendant cleanup")
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
    except _WorkerCleanupIncomplete as exc:
        cleanup_failure = exc
        raise
    finally:
        try:
            temporary.cleanup()
        finally:
            if cleanup_failure is not None:
                # A result-directory error must not turn an unresolved writer
                # into an ordinary export rejection at the caller.
                raise cleanup_failure


def main(argv: Sequence[str] | None = None) -> int:
    completion = adopt_supervisor_completion()
    cleanup_state = _WorkerCleanupState()
    pending_error = None
    try:
        return _main(argv, cleanup_state=cleanup_state)
    except BaseException as exc:
        pending_error = exc
        raise
    finally:
        completion.finish(cleanup_state, pending_error=pending_error)


def _main(argv: Sequence[str] | None, *, cleanup_state: _WorkerCleanupState) -> int:
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
        try:
            return _supervise([
                sys.executable, "-m", "ensemble_prover.solved_export_process", "--worker", *arguments,
            ], cleanup_state=cleanup_state)
        except _WorkerCleanupIncomplete as exc:
            print(str(exc), file=sys.stderr, flush=True)
            return WORKER_CLEANUP_INCOMPLETE_EXIT_CODE
    result = _export_one(args.output_dir, args.lean_project_dir, args.solved_dir)
    args.result_path.write_text(json.dumps(result, allow_nan=False), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
