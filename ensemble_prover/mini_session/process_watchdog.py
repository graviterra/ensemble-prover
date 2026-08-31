"""Process supervision and opt-in hard deadlines for CLI search sessions.

Arbitrary asyncio code can suppress cancellation, spawn resistant child tasks,
and keep ``asyncio.run`` in shutdown forever.  The supported hard-deadline
surface is therefore a CLI worker process that owns its clients, Lean runner,
event loop, and proof state. Deadline regions publish small atomic lease
messages to the parent only when hard-operation escalation is explicitly
enabled. By default, local operation expiry remains recoverable and cannot
stop the complete run; process exit, channel loss, and external termination
remain supervised.

This is an internal support module used by ``ensemble_prover.mini_prover``.
Direct programmatic APIs accept live runtime objects and remain cooperative;
they cannot be moved across event-loop or process-spawn boundaries safely.
"""

from __future__ import annotations

import ctypes
import hashlib
import json
import math
import os
import re
import selectors
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple


_WATCHDOG_FD_ENV = "ENSEMBLE_MINI_WATCHDOG_FD"
_WATCHDOG_NONCE_ENV = "ENSEMBLE_MINI_WATCHDOG_NONCE"
_WATCHDOG_WORKER_ENV = "ENSEMBLE_MINI_WATCHDOG_WORKER"
_WATCHDOG_OVERALL_DEADLINE_ENV = "ENSEMBLE_MINI_WATCHDOG_OVERALL_DEADLINE"
_WATCHDOG_HARD_OPERATION_DEADLINES_ENV = (
    "ENSEMBLE_MINI_WATCHDOG_HARD_OPERATION_DEADLINES"
)
_WATCHDOG_SHUTDOWN_TIMEOUT_ENV = "ENSEMBLE_MINI_WATCHDOG_SHUTDOWN_TIMEOUT_S"
_WATCHDOG_STARTUP_TIMEOUT_ENV = "ENSEMBLE_MINI_WATCHDOG_STARTUP_TIMEOUT_S"
_WATCHDOG_DEFER_EXPORT_ENV = "ENSEMBLE_MINI_DEFER_SOLVED_EXPORT"
_STAGED_SOLUTION_RECEIPT_NAME = "pre_export_solved_receipt.json"
_STAGED_SOLUTION_SUMMARY_NAME = "pre_export_solved_summary.json"
_WRITE_LOCK = threading.Lock()
_MAX_MESSAGE_BYTES = 2048  # Below Linux PIPE_BUF: concurrent writes stay atomic.
_POLL_INTERVAL_S = 0.025
_COOPERATIVE_STOP_GRACE_S = 120.0
_DEADLINE_CLEANUP_GRACE_S = 0.40
_CHANNEL_EOF_REAP_GRACE_S = 0.50
_TERMINATE_GRACE_S = 0.25
_WATCHDOG_RECOVERY_MAX_BYTES = 16 * 1024 * 1024
_WATCHDOG_IDENTITY_SAMPLE_COUNT = 64
_STARTUP_TIMEOUT_S = 0.0
_DEFAULT_OVERALL_TIMEOUT_S = 0.0


def _reject_nonfinite_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant: {value}")


def _strict_json_loads(value: str | bytes) -> Any:
    parsed = json.loads(value, parse_constant=_reject_nonfinite_json_constant)

    def validate(item: Any) -> None:
        if isinstance(item, float):
            if not math.isfinite(item):
                raise ValueError("non-finite JSON number")
            return
        if isinstance(item, Mapping):
            for child in item.values():
                validate(child)
            return
        if isinstance(item, (list, tuple)):
            for child in item:
                validate(child)

    validate(parsed)
    return parsed


def _read_bounded_json_object(path: Path) -> Dict[str, Any]:
    descriptor = -1
    try:
        before = path.lstat()
        if not stat.S_ISREG(before.st_mode):
            return {}
        flags = os.O_RDONLY
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        descriptor = os.open(path, flags)
        opened_before = os.fstat(descriptor)
        size = int(opened_before.st_size)
        if (
            not stat.S_ISREG(opened_before.st_mode)
            or size <= 0
            or size > _WATCHDOG_RECOVERY_MAX_BYTES
        ):
            return {}
        chunks: list[bytes] = []
        remaining = size
        while remaining:
            chunk = os.read(descriptor, remaining)
            if not chunk:
                return {}
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            return {}
        opened_after = os.fstat(descriptor)
        after = path.lstat()
        identities = {
            (
                int(item.st_ino),
                int(item.st_mtime_ns),
                int(item.st_ctime_ns),
                int(item.st_size),
            )
            for item in (before, opened_before, opened_after, after)
        }
        if len(identities) != 1:
            return {}
        raw = b"".join(chunks)
        value = _strict_json_loads(raw)
    except Exception:
        return {}
    finally:
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass
    return dict(value) if isinstance(value, dict) else {}


def _stable_full_file_sha256(
    path: Path,
    *,
    expected_size: int | None = None,
) -> tuple[int, str] | None:
    """Hash one frozen artifact without imposing a proof-size ceiling."""

    descriptor = -1
    try:
        before = path.lstat()
        if not stat.S_ISREG(before.st_mode):
            return None
        flags = os.O_RDONLY
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        descriptor = os.open(path, flags)
        opened_before = os.fstat(descriptor)
        if not stat.S_ISREG(opened_before.st_mode):
            return None
        size = int(opened_before.st_size)
        if (
            expected_size is not None
            and size != int(expected_size)
        ):
            return None
        digest = hashlib.sha256()
        remaining = size
        while remaining:
            chunk = os.read(descriptor, min(1024 * 1024, remaining))
            if not chunk:
                return None
            digest.update(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            return None
        opened_after = os.fstat(descriptor)
        after = path.lstat()
    except OSError:
        return None
    finally:
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass
    identities = {
        (
            int(item.st_ino),
            int(item.st_mtime_ns),
            int(item.st_ctime_ns),
            int(item.st_size),
        )
        for item in (before, opened_before, opened_after, after)
    }
    if len(identities) != 1:
        return None
    return int(after.st_size), digest.hexdigest()


def _stable_full_json_object_with_sha256(
    path: Path,
    *,
    expected_size: int,
) -> tuple[int, str, Dict[str, Any]] | None:
    """Read, hash, and parse one immutable regular JSON artifact.

    The staged proof may legitimately exceed the bounded watchdog-recovery
    reader.  Reading and hashing through the same no-follow descriptor binds
    the validated fields to the exact bytes named by the receipt and closes
    the path-swap gap between a separate hash and parse.
    """

    descriptor = -1
    try:
        before = path.lstat()
        if not stat.S_ISREG(before.st_mode):
            return None
        flags = os.O_RDONLY
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        descriptor = os.open(path, flags)
        opened_before = os.fstat(descriptor)
        size = int(opened_before.st_size)
        if (
            not stat.S_ISREG(opened_before.st_mode)
            or size != int(expected_size)
        ):
            return None
        digest = hashlib.sha256()
        chunks: list[bytes] = []
        remaining = size
        while remaining:
            chunk = os.read(descriptor, min(1024 * 1024, remaining))
            if not chunk:
                return None
            chunks.append(chunk)
            digest.update(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            return None
        opened_after = os.fstat(descriptor)
        after = path.lstat()
        identities = {
            (
                int(item.st_ino),
                int(item.st_mtime_ns),
                int(item.st_ctime_ns),
                int(item.st_size),
            )
            for item in (before, opened_before, opened_after, after)
        }
        if len(identities) != 1:
            return None
        value = _strict_json_loads(b"".join(chunks))
        if not isinstance(value, dict):
            return None
        return int(after.st_size), digest.hexdigest(), dict(value)
    except Exception:
        return None
    finally:
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass


_SHUTDOWN_TIMEOUT_S = 120.0
# Private supervisor/parent receipt: the worker finalized the mathematical
# root and durably staged its proof, but a cancellation-resistant loser kept
# ``asyncio.run`` shutdown alive until the dedicated shutdown lease expired.
# The supervisor has already killed the complete worker tree before returning
# this code.  The CLI parent may therefore run the ordinary independent Lean
# export verification against the frozen staged summary.
VERIFY_STAGED_SOLUTION_EXIT_CODE = 76
_PR_SET_CHILD_SUBREAPER = 36
_PR_GET_CHILD_SUBREAPER = 37


class ProcessWatchdogProtocolError(RuntimeError):
    """The isolated worker can no longer prove that it is supervised."""


def is_watchdog_worker() -> bool:
    """Return true only for a worker with a complete inherited channel."""

    if os.environ.get(_WATCHDOG_WORKER_ENV, "") != "1":
        return False
    return bool(
        os.environ.get(_WATCHDOG_FD_ENV, "").strip()
        and os.environ.get(_WATCHDOG_NONCE_ENV, "").strip()
    )


def worker_overall_deadline() -> float:
    try:
        return float(os.environ.get(_WATCHDOG_OVERALL_DEADLINE_ENV, "") or 0.0)
    except (TypeError, ValueError):
        return 0.0


def worker_shutdown_timeout_s() -> float:
    """Return the explicitly configured event-loop shutdown bound, or zero."""

    try:
        return max(
            0.0,
            float(
                os.environ.get(_WATCHDOG_SHUTDOWN_TIMEOUT_ENV, "")
                or _SHUTDOWN_TIMEOUT_S
            ),
        )
    except (TypeError, ValueError):
        return float(_SHUTDOWN_TIMEOUT_S)


def hard_operation_deadlines_enabled() -> bool:
    """Whether local operation leases may terminate the complete worker.

    Local Lean/provider/tool timeouts remain active independently.  This flag
    controls only the parent supervisor's stronger escalation from one late
    operation to destruction of the whole resumable proof-search process.
    """

    return os.environ.get(_WATCHDOG_HARD_OPERATION_DEADLINES_ENV, "") == "1"


def worker_startup_timeout_s() -> float:
    """Return the supervisor's startup-sized bound for restore/merge work."""

    raw = os.environ.get(_WATCHDOG_STARTUP_TIMEOUT_ENV, "").strip()
    try:
        value = float(raw) if raw else _STARTUP_TIMEOUT_S
    except (TypeError, ValueError):
        return _STARTUP_TIMEOUT_S
    return value if math.isfinite(value) and value >= 0.0 else _STARTUP_TIMEOUT_S


def signal_worker_ready() -> None:
    """Prove that isolated-worker startup completed and search may begin."""

    if _worker_channel() is not None:
        _send_message(
            {
                "event": "ready",
                "token": f"ready-{os.getpid()}",
                "label": "mini_session_worker_ready",
            }
        )


def _worker_channel() -> Optional[Tuple[int, str]]:
    raw_fd = os.environ.get(_WATCHDOG_FD_ENV, "").strip()
    nonce = os.environ.get(_WATCHDOG_NONCE_ENV, "").strip()
    if not raw_fd and not nonce:
        if os.environ.get(_WATCHDOG_WORKER_ENV, "") == "1":
            raise ProcessWatchdogProtocolError("watchdog worker channel is missing")
        return None
    try:
        fd = int(raw_fd)
    except (TypeError, ValueError) as exc:
        raise ProcessWatchdogProtocolError("watchdog worker fd is invalid") from exc
    if fd < 0 or not nonce:
        raise ProcessWatchdogProtocolError("watchdog worker channel is incomplete")
    return fd, nonce


def _send_message(payload: Dict[str, Any]) -> bool:
    channel = _worker_channel()
    if channel is None:
        return False
    fd, nonce = channel
    message = dict(payload)
    message["nonce"] = nonce
    message["sent_monotonic"] = time.monotonic()
    data = (json.dumps(message, sort_keys=True, separators=(",", ":")) + "\n").encode(
        "utf-8"
    )
    if len(data) > _MAX_MESSAGE_BYTES:
        raise ProcessWatchdogProtocolError("watchdog message exceeds atomic frame cap")
    try:
        with _WRITE_LOCK:
            written = os.write(fd, data)
    except OSError as exc:
        raise ProcessWatchdogProtocolError("watchdog channel write failed") from exc
    if written != len(data):
        raise ProcessWatchdogProtocolError("watchdog channel write was partial")
    return True


@dataclass
class ProcessDeadlineLease:
    """One independently tracked deadline region in the isolated worker."""

    token: str
    deadline_monotonic: float
    label: str
    enabled: bool
    _closed: bool = False
    _abandoned: bool = False

    def abandon(self, reason: str) -> None:
        """Keep the lease armed until the parent kills or the worker exits."""

        if not self.enabled or self._closed or self._abandoned:
            return
        self._abandoned = True
        _send_message(
            {
                "event": "abandon",
                "token": self.token,
                "deadline": self.deadline_monotonic,
                "label": self.label,
                "reason": str(reason or "deadline_region_abandoned")[:500],
            }
        )

    def close(self) -> None:
        """Release a settled region; an abandoned lease is intentionally sticky."""

        if not self.enabled or self._closed or self._abandoned:
            return
        _send_message(
            {
                "event": "end",
                "token": self.token,
                "deadline": self.deadline_monotonic,
                "label": self.label,
            }
        )
        self._closed = True

    def settle_timeout(self) -> None:
        """Release after the awaited operation cooperatively times out.

        Unlike a successful ``end``, this may arrive during cleanup grace:
        the operation produced no accepted result and has already settled.
        """

        if not self.enabled or self._closed or self._abandoned:
            return
        _send_message(
            {
                "event": "timeout",
                "token": self.token,
                "deadline": self.deadline_monotonic,
                "label": self.label,
            }
        )
        self._closed = True

    def close_at_transaction_commit(self) -> bool:
        """Release at a transaction's already-passed deadline gate."""

        if not self.enabled or self._closed or self._abandoned:
            return not self.enabled or self._closed
        decision_monotonic = time.monotonic()
        if decision_monotonic > self.deadline_monotonic:
            return False
        _send_message(
            {
                "event": "commit",
                "token": self.token,
                "deadline": self.deadline_monotonic,
                "label": self.label,
                "decision_monotonic": decision_monotonic,
            }
        )
        self._closed = True
        return True


def begin_process_deadline(
    *,
    deadline_monotonic: float,
    label: str,
    supervisor_enforced: bool = False,
) -> ProcessDeadlineLease:
    """Announce a deadline before entering an untrusted async region."""

    deadline = float(deadline_monotonic or 0.0)
    channel = _worker_channel()
    enabled = bool(
        channel is not None
        and deadline > 0.0
        and (hard_operation_deadlines_enabled() or bool(supervisor_enforced))
    )
    lease = ProcessDeadlineLease(
        token=uuid.uuid4().hex,
        deadline_monotonic=deadline,
        label=str(label or "mini_session_deadline")[:200],
        enabled=enabled,
    )
    if enabled:
        _send_message(
            {
                "event": "start",
                "token": lease.token,
                "deadline": deadline,
                "label": lease.label,
            }
        )
    return lease


def _enable_child_subreaper() -> int:
    """Adopt orphaned worker grandchildren so they remain killable/reapable."""

    try:
        libc = ctypes.CDLL(None, use_errno=True)
        prior = ctypes.c_int(0)
        if libc.prctl(
            _PR_GET_CHILD_SUBREAPER,
            ctypes.byref(prior),
            0,
            0,
            0,
        ) != 0:
            raise OSError(ctypes.get_errno(), "prctl(PR_GET_CHILD_SUBREAPER) failed")
        if libc.prctl(_PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "prctl(PR_SET_CHILD_SUBREAPER) failed")
        return int(prior.value)
    except Exception as exc:
        raise RuntimeError("Mini hard supervision requires Linux subreaper support") from exc


def _restore_child_subreaper(prior: int) -> None:
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        if libc.prctl(_PR_SET_CHILD_SUBREAPER, int(bool(prior)), 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "prctl(PR_SET_CHILD_SUBREAPER) failed")
    except Exception:
        # Worker cleanup and the returned status remain authoritative.  Do not
        # mask them if the embedding process changes privilege mid-call.
        pass


def _proc_identity(pid: int) -> Optional[Tuple[int, int]]:
    """Return ``(pid, starttime)`` so PID reuse cannot redirect a signal."""

    try:
        raw = Path(f"/proc/{int(pid)}/stat").read_text(encoding="utf-8")
        tail = raw[raw.rfind(")") + 2 :].split()
        return int(pid), int(tail[19])
    except (OSError, ValueError, IndexError):
        return None


def _proc_child_pids(pid: int) -> Tuple[int, ...]:
    """Return one process's kernel-maintained direct-child list.

    The supervisor is a private subreaper, so every owned process is either a
    descendant of the worker or is reparented directly to the supervisor.
    Linux records parenthood per thread, so inspect each task's ``children``
    file; this remains bounded by the owned process's thread count and avoids
    scanning every process on the host.
    """

    try:
        task_entries = tuple(Path(f"/proc/{int(pid)}/task").iterdir())
    except OSError:
        return ()
    children: set[int] = set()
    for task_entry in task_entries:
        if not task_entry.name.isdigit():
            continue
        try:
            raw = Path(task_entry, "children").read_text(encoding="utf-8")
        except OSError:
            continue
        for value in raw.split():
            try:
                child = int(value)
            except ValueError:
                continue
            if child > 0:
                children.add(child)
    return tuple(sorted(children))


def _refresh_known_tree(
    known: Dict[int, int],
    *,
    ownership_nonce: str,
) -> None:
    del ownership_nonce  # lineage is authoritative inside the private subreaper

    # This function is called before every 25 ms deadline poll.  Its former
    # implementation scanned all of /proc and opened every process's environ.
    # On process-dense hosts one scan took minutes, so the supervisor could not
    # read a queued lease frame or enforce a 60-second deadline for hours.  The
    # private supervisor has exactly one intentional child (the worker), and
    # PR_SET_CHILD_SUBREAPER reparents orphaned worker descendants back to it.
    # A bounded traversal of kernel child lists is therefore both complete and
    # responsive, including for env-scrubbed/new-session double forks.
    supervisor_pid = os.getpid()
    pending = [
        supervisor_pid,
        *(
            pid
            for pid, started in tuple(known.items())
            if _identity_alive(pid, started)
        ),
    ]
    visited: set[int] = set()
    while pending:
        parent = pending.pop()
        if parent in visited:
            continue
        visited.add(parent)
        for child in _proc_child_pids(parent):
            identity = _proc_identity(child)
            if identity is None:
                continue
            recorded_start = known.get(child)
            if recorded_start != identity[1]:
                known[child] = identity[1]
            if child not in visited:
                pending.append(child)


def _identity_alive(pid: int, starttime: int) -> bool:
    return _proc_identity(pid) == (pid, starttime)


def _signal_known(known: Dict[int, int], sig: signal.Signals) -> None:
    for pid, started in list(known.items()):
        if not _identity_alive(pid, started):
            continue
        try:
            os.kill(pid, sig)
        except ProcessLookupError:
            pass
        except OSError:
            pass


def _reap_known_children_nonblocking(
    known: Dict[int, int],
    *,
    root_pid: int,
) -> None:
    """Reap only adopted worker descendants; ``Popen`` owns the root status."""

    for pid in list(known):
        if pid == root_pid:
            continue
        try:
            os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            continue
        except OSError:
            continue


def _terminate_worker_tree(
    proc: subprocess.Popen[Any],
    known: Dict[int, int],
    *,
    ownership_nonce: str,
) -> None:
    """Sweep the worker tree without allowing repeat signals to interrupt it."""

    handled_signals = {signal.SIGTERM, signal.SIGINT, signal.SIGHUP}
    prior_signal_mask = signal.pthread_sigmask(signal.SIG_BLOCK, handled_signals)
    try:
        _terminate_worker_tree_blocked(
            proc,
            known,
            ownership_nonce=ownership_nonce,
        )
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, prior_signal_mask)


def _terminate_worker_tree_blocked(
    proc: subprocess.Popen[Any],
    known: Dict[int, int],
    *,
    ownership_nonce: str,
) -> None:
    """Quiesce, discover, kill, and reap the complete private worker tree."""

    root_identity = _proc_identity(proc.pid)
    if root_identity is not None:
        known.setdefault(*root_identity)
    # Never resume the tree for a catchable TERM: an adversarial termination
    # handler can fork new session/env-scrubbed children throughout grace.
    # SIGSTOP is uncatchable, so repeated stop/discovery reaches a quiescent
    # ownership closure before SIGKILL.
    stable_rounds = 0
    prior_pids: set[int] = set()
    for _ in range(64):
        _refresh_known_tree(known, ownership_nonce=ownership_nonce)
        _signal_known(known, signal.SIGSTOP)
        time.sleep(0.005)
        _refresh_known_tree(known, ownership_nonce=ownership_nonce)
        current_pids = {
            pid for pid, started in known.items() if _identity_alive(pid, started)
        }
        if current_pids == prior_pids:
            stable_rounds += 1
        else:
            stable_rounds = 0
            prior_pids = current_pids
        if stable_rounds >= 3:
            break
    _signal_known(known, signal.SIGKILL)

    # Killing ancestors reparents their children to this private subreaper.
    # Continue stop/discover/kill until the owned set is empty so a child that
    # crossed the last pre-kill scan cannot escape.
    kill_expires = time.monotonic() + max(1.0, _TERMINATE_GRACE_S * 4.0)
    while time.monotonic() < kill_expires:
        _refresh_known_tree(known, ownership_nonce=ownership_nonce)
        _signal_known(known, signal.SIGSTOP)
        _refresh_known_tree(known, ownership_nonce=ownership_nonce)
        _signal_known(known, signal.SIGKILL)
        _reap_known_children_nonblocking(known, root_pid=proc.pid)
        proc.poll()  # Reap the Popen-owned root so its zombie is not "alive".
        if not any(_identity_alive(pid, started) for pid, started in known.items()):
            break
        time.sleep(0.005)
    try:
        proc.wait(timeout=_TERMINATE_GRACE_S)
    except (subprocess.TimeoutExpired, ChildProcessError):
        pass
    _reap_known_children_nonblocking(known, root_pid=proc.pid)


# token -> (deadline, label, abandoned_reason)
_ActiveLease = Tuple[float, str, str]


def _consume_messages(
    buffer: bytearray,
    active: Dict[str, _ActiveLease],
    *,
    expected_nonce: str,
    ready_deadline: float,
) -> Tuple[Optional[str], bool]:
    """Apply complete frames; return ``(violation, saw_ready)``.

    Lease traffic can legitimately occur during initialization. It must not
    satisfy the independent startup handshake: only an explicit READY frame
    proves that all required runtime resources were initialized.
    """

    saw_ready = False
    while True:
        newline = buffer.find(b"\n")
        if newline < 0:
            if len(buffer) > _MAX_MESSAGE_BYTES:
                return "watchdog_message_too_large", saw_ready
            return None, saw_ready
        raw = bytes(buffer[:newline])
        del buffer[: newline + 1]
        if len(raw) > _MAX_MESSAGE_BYTES:
            return "watchdog_message_too_large", saw_ready
        try:
            message = _strict_json_loads(raw.decode("utf-8"))
        except (
            UnicodeDecodeError,
            json.JSONDecodeError,
            RecursionError,
            ValueError,
            OverflowError,
        ):
            return "watchdog_malformed_message", saw_ready
        if not isinstance(message, dict) or message.get("nonce") != expected_nonce:
            return "watchdog_invalid_nonce_or_frame", saw_ready
        event = str(message.get("event") or "")
        token = str(message.get("token") or "")
        label = str(message.get("label") or "mini_session_deadline")[:200]
        try:
            sent = float(message.get("sent_monotonic") or 0.0)
        except (TypeError, ValueError):
            return "watchdog_invalid_send_time", saw_ready
        if not token or not math.isfinite(sent) or sent <= 0.0:
            return "watchdog_missing_token_or_send_time", saw_ready
        if event == "start":
            try:
                deadline = float(message.get("deadline") or 0.0)
            except (TypeError, ValueError):
                return "watchdog_invalid_deadline", saw_ready
            if not math.isfinite(deadline) or deadline <= 0.0 or token in active:
                return "watchdog_invalid_start", saw_ready
            active[token] = (deadline, label, "")
        elif event == "ready":
            # A standalone handshake has no lease state.
            if ready_deadline > 0.0 and sent > ready_deadline:
                return "watchdog_worker_startup_timeout:late_ready", saw_ready
            saw_ready = True
            continue
        elif event == "end":
            entry = active.get(token)
            if entry is None:
                return "watchdog_unknown_end", saw_ready
            # Cleanup grace lets a cooperative timeout report abandonment and
            # unwind.  It is never extra execution/publication budget.
            if sent > entry[0]:
                return f"watchdog_late_end:{entry[1]}", saw_ready
            del active[token]
        elif event == "abandon":
            entry = active.get(token)
            if entry is None:
                return "watchdog_unknown_abandon", saw_ready
            active[token] = (
                min(entry[0], sent),
                entry[1],
                str(message.get("reason") or "deadline_region_abandoned")[:500],
            )
        elif event == "timeout":
            entry = active.get(token)
            if entry is None:
                return "watchdog_unknown_timeout", saw_ready
            if sent > entry[0] + _DEADLINE_CLEANUP_GRACE_S:
                return f"watchdog_late_timeout_settlement:{entry[1]}", saw_ready
            del active[token]
        elif event == "commit":
            entry = active.get(token)
            if entry is None:
                return "watchdog_unknown_commit", saw_ready
            try:
                decision = float(message.get("decision_monotonic") or 0.0)
            except (TypeError, ValueError):
                return "watchdog_invalid_transaction_commit", saw_ready
            # Only DeadlineMutationTransaction emits this immediately after
            # its final predicate.  The decision must be timely; grace covers
            # scheduling/frame delivery after that decision.
            if (
                not math.isfinite(decision)
                or decision <= 0.0
                or decision > entry[0]
                or sent > entry[0] + _DEADLINE_CLEANUP_GRACE_S
            ):
                return f"watchdog_late_transaction_commit:{entry[1]}", saw_ready
            del active[token]
        else:
            return "watchdog_unknown_event", saw_ready


def _violation_failure_class(violation: str) -> Tuple[str, bool]:
    detail = str(violation or "watchdog_failure")
    if detail == f"watchdog_supervisor_signal:{int(signal.SIGINT)}":
        # SIGINT is the operator/user cancellation convention. If the worker
        # cannot publish its own terminal summary before the supervisor sweep,
        # the fallback must preserve that semantic classification.
        return "user_interrupted", False
    if detail.startswith(
        (
            "watchdog_deadline_expired:",
            "watchdog_late_end:",
            "watchdog_late_timeout_settlement:",
            "watchdog_late_transaction_commit:",
            "watchdog_worker_overall_timeout",
            "watchdog_worker_startup_timeout",
            "watchdog_cooperative_stop_timeout:",
        )
    ):
        return "mini_session_worker_hard_timeout", True
    if detail.startswith(
        (
            "watchdog_worker_exited_with_active_lease:",
            "watchdog_worker_exit_nonzero:",
            "watchdog_supervisor_signal:",
            "watchdog_supervisor_parent_lost",
        )
    ):
        return "mini_session_worker_process_failure", False
    return "mini_session_worker_protocol_failure", False


def _recent_jsonl_lines(path: Path) -> Tuple[list[str], bool, int]:
    """Read only a fixed-size suffix, starting on a complete JSONL line."""

    size = int(path.stat().st_size)
    start = max(0, size - _WATCHDOG_RECOVERY_MAX_BYTES)
    with path.open("rb") as handle:
        handle.seek(max(0, start - 1))
        payload = handle.read(
            _WATCHDOG_RECOVERY_MAX_BYTES + (1 if start > 0 else 0)
        )
    if start > 0:
        preceding = payload[:1]
        payload = payload[1:]
        if preceding != b"\n":
            newline = payload.find(b"\n")
            payload = payload[newline + 1 :] if newline >= 0 else b""
    return (
        payload.decode("utf-8", errors="replace").splitlines(),
        start > 0,
        len(payload),
    )


def _watchdog_turns_snapshot_identity(path: Path) -> Tuple[int, int, int]:
    """Capture a turns-file race identity without reading its payload."""

    stat = path.stat()
    return int(stat.st_ino), int(stat.st_mtime_ns), int(stat.st_size)


def _argv_option(argv: Sequence[str], option: str, default: str = "") -> str:
    prefix = option + "="
    for index, item in enumerate(argv):
        text = str(item or "")
        if text.startswith(prefix):
            return text[len(prefix) :]
        if text == option and index + 1 < len(argv):
            return str(argv[index + 1] or "")
    return default


def _recover_watchdog_turn_metadata(
    output_dir: Path,
    *,
    worker_argv: Sequence[str] = (),
) -> Dict[str, Any]:
    """Recover bounded terminal diagnostics when the worker wrote no summary."""

    turns_path = output_dir / "turns.jsonl"
    if not turns_path.is_file():
        return {}
    last_turn: Dict[str, Any] = {}
    recovered_usage: Dict[str, Any] = {}
    recovered_usage_positions: Dict[str, int] = {}
    authoritative_usage: Dict[str, Any] = {}
    authoritative_usage_turn_index = 0
    legacy_observed_usage_cost = 0.0
    legacy_usage_events_seen = 0
    legacy_usage_turn_index = 0
    legacy_accounting_turn_index = 0
    token_keys = (
        "input_tokens",
        "output_tokens",
        "cached_input_tokens",
        "cache_write_tokens",
        "prompt_cache_miss_tokens",
        "reasoning_output_tokens",
    )
    recovered_token_totals = {key: 0 for key in token_keys}
    recovered_role_token_totals: Dict[str, Dict[str, int]] = {}
    recovered_usage_events = 0
    recovered_usage_missing_events = 0
    recovered_usage_counter_contributions: list[Dict[str, int]] = []
    recovered_token_turn_index = 0
    records_scanned = 0
    invalid_records = 0
    invalid_usage_counters = 0
    invalid_turn_indices = 0
    first_valid_turn_index = 0
    last_valid_turn_index = 0
    last_invalid_record_position = 0
    last_cumulative_accounting_position = 0
    authoritative_usage_position = 0
    scan_truncated = False
    bytes_scanned = 0
    try:
        lines, scan_truncated, bytes_scanned = _recent_jsonl_lines(turns_path)
        for line_position, line in enumerate(lines, start=1):
            if not line.strip():
                continue
            try:
                record = _strict_json_loads(line)
            except (
                json.JSONDecodeError,
                RecursionError,
                ValueError,
                OverflowError,
            ):
                invalid_records += 1
                last_invalid_record_position = line_position
                continue
            if not isinstance(record, dict):
                invalid_records += 1
                last_invalid_record_position = line_position
                continue
            records_scanned += 1
            raw_turn_index = record.get("turn_index")
            valid_turn_index = bool(
                isinstance(raw_turn_index, int)
                and not isinstance(raw_turn_index, bool)
                and raw_turn_index > 0
                and (
                    last_valid_turn_index == 0
                    or raw_turn_index == last_valid_turn_index + 1
                )
            )
            if valid_turn_index:
                if first_valid_turn_index == 0:
                    first_valid_turn_index = int(raw_turn_index)
                last_valid_turn_index = int(raw_turn_index)
            else:
                invalid_turn_indices += 1
            last_turn = record
            phase = str(record.get("phase") or "")
            verdict = str(record.get("verdict") or "")
            usage_counter_event = phase == "llm_usage" and verdict in {
                "llm_usage_recorded",
                "llm_usage_missing",
                "llm_late_dispatch_missing_usage",
                "llm_late_pre_generation_rejection_recorded",
            }
            token_event = phase == "llm_usage" and verdict in {
                "llm_usage_recorded",
                "llm_usage_missing",
            }
            turn_index_value = record.get("turn_index")
            event_turn_index = (
                int(turn_index_value)
                if isinstance(turn_index_value, int)
                and not isinstance(turn_index_value, bool)
                and turn_index_value > 0
                else 0
            )
            usage_contribution: Optional[Dict[str, int]] = None
            if usage_counter_event:
                recovered_usage_events += 1
                if event_turn_index > 0:
                    usage_contribution = {
                        "turn_index": event_turn_index,
                        "llm_usage_events": 1,
                        "llm_usage_missing_events": 0,
                    }
                    recovered_usage_counter_contributions.append(
                        usage_contribution
                    )
                if bool(record.get("usage_missing")) or verdict in {
                    "llm_usage_missing",
                    "llm_late_dispatch_missing_usage",
                }:
                    recovered_usage_missing_events += 1
                    if usage_contribution is not None:
                        usage_contribution["llm_usage_missing_events"] = 1
            if token_event:
                recovered_token_turn_index = max(
                    recovered_token_turn_index,
                    event_turn_index,
                )
                role = str(record.get("role") or "").strip()
                role = {"prove": "prover", "refine": "refiner"}.get(
                    role,
                    role,
                )
                safe_role = (
                    role
                    if role
                    and len(role) <= 64
                    and all(char.isalnum() or char == "_" for char in role)
                    else ""
                )
                role_totals = (
                    recovered_role_token_totals.setdefault(
                        safe_role,
                        {key: 0 for key in token_keys},
                    )
                    if safe_role
                    else None
                )
                for key in token_keys:
                    value = record.get(key, 0)
                    if (
                        not isinstance(value, (int, float))
                        or isinstance(value, bool)
                        or not math.isfinite(float(value))
                        or float(value) < 0.0
                        or not float(value).is_integer()
                    ):
                        if key in record:
                            invalid_usage_counters += 1
                        continue
                    decoded = int(value)
                    recovered_token_totals[key] += decoded
                    if role_totals is not None:
                        role_totals[key] += decoded
                    if usage_contribution is not None:
                        usage_contribution[key] = decoded
                        if safe_role:
                            usage_contribution[f"{safe_role}_{key}"] = decoded
                event_cost = record.get("cost_usd")
                if (
                    isinstance(event_cost, (int, float))
                    and not isinstance(event_cost, bool)
                    and math.isfinite(float(event_cost))
                    and float(event_cost) >= 0.0
                ):
                    legacy_observed_usage_cost += float(event_cost)
                    legacy_usage_events_seen += 1
                    event_turn_index = record.get("turn_index")
                    if (
                        isinstance(event_turn_index, int)
                        and not isinstance(event_turn_index, bool)
                        and event_turn_index > 0
                    ):
                        legacy_usage_turn_index = event_turn_index
            numeric_usage_keys = (
                "accounted_cost_usd",
                "committed_cost_usd",
                "llm_budget_accounted_cost_usd",
                "llm_budget_committed_cost_usd",
                "llm_observed_usage_cost_usd",
                "llm_conservative_unknown_exposure_usd",
                "cost_usd",
                "estimated_cost_usd",
                "reservation_cost_usd",
            )
            boolean_usage_keys = (
                "cost_accounting_incomplete",
                "llm_cost_accounting_incomplete",
                "llm_budget_accounted_cost_is_conservative_upper_bound",
            )
            text_usage_keys = (
                "usage_status",
                "missing_usage_reason",
                "model",
                "call_kind",
            )
            if any(
                key in record
                for key in (
                    *numeric_usage_keys,
                    *boolean_usage_keys,
                    *text_usage_keys,
                )
            ):
                for key in numeric_usage_keys:
                    value = record.get(key)
                    if (
                        isinstance(value, (int, float))
                        and not isinstance(value, bool)
                        and math.isfinite(float(value))
                        and float(value) >= 0.0
                    ):
                        recovered_usage[key] = float(value)
                        recovered_usage_positions[key] = line_position
                        if key in {
                            "accounted_cost_usd",
                            "llm_budget_accounted_cost_usd",
                        }:
                            last_cumulative_accounting_position = line_position
                        if key == "llm_budget_accounted_cost_usd":
                            event_turn_index = record.get("turn_index")
                            if (
                                isinstance(event_turn_index, int)
                                and not isinstance(event_turn_index, bool)
                                and event_turn_index > 0
                            ):
                                legacy_accounting_turn_index = event_turn_index
                for key in boolean_usage_keys:
                    value = record.get(key)
                    if isinstance(value, bool):
                        recovered_usage[key] = value
                        recovered_usage_positions[key] = line_position
                for key in text_usage_keys:
                    value = record.get(key)
                    if isinstance(value, str) and value.strip():
                        recovered_usage[key] = value
                        recovered_usage_positions[key] = line_position
                authority_numeric_keys = (
                    "llm_observed_usage_cost_usd",
                    "llm_conservative_unknown_exposure_usd",
                    "llm_budget_accounted_cost_usd",
                    "llm_budget_committed_cost_usd",
                )
                authority_numeric = {
                    key: float(record[key])
                    for key in authority_numeric_keys
                    if isinstance(record.get(key), (int, float))
                    and not isinstance(record.get(key), bool)
                    and math.isfinite(float(record[key]))
                    and float(record[key]) >= 0.0
                }
                authority_booleans = {
                    key: record[key]
                    for key in boolean_usage_keys
                    if isinstance(record.get(key), bool)
                }
                if (
                    len(authority_numeric) == len(authority_numeric_keys)
                    and len(authority_booleans) == len(boolean_usage_keys)
                ):
                    observed = authority_numeric["llm_observed_usage_cost_usd"]
                    unknown = authority_numeric[
                        "llm_conservative_unknown_exposure_usd"
                    ]
                    accounted = authority_numeric[
                        "llm_budget_accounted_cost_usd"
                    ]
                    committed = authority_numeric[
                        "llm_budget_committed_cost_usd"
                    ]
                    incomplete = bool(unknown > 1e-12)
                    coherent = bool(
                        math.isclose(
                            accounted,
                            observed + unknown,
                            rel_tol=1e-9,
                            abs_tol=1e-9,
                        )
                        and committed + 1e-9 >= accounted
                        and all(
                            bool(authority_booleans[key]) == incomplete
                            for key in boolean_usage_keys
                        )
                    )
                    if coherent:
                        # Treat the cumulative authority fields as one atomic
                        # snapshot. A later partial/legacy record must not mix
                        # a new accounted total with stale observed/unknown
                        # components from this receipt.
                        authoritative_usage = {
                            **authority_numeric,
                            **authority_booleans,
                        }
                        authoritative_usage_position = line_position
                        turn_index = record.get("turn_index")
                        if (
                            isinstance(turn_index, int)
                            and not isinstance(turn_index, bool)
                            and turn_index > 0
                        ):
                            authoritative_usage_turn_index = turn_index
    except OSError:
        return {}

    def selected(record: Mapping[str, Any], keys: Sequence[str]) -> Dict[str, Any]:
        return {
            key: record.get(key)
            for key in keys
            if key in record
        }

    contribution_trace_valid = bool(
        invalid_records == 0
        and invalid_usage_counters == 0
        and invalid_turn_indices == 0
    )
    complete_usage_trace = bool(
        not scan_truncated
        and contribution_trace_valid
        and first_valid_turn_index == 1
    )
    recovered: Dict[str, Any] = {
        "watchdog_recovered_records_scanned": records_scanned,
        "watchdog_recovery_scan_truncated": scan_truncated,
        "watchdog_recovery_invalid_records": invalid_records,
        "watchdog_recovery_invalid_usage_counters": invalid_usage_counters,
        "watchdog_recovery_invalid_turn_indices": invalid_turn_indices,
        "watchdog_recovery_usage_complete": complete_usage_trace,
        "watchdog_recovery_first_turn_index": first_valid_turn_index,
        "watchdog_recovery_last_turn_index": last_valid_turn_index,
        "watchdog_recovery_bytes_scanned": bytes_scanned,
        "watchdog_recovered_last_turn": selected(
            last_turn,
            (
                "turn_index",
                "ts",
                "elapsed_s",
                "phase",
                "verdict",
                "action_id",
                "action_dispatch_id",
                "session_scope",
            ),
        ),
    }
    if complete_usage_trace and recovered_usage_events > 0:
        recovered.update(recovered_token_totals)
        recovered["llm_usage_events"] = recovered_usage_events
        recovered["llm_usage_missing_events"] = recovered_usage_missing_events
        for role, totals in recovered_role_token_totals.items():
            for key, value in totals.items():
                recovered[f"{role}_{key}"] = value
        recovered["watchdog_recovered_token_turn_index"] = (
            recovered_token_turn_index
        )
    if contribution_trace_valid and recovered_usage_events > 0:
        recovered["_watchdog_recovered_usage_counter_contributions"] = list(
            recovered_usage_counter_contributions
        )
    if (
        not authoritative_usage
        and complete_usage_trace
        and legacy_usage_events_seen > 0
    ):
        legacy_accounted = recovered_usage.get(
            "llm_budget_accounted_cost_usd"
        )
        legacy_committed = recovered_usage.get(
            "llm_budget_committed_cost_usd"
        )
        if (
            isinstance(legacy_accounted, (int, float))
            and not isinstance(legacy_accounted, bool)
            and math.isfinite(float(legacy_accounted))
            and float(legacy_accounted) + 1e-9 >= legacy_observed_usage_cost
            and isinstance(legacy_committed, (int, float))
            and not isinstance(legacy_committed, bool)
            and math.isfinite(float(legacy_committed))
            and float(legacy_committed) + 1e-9 >= float(legacy_accounted)
        ):
            # Pre-authority traces still contain additive per-call exact cost
            # plus a cumulative accounted upper bound. A complete trace can
            # therefore recover the two components without relabeling the
            # upper bound as observed spend. Never do this on a truncated
            # suffix, where the missing prefix would undercount exact cost.
            legacy_unknown = max(
                0.0,
                float(legacy_accounted) - legacy_observed_usage_cost,
            )
            legacy_incomplete = bool(legacy_unknown > 1e-12)
            authoritative_usage = {
                "llm_observed_usage_cost_usd": legacy_observed_usage_cost,
                "llm_conservative_unknown_exposure_usd": legacy_unknown,
                "llm_budget_accounted_cost_usd": float(legacy_accounted),
                "llm_budget_committed_cost_usd": float(legacy_committed),
                "cost_accounting_incomplete": legacy_incomplete,
                "llm_cost_accounting_incomplete": legacy_incomplete,
                "llm_budget_accounted_cost_is_conservative_upper_bound": (
                    legacy_incomplete
                ),
            }
            # The final legacy accounted total may come from a later
            # recovery/reversal event rather than the last ordinary settle.
            # Its turn is the crash-cut authority for summary precedence.
            authoritative_usage_turn_index = (
                legacy_accounting_turn_index or legacy_usage_turn_index
            )
    accounting_source: Dict[str, Any] = {}
    atomic_authority_selected = False
    if complete_usage_trace:
        accounting_source = {**recovered_usage, **authoritative_usage}
        atomic_authority_selected = bool(authoritative_usage)
    elif (
        invalid_usage_counters == 0
        and invalid_turn_indices == 0
        and last_cumulative_accounting_position > last_invalid_record_position
    ):
        incomplete_accounting_keys = (
            "accounted_cost_usd",
            "committed_cost_usd",
            "llm_budget_accounted_cost_usd",
            "llm_budget_committed_cost_usd",
            "cost_accounting_incomplete",
            "llm_cost_accounting_incomplete",
            "llm_budget_accounted_cost_is_conservative_upper_bound",
            "usage_status",
            "missing_usage_reason",
            "model",
            "call_kind",
        )
        accounting_source = {
            key: recovered_usage[key]
            for key in incomplete_accounting_keys
            if key in recovered_usage
            and recovered_usage_positions.get(key, 0)
            > last_invalid_record_position
        }
        if authoritative_usage_position > last_invalid_record_position:
            accounting_source.update(authoritative_usage)
            atomic_authority_selected = True
    atomic_authority_keys = {
        "llm_observed_usage_cost_usd",
        "llm_conservative_unknown_exposure_usd",
        "llm_budget_accounted_cost_usd",
        "llm_budget_committed_cost_usd",
        "cost_accounting_incomplete",
        "llm_cost_accounting_incomplete",
        "llm_budget_accounted_cost_is_conservative_upper_bound",
    }
    if not atomic_authority_selected:
        # Fieldwise recovery can encounter a syntactically complete but
        # algebraically inconsistent bundle. Retain its cumulative ceiling,
        # but do not publish observed/unknown/completeness claims that failed
        # the atomic coherence validator above.
        for key in (
            "llm_observed_usage_cost_usd",
            "llm_conservative_unknown_exposure_usd",
            "cost_accounting_incomplete",
            "llm_cost_accounting_incomplete",
            "llm_budget_accounted_cost_is_conservative_upper_bound",
        ):
            accounting_source.pop(key, None)
        accounting_source.pop("cost_usd", None)
        accounted_candidates = [
            float(accounting_source[key])
            for key in (
                "accounted_cost_usd",
                "llm_budget_accounted_cost_usd",
            )
            if isinstance(accounting_source.get(key), (int, float))
            and not isinstance(accounting_source.get(key), bool)
            and math.isfinite(float(accounting_source[key]))
            and float(accounting_source[key]) >= 0.0
        ]
        accounted_ceiling = (
            max(accounted_candidates) if accounted_candidates else None
        )
        if accounted_ceiling is not None:
            accounting_source["accounted_cost_usd"] = accounted_ceiling
            accounting_source["llm_budget_accounted_cost_usd"] = (
                accounted_ceiling
            )
        else:
            accounting_source.pop("accounted_cost_usd", None)
            accounting_source.pop("llm_budget_accounted_cost_usd", None)
        committed_candidates = [
            float(accounting_source[key])
            for key in (
                "committed_cost_usd",
                "llm_budget_committed_cost_usd",
            )
            if isinstance(accounting_source.get(key), (int, float))
            and not isinstance(accounting_source.get(key), bool)
            and math.isfinite(float(accounting_source[key]))
            and float(accounting_source[key]) >= 0.0
        ]
        committed_ceiling = (
            max(committed_candidates) if committed_candidates else None
        )
        if committed_ceiling is not None and (
            accounted_ceiling is None
            or committed_ceiling + 1e-9 >= accounted_ceiling
        ):
            accounting_source["committed_cost_usd"] = committed_ceiling
            accounting_source["llm_budget_committed_cost_usd"] = (
                committed_ceiling
            )
        else:
            accounting_source.pop("committed_cost_usd", None)
            accounting_source.pop("llm_budget_committed_cost_usd", None)
    if atomic_authority_selected and atomic_authority_keys.issubset(
        accounting_source
    ):
        # Compatibility aliases must identify the same winning atomic ledger;
        # a later partial legacy record cannot leave consumers two totals.
        accounting_source["accounted_cost_usd"] = accounting_source[
            "llm_budget_accounted_cost_usd"
        ]
        accounting_source["committed_cost_usd"] = accounting_source[
            "llm_budget_committed_cost_usd"
        ]
    if accounting_source:
        accounting = selected(
            accounting_source,
            (
                "accounted_cost_usd",
                "committed_cost_usd",
                "llm_budget_accounted_cost_usd",
                "llm_budget_committed_cost_usd",
                "llm_observed_usage_cost_usd",
                "llm_conservative_unknown_exposure_usd",
                "cost_accounting_incomplete",
                "llm_cost_accounting_incomplete",
                "llm_budget_accounted_cost_is_conservative_upper_bound",
                "cost_usd",
                "estimated_cost_usd",
                "reservation_cost_usd",
                "usage_status",
                "missing_usage_reason",
                "model",
                "call_kind",
            ),
        )
        for key in (
            "accounted_cost_usd",
            "committed_cost_usd",
            "llm_budget_accounted_cost_usd",
            "llm_budget_committed_cost_usd",
            "llm_observed_usage_cost_usd",
            "llm_conservative_unknown_exposure_usd",
            "cost_usd",
            "estimated_cost_usd",
            "reservation_cost_usd",
        ):
            if key not in accounting:
                continue
            try:
                numeric = float(accounting[key])
            except (TypeError, ValueError, OverflowError):
                accounting.pop(key, None)
                continue
            if (
                isinstance(accounting[key], bool)
                or not isinstance(accounting[key], (int, float))
                or not math.isfinite(numeric)
                or numeric < 0.0
            ):
                accounting.pop(key, None)
                continue
            accounting[key] = numeric
        if accounting:
            recovered["watchdog_recovered_accounting"] = accounting
            if authoritative_usage_turn_index > 0:
                recovered["watchdog_recovered_accounting_turn_index"] = (
                    authoritative_usage_turn_index
                )
    return recovered


def _write_failure_summary(
    output_dir: Optional[Path],
    *,
    theorem_name: str,
    violation: str,
    initial_summary_identity: Optional[Tuple[int, int, int, str]] = None,
    worker_argv: Sequence[str] = (),
) -> None:
    """Atomically downgrade a failed worker using the normal Mini schema."""

    if output_dir is None:
        return
    try:
        output_dir.mkdir(parents=True, exist_ok=True)
        failure_reason, timed_out = _violation_failure_class(violation)
        shutdown_timeout = str(violation or "").startswith(
            (
                "watchdog_deadline_expired:mini_session_asyncio_shutdown",
                "watchdog_cooperative_stop_timeout:",
            )
        )
        existing: Dict[str, Any] = {}
        summary_path = output_dir / "summary.json"
        candidate = _read_bounded_json_object(summary_path)
        if (
            isinstance(candidate, dict)
            and _artifact_identity(summary_path) != initial_summary_identity
            and not bool(
                candidate.get("solved")
                or candidate.get("pre_export_solved")
                or candidate.get("session_root_finalized")
                or candidate.get("solved_export_verified")
            )
            and str(candidate.get("problem") or candidate.get("theorem") or "")
            == str(theorem_name or "")
        ):
            existing = dict(candidate)
        try:
            recovered = _recover_watchdog_turn_metadata(
                output_dir,
                worker_argv=worker_argv,
            )
        except Exception as recovery_error:
            recovered = {
                "watchdog_recovery_error": (
                    f"{type(recovery_error).__name__}: {recovery_error}"
                )[:500]
            }
        recovered_accounting = dict(
            recovered.get("watchdog_recovered_accounting") or {}
        )
        recovered_usage_counter_contributions = list(
            recovered.pop(
                "_watchdog_recovered_usage_counter_contributions",
                (),
            )
        )
        recovered_last_turn_index = recovered.get(
            "watchdog_recovery_last_turn_index"
        )
        if (
            bool(recovered.get("watchdog_recovery_usage_complete", False))
            and isinstance(recovered_last_turn_index, int)
            and not isinstance(recovered_last_turn_index, bool)
            and recovered_last_turn_index > 0
        ):
            # A complete append-only scan proves an authoritative crash cut.
            # Publishing it allows a later watchdog pass to recognize newly
            # appended events instead of treating its own old fallback as a
            # timeless controller summary.
            recovered["total_turns"] = recovered_last_turn_index
        if (
            "llm_budget_accounted_cost_usd" not in recovered_accounting
            and "accounted_cost_usd" in recovered_accounting
        ):
            recovered_accounting["llm_budget_accounted_cost_usd"] = (
                recovered_accounting["accounted_cost_usd"]
            )
        if (
            "llm_budget_committed_cost_usd" not in recovered_accounting
            and "committed_cost_usd" in recovered_accounting
        ):
            recovered_accounting["llm_budget_committed_cost_usd"] = (
                recovered_accounting["committed_cost_usd"]
            )
        if "llm_observed_usage_cost_usd" in recovered_accounting:
            recovered_accounting["cost_usd"] = recovered_accounting[
                "llm_observed_usage_cost_usd"
            ]
            recovered_accounting["estimated_unknown_cost_usd"] = (
                recovered_accounting.get(
                    "llm_conservative_unknown_exposure_usd",
                    recovered_accounting.get("estimated_unknown_cost_usd", 0.0),
                )
            )
        elif "llm_budget_accounted_cost_usd" in recovered_accounting:
            recovered_accounting["cost_usd"] = recovered_accounting[
                "llm_budget_accounted_cost_usd"
            ]
        if recovered_accounting:
            # Keep the nested recovery diagnostic identical to the normalized
            # top-level aliases; retaining the last event's per-call cost or
            # unknown delta here would present two conflicting ledgers.
            recovered["watchdog_recovered_accounting"] = dict(
                recovered_accounting
            )
        existing_observed = existing.get("llm_observed_usage_cost_usd")
        existing_unknown = existing.get(
            "llm_conservative_unknown_exposure_usd"
        )
        existing_accounted = existing.get("llm_budget_accounted_cost_usd")
        existing_authority_numbers = (
            existing_observed,
            existing_unknown,
            existing_accounted,
        )
        existing_authority_flags = tuple(
            existing.get(key)
            for key in (
                "cost_accounting_incomplete",
                "llm_cost_accounting_incomplete",
                "llm_budget_accounted_cost_is_conservative_upper_bound",
            )
        )
        existing_has_accounting_authority = bool(
            all(
                isinstance(value, (int, float))
                and not isinstance(value, bool)
                and math.isfinite(float(value))
                and float(value) >= 0.0
                for value in existing_authority_numbers
            )
            and all(isinstance(value, bool) for value in existing_authority_flags)
            and math.isclose(
                float(existing_accounted or 0.0),
                float(existing_observed or 0.0)
                + float(existing_unknown or 0.0),
                rel_tol=1e-9,
                abs_tol=1e-9,
            )
            and all(
                bool(value) == bool(float(existing_unknown or 0.0) > 1e-12)
                for value in existing_authority_flags
            )
        )
        existing_turn_count = existing.get("total_turns")
        recovered_accounting_turn_index = recovered.get(
            "watchdog_recovered_accounting_turn_index"
        )
        recovered_authority_is_newer = bool(
            existing_has_accounting_authority
            and isinstance(existing_turn_count, int)
            and not isinstance(existing_turn_count, bool)
            and isinstance(recovered_accounting_turn_index, int)
            and not isinstance(recovered_accounting_turn_index, bool)
            and recovered_accounting_turn_index > existing_turn_count
        )
        existing_failure_reason = str(existing.get("failure_reason") or "")
        existing_failure_detail = str(
            existing.get("failure_reason_detail")
            or existing.get("worker_failure_detail")
            or ""
        )
        if (
            failure_reason == "user_interrupted"
            and str(violation or "") == "watchdog_supervisor_signal:2"
            and existing_failure_detail == str(violation or "")
            and existing_failure_reason == "mini_session_worker_process_failure"
        ):
            existing_failure_reason = failure_reason
        payload = {
            **recovered,
            **recovered_accounting,
            **existing,
            "problem": str(theorem_name or ""),
            "theorem": str(theorem_name or ""),
            "solved": False,
            "pre_export_solved": False,
            "session_root_finalized": False,
            "disproved": False,
            "final_proof": None,
            "final_proof_helpers": [],
            "proof": None,
            "failure_reason": existing_failure_reason or failure_reason,
            "failure_reason_detail": (
                existing.get("failure_reason_detail")
                or str(violation or "watchdog_failure")
            ),
            "worker_failure_reason": failure_reason,
            "worker_failure_detail": str(violation or "watchdog_failure"),
            "worker_shutdown_timeout": bool(shutdown_timeout and timed_out),
            "mini_session_process_isolated": True,
            "mini_session_worker_timeout": timed_out,
            "root_proof_certificate": None,
            "root_disproof_certificate": None,
            "solved_export_verified": False,
            "mini_solved_export_status": "not_attempted",
        }
        # Recovery diagnostics describe this scan, never an older watchdog
        # fallback. Controller-owned accounting still follows the explicit
        # authority/cut merge rules below.
        payload.update(
            {
                key: value
                for key, value in recovered.items()
                if key.startswith("watchdog_")
            }
        )
        recovered_counter_keys = {
            key
            for key, value in recovered.items()
            if (
                key in {"llm_usage_events", "llm_usage_missing_events"}
                or any(key == suffix or key.endswith(f"_{suffix}") for suffix in (
                    "input_tokens",
                    "output_tokens",
                    "cached_input_tokens",
                    "cache_write_tokens",
                    "prompt_cache_miss_tokens",
                    "reasoning_output_tokens",
                ))
            )
            and isinstance(value, int)
            and not isinstance(value, bool)
            and value >= 0
        }
        recovered_first_turn_index = recovered.get(
            "watchdog_recovery_first_turn_index"
        )
        recovered_counters_are_authoritative = not existing_has_accounting_authority
        if recovered_counters_are_authoritative:
            for key in recovered_counter_keys:
                # A complete append-only trace replaces legacy/partial
                # counters. A coherent modern controller summary still wins
                # when it is at least as new: event sinks are best-effort and
                # can omit an accounting mutation that reached the summary.
                payload[key] = int(recovered[key])
            if (
                bool(recovered.get("watchdog_recovery_usage_complete", False))
                and isinstance(recovered_last_turn_index, int)
                and not isinstance(recovered_last_turn_index, bool)
                and recovered_last_turn_index > 0
            ):
                payload["total_turns"] = recovered_last_turn_index
        elif (
            isinstance(existing_turn_count, int)
            and not isinstance(existing_turn_count, bool)
            and existing_turn_count >= 0
            and isinstance(recovered_first_turn_index, int)
            and not isinstance(recovered_first_turn_index, bool)
            and 0 < recovered_first_turn_index <= existing_turn_count + 1
        ):
            # The controller summary is the authoritative prefix because its
            # event sink is best-effort. Add only trace events proven newer
            # than that prefix; replacing with the full trace could discard a
            # prefix event that reached memory but not JSONL.
            merged_counter_turn = existing_turn_count
            for key in recovered_counter_keys:
                existing_value = existing.get(key)
                if isinstance(existing_value, int) and not isinstance(
                    existing_value,
                    bool,
                ):
                    payload[key] = existing_value
                else:
                    payload.pop(key, None)
            for contribution in recovered_usage_counter_contributions:
                contribution_turn = contribution.get("turn_index", 0)
                if contribution_turn <= existing_turn_count:
                    continue
                merged_counter_turn = max(
                    merged_counter_turn,
                    contribution_turn,
                )
                for key, value in contribution.items():
                    if key == "turn_index":
                        continue
                    payload[key] = max(0, int(payload.get(key, 0) or 0)) + max(
                        0,
                        int(value or 0),
                    )
            payload["total_turns"] = merged_counter_turn
        if recovered_accounting and (
            not existing_has_accounting_authority
            or recovered_authority_is_newer
        ):
            # A legacy/partial unsolved summary may call its conservative
            # accounted total ``cost_usd`` and omit the authority fields.  It
            # must not overwrite the coherent cumulative usage snapshot just
            # recovered from the append-only turn ledger.  A modern summary
            # carrying a coherent bundle remains authoritative unless its own
            # ``total_turns`` proves that the append-only turn ledger contains
            # a newer cumulative authority receipt.
            payload.update(recovered_accounting)
        elif existing_has_accounting_authority:
            # Normalize compatibility aliases from the same winning bundle.
            # A field absent from the existing summary must not leak through
            # from an older recovered turn and contradict its authority.
            payload["cost_usd"] = float(existing_observed)
            payload["estimated_unknown_cost_usd"] = float(existing_unknown)
            existing_committed = existing.get(
                "llm_budget_committed_cost_usd",
                existing_accounted,
            )
            payload["llm_budget_committed_cost_usd"] = (
                float(existing_committed)
                if isinstance(existing_committed, (int, float))
                and not isinstance(existing_committed, bool)
                and math.isfinite(float(existing_committed))
                and float(existing_committed) >= float(existing_accounted)
                else float(existing_accounted)
            )
        _write_summary_and_activation(output_dir, payload)
    except OSError:
        # The stable exit code/stderr reason remains authoritative if the
        # output filesystem itself is unavailable.
        pass


def _write_summary_and_activation(output_dir: Path, payload: Dict[str, Any]) -> None:
    destination = output_dir / "summary.json"
    temporary = output_dir / f".summary.watchdog.{os.getpid()}.{uuid.uuid4().hex}.tmp"

    def replace_summary() -> None:
        temporary.write_text(
            json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n",
            encoding="utf-8",
        )
        os.replace(temporary, destination)

    replace_summary()
    try:
        from ensemble_prover.activation_telemetry import (
            ACTIVATION_ARTIFACT_NAME,
            build_activation_telemetry,
            compact_activation_summary,
        )

        events: list[Dict[str, Any]] = []
        malformed = 0
        scan_truncated = False
        turns_fingerprint: Dict[str, Any] = {}
        turns_path = output_dir / "turns.jsonl"
        if turns_path.is_file():
            for _attempt in range(3):
                before = _watchdog_turns_snapshot_identity(turns_path)
                candidate_events: list[Dict[str, Any]] = []
                candidate_malformed = 0
                lines, candidate_truncated, _bytes_scanned = _recent_jsonl_lines(
                    turns_path
                )
                for line in lines:
                    if not line.strip():
                        continue
                    try:
                        record = _strict_json_loads(line)
                    except (
                        json.JSONDecodeError,
                        RecursionError,
                        ValueError,
                        OverflowError,
                    ):
                        candidate_malformed += 1
                        continue
                    if isinstance(record, dict):
                        candidate_events.append(record)
                    else:
                        candidate_malformed += 1
                after = _watchdog_turns_snapshot_identity(turns_path)
                if before and before == after:
                    candidate_fingerprint: Dict[str, Any] = {}
                    if not candidate_truncated:
                        from ensemble_prover.activation_telemetry import (
                            _turns_fingerprint,
                        )

                        candidate_fingerprint = _turns_fingerprint(turns_path)
                        if (
                            not candidate_fingerprint
                            or _watchdog_turns_snapshot_identity(turns_path) != after
                        ):
                            continue
                    events = candidate_events
                    malformed = candidate_malformed
                    scan_truncated = candidate_truncated
                    turns_fingerprint = candidate_fingerprint
                    break
            else:
                raise RuntimeError(
                    "watchdog turns snapshot changed during telemetry classification"
                )
        activation = build_activation_telemetry(
            events,
            summary=payload,
            run_dir=output_dir,
        )
        activation["malformed_event_count"] = int(
            activation.get("malformed_event_count", 0) or 0
        ) + malformed
        activation["watchdog_bounded_recovery"] = True
        activation["watchdog_recovery_scan_truncated"] = bool(scan_truncated)
        activation["activation_counts_are_lower_bound"] = bool(scan_truncated)
        if turns_fingerprint and not scan_truncated:
            activation.update(turns_fingerprint)
        payload["activation_telemetry"] = compact_activation_summary(activation)
        replace_summary()
        from ensemble_prover.activation_telemetry import _summary_fingerprint

        activation.update(_summary_fingerprint(destination))
        activation_destination = output_dir / ACTIVATION_ARTIFACT_NAME
        activation_temporary = output_dir / (
            f".{ACTIVATION_ARTIFACT_NAME}.{uuid.uuid4().hex}.tmp"
        )
        activation_temporary.write_text(
            json.dumps(
                activation,
                indent=2,
                ensure_ascii=False,
                sort_keys=True,
                allow_nan=False,
            ),
            encoding="utf-8",
        )
        os.replace(activation_temporary, activation_destination)
    except Exception:
        # The summary remains authoritative if telemetry cannot be rebuilt.
        pass


def _nonzero_worker_summary_is_authoritative(
    summary_path: Path,
    *,
    theorem_name: str,
    initial_identity: Optional[Tuple[int, int, int, str]],
) -> bool:
    try:
        current_identity = _artifact_identity(summary_path)
        if current_identity == initial_identity:
            return False
        payload = _read_bounded_json_object(summary_path)
    except Exception:
        return False
    if not payload:
        return False
    if bool(
        payload.get("solved")
        or payload.get("pre_export_solved")
        or payload.get("session_root_finalized")
        or payload.get("solved_export_verified")
    ):
        return False
    problem = str(payload.get("problem") or payload.get("theorem") or "")
    if theorem_name and problem != theorem_name:
        return False
    return bool(str(payload.get("failure_reason") or "").strip())


def _fresh_staged_solution_is_authoritative(
    output_dir: Optional[Path],
    *,
    theorem_name: str,
    initial_identity: Optional[Tuple[int, int, int, str]],
    initial_receipt_identity: Optional[Tuple[int, int, int, str]] = None,
) -> bool:
    """Recognize the exact fail-closed handoff written by a solved worker.

    This receipt never makes a run solved.  It only permits the isolated CLI
    parent to invoke the existing independent solved-export verifier after a
    resistant sibling forced the supervisor to sweep the worker tree during
    ``asyncio.run`` shutdown.
    """

    if output_dir is None:
        return False
    staged_summary_path = output_dir / _STAGED_SOLUTION_SUMMARY_NAME

    def fields_are_valid(payload: Mapping[str, Any]) -> bool:
        problem = str(payload.get("problem") or payload.get("theorem") or "")
        final_proof = payload.get("final_proof")
        helpers = payload.get("final_proof_helpers")
        return bool(
            theorem_name
            and problem == str(theorem_name)
            and payload.get("solved") is False
            and payload.get("pre_export_solved") is True
            and payload.get("session_root_finalized") is True
            and isinstance(final_proof, str)
            and bool(final_proof.strip())
            and isinstance(helpers, list)
            and payload.get("disproved") is False
            and payload.get("root_disproof_certificate") is None
            and payload.get("failure_reason") == "solved_export_not_attempted"
            and payload.get("solved_export_verified") is False
            and payload.get("mini_solved_export_status") == "not_attempted"
        )

    receipt_path = output_dir / _STAGED_SOLUTION_RECEIPT_NAME
    try:
        receipt_lstat = receipt_path.lstat()
    except OSError:
        receipt_lstat = None
    receipt_identity = (
        _artifact_identity(receipt_path)
        if receipt_lstat is not None and stat.S_ISREG(receipt_lstat.st_mode)
        else None
    )
    if (
        receipt_identity is not None
        and receipt_identity != initial_receipt_identity
    ):
        receipt = _read_bounded_json_object(receipt_path)
        receipt_hash = str(receipt.get("summary_sha256") or "")
        receipt_size = receipt.get("summary_size_bytes")
        receipt_is_valid = bool(
            receipt.get("schema") == "mini_pre_export_solved_receipt_v1"
            and receipt.get("theorem") == str(theorem_name)
            and receipt.get("pre_export_solved") is True
            and receipt.get("session_root_finalized") is True
            and isinstance(receipt_size, int)
            and not isinstance(receipt_size, bool)
            and receipt_size >= 0
            and re.fullmatch(r"[0-9a-f]{64}", receipt_hash)
        )
        if receipt_is_valid:
            stable_summary = _stable_full_json_object_with_sha256(
                staged_summary_path,
                expected_size=receipt_size,
            )
            if (
                stable_summary is not None
                and stable_summary[:2] == (receipt_size, receipt_hash)
                and fields_are_valid(stable_summary[2])
            ):
                return True
    # Current workers always publish the immutable summary and its receipt as
    # one handoff protocol. A mutable summary.json is never authority for
    # promoting unrelated staged bytes when that receipt is absent or stale.
    return False


def write_staged_solution_receipt(
    output_dir: Path,
    *,
    theorem_name: str,
    summary: Mapping[str, Any],
) -> Path:
    """Atomically bind a small shutdown handoff to the exact full summary."""

    output_dir = Path(output_dir)
    staged_summary_path = output_dir / _STAGED_SOLUTION_SUMMARY_NAME
    problem = str(summary.get("problem") or summary.get("theorem") or "")
    final_proof = summary.get("final_proof")
    if not bool(
        theorem_name
        and problem == str(theorem_name)
        and summary.get("solved") is False
        and summary.get("pre_export_solved") is True
        and summary.get("session_root_finalized") is True
        and isinstance(final_proof, str)
        and bool(final_proof.strip())
        and isinstance(summary.get("final_proof_helpers"), list)
        and summary.get("disproved") is False
        and summary.get("root_disproof_certificate") is None
        and summary.get("failure_reason") == "solved_export_not_attempted"
        and summary.get("solved_export_verified") is False
        and summary.get("mini_solved_export_status") == "not_attempted"
    ):
        raise ValueError("summary is not an exact staged solved handoff")
    staged_temporary = output_dir / (
        f".{_STAGED_SOLUTION_SUMMARY_NAME}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )
    staged_temporary.write_text(
        json.dumps(dict(summary), indent=2, sort_keys=True, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    os.replace(staged_temporary, staged_summary_path)
    stable_summary = _stable_full_file_sha256(staged_summary_path)
    if stable_summary is None:
        raise OSError("summary changed while staging solved handoff")
    summary_size, summary_hash = stable_summary
    payload = {
        "schema": "mini_pre_export_solved_receipt_v1",
        "theorem": str(theorem_name),
        "pre_export_solved": True,
        "session_root_finalized": True,
        "summary_size_bytes": summary_size,
        "summary_sha256": summary_hash,
    }
    destination = output_dir / _STAGED_SOLUTION_RECEIPT_NAME
    temporary = output_dir / (
        f".{_STAGED_SOLUTION_RECEIPT_NAME}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )
    temporary.write_text(
        json.dumps(payload, sort_keys=True, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, destination)
    return destination


def _promote_staged_solution_summary(output_dir: Path) -> bool:
    """Atomically install the immutable staged handoff after worker sweep."""

    staged = Path(output_dir) / _STAGED_SOLUTION_SUMMARY_NAME
    destination = Path(output_dir) / "summary.json"
    try:
        staged_stat = staged.lstat()
        if not stat.S_ISREG(staged_stat.st_mode):
            return False
        os.replace(staged, destination)
    except OSError:
        return False
    return True


def _artifact_identity(path: Path) -> Optional[Tuple[int, int, int, str]]:
    """Return a race-checked identity without scanning an unbounded artifact.

    Small artifacts are hashed completely. Large append-heavy traces are
    sampled evenly across a fixed byte budget; ctime is bound into the digest
    so an in-place write outside a sampled window still invalidates the
    snapshot even when a caller restores mtime.
    """

    descriptor = -1
    try:
        before = path.lstat()
        if not stat.S_ISREG(before.st_mode):
            return None
        flags = os.O_RDONLY
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        descriptor = os.open(path, flags)
        opened_before = os.fstat(descriptor)
        if not stat.S_ISREG(opened_before.st_mode):
            return None
        digest = hashlib.sha256()
        digest.update(b"watchdog-artifact-identity-v2\0")
        digest.update(str(int(before.st_ctime_ns)).encode("ascii"))
        digest.update(b"\0")
        digest.update(str(int(before.st_size)).encode("ascii"))
        size = max(0, int(opened_before.st_size))
        budget = max(1, int(_WATCHDOG_RECOVERY_MAX_BYTES))
        if size <= budget:
            windows = ((0, size),)
        else:
            sample_count = max(
                1,
                min(int(_WATCHDOG_IDENTITY_SAMPLE_COUNT), budget),
            )
            block_size = max(1, budget // sample_count)
            extent = max(0, size - block_size)
            windows = tuple(
                (
                    0
                    if sample_count == 1
                    else (extent * index) // (sample_count - 1),
                    block_size,
                )
                for index in range(sample_count)
            )
        for offset, length in windows:
            chunk = os.pread(descriptor, length, offset)
            if len(chunk) != length:
                return None
            digest.update(int(offset).to_bytes(8, "big", signed=False))
            digest.update(chunk)
        opened_after = os.fstat(descriptor)
        after = path.lstat()
    except OSError:
        return None
    finally:
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass
    before_identity = (
        before.st_ino,
        before.st_mtime_ns,
        before.st_ctime_ns,
        before.st_size,
    )
    if before_identity != (
        opened_before.st_ino,
        opened_before.st_mtime_ns,
        opened_before.st_ctime_ns,
        opened_before.st_size,
    ) or before_identity != (
        opened_after.st_ino,
        opened_after.st_mtime_ns,
        opened_after.st_ctime_ns,
        opened_after.st_size,
    ) or before_identity != (
        after.st_ino,
        after.st_mtime_ns,
        after.st_ctime_ns,
        after.st_size,
    ):
        return None
    return (
        int(after.st_ino),
        int(after.st_mtime_ns),
        int(after.st_size),
        digest.hexdigest(),
    )


def _run_cli_worker_in_dedicated_supervisor(
    argv: Sequence[str],
    *,
    overall_timeout_s: float = _DEFAULT_OVERALL_TIMEOUT_S,
    worker_command: Optional[Sequence[str]] = None,
    output_dir: Optional[Path] = None,
    theorem_name: str = "",
    startup_timeout_s: float = _STARTUP_TIMEOUT_S,
    hard_operation_deadlines: bool = False,
    shutdown_timeout_s: float = _SHUTDOWN_TIMEOUT_S,
    parent_watch_fd: int = -1,
    cooperative_stop_signals: Optional[list] = None,
    cooperative_stop_grace_s: float = _COOPERATIVE_STOP_GRACE_S,
) -> int:
    """Run the Mini CLI in a supervised worker process (Linux/POSIX only)."""

    if os.name != "posix" or not Path("/proc").is_dir():
        raise RuntimeError("Mini hard-deadline supervision requires Linux /proc")
    read_fd, write_fd = os.pipe()
    os.set_inheritable(write_fd, True)
    nonce = uuid.uuid4().hex
    now = time.monotonic()
    overall_timeout = max(0.0, float(overall_timeout_s or 0.0))
    overall_deadline = now + overall_timeout if overall_timeout > 0.0 else 0.0
    startup_timeout = max(0.0, float(startup_timeout_s or 0.0))
    startup_deadline = 0.0
    if startup_timeout > 0.0:
        startup_deadline = now + startup_timeout
        if overall_deadline > 0.0:
            startup_deadline = min(overall_deadline, startup_deadline)
    env = os.environ.copy()
    env[_WATCHDOG_WORKER_ENV] = "1"
    env[_WATCHDOG_FD_ENV] = str(write_fd)
    env[_WATCHDOG_NONCE_ENV] = nonce
    env[_WATCHDOG_OVERALL_DEADLINE_ENV] = repr(overall_deadline)
    env[_WATCHDOG_HARD_OPERATION_DEADLINES_ENV] = (
        "1" if bool(hard_operation_deadlines) else "0"
    )
    env[_WATCHDOG_SHUTDOWN_TIMEOUT_ENV] = repr(
        max(0.0, float(shutdown_timeout_s or 0.0))
    )
    env[_WATCHDOG_STARTUP_TIMEOUT_ENV] = repr(startup_timeout)
    env[_WATCHDOG_DEFER_EXPORT_ENV] = "1"
    command = (
        list(worker_command)
        if worker_command is not None
        else [sys.executable, "-m", "ensemble_prover.mini_prover", *list(argv)]
    )
    proc: Optional[subprocess.Popen[Any]] = None
    selector = selectors.DefaultSelector()
    active: Dict[str, _ActiveLease] = {}
    known: Dict[int, int] = {}
    buffer = bytearray()
    violation = ""
    saw_ready = False
    eof = False
    initial_summary_identity = (
        _artifact_identity(output_dir / "summary.json")
        if output_dir is not None
        else None
    )
    initial_staged_receipt_identity = (
        _artifact_identity(output_dir / _STAGED_SOLUTION_RECEIPT_NAME)
        if output_dir is not None
        else None
    )

    previous_subreaper = _enable_child_subreaper()
    try:
        proc = subprocess.Popen(
            command,
            env=env,
            pass_fds=(write_fd,),
            start_new_session=True,
        )
        identity = _proc_identity(proc.pid)
        if identity is None:
            violation = "watchdog_worker_identity_unavailable"
        else:
            known[identity[0]] = identity[1]
        os.close(write_fd)
        write_fd = -1
        os.set_blocking(read_fd, False)
        selector.register(read_fd, selectors.EVENT_READ)
        if parent_watch_fd >= 0:
            os.set_blocking(parent_watch_fd, False)
            selector.register(parent_watch_fd, selectors.EVENT_READ)
        cooperative_stop_sent = 0.0
        while not violation:
            cooperative_stop_expired = False
            _refresh_known_tree(known, ownership_nonce=nonce)
            if parent_watch_fd >= 0:
                try:
                    parent_state = os.read(parent_watch_fd, 1)
                except BlockingIOError:
                    parent_state = None
                if parent_state == b"":
                    violation = "watchdog_supervisor_parent_lost"
                    break
            # MP-FU-009 cooperative stop: forward the first termination
            # signal to the worker as SIGTERM so it can run its
            # cancellation barrier and author its own terminal summary.
            # The SIGSTOP/SIGKILL sweep remains the bounded backstop.
            if cooperative_stop_signals and cooperative_stop_sent <= 0.0:
                cooperative_stop_sent = time.monotonic()
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except (ProcessLookupError, PermissionError, OSError):
                    try:
                        proc.terminate()
                    except (ProcessLookupError, OSError):
                        pass
            elif (
                cooperative_stop_sent > 0.0
                and time.monotonic() - cooperative_stop_sent
                >= max(0.0, float(cooperative_stop_grace_s))
            ):
                cooperative_stop_expired = True
            # Drain/reap first so a timely queued END or clean exit wins the
            # scheduling race at the nominal deadline.
            while True:
                try:
                    chunk = os.read(read_fd, 65_536)
                except BlockingIOError:
                    break
                if not chunk:
                    eof = True
                    break
                buffer.extend(chunk)
            message_violation, ready_now = _consume_messages(
                buffer,
                active,
                expected_nonce=nonce,
                ready_deadline=startup_deadline,
            )
            saw_ready = saw_ready or ready_now
            if message_violation:
                violation = message_violation
                break
            returncode = proc.poll()
            if returncode is not None:
                if buffer:
                    violation = "watchdog_partial_frame_at_worker_exit"
                    break
                non_shutdown = [
                    label
                    for _deadline, label, _reason in active.values()
                    if label != "mini_session_asyncio_shutdown"
                ]
                if non_shutdown and not cooperative_stop_signals:
                    # A cooperative stop cancels the work that held the
                    # lease; the worker exits with it deliberately armed.
                    # Treating that as a protocol violation would clobber
                    # the worker-authored terminal summary.
                    violation = f"watchdog_worker_exited_with_active_lease:{non_shutdown[0]}"
                    break
                # Kill/reap any worker-owned external descendants even on a
                # clean leader exit; none may outlive the isolated run.
                _terminate_worker_tree(proc, known, ownership_nonce=nonce)
                if int(returncode) != 0 and output_dir is not None:
                    summary_path = output_dir / "summary.json"
                    # A worker killed by the cooperative stop's SIGTERM (no
                    # authoritative summary of its own) is a manual stop, not
                    # an ordinary worker failure — keep the historical
                    # supervisor-signal verdict for that case.
                    exit_violation = (
                        "watchdog_supervisor_signal:"
                        f"{int(cooperative_stop_signals[0])}"
                        if cooperative_stop_signals
                        else f"watchdog_worker_exit_nonzero:{returncode}"
                    )
                    if not _nonzero_worker_summary_is_authoritative(
                        summary_path,
                        theorem_name=theorem_name,
                        initial_identity=initial_summary_identity,
                    ):
                        _write_failure_summary(
                            output_dir,
                            theorem_name=theorem_name,
                            violation=exit_violation,
                            initial_summary_identity=initial_summary_identity,
                            worker_argv=argv,
                        )
                    else:
                        try:
                            current_payload = _read_bounded_json_object(summary_path)
                            if not current_payload:
                                raise ValueError("worker summary is absent or oversized")
                            _write_summary_and_activation(output_dir, current_payload)
                        except Exception:
                            _write_failure_summary(
                                output_dir,
                                theorem_name=theorem_name,
                                violation=exit_violation,
                                initial_summary_identity=initial_summary_identity,
                                worker_argv=argv,
                            )
                return int(returncode)
            if cooperative_stop_expired:
                violation = (
                    "watchdog_cooperative_stop_timeout:"
                    f"{int(cooperative_stop_signals[0])}"
                )
                break
            if eof:
                # Pipe EOF and process reaping are separate kernel events.
                # A worker that has already written an authoritative summary
                # can close its last fd a scheduling quantum before poll()
                # reports exit; classifying that ordinary exit as protocol
                # failure overwrites the real setup/search exception. A
                # worker that deliberately drops supervision but keeps
                # running still fails closed after this short reap-only grace.
                try:
                    proc.wait(timeout=_CHANNEL_EOF_REAP_GRACE_S)
                except subprocess.TimeoutExpired:
                    violation = "watchdog_channel_eof_while_worker_running"
                    break
                continue
            now = time.monotonic()
            if (
                startup_deadline > 0.0
                and not saw_ready
                and now >= startup_deadline
            ):
                violation = "watchdog_worker_startup_timeout"
                break
            if overall_deadline > 0.0 and now >= overall_deadline:
                violation = "watchdog_worker_overall_timeout"
                break
            expired = [
                (deadline, label, reason)
                for deadline, label, reason in active.values()
                if now >= deadline + _DEADLINE_CLEANUP_GRACE_S
            ]
            if expired:
                _deadline, label, reason = min(expired)
                violation = (
                    f"watchdog_deadline_expired:{label}"
                    + (f":{reason}" if reason else "")
                )
                break
            timeout = _POLL_INTERVAL_S
            if cooperative_stop_sent > 0.0:
                grace_deadline = cooperative_stop_sent + max(
                    0.0, float(cooperative_stop_grace_s)
                )
                timeout = min(timeout, max(0.0, grace_deadline - now))
            if overall_deadline > 0.0:
                timeout = min(timeout, overall_deadline - now)
            if startup_deadline > 0.0 and not saw_ready:
                timeout = min(timeout, startup_deadline - now)
            if active:
                nearest = min(
                    deadline + _DEADLINE_CLEANUP_GRACE_S
                    for deadline, _label, _reason in active.values()
                )
                timeout = min(timeout, max(0.0, nearest - now))
            selector.select(max(0.0, timeout))
    finally:
        if proc is not None and (violation or proc.poll() is None):
            _terminate_worker_tree(proc, known, ownership_nonce=nonce)
        try:
            selector.close()
        finally:
            for fd in (read_fd, write_fd):
                if fd >= 0:
                    try:
                        os.close(fd)
                    except OSError:
                        pass
            if parent_watch_fd >= 0:
                try:
                    os.close(parent_watch_fd)
                except OSError:
                    pass
            _restore_child_subreaper(previous_subreaper)
    if violation:
        shutdown_swept_staged_solution = bool(
            violation.startswith(
                "watchdog_deadline_expired:mini_session_asyncio_shutdown"
            )
            and _fresh_staged_solution_is_authoritative(
                output_dir,
                theorem_name=theorem_name,
                initial_identity=initial_summary_identity,
                initial_receipt_identity=initial_staged_receipt_identity,
            )
        )
        if shutdown_swept_staged_solution:
            if not _promote_staged_solution_summary(Path(output_dir)):
                shutdown_swept_staged_solution = False
        if shutdown_swept_staged_solution:
            print(
                "Mini-session worker shutdown was swept after root "
                "finalization; independently verifying the staged proof",
                file=sys.stderr,
            )
            return VERIFY_STAGED_SOLUTION_EXIT_CODE
        _write_failure_summary(
            output_dir,
            theorem_name=theorem_name,
            violation=violation,
            initial_summary_identity=initial_summary_identity,
            worker_argv=argv,
        )
        print(f"Mini-session worker terminated: {violation}", file=sys.stderr)
        return 124
    return int(proc.returncode if proc is not None and proc.returncode is not None else 1)


def _wait_for_supervisor(proc: Any, *, max_interrupts: int = 5) -> int:
    """Wait for the supervisor without letting Ctrl-C SIGKILL it mid-teardown.

    CPython's ``subprocess.run`` kills its child on ANY exception — including
    the KeyboardInterrupt the parent shares with the supervisor's own SIGINT.
    That race could orphan the worker (own session, dead subreaper) with no
    summary and no reaper: the exact late-child-work failure MP-FU-009
    closes. The supervisor owns teardown; the parent just keeps waiting. If
    the user keeps interrupting, the parent eventually stops waiting WITHOUT
    killing the supervisor — parent exit closes ``parent_watch_fd``, and the
    supervisor's parent-lost path sweeps the worker tree.
    """

    interrupts = 0
    while True:
        try:
            return int(proc.wait())
        except KeyboardInterrupt:
            interrupts += 1
            if interrupts >= max(1, int(max_interrupts)):
                print(
                    "Mini watchdog: giving up foreground wait after repeated "
                    "interrupts; supervisor continues teardown in background",
                    file=sys.stderr,
                )
                return 130


def run_cli_worker_under_watchdog(
    argv: Sequence[str],
    *,
    overall_timeout_s: float = _DEFAULT_OVERALL_TIMEOUT_S,
    worker_command: Optional[Sequence[str]] = None,
    output_dir: Optional[Path] = None,
    theorem_name: str = "",
    startup_timeout_s: float = _STARTUP_TIMEOUT_S,
    hard_operation_deadlines: bool = False,
    shutdown_timeout_s: float = _SHUTDOWN_TIMEOUT_S,
    cooperative_stop_grace_s: float = _COOPERATIVE_STOP_GRACE_S,
) -> int:
    """Run crash/process supervision in a private process.

    Process isolation, parent-loss detection, worker exit handling, and
    explicitly requested operation/lifecycle deadlines protect unattended
    runs. Aggregate startup and runtime wall clocks default to disabled because
    they cannot distinguish a hung worker from healthy long-running proof work.
    """

    if os.name != "posix" or not Path("/proc").is_dir():
        raise RuntimeError("Mini hard-deadline supervision requires Linux /proc")
    spec = {
        "argv": list(argv),
        "overall_timeout_s": float(overall_timeout_s or 0.0),
        "worker_command": list(worker_command) if worker_command is not None else None,
        "output_dir": str(output_dir) if output_dir is not None else None,
        "theorem_name": str(theorem_name or ""),
        "startup_timeout_s": float(startup_timeout_s or 0.0),
        "hard_operation_deadlines": bool(hard_operation_deadlines),
        "shutdown_timeout_s": float(shutdown_timeout_s or 0.0),
        "cooperative_stop_grace_s": float(cooperative_stop_grace_s),
    }
    spec_path = ""
    parent_read_fd = -1
    parent_write_fd = -1
    try:
        parent_read_fd, parent_write_fd = os.pipe()
        spec["parent_watch_fd"] = parent_read_fd
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            prefix="ensemble-mini-watchdog-",
            suffix=".json",
            delete=False,
        ) as handle:
            json.dump(spec, handle, sort_keys=True)
            spec_path = handle.name
        supervisor_proc = subprocess.Popen(
            [sys.executable, "-m", __name__, "--supervisor-spec", spec_path],
            pass_fds=(parent_read_fd,),
        )
        return _wait_for_supervisor(supervisor_proc)
    finally:
        if spec_path:
            try:
                Path(spec_path).unlink()
            except OSError:
                pass
        for fd in (parent_read_fd, parent_write_fd):
            if fd >= 0:
                try:
                    os.close(fd)
                except OSError:
                    pass


def _dedicated_supervisor_main(argv: Sequence[str]) -> int:
    if len(argv) != 2 or argv[0] != "--supervisor-spec":
        print("invalid Mini watchdog supervisor invocation", file=sys.stderr)
        return 125
    try:
        supervisor_spec_path = Path(argv[1])
        raw_payload = supervisor_spec_path.read_text(encoding="utf-8")
        payload = _strict_json_loads(raw_payload)
        if not isinstance(payload, dict):
            raise TypeError("supervisor specification must be an object")
        worker_argv = tuple(str(item) for item in (payload.get("argv") or ()))
        output_value = payload.get("output_dir")
        supervised_output_dir = (
            Path(str(output_value)) if output_value is not None else None
        )
        initial_summary_identity = (
            _artifact_identity(supervised_output_dir / "summary.json")
            if supervised_output_dir is not None
            else None
        )

        class SupervisorTermination(BaseException):
            def __init__(self, signum: int) -> None:
                self.signum = int(signum)

        cooperative_stop_signals: list = []

        def terminate_supervisor(signum: int, _frame: Any) -> None:
            # First signal: request a cooperative worker stop (MP-FU-009);
            # the poll loop forwards SIGTERM and starts the bounded grace.
            # A repeat signal escalates to the immediate freeze-and-kill
            # sweep, and further repeats are ignored while it runs.
            if not cooperative_stop_signals:
                cooperative_stop_signals.append(int(signum))
                return
            for handled_signal in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
                signal.signal(handled_signal, signal.SIG_IGN)
            raise SupervisorTermination(signum)

        for handled_signal in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(handled_signal, terminate_supervisor)
        # Unlinking the spec is the parent-visible supervisor readiness
        # receipt. Publish it only after termination handlers are installed;
        # otherwise an immediate parent signal can kill the supervisor in the
        # narrow parse-to-handler window and bypass worker-tree cleanup.
        try:
            supervisor_spec_path.unlink()
        except OSError:
            pass
        try:
            supervised_rc = _run_cli_worker_in_dedicated_supervisor(
            worker_argv,
            overall_timeout_s=float(payload.get("overall_timeout_s") or 0.0),
            worker_command=(
                tuple(str(item) for item in payload["worker_command"])
                if payload.get("worker_command") is not None
                else None
            ),
            output_dir=supervised_output_dir,
            theorem_name=str(payload.get("theorem_name") or ""),
            startup_timeout_s=float(
                payload.get("startup_timeout_s") or 0.0
            ),
            hard_operation_deadlines=bool(
                payload.get("hard_operation_deadlines", False)
            ),
            shutdown_timeout_s=float(payload.get("shutdown_timeout_s") or 0.0),
            parent_watch_fd=int(payload.get("parent_watch_fd", -1) or -1),
            cooperative_stop_signals=cooperative_stop_signals,
            cooperative_stop_grace_s=float(
                _COOPERATIVE_STOP_GRACE_S
                if payload.get("cooperative_stop_grace_s") is None
                else payload.get("cooperative_stop_grace_s")
            ),
            )
            if cooperative_stop_signals and supervised_rc != 0:
                # rc 0 means the worker finished its work during the grace —
                # surface the clean result, not the interrupt convention.
                # Preserve the historical signal-exit convention regardless
                # of whether the worker exited cooperatively or was swept.
                return 128 + int(cooperative_stop_signals[0])
            return supervised_rc
        except SupervisorTermination as exc:
            _write_failure_summary(
                supervised_output_dir,
                theorem_name=str(payload.get("theorem_name") or ""),
                violation=f"watchdog_supervisor_signal:{exc.signum}",
                initial_summary_identity=initial_summary_identity,
                worker_argv=worker_argv,
            )
            return 128 + exc.signum
    except Exception as exc:
        print(
            f"Mini watchdog supervisor failed: {type(exc).__name__}: {exc}",
            file=sys.stderr,
        )
        return 125


__all__ = [
    "VERIFY_STAGED_SOLUTION_EXIT_CODE",
    "ProcessDeadlineLease",
    "ProcessWatchdogProtocolError",
    "begin_process_deadline",
    "hard_operation_deadlines_enabled",
    "is_watchdog_worker",
    "run_cli_worker_under_watchdog",
    "signal_worker_ready",
    "worker_startup_timeout_s",
    "worker_overall_deadline",
    "worker_shutdown_timeout_s",
    "write_staged_solution_receipt",
]


if __name__ == "__main__":
    raise SystemExit(_dedicated_supervisor_main(sys.argv[1:]))
