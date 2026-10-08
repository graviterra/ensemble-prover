"""Manage isolated persistent Lean verifier workers and their protocol."""

from __future__ import annotations

import asyncio
import json
import logging
import os
import shutil
import sys
import time
from collections import OrderedDict
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Callable, Dict, Optional

from .config import LeanConfig, _resolve_lean_scratch_root
from .runtime_context import mark_runtime_owned_callback
from .subprocess_cleanup import (
    request_process_termination_nowait,
    terminate_and_reap_process,
)
from .local_inference.network_policy import owned_worker_environment, current_network_policy

logger = logging.getLogger(__name__)

PERSISTENT_VERIFIER_PROTOCOL = "persistent_verifier_transport"
PERSISTENT_VERIFIER_VERSION = "1.0"
DEFAULT_MAX_MESSAGE_BYTES = 16 * 1024 * 1024
STDERR_TAIL_BYTES = 64 * 1024

# Upper bound on how long a caller parked on an empty lane may sleep before
# re-checking availability. Lane changes normally wake it immediately via the
# queue's change event; this periodic backstop covers a terminal transition
# that updated worker/lane state without routing through that signal, so the
# caller still falls back promptly instead of at the lane timeout.
_LANE_CHANGE_POLL_S = 0.05


def _protocol_major(version: str) -> str:
    text = str(version or "").strip()
    return text.split(".", 1)[0] if text else ""


def _timestamp_unix_s() -> float:
    return float(time.time())


def _status_with_output(status: str, output: str) -> str:
    detail = str(output or "").strip()
    if not detail:
        return str(status or "")
    return f"{detail}\n{status}"


def _consume_task_exception(task: "asyncio.Future[Any]") -> None:
    if task.cancelled():
        return
    try:
        task.exception()
    except BaseException:
        pass


def _lane_release_callback(
    lane_inflight: Dict[str, int],
    lane: str,
    changed: asyncio.Event,
) -> Callable[..., None]:
    """Once-only lane-slot release, usable as a task done-callback.

    Must be a named module-level factory, not an inline lambda: only callables
    on ``runtime_context._TRUSTED_RUNTIME_CALLBACKS`` authenticate. An
    unauthenticated ``mark_runtime_owned_callback`` is a silent no-op, so
    MiniSession rewrites the callback to a no-op once the action boundary
    closes; the lane slot is then never released and every later request
    routed to that lane sees a phantom in-flight worker that can never arrive.

    Captures exactly the pool's lane-in-flight dict, one lane name, and the
    lane queue's change event -- which is what the ``lane_release`` policy
    admits -- so it can only adjust one counter it already owns and wake the
    queue's parked waiters.
    """

    def release_lane_slot(_finished: Any = None) -> None:
        remaining = int(lane_inflight.get(lane, 0)) - 1
        lane_inflight[lane] = remaining if remaining > 0 else 0
        changed.set()

    return release_lane_slot


@dataclass
class VerifierRequest:
    request_id: str
    mode: str
    content: str
    goal_name: str
    timeout_s: float
    warning_as_error: bool
    max_heartbeats: int | None
    queue_class: str
    document_uri: str
    metadata: Dict[str, Any]


@dataclass
class VerifierResponse:
    request_id: str
    ok: bool
    returncode: int
    output: str
    backend_kind: str
    worker_id: str
    worker_generation: int
    service_time_s: float
    queue_wait_s: float = 0.0
    failure_kind: str = ""
    # None preserves legacy adapter behavior; native completion carries an
    # explicit empty status, distinct from any words quoted by diagnostics.
    runtime_status: Optional[str] = None
    document_version: int = 0
    context_key: str = ""
    request_completed: bool = False
    startup_time_s: float = 0.0
    context_family_key: str = ""


class PersistentVerifierError(RuntimeError):
    pass


class PersistentVerifierUnavailableError(PersistentVerifierError):
    pass


class PersistentVerifierFrameError(PersistentVerifierError):
    """A bounded transport failure, distinct from a Lean process crash."""

    def __init__(self, message: str, failure_kind: str):
        super().__init__(message)
        self.failure_kind = failure_kind


async def read_bounded_json_line(
    reader: asyncio.StreamReader, *, max_bytes: int, timeout_s: float
) -> bytes:
    """Read fragmented NDJSON without relying on StreamReader's line limit."""
    parts: list[bytes] = []
    size = 0
    async with asyncio.timeout(max(0.001, timeout_s)):
        while True:
            try:
                part = await reader.readuntil(b"\n")
            except asyncio.LimitOverrunError as exc:
                # Consume only this frame's known non-delimiter prefix. Bytes
                # belonging to a subsequent frame remain in the reader.
                part = await reader.readexactly(min(exc.consumed, max_bytes - size + 1))
                size += len(part)
                if size > max_bytes:
                    raise PersistentVerifierFrameError(
                        "persistent verifier message exceeds byte limit", "transport_oversized"
                    ) from exc
                parts.append(part)
                continue
            except asyncio.IncompleteReadError as exc:
                if size or exc.partial:
                    raise PersistentVerifierFrameError(
                        "persistent verifier message ended before newline", "transport_truncated"
                    ) from exc
                raise PersistentVerifierError("persistent verifier worker closed stdout") from exc
            size += len(part)
            if size > max_bytes:
                raise PersistentVerifierFrameError(
                    "persistent verifier message exceeds byte limit", "transport_oversized"
                )
            parts.append(part)
            return b"".join(parts)


def _process_tree_rss_bytes(pid: int) -> int:
    """Read resident memory for the owned worker and its Lean descendants."""
    total = 0
    pending = [pid]
    seen: set[int] = set()
    while pending:
        child = pending.pop()
        if child in seen:
            continue
        seen.add(child)
        try:
            total += int(Path(f"/proc/{child}/statm").read_text().split()[1]) * os.sysconf("SC_PAGE_SIZE")
            pending.extend(int(value) for value in Path(f"/proc/{child}/task/{child}/children").read_text().split())
        except (OSError, ValueError, IndexError):
            continue
    return total


class PersistentVerifierFatalError(PersistentVerifierError):
    def __init__(self, response: VerifierResponse, failure_kind: str):
        super().__init__(str(response.output or failure_kind or "persistent verifier fatal"))
        self.response = response
        self.failure_kind = str(failure_kind or "fatal")
        self.response.failure_kind = self.failure_kind


class PersistentVerifierWorker:
    def __init__(
        self,
        cfg: LeanConfig,
        worker_index: int,
        *,
        queue_class: str = "main",
    ):
        self.cfg = cfg
        self.worker_index = int(worker_index)
        # Workers are tagged with the queue class they serve so the
        # pool can route requests and re-queue workers to the correct
        # sub-pool. Default "main" preserves backward compatibility
        # for existing tests that construct workers directly.
        self.queue_class = str(queue_class or "main")
        # worker_id includes the class so oracle and main workers are
        # distinguishable in logs/stats without colliding on indices.
        if self.queue_class == "main":
            self.worker_id = f"worker-{self.worker_index + 1:04d}"
        else:
            self.worker_id = (
                f"worker-{self.queue_class}-{self.worker_index + 1:04d}"
            )
        self.project_dir = Path(cfg.project_dir).resolve()
        self.repo_root = Path(__file__).resolve().parents[1]
        scratch_root = _resolve_lean_scratch_root(cfg)
        self.temp_root = scratch_root / ".persistent_verifier" / self.worker_id
        self.temp_root.mkdir(parents=True, exist_ok=True)
        self.generation: int = 0
        self.session_id: str = ""
        self.state: str = "cold"
        self._proc: Optional[asyncio.subprocess.Process] = None
        self._stderr_task: Optional[asyncio.Task[None]] = None
        self._lock = asyncio.Lock()
        self._requests_served: int = 0
        self._transport_startups: int = 0
        self._transport_startup_failures: int = 0
        self._transport_handshake_failures: int = 0
        self._transport_requests: int = 0
        self._transport_completions: int = 0
        self._transport_failures: int = 0
        self._transport_fatals: int = 0
        self._transport_timeouts: int = 0
        self._transport_stale_messages: int = 0
        self._transport_protocol_errors: int = 0
        self._transport_restarts: int = 0
        self._transport_shutdown_failures: int = 0
        self._transport_queue_wait_s: float = 0.0
        self._transport_service_time_s: float = 0.0
        self._worker_crashes: int = 0
        self._worker_timeouts: int = 0
        self._worker_protocol_failures: int = 0
        self._worker_recycles: int = 0
        self._worker_cancellations: int = 0
        self._stderr_tail = b""
        # Document-family affinity only; exact audited identities remain in
        # each request and response and never authorize a result from this LRU.
        self._context_keys: OrderedDict[str, None] = OrderedDict()
        self._rss_bytes = 0

    def _message_envelope(self, msg_type: str) -> Dict[str, Any]:
        return {
            "protocol": PERSISTENT_VERIFIER_PROTOCOL,
            "version": PERSISTENT_VERIFIER_VERSION,
            "type": str(msg_type or ""),
            "worker_id": self.worker_id,
            "worker_generation": int(self.generation),
            "timestamp_unix_s": _timestamp_unix_s(),
        }

    def _message_matches_generation(self, msg: Dict[str, Any]) -> bool:
        return int(msg.get("worker_generation", -1)) == int(self.generation)

    async def _drain_stderr(self) -> None:
        proc = self._proc
        if proc is None or proc.stderr is None:
            return
        try:
            while True:
                chunk = await proc.stderr.read(8192)
                if not chunk:
                    break
                self._stderr_tail = (self._stderr_tail + chunk)[-STDERR_TAIL_BYTES:]
                text = chunk.decode(errors="replace").rstrip()
                if text:
                    logger.debug(
                        "Persistent verifier worker stderr [%s gen=%d]: %s",
                        self.worker_id,
                        self.generation,
                        text,
                    )
        except Exception:
            logger.debug(
                "Persistent verifier stderr drain failed for %s",
                self.worker_id,
                exc_info=True,
            )

    async def _send_message(self, payload: Dict[str, Any]) -> None:
        proc = self._proc
        if proc is None or proc.stdin is None:
            raise PersistentVerifierError("persistent verifier worker stdin unavailable")
        body = (json.dumps(payload, separators=(",", ":"), ensure_ascii=False) + "\n").encode("utf-8")
        if len(body) > int(getattr(self.cfg, "persistent_max_message_bytes", DEFAULT_MAX_MESSAGE_BYTES)):
            raise PersistentVerifierFrameError("persistent verifier request exceeds byte limit", "transport_oversized")
        proc.stdin.write(body)
        await proc.stdin.drain()

    async def _read_message(self, timeout_s: float) -> Dict[str, Any]:
        proc = self._proc
        if proc is None or proc.stdout is None:
            raise PersistentVerifierError("persistent verifier worker stdout unavailable")
        raw = await read_bounded_json_line(
            proc.stdout,
            max_bytes=int(getattr(self.cfg, "persistent_max_message_bytes", DEFAULT_MAX_MESSAGE_BYTES)),
            timeout_s=timeout_s,
        )
        if not raw:
            rc = proc.returncode if proc.returncode is not None else "unknown"
            raise PersistentVerifierError(
                f"persistent verifier worker exited before reply (returncode={rc})"
            )
        try:
            msg = json.loads(raw.decode("utf-8"))
        except Exception as exc:
            self._transport_protocol_errors += 1
            raise PersistentVerifierFrameError(
                "invalid persistent verifier JSON", "transport_malformed"
            ) from exc
        if not isinstance(msg, dict):
            self._transport_protocol_errors += 1
            raise PersistentVerifierFrameError("persistent verifier message must be a JSON object", "transport_malformed")
        if type(msg.get("worker_generation")) is not int:
            raise PersistentVerifierFrameError("persistent verifier generation must be an integer", "transport_malformed")
        if str(msg.get("protocol", "")) != PERSISTENT_VERIFIER_PROTOCOL:
            self._transport_protocol_errors += 1
            raise PersistentVerifierFrameError(
                "unexpected persistent verifier protocol", "protocol_desync"
            )
        if _protocol_major(str(msg.get("version", ""))) != _protocol_major(
            PERSISTENT_VERIFIER_VERSION
        ):
            self._transport_protocol_errors += 1
            raise PersistentVerifierFrameError(
                "unexpected persistent verifier version", "protocol_desync"
            )
        if str(msg.get("worker_id", "")) != self.worker_id:
            self._transport_protocol_errors += 1
            raise PersistentVerifierFrameError(
                "unexpected persistent verifier worker id", "protocol_desync"
            )
        return msg

    async def _kill_process(self) -> None:
        proc = self._proc
        stderr_task = self._stderr_task
        self._proc = None
        self._stderr_task = None
        self._context_keys.clear()
        self._rss_bytes = 0
        if proc is None:
            return
        await terminate_and_reap_process(
            proc,
            auxiliary_tasks=(stderr_task,) if stderr_task is not None else (),
            kill_process_group=True,
            log=logger,
        )

    async def start(self) -> bool:
        async with self._lock:
            policy_id = current_network_policy().policy_id
            if (self._proc is not None and self.state in {"idle", "busy"}
                    and getattr(self._proc, "returncode", None) is None
                    and getattr(self, "_network_policy_id", None) == policy_id):
                # Only a subprocess that is still running counts as healthy.
                # A worker whose child exited (returncode set) falls through
                # and is rebuilt, because the next write would otherwise fail
                # with a broken-pipe transport error.
                return True
            await self._kill_process()
            self.generation += 1
            self.session_id = ""
            self.state = "starting"
            self.temp_root.mkdir(parents=True, exist_ok=True)
            self._transport_startups += 1
            logger.info(
                "Persistent verifier worker starting: %s gen=%d",
                self.worker_id,
                self.generation,
            )
            try:
                proc = await asyncio.create_subprocess_exec(
                    sys.executable,
                    "-m",
                    "ensemble_prover.persistent_verifier_worker",
                    "--worker-id",
                    self.worker_id,
                    "--generation",
                    str(self.generation),
                    cwd=str(self.repo_root),
                    stdin=asyncio.subprocess.PIPE,
                    stdout=asyncio.subprocess.PIPE,
                    stderr=asyncio.subprocess.PIPE,
                    start_new_session=True,
                    env=owned_worker_environment(
                        os.environ,
                        overrides={"PYTHONUNBUFFERED": "1"},
                    ),
                )
                self._proc = proc
                self._network_policy_id = policy_id
                self._stderr_task = asyncio.create_task(self._drain_stderr())
                hello = await self._read_message(
                    float(self.cfg.persistent_worker_start_timeout_s)
                )
                if not self._message_matches_generation(hello):
                    self._transport_stale_messages += 1
                    raise PersistentVerifierError("stale persistent verifier hello")
                if str(hello.get("type", "")) != "hello":
                    self._transport_handshake_failures += 1
                    raise PersistentVerifierError(
                        f"expected hello from persistent verifier worker, got {hello.get('type')!r}"
                    )
                self.session_id = str(hello.get("session_id", "") or "")
                if not self.session_id:
                    self._transport_handshake_failures += 1
                    raise PersistentVerifierError("persistent verifier hello missing session_id")
                await self._send_message(
                    {
                        **self._message_envelope("initialize"),
                        "session_id": self.session_id,
                        "project_dir": str(self.project_dir),
                        "temp_root": str(self.temp_root),
                        "startup_timeout_s": float(
                            self.cfg.persistent_worker_start_timeout_s
                        ),
                        "log_level": "INFO",
                        "max_message_bytes": int(getattr(self.cfg, "persistent_max_message_bytes", DEFAULT_MAX_MESSAGE_BYTES)),
                        "lsp_max_message_bytes": int(getattr(self.cfg, "persistent_lsp_max_message_bytes", 32 * 1024 * 1024)),
                        "context_slots": int(getattr(self.cfg, "persistent_context_slots", 4)),
                    }
                )
                while True:
                    msg = await self._read_message(
                        float(self.cfg.persistent_worker_start_timeout_s)
                    )
                    if not self._message_matches_generation(msg):
                        self._transport_stale_messages += 1
                        continue
                    msg_type = str(msg.get("type", "") or "")
                    if msg_type == "ready":
                        self.state = "idle"
                        self._requests_served = 0
                        logger.info(
                            "Persistent verifier worker ready: %s gen=%d",
                            self.worker_id,
                            self.generation,
                        )
                        return True
                    if msg_type == "fatal":
                        self._transport_handshake_failures += 1
                        raise PersistentVerifierError(
                            f"persistent verifier fatal during startup: {msg.get('output', '')}"
                        )
                    self._transport_protocol_errors += 1
                    raise PersistentVerifierError(
                        f"unexpected persistent verifier startup message: {msg_type!r}"
                    )
            except asyncio.CancelledError:
                self._transport_startup_failures += 1
                self.state = "poisoned"
                try:
                    await asyncio.shield(self._kill_process())
                except BaseException:
                    pass
                raise
            except Exception:
                self._transport_startup_failures += 1
                self.state = "poisoned"
                await self._kill_process()
                logger.warning(
                    "Persistent verifier worker failed to start: %s gen=%d",
                    self.worker_id,
                    self.generation,
                    exc_info=True,
                )
                return False

    async def restart(self) -> bool:
        self._transport_restarts += 1
        self.state = "restarting"
        await self._kill_process()
        return await self.start()

    def needs_recycle(self) -> bool:
        limit = int(getattr(self.cfg, "persistent_max_requests_per_worker", 200) or 200)
        rss_limit = int(getattr(self.cfg, "persistent_context_max_rss_mb", 16384)) * 1024 * 1024
        return (limit > 0 and self._requests_served >= limit) or (rss_limit > 0 and self._rss_bytes > rss_limit)

    def reset_stats(self) -> None:
        self._transport_startups = 0
        self._transport_startup_failures = 0
        self._transport_handshake_failures = 0
        self._transport_requests = 0
        self._transport_completions = 0
        self._transport_failures = 0
        self._transport_fatals = 0
        self._transport_timeouts = 0
        self._transport_stale_messages = 0
        self._transport_protocol_errors = 0
        self._transport_restarts = 0
        self._transport_shutdown_failures = 0
        self._transport_queue_wait_s = 0.0
        self._transport_service_time_s = 0.0
        self._worker_crashes = 0
        self._worker_timeouts = 0
        self._worker_protocol_failures = 0
        self._worker_recycles = 0
        self._worker_cancellations = 0
        self._requests_served = 0

    def _transport_failure_response(
        self,
        request: VerifierRequest,
        output: str,
        *,
        partial_output: str,
        queue_wait_s: float,
    ) -> VerifierResponse:
        """Build the bounded fatal response for a dead or unwritable worker.

        Transport failures are reported to the pool as a fatal response so the
        pool-owned restart path rebuilds the worker (or the caller falls back)
        instead of an opaque exception escaping and leaving the worker stuck
        in ``busy``.
        """

        return VerifierResponse(
            request_id=str(request.request_id),
            ok=False,
            returncode=1,
            output=_status_with_output(output, partial_output),
            backend_kind="persistent_process",
            worker_id=self.worker_id,
            worker_generation=int(self.generation),
            service_time_s=0.0,
            queue_wait_s=float(queue_wait_s),
        )

    async def execute(
        self,
        request: VerifierRequest,
        *,
        queue_wait_s: float = 0.0,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> VerifierResponse:
        async with self._lock:
            if (
                self._proc is None
                or self.state not in {"idle", "busy"}
                or getattr(self._proc, "returncode", None) is not None
            ):
                # The worker's subprocess is missing or already dead, so it
                # cannot serve this request. Do NOT call self.start() here:
                # self._lock is held and start() re-acquires it, which would
                # deadlock. Instead surface a bounded fatal so the pool-owned
                # restart path rebuilds this worker and the caller falls back.
                response = self._transport_failure_response(
                    request,
                    "persistent verifier worker is not running",
                    partial_output="",
                    queue_wait_s=queue_wait_s,
                )
                self.state = "poisoned"
                if self._proc is not None:
                    self._worker_crashes += 1
                await self._kill_process()
                raise PersistentVerifierFatalError(response, "lean_backend_crash")
            self.state = "busy"
            try:
                return await self._execute_locked(
                    request,
                    queue_wait_s=queue_wait_s,
                    dispatch_observer=dispatch_observer,
                )
            except asyncio.CancelledError:
                # Caller cancellation reached us mid-execute. The Lean
                # compilation cannot be interrupted in-process
                # (supports_cancel: False — see persistent_verifier_worker.py),
                # so the subprocess is now in an indeterminate state
                # with potentially unconsumed reply bytes for the
                # cancelled request. A later caller on this same worker
                # could read stale replies and protocol-desync.
                # Kill the subprocess and mark the worker poisoned so
                # the pool layer rebuilds or recycles it instead of
                # re-queuing a dirty worker.
                self._worker_cancellations += 1
                self.state = "poisoned"
                # Shield the kill from re-cancellation so a second
                # cancel arriving mid-cleanup cannot leave us with a
                # live subprocess and stderr task.
                try:
                    await asyncio.shield(self._kill_process())
                except BaseException:
                    # Swallow any cleanup failure — the original
                    # CancelledError is what we must propagate.
                    pass
                raise

    async def _execute_locked(
        self,
        request: VerifierRequest,
        *,
        queue_wait_s: float = 0.0,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> VerifierResponse:
        """Run one request assuming the caller holds self._lock and has
        already set self.state = 'busy'. Extracted so the outer execute
        can wrap it in a BaseException handler that survives caller
        cancellation without polluting the subprocess state."""
        partial_output = ""
        started = time.monotonic()
        self._transport_requests += 1
        self._transport_queue_wait_s += float(queue_wait_s)
        total_timeout_s = float(request.timeout_s) + float(
            getattr(self.cfg, "persistent_request_timeout_buffer_s", 2.0) or 2.0
        )
        if total_timeout_s <= 0.0:
            total_timeout_s = 1.0
        try:
            await self._send_message(
                {
                    **self._message_envelope("check"),
                    "session_id": self.session_id,
                    "request_id": str(request.request_id),
                    "mode": str(request.mode),
                    "goal_name": str(request.goal_name),
                    "document_uri": str(request.document_uri),
                    "content": str(request.content),
                    "warning_as_error": bool(request.warning_as_error),
                    "max_heartbeats": request.max_heartbeats,
                    "timeout_s": float(request.timeout_s),
                    "queue_class": str(request.queue_class),
                    "metadata": dict(request.metadata or {}),
                }
            )
        except Exception as exc:
            # The subprocess can die between the liveness check and this write
            # (or its stdin pipe can already be broken). Convert that transport
            # failure into the same bounded fatal used for a mid-request crash
            # so the pool restarts the worker rather than leaving it busy with
            # a stale request queued behind it.
            self._worker_crashes += 1
            self.state = "poisoned"
            response = self._transport_failure_response(
                request,
                "persistent verifier worker transport failed before dispatch",
                partial_output=partial_output,
                queue_wait_s=queue_wait_s,
            )
            await self._kill_process()
            raise PersistentVerifierFatalError(response, getattr(exc, "failure_kind", "lean_backend_crash"))
        if dispatch_observer is not None:
            try:
                dispatch_observer()
            except Exception:
                pass
        while True:
            remaining_s = total_timeout_s - (time.monotonic() - started)
            if remaining_s <= 0.0:
                self._transport_timeouts += 1
                self._worker_timeouts += 1
                self.state = "poisoned"
                response = VerifierResponse(
                    request_id=str(request.request_id),
                    ok=False,
                    returncode=1,
                    output=_status_with_output("Lean timeout", partial_output),
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=max(0.0, time.monotonic() - started),
                    queue_wait_s=float(queue_wait_s),
                )
                await self._kill_process()
                raise PersistentVerifierFatalError(response, "timeout_poison")
            try:
                msg = await self._read_message(remaining_s)
            except asyncio.TimeoutError:
                self._transport_timeouts += 1
                self._worker_timeouts += 1
                self.state = "poisoned"
                response = VerifierResponse(
                    request_id=str(request.request_id),
                    ok=False,
                    returncode=1,
                    output=_status_with_output("Lean timeout", partial_output),
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=max(0.0, time.monotonic() - started),
                    queue_wait_s=float(queue_wait_s),
                )
                await self._kill_process()
                raise PersistentVerifierFatalError(response, "timeout_poison")
            except Exception as exc:
                failure_kind = getattr(exc, "failure_kind", "lean_backend_crash")
                if isinstance(exc, PersistentVerifierFrameError):
                    self._worker_protocol_failures += 1
                    self._transport_protocol_errors += 1
                else:
                    self._worker_crashes += 1
                self.state = "poisoned"
                response = VerifierResponse(
                    request_id=str(request.request_id),
                    ok=False,
                    returncode=1,
                    output=_status_with_output(
                        str(exc) if isinstance(exc, PersistentVerifierFrameError) else "persistent verifier worker crashed",
                        partial_output,
                    ),
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=max(0.0, time.monotonic() - started),
                    queue_wait_s=float(queue_wait_s),
                )
                await self._kill_process()
                raise PersistentVerifierFatalError(response, failure_kind)
            if not self._message_matches_generation(msg):
                self._transport_stale_messages += 1
                continue
            msg_type = str(msg.get("type", "") or "")
            scoped_request_id = str(msg.get("request_id", "") or "")
            if msg_type in {"accepted", "diagnostics", "completed", "failed", "fatal"}:
                if scoped_request_id != str(request.request_id):
                    self._worker_protocol_failures += 1
                    self._transport_protocol_errors += 1
                    self.state = "poisoned"
                    response = VerifierResponse(
                        request_id=str(request.request_id),
                        ok=False,
                        returncode=1,
                        output="persistent verifier protocol desynchronization detected",
                        backend_kind="persistent_process",
                        worker_id=self.worker_id,
                        worker_generation=int(self.generation),
                        service_time_s=max(0.0, time.monotonic() - started),
                        queue_wait_s=float(queue_wait_s),
                    )
                    await self._kill_process()
                    raise PersistentVerifierFatalError(response, "protocol_desync")
            if msg_type == "accepted":
                continue
            if msg_type == "diagnostics":
                partial_output = str(msg.get("partial_output", "") or partial_output)
                continue
            if msg_type == "completed":
                if (request.metadata or {}).get("stable_context") and (
                    msg.get("request_completed") is not True
                    or type(msg.get("document_version")) is not int
                    or msg["document_version"] <= 0
                    or msg.get("context_key") != (request.metadata or {}).get("context_key")
                    or ((request.metadata or {}).get("context_family_key") is not None
                        and msg.get("context_family_key") != request.metadata["context_family_key"])
                ):
                    self.state = "poisoned"
                    response = self._transport_failure_response(request, "persistent verifier omitted versioned context completion", partial_output="", queue_wait_s=queue_wait_s)
                    await self._kill_process()
                    raise PersistentVerifierFatalError(response, "protocol_desync")
                response = VerifierResponse(
                    request_id=str(request.request_id),
                    ok=bool(msg.get("ok", False)),
                    returncode=int(msg.get("returncode", 1)),
                    output=str(msg.get("output", "") or ""),
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=float(
                        msg.get("service_time_s", time.monotonic() - started) or 0.0
                    ),
                    queue_wait_s=float(queue_wait_s),
                    runtime_status="",
                    document_version=int(msg.get("document_version", 0)),
                    context_key=str(msg.get("context_key", "")),
                    context_family_key=str(msg.get("context_family_key", "")),
                    request_completed=msg.get("request_completed") is True,
                )
                self.state = str(msg.get("worker_state_after", "idle") or "idle")
                self._transport_completions += 1
                self._transport_service_time_s += max(0.0, response.service_time_s)
                self._requests_served += 1
                context_family_key = str((request.metadata or {}).get(
                    "context_family_key", (request.metadata or {}).get("context_key", ""),
                ))
                if context_family_key and (request.metadata or {}).get("stable_context"):
                    self._context_keys[context_family_key] = None
                    self._context_keys.move_to_end(context_family_key)
                    while len(self._context_keys) > max(1, int(getattr(self.cfg, "persistent_context_slots", 4))):
                        self._context_keys.popitem(last=False)
                if self._proc is not None and getattr(self._proc, "pid", None):
                    self._rss_bytes = _process_tree_rss_bytes(self._proc.pid)
                return response
            if msg_type == "failed":
                response = VerifierResponse(
                    request_id=str(request.request_id),
                    ok=False,
                    returncode=int(msg.get("returncode", 1)),
                    output=str(msg.get("output", "") or ""),
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=max(0.0, time.monotonic() - started),
                    queue_wait_s=float(queue_wait_s),
                    failure_kind=str(msg.get("failure_kind", "") or ""),
                )
                self.state = str(msg.get("worker_state_after", "idle") or "idle")
                self._transport_failures += 1
                self._transport_service_time_s += max(0.0, response.service_time_s)
                self._requests_served += 1
                return response
            if msg_type == "fatal":
                response = VerifierResponse(
                    request_id=str(request.request_id),
                    ok=False,
                    returncode=int(msg.get("returncode", 1)),
                    output=str(msg.get("output", "") or ""),
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=max(0.0, time.monotonic() - started),
                    queue_wait_s=float(queue_wait_s),
                )
                self.state = "poisoned"
                self._transport_fatals += 1
                self._transport_service_time_s += max(0.0, response.service_time_s)
                self._requests_served += 1
                failure_kind = str(msg.get("failure_kind", "") or "fatal")
                if failure_kind == "timeout_poison":
                    self._worker_timeouts += 1
                elif failure_kind in {
                    "protocol_desync",
                    "worker_internal_corruption",
                    "unrecoverable_transport_error",
                }:
                    self._worker_protocol_failures += 1
                else:
                    self._worker_crashes += 1
                await self._kill_process()
                raise PersistentVerifierFatalError(response, failure_kind)
            self._worker_protocol_failures += 1
            self._transport_protocol_errors += 1
            self.state = "poisoned"
            await self._kill_process()
            raise PersistentVerifierFatalError(
                VerifierResponse(
                    request_id=str(request.request_id),
                    ok=False,
                    returncode=1,
                    output=f"unexpected persistent verifier message: {msg_type!r}",
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=max(0.0, time.monotonic() - started),
                    queue_wait_s=float(queue_wait_s),
                ),
                "protocol_desync",
            )

    async def close(self) -> None:
        async with self._lock:
            proc = self._proc
            if proc is None:
                self.state = "closed"
                return
            try:
                if proc.stdin is not None and proc.stdout is not None:
                    await self._send_message(
                        {
                            **self._message_envelope("shutdown"),
                            "session_id": self.session_id,
                        }
                    )
                    deadline = time.monotonic() + 1.5
                    while time.monotonic() < deadline:
                        msg = await self._read_message(max(0.1, deadline - time.monotonic()))
                        if not self._message_matches_generation(msg):
                            self._transport_stale_messages += 1
                            continue
                        if str(msg.get("type", "") or "") == "shutdown_ack":
                            break
            except Exception:
                self._transport_shutdown_failures += 1
            finally:
                await self._kill_process()
                self.state = "closed"
                try:
                    shutil.rmtree(self.temp_root, ignore_errors=True)
                except Exception:
                    pass

    def close_nowait(self) -> None:
        proc = self._proc
        self._proc = None
        if proc is not None:
            request_process_termination_nowait(
                proc,
                kill_process_group=True,
                log=logger,
            )
        if self._stderr_task is not None:
            self._stderr_task.cancel()
            self._stderr_task = None
        self.state = "closed"
        try:
            shutil.rmtree(self.temp_root, ignore_errors=True)
        except Exception:
            pass

    def stats(self) -> Dict[str, Any]:
        return {
            "persistent_transport_startups": int(self._transport_startups),
            "persistent_transport_startup_failures": int(
                self._transport_startup_failures
            ),
            "persistent_transport_handshake_failures": int(
                self._transport_handshake_failures
            ),
            "persistent_transport_requests": int(self._transport_requests),
            "persistent_transport_completions": int(self._transport_completions),
            "persistent_transport_failures": int(self._transport_failures),
            "persistent_transport_fatals": int(self._transport_fatals),
            "persistent_transport_timeouts": int(self._transport_timeouts),
            "persistent_transport_stale_messages": int(
                self._transport_stale_messages
            ),
            "persistent_transport_protocol_errors": int(
                self._transport_protocol_errors
            ),
            "persistent_transport_restarts": int(self._transport_restarts),
            "persistent_transport_shutdown_failures": int(
                self._transport_shutdown_failures
            ),
            "persistent_transport_queue_wait_s": float(self._transport_queue_wait_s),
            "persistent_transport_service_time_s": float(
                self._transport_service_time_s
            ),
            "persistent_worker_crashes": int(self._worker_crashes),
            "persistent_worker_timeouts": int(self._worker_timeouts),
            "persistent_worker_protocol_failures": int(
                self._worker_protocol_failures
            ),
            "persistent_worker_recycles": int(self._worker_recycles),
            "persistent_worker_cancellations": int(self._worker_cancellations),
            "persistent_requests_served": int(self._requests_served),
            "state": str(self.state),
        }


class _LaneWorkerQueue(asyncio.Queue[PersistentVerifierWorker]):
    """Worker queue that signals lane-state changes to queued callers.

    ``put_nowait`` is the single funnel for every requeue (``put`` delegates
    to it), so setting ``changed`` here wakes parked callers whenever a worker
    becomes available, regardless of whether the pool or a test put it there.
    Terminal lane transitions set the same event directly so a caller waiting
    out a recovery that then failed can re-check and fall back promptly.
    """

    def __init__(self) -> None:
        super().__init__()
        self.changed: asyncio.Event = asyncio.Event()

    def put_nowait(self, item: PersistentVerifierWorker) -> None:
        super().put_nowait(item)
        self.changed.set()


class PersistentVerifierPool:
    def __init__(self, cfg: LeanConfig):
        self.cfg = cfg
        self.project_dir = Path(cfg.project_dir).resolve()
        # Retain worker_count as the main-worker count for compatibility with
        # callers that read statistics or configure the pool directly.
        self.main_worker_count = max(1, int(cfg.persistent_workers or 1))
        # Oracle sub-pool: reserved for requests tagged with
        # queue_class="oracle" (tactic oracle calls like exact?/apply?)
        # so oracle bursts do not starve main proof checks at the
        # worker-pool layer. If 0, the pool runs in single-queue
        # legacy mode and oracle requests share the main queue.
        self.oracle_worker_count = max(
            0, int(getattr(cfg, "persistent_oracle_workers", 0) or 0)
        )
        self.worker_count = self.main_worker_count + self.oracle_worker_count
        self._workers_main = [
            PersistentVerifierWorker(cfg, idx, queue_class="main")
            for idx in range(self.main_worker_count)
        ]
        self._workers_oracle = [
            PersistentVerifierWorker(
                cfg, self.main_worker_count + idx, queue_class="oracle"
            )
            for idx in range(self.oracle_worker_count)
        ]
        self._workers = self._workers_main + self._workers_oracle
        # Main queue. Kept as `_available` (not `_available_main`) so
        # existing callers and tests that touch pool._available
        # directly continue to work.
        self._available: asyncio.Queue[PersistentVerifierWorker] = _LaneWorkerQueue()
        self._available_oracle: Optional[asyncio.Queue[PersistentVerifierWorker]] = (
            _LaneWorkerQueue() if self.oracle_worker_count > 0 else None
        )
        self._started = False
        self._closing = False
        self._background_tasks: set[asyncio.Task[Any]] = set()
        self._start_lock = asyncio.Lock()
        self._request_count: int = 0
        self._success_count: int = 0
        self._failure_count: int = 0
        self._fallback_count: int = 0
        self._queue_wait_total_s: float = 0.0
        self._queue_wait_max_s: float = 0.0
        self._service_time_total_s: float = 0.0
        self._service_time_max_s: float = 0.0
        self._restart_elapsed_s: float = 0.0
        self._restarts_active: int = 0
        # Per-lane count of workers currently checked out of a sub-pool
        # queue (busy serving a request or being restarted). A lane with
        # a non-zero count can still put a worker back on its queue; a
        # lane at zero whose queue is empty cannot, so a request for it
        # must fail through the unavailable/fallback path instead of
        # waiting out the queue timeout. Keyed by lane name ("main" or
        # "oracle") so both sub-pools are tracked independently.
        self._lane_inflight: Dict[str, int] = {"main": 0, "oracle": 0}
        # Per-class request counters for telemetry — surface through
        # pool.stats() so operators can verify separation in prod.
        self._request_count_main: int = 0
        self._request_count_oracle: int = 0
        self._transport_consecutive_failures = 0
        self._transport_failure_counts: OrderedDict[tuple[str, str], int] = OrderedDict()
        self._transport_circuit_open_until = 0.0
        self._transport_circuit_reason = ""

    def _record_transport_failure(self, failure_kind: str, scope: str = "") -> None:
        if failure_kind not in {"transport_oversized", "transport_truncated", "transport_malformed", "protocol_desync", "lean_backend_crash", "startup_failure", "completion_unavailable"}:
            return
        key = (scope, failure_kind)
        self._transport_failure_counts[key] = self._transport_failure_counts.get(key, 0) + 1
        self._transport_failure_counts.move_to_end(key)
        while len(self._transport_failure_counts) > 64:
            self._transport_failure_counts.popitem(last=False)
        self._transport_consecutive_failures = max(self._transport_failure_counts.values())
        threshold = max(1, int(getattr(self.cfg, "persistent_transport_failure_threshold", 2)))
        if self._transport_consecutive_failures >= threshold:
            self._transport_circuit_open_until = time.monotonic() + max(0.0, float(getattr(self.cfg, "persistent_transport_circuit_cooldown_s", 60.0)))
            self._transport_circuit_reason = failure_kind

    @staticmethod
    def _take_available_worker(source_queue: "asyncio.Queue[PersistentVerifierWorker]", context_key: str) -> PersistentVerifierWorker:
        workers = []
        for _ in range(source_queue.qsize()):
            workers.append(source_queue.get_nowait())
        if not workers:
            raise asyncio.QueueEmpty
        selected = next((worker for worker in workers if context_key and context_key in getattr(worker, "_context_keys", {})), workers[0])
        for worker in workers:
            if worker is not selected:
                source_queue.put_nowait(worker)
        return selected

    def _target_queue_for(
        self, worker: PersistentVerifierWorker
    ) -> "asyncio.Queue[PersistentVerifierWorker]":
        """Return the queue a worker should be re-queued to after a
        request completes. Falls back to the main queue for workers
        whose queue_class attribute is missing (legacy fake workers
        in existing tests) or when no oracle sub-pool exists."""
        worker_class = getattr(worker, "queue_class", "main")
        if worker_class == "oracle" and self._available_oracle is not None:
            return self._available_oracle
        return self._available

    def _pick_request_queue(
        self, queue_class: str
    ) -> "asyncio.Queue[PersistentVerifierWorker]":
        """Return the queue to pull a worker from for a given request
        class. Oracle requests fall back to the main queue when no
        oracle sub-pool is configured (legacy / persistent_oracle_workers=0)."""
        if queue_class == "oracle" and self._available_oracle is not None:
            return self._available_oracle
        return self._available

    def _lane_name_for_queue(
        self, queue: "asyncio.Queue[PersistentVerifierWorker]"
    ) -> str:
        """Map a sub-pool queue to its lane name.

        Routing, worker re-queue, and in-flight accounting all have to
        agree on a single label per sub-pool, so the label is derived
        from queue identity rather than from a caller-supplied string.
        """
        if self._available_oracle is not None and queue is self._available_oracle:
            return "oracle"
        return "main"

    def _workers_in_lane(
        self, queue: "asyncio.Queue[PersistentVerifierWorker]"
    ) -> list[PersistentVerifierWorker]:
        if self._available_oracle is not None and queue is self._available_oracle:
            return self._workers_oracle
        return self._workers_main

    def _reserve_lane_slot(
        self, queue: "asyncio.Queue[PersistentVerifierWorker]"
    ) -> str:
        """Record that a worker was checked out of *queue*'s lane.

        The slot is held until that worker is back on a queue (or has
        been closed), which lets :meth:`_lane_may_supply_worker` tell a
        lane with work in flight apart from a lane that has genuinely
        run dry.
        """
        lane = self._lane_name_for_queue(queue)
        self._lane_inflight[lane] = int(self._lane_inflight.get(lane, 0)) + 1
        return lane

    def _queue_for_lane(
        self, lane: str
    ) -> "asyncio.Queue[PersistentVerifierWorker]":
        """Return the sub-pool queue that serves *lane*.

        Inverse of :meth:`_lane_name_for_queue`, so lane accounting can reach
        the queue whose parked callers must re-check availability.
        """
        if lane == "oracle" and self._available_oracle is not None:
            return self._available_oracle
        return self._available

    def _notify_lane_changed(self, lane: str) -> None:
        """Wake callers parked on *lane*'s queue to re-check availability."""
        changed = getattr(self._queue_for_lane(lane), "changed", None)
        if changed is not None:
            changed.set()

    def _release_lane_slot(self, lane: str) -> None:
        remaining = int(self._lane_inflight.get(lane, 0)) - 1
        self._lane_inflight[lane] = remaining if remaining > 0 else 0
        # Wake any caller parked on this lane: the release either requeued the
        # worker first (the queue's own put already signalled) or the lane is
        # now terminal, and a waiting caller must re-check rather than sleep
        # until the lane timeout.
        self._notify_lane_changed(lane)

    def _lane_may_supply_worker(
        self, queue: "asyncio.Queue[PersistentVerifierWorker]"
    ) -> bool:
        """Return True when a worker could still arrive on *queue*.

        A lane can still deliver a worker while one of its workers is
        checked out: a busy worker is re-queued on completion and a
        restarted worker is re-queued once recovery settles. A lane
        whose workers are idle-but-unqueued, dead, poisoned, or cold has
        no pending recovery, so waiting on its empty queue only burns
        the caller's deadline. A closing pool never re-queues.
        """
        if self._closing:
            return False
        lane = self._lane_name_for_queue(queue)
        if int(self._lane_inflight.get(lane, 0)) > 0:
            return True
        # Also honor workers explicitly marked busy or mid-recovery even
        # if their checkout was not tracked here (for example a caller
        # that sets state directly); each of these can plausibly put a
        # worker back on this lane.
        for worker in self._workers_in_lane(queue):
            if str(getattr(worker, "state", "") or "") in {
                "busy",
                "restarting",
                "starting",
            }:
                return True
        return False

    async def _restart_and_requeue_worker(
        self,
        worker: PersistentVerifierWorker,
        target_queue: "asyncio.Queue[PersistentVerifierWorker]",
    ) -> None:
        started = time.monotonic()
        self._restarts_active += 1
        try:
            try:
                restarted = await worker.restart()
            except BaseException:
                restarted = False
            if restarted and not self._closing and self._started:
                await target_queue.put(worker)
            elif restarted:
                await self._close_worker_best_effort(worker)
            elif not self._closing:
                # Recovery failed: the worker cannot serve this lane unless a
                # later start() rebuilds it, so it must not keep the lane looking
                # recoverable. A worker left in a "starting"/"restarting" state
                # would hold queued callers until the lane timeout; mark it
                # terminal so the done callback below, which releases the lane
                # slot and wakes those callers, lets them fall back promptly. A
                # closing pool has already retired the worker, so leave its
                # terminal state alone.
                try:
                    worker.state = "poisoned"
                except Exception:
                    pass
        finally:
            # Recovery can outlive the caller and overlap other checks. Keep
            # its complete lifetime in backend maintenance telemetry without
            # adding it to action, startup, queue, or request-service totals.
            self._restart_elapsed_s += max(0.0, time.monotonic() - started)
            self._restarts_active -= 1

    async def _close_worker_best_effort(
        self, worker: PersistentVerifierWorker
    ) -> None:
        close = getattr(worker, "close", None)
        close_nowait = getattr(worker, "close_nowait", None)
        try:
            if callable(close):
                await close()
            elif callable(close_nowait):
                close_nowait()
        except BaseException:
            pass

    def _track_background_task(self, task: "asyncio.Task[Any]") -> None:
        self._background_tasks.add(task)
        task.add_done_callback(
            mark_runtime_owned_callback(self._background_tasks.discard)
        )
        task.add_done_callback(mark_runtime_owned_callback(_consume_task_exception))

    def _schedule_restart_and_requeue(
        self,
        worker: PersistentVerifierWorker,
        target_queue: "asyncio.Queue[PersistentVerifierWorker]",
    ) -> "asyncio.Task[None]":
        task = asyncio.create_task(
            self._restart_and_requeue_worker(worker, target_queue)
        )
        # The worker already holds a lane slot from checkout. Release it
        # only once the restart settles: on success the worker is back on
        # the queue before this callback runs, so a concurrent request
        # for the lane either finds the worker or keeps waiting rather
        # than failing while recovery is still in flight.
        lane = self._lane_name_for_queue(target_queue)
        changed = getattr(target_queue, "changed", None)
        if changed is None:
            changed = asyncio.Event()
        task.add_done_callback(
            mark_runtime_owned_callback(
                _lane_release_callback(self._lane_inflight, lane, changed)
            )
        )
        self._track_background_task(task)
        return task

    async def _acquire_worker(
        self,
        source_queue: "asyncio.Queue[PersistentVerifierWorker]",
        request_queue_class: str,
        context_key: str = "",
    ) -> PersistentVerifierWorker:
        """Wait for a worker without stranding a caller on a dead lane.

        The queue is polled with ``get_nowait`` rather than awaited directly:
        the successful dequeue and the caller's lane-slot reservation then
        happen in the same scheduling step (see ``execute``), so a competing
        request cannot observe an empty queue with no slot held. Between polls
        the caller parks on the lane queue's change event, set whenever a
        worker is queued or a lane slot is released. Re-checking availability
        after every wake lets a terminal transition -- a recovery that failed
        and left the lane with no worker and nothing in flight -- fail the
        caller promptly so its own fallback can run, instead of holding it
        until the lane timeout.
        """

        changed = getattr(source_queue, "changed", None)
        while True:
            try:
                return self._take_available_worker(source_queue, context_key)
            except asyncio.QueueEmpty:
                pass
            if not self._lane_may_supply_worker(source_queue):
                raise PersistentVerifierUnavailableError(
                    "no persistent verifier workers available for the "
                    f"{request_queue_class} lane"
                )
            if changed is None:
                # Plain-queue fallback (no change signal available): keep the
                # pre-existing single await, still bounded by the caller.
                return await source_queue.get()
            # Clear before re-checking so a signal raised between the poll
            # above and the wait below is never lost.
            changed.clear()
            try:
                return self._take_available_worker(source_queue, context_key)
            except asyncio.QueueEmpty:
                pass
            if not self._lane_may_supply_worker(source_queue):
                raise PersistentVerifierUnavailableError(
                    "no persistent verifier workers available for the "
                    f"{request_queue_class} lane"
                )
            try:
                async with asyncio.timeout(_LANE_CHANGE_POLL_S):
                    await changed.wait()
            except asyncio.TimeoutError:
                # Backstop for a terminal transition applied directly to lane
                # state rather than through the queue's change event.
                continue

    async def start(self) -> bool:
        self._closing = False
        if self._started and any(w.state in {"idle", "busy"} for w in self._workers):
            return True
        async with self._start_lock:
            if self._started and any(w.state in {"idle", "busy"} for w in self._workers):
                return True
            # Drain both queues before repopulating.
            for queue in (self._available, self._available_oracle):
                if queue is None:
                    continue
                while not queue.empty():
                    try:
                        queue.get_nowait()
                    except asyncio.QueueEmpty:
                        break
            started_any = False
            for worker in self._workers:
                ok = await worker.start()
                if ok:
                    await self._target_queue_for(worker).put(worker)
                    started_any = True
            self._started = started_any
            return started_any

    async def execute(
        self,
        request: VerifierRequest,
        *,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> VerifierResponse:
        operation_started = time.monotonic()
        if operation_started < self._transport_circuit_open_until:
            raise PersistentVerifierUnavailableError(f"persistent transport circuit open: {self._transport_circuit_reason}")
        try:
            async with asyncio.timeout(max(0.001, request.timeout_s)):
                started = await self.start()
        except asyncio.TimeoutError as exc:
            self._record_transport_failure("startup_failure")
            raise PersistentVerifierUnavailableError("persistent verifier startup exceeded request deadline") from exc
        if not started:
            self._record_transport_failure("startup_failure")
            raise PersistentVerifierUnavailableError(
                "persistent verifier pool unavailable"
            )
        queue_started = time.monotonic()
        startup_time_s = max(0.0, queue_started - operation_started)
        request_queue_class = str(
            getattr(request, "queue_class", "main") or "main"
        )
        source_queue = self._pick_request_queue(request_queue_class)
        remaining_s = request.timeout_s - (time.monotonic() - operation_started)
        if remaining_s <= 0:
            raise PersistentVerifierUnavailableError("persistent verifier request deadline exhausted during startup")
        lane_wait_s = min(remaining_s, max(1.0, float(self.cfg.persistent_worker_start_timeout_s)))
        try:
            async with asyncio.timeout(lane_wait_s):
                worker = await self._acquire_worker(
                    source_queue, request_queue_class,
                    str((request.metadata or {}).get("context_family_key", (request.metadata or {}).get("context_key", "")))
                    if (request.metadata or {}).get("stable_context") else "",
                )
        except asyncio.TimeoutError as exc:
            raise PersistentVerifierUnavailableError(
                "no persistent verifier workers became available"
            ) from exc
        queue_wait_s = max(0.0, time.monotonic() - queue_started)
        self._request_count += 1
        if request_queue_class == "oracle":
            self._request_count_oracle += 1
        else:
            self._request_count_main += 1
        self._queue_wait_total_s += queue_wait_s
        self._queue_wait_max_s = max(self._queue_wait_max_s, queue_wait_s)
        # Worker's own re-queue destination — determined by the
        # worker's queue_class, NOT by the request's queue_class.
        # This keeps sub-pools isolated: a main worker that picked
        # up an oracle request (only possible in single-queue legacy
        # mode) goes back to main, and an oracle worker always goes
        # back to oracle.
        target_queue = self._target_queue_for(worker)
        # Hold a slot on the lane this worker came from until it is back
        # on a queue or closed. While the slot is held, a concurrent
        # request routed to the same lane treats the lane as still able
        # to supply a worker.
        lane = self._reserve_lane_slot(target_queue)
        # Track pool ownership separately from worker state. Cancellation or
        # restart can leave a worker poisoned or starting; either state still
        # requires explicit cleanup and eventual requeue/replacement. Otherwise
        # a single-worker pool could lose its only worker and stall later requests.
        worker_owned = True

        try:
            remaining_s = request.timeout_s - (time.monotonic() - operation_started)
            if remaining_s <= 0:
                raise PersistentVerifierUnavailableError("persistent verifier request deadline exhausted in queue")
            response = await worker.execute(
                replace(request, timeout_s=remaining_s),
                queue_wait_s=queue_wait_s,
                **(
                    {"dispatch_observer": dispatch_observer}
                    if dispatch_observer is not None
                    else {}
                ),
            )
            response.startup_time_s = startup_time_s
            self._service_time_total_s += max(0.0, response.service_time_s)
            self._service_time_max_s = max(
                self._service_time_max_s, max(0.0, response.service_time_s)
            )
            if response.returncode == 0:
                self._success_count += 1
            else:
                self._failure_count += 1
            # A small source-admission success does not demonstrate that the
            # proof lane can carry a large audit result. Reset only the lane
            # whose complete response has actually succeeded.
            for key in list(self._transport_failure_counts):
                if key[0] == request.mode or key[1] == "startup_failure":
                    self._transport_failure_counts.pop(key)
            self._transport_consecutive_failures = max(self._transport_failure_counts.values(), default=0)
            if not self._transport_consecutive_failures:
                self._transport_circuit_reason = ""
            return response
        except PersistentVerifierFatalError as exc:
            response = exc.response
            response.startup_time_s = startup_time_s
            self._record_transport_failure(exc.failure_kind, request.mode)
            self._failure_count += 1
            self._service_time_total_s += max(0.0, response.service_time_s)
            self._service_time_max_s = max(
                self._service_time_max_s, max(0.0, response.service_time_s)
            )
            worker_owned = False
            cleanup_task = self._schedule_restart_and_requeue(worker, target_queue)
            try:
                # Recovery belongs to the pool; it must not consume a fresh
                # startup allowance before the caller can fund its fallback.
                async with asyncio.timeout(max(0.001, min(0.05, request.timeout_s - (time.monotonic() - operation_started)))):
                    await asyncio.shield(cleanup_task)
            except BaseException:
                pass
            return response
        except asyncio.CancelledError as cancel_exc:
            # Worker.execute's own cancellation handler has already
            # killed the subprocess and marked the worker as poisoned
            # (see PersistentVerifierWorker.execute). We must
            # restart the worker (fresh subprocess) rather than re-queue the
            # poisoned one. Run the restart in its own task so a second
            # cancellation of this caller cannot orphan the worker.
            worker_owned = False
            cleanup_task = self._schedule_restart_and_requeue(worker, target_queue)
            try:
                async with asyncio.timeout(0.05):
                    await asyncio.shield(cleanup_task)
            except (asyncio.CancelledError, asyncio.TimeoutError):
                pass
            raise cancel_exc
        finally:
            # Happy-path re-queue: if we still own the worker, it
            # finished successfully and should go back on the queue.
            # Fatal/cancel paths already handled their own cleanup.
            if worker_owned:
                if worker.needs_recycle():
                    worker._worker_recycles += 1
                    cleanup_task = self._schedule_restart_and_requeue(
                        worker,
                        target_queue,
                    )
                    try:
                        async with asyncio.timeout(0.05):
                            await asyncio.shield(cleanup_task)
                    except BaseException:
                        pass
                else:
                    if not self._closing and self._started:
                        await target_queue.put(worker)
                    else:
                        await self._close_worker_best_effort(worker)
                    # Released only after the worker is back on its queue
                    # (or closed) so no request can observe the lane as
                    # empty while this worker is still in transition.
                    self._release_lane_slot(lane)

    async def close(self) -> None:
        self._closing = True
        self._notify_lane_changed("main")
        self._notify_lane_changed("oracle")
        pending_tasks = [task for task in self._background_tasks if not task.done()]
        for task in pending_tasks:
            task.cancel()
        if pending_tasks:
            await asyncio.gather(*pending_tasks, return_exceptions=True)
        self._background_tasks.clear()
        for worker in self._workers:
            await worker.close()
        for queue in (self._available, self._available_oracle):
            if queue is None:
                continue
            while not queue.empty():
                try:
                    queue.get_nowait()
                except asyncio.QueueEmpty:
                    break
        self._started = False

    def close_nowait(self) -> None:
        self._closing = True
        self._notify_lane_changed("main")
        self._notify_lane_changed("oracle")
        for task in list(self._background_tasks):
            task.cancel()
        self._background_tasks.clear()
        for worker in self._workers:
            worker.close_nowait()
        for queue in (self._available, self._available_oracle):
            if queue is None:
                continue
            while not queue.empty():
                try:
                    queue.get_nowait()
                except asyncio.QueueEmpty:
                    break
        self._started = False

    def reset_stats(self) -> None:
        self._request_count = 0
        self._request_count_main = 0
        self._request_count_oracle = 0
        self._success_count = 0
        self._failure_count = 0
        self._fallback_count = 0
        self._queue_wait_total_s = 0.0
        self._queue_wait_max_s = 0.0
        self._service_time_total_s = 0.0
        self._service_time_max_s = 0.0
        self._restart_elapsed_s = 0.0
        for worker in self._workers:
            worker.reset_stats()

    def stats(self) -> Dict[str, Any]:
        worker_stats = [worker.stats() for worker in self._workers]
        idle_count = sum(1 for worker in self._workers if worker.state == "idle")
        busy_count = sum(1 for worker in self._workers if worker.state == "busy")
        stats: Dict[str, Any] = {
            "persistent_worker_count": int(self.worker_count),
            "persistent_worker_count_main": int(self.main_worker_count),
            "persistent_worker_count_oracle": int(self.oracle_worker_count),
            "persistent_worker_idle_count": int(idle_count),
            "persistent_worker_busy_count": int(busy_count),
            "persistent_worker_startups": 0,
            "persistent_worker_restarts": 0,
            "persistent_worker_crashes": 0,
            "persistent_worker_timeouts": 0,
            "persistent_worker_protocol_failures": 0,
            "persistent_worker_recycles": 0,
            "persistent_worker_cancellations": 0,
            "persistent_backend_requests": int(self._request_count),
            "persistent_backend_requests_main": int(self._request_count_main),
            "persistent_backend_requests_oracle": int(self._request_count_oracle),
            "persistent_backend_successes": int(self._success_count),
            "persistent_backend_failures": int(self._failure_count),
            "persistent_backend_fallbacks": int(self._fallback_count),
            "persistent_queue_wait_s_total": float(self._queue_wait_total_s),
            "persistent_queue_wait_s_max": float(self._queue_wait_max_s),
            "persistent_service_time_s_total": float(self._service_time_total_s),
            "persistent_service_time_s_max": float(self._service_time_max_s),
            "persistent_restart_elapsed_s": float(self._restart_elapsed_s),
            "persistent_restarts_active": int(self._restarts_active),
            "persistent_restart_accounting_scope": (
                "settled_backend_maintenance_nonadditive_with_action_wall_time"
            ),
            "persistent_transport_circuit_open": time.monotonic() < self._transport_circuit_open_until,
            "persistent_transport_circuit_reason": self._transport_circuit_reason,
            "persistent_transport_consecutive_failures": self._transport_consecutive_failures,
            "persistent_transport_startups": 0,
            "persistent_transport_startup_failures": 0,
            "persistent_transport_handshake_failures": 0,
            "persistent_transport_requests": 0,
            "persistent_transport_completions": 0,
            "persistent_transport_failures": 0,
            "persistent_transport_fatals": 0,
            "persistent_transport_timeouts": 0,
            "persistent_transport_stale_messages": 0,
            "persistent_transport_protocol_errors": 0,
            "persistent_transport_restarts": 0,
            "persistent_transport_shutdown_failures": 0,
            "persistent_transport_queue_wait_s": 0.0,
            "persistent_transport_service_time_s": 0.0,
        }
        for item in worker_stats:
            stats["persistent_worker_startups"] += int(
                item.get("persistent_transport_startups", 0)
            )
            stats["persistent_worker_restarts"] += int(
                item.get("persistent_transport_restarts", 0)
            )
            stats["persistent_worker_crashes"] += int(
                item.get("persistent_worker_crashes", 0)
            )
            stats["persistent_worker_timeouts"] += int(
                item.get("persistent_worker_timeouts", 0)
            )
            stats["persistent_worker_protocol_failures"] += int(
                item.get("persistent_worker_protocol_failures", 0)
            )
            stats["persistent_worker_recycles"] += int(
                item.get("persistent_worker_recycles", 0)
            )
            stats["persistent_worker_cancellations"] += int(
                item.get("persistent_worker_cancellations", 0)
            )
            stats["persistent_transport_startups"] += int(
                item.get("persistent_transport_startups", 0)
            )
            stats["persistent_transport_startup_failures"] += int(
                item.get("persistent_transport_startup_failures", 0)
            )
            stats["persistent_transport_handshake_failures"] += int(
                item.get("persistent_transport_handshake_failures", 0)
            )
            stats["persistent_transport_requests"] += int(
                item.get("persistent_transport_requests", 0)
            )
            stats["persistent_transport_completions"] += int(
                item.get("persistent_transport_completions", 0)
            )
            stats["persistent_transport_failures"] += int(
                item.get("persistent_transport_failures", 0)
            )
            stats["persistent_transport_fatals"] += int(
                item.get("persistent_transport_fatals", 0)
            )
            stats["persistent_transport_timeouts"] += int(
                item.get("persistent_transport_timeouts", 0)
            )
            stats["persistent_transport_stale_messages"] += int(
                item.get("persistent_transport_stale_messages", 0)
            )
            stats["persistent_transport_protocol_errors"] += int(
                item.get("persistent_transport_protocol_errors", 0)
            )
            stats["persistent_transport_restarts"] += int(
                item.get("persistent_transport_restarts", 0)
            )
            stats["persistent_transport_shutdown_failures"] += int(
                item.get("persistent_transport_shutdown_failures", 0)
            )
            stats["persistent_transport_queue_wait_s"] += float(
                item.get("persistent_transport_queue_wait_s", 0.0)
            )
            stats["persistent_transport_service_time_s"] += float(
                item.get("persistent_transport_service_time_s", 0.0)
            )
        return stats
