"""Manage isolated persistent Lean verifier workers and their protocol."""

from __future__ import annotations

import asyncio
import json
import logging
import os
import shutil
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Optional

from .config import LeanConfig, _resolve_lean_scratch_root
from .runtime_context import mark_runtime_owned_callback
from .subprocess_cleanup import (
    request_process_termination_nowait,
    terminate_and_reap_process,
)

logger = logging.getLogger(__name__)

PERSISTENT_VERIFIER_PROTOCOL = "persistent_verifier_transport"
PERSISTENT_VERIFIER_VERSION = "1.0"


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


class PersistentVerifierError(RuntimeError):
    pass


class PersistentVerifierUnavailableError(PersistentVerifierError):
    pass


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
                line = await proc.stderr.readline()
                if not line:
                    break
                text = line.decode(errors="replace").rstrip()
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
        body = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
        proc.stdin.write((body + "\n").encode("utf-8"))
        await proc.stdin.drain()

    async def _read_message(self, timeout_s: float) -> Dict[str, Any]:
        proc = self._proc
        if proc is None or proc.stdout is None:
            raise PersistentVerifierError("persistent verifier worker stdout unavailable")
        raw = await asyncio.wait_for(proc.stdout.readline(), timeout=max(0.1, timeout_s))
        if not raw:
            rc = proc.returncode if proc.returncode is not None else "unknown"
            raise PersistentVerifierError(
                f"persistent verifier worker exited before reply (returncode={rc})"
            )
        try:
            msg = json.loads(raw.decode("utf-8"))
        except Exception as exc:
            self._transport_protocol_errors += 1
            raise PersistentVerifierError(
                f"invalid persistent verifier JSON: {raw[:200]!r}"
            ) from exc
        if not isinstance(msg, dict):
            self._transport_protocol_errors += 1
            raise PersistentVerifierError("persistent verifier message must be a JSON object")
        if str(msg.get("protocol", "")) != PERSISTENT_VERIFIER_PROTOCOL:
            self._transport_protocol_errors += 1
            raise PersistentVerifierError(
                f"unexpected persistent verifier protocol: {msg.get('protocol')!r}"
            )
        if _protocol_major(str(msg.get("version", ""))) != _protocol_major(
            PERSISTENT_VERIFIER_VERSION
        ):
            self._transport_protocol_errors += 1
            raise PersistentVerifierError(
                f"unexpected persistent verifier version: {msg.get('version')!r}"
            )
        if str(msg.get("worker_id", "")) != self.worker_id:
            self._transport_protocol_errors += 1
            raise PersistentVerifierError(
                f"unexpected persistent verifier worker id: {msg.get('worker_id')!r}"
            )
        return msg

    async def _kill_process(self) -> None:
        proc = self._proc
        stderr_task = self._stderr_task
        self._proc = None
        self._stderr_task = None
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
            if self._proc is not None and self.state in {"idle", "busy"}:
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
                    env={**os.environ, "PYTHONUNBUFFERED": "1"},
                )
                self._proc = proc
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
        return limit > 0 and self._requests_served >= limit

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

    async def execute(
        self,
        request: VerifierRequest,
        *,
        queue_wait_s: float = 0.0,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> VerifierResponse:
        async with self._lock:
            if self._proc is None or self.state not in {"idle", "busy"}:
                ok = await self.start()
                if not ok:
                    raise PersistentVerifierError("persistent verifier worker unavailable")
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
            except Exception:
                self._worker_crashes += 1
                self.state = "poisoned"
                response = VerifierResponse(
                    request_id=str(request.request_id),
                    ok=False,
                    returncode=1,
                    output=_status_with_output(
                        "persistent verifier worker crashed",
                        partial_output,
                    ),
                    backend_kind="persistent_process",
                    worker_id=self.worker_id,
                    worker_generation=int(self.generation),
                    service_time_s=max(0.0, time.monotonic() - started),
                    queue_wait_s=float(queue_wait_s),
                )
                await self._kill_process()
                raise PersistentVerifierFatalError(response, "lean_backend_crash")
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
                )
                self.state = str(msg.get("worker_state_after", "idle") or "idle")
                self._transport_completions += 1
                self._transport_service_time_s += max(0.0, response.service_time_s)
                self._requests_served += 1
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


class PersistentVerifierPool:
    def __init__(self, cfg: LeanConfig):
        self.cfg = cfg
        self.project_dir = Path(cfg.project_dir).resolve()
        # Main worker count: used to be `worker_count`. Kept under
        # that name for backward compatibility with stats callers
        # and existing tests that set pool.worker_count directly.
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
        self._available: asyncio.Queue[PersistentVerifierWorker] = asyncio.Queue()
        self._available_oracle: Optional[asyncio.Queue[PersistentVerifierWorker]] = (
            asyncio.Queue() if self.oracle_worker_count > 0 else None
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
        # Per-class request counters for telemetry — surface through
        # pool.stats() so operators can verify separation in prod.
        self._request_count_main: int = 0
        self._request_count_oracle: int = 0

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

    async def _restart_and_requeue_worker(
        self,
        worker: PersistentVerifierWorker,
        target_queue: "asyncio.Queue[PersistentVerifierWorker]",
    ) -> None:
        try:
            restarted = await worker.restart()
        except BaseException:
            restarted = False
        if restarted and not self._closing and self._started:
            await target_queue.put(worker)
        elif restarted:
            await self._close_worker_best_effort(worker)

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
        self._track_background_task(task)
        return task

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
        if not await self.start():
            raise PersistentVerifierUnavailableError(
                "persistent verifier pool unavailable"
            )
        queue_started = time.monotonic()
        request_queue_class = str(
            getattr(request, "queue_class", "main") or "main"
        )
        source_queue = self._pick_request_queue(request_queue_class)
        try:
            worker = await asyncio.wait_for(
                source_queue.get(),
                timeout=max(1.0, float(self.cfg.persistent_worker_start_timeout_s)),
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
        # Explicit ownership flag — the previous implementation gated
        # worker re-queue on worker.state == "idle" in a finally block,
        # which was unsafe: any cleanup path that left the state as
        # something other than "idle" (cancellation → "poisoned",
        # restart-in-progress → "starting", etc.) permanently lost the
        # worker from the pool. With persistent_workers=1, a single
        # cancellation would drain the pool forever and every
        # subsequent request would wait persistent_worker_start_timeout_s
        # before falling back to REPL.
        worker_owned = True

        try:
            response = await worker.execute(
                request,
                queue_wait_s=queue_wait_s,
                **(
                    {"dispatch_observer": dispatch_observer}
                    if dispatch_observer is not None
                    else {}
                ),
            )
            self._service_time_total_s += max(0.0, response.service_time_s)
            self._service_time_max_s = max(
                self._service_time_max_s, max(0.0, response.service_time_s)
            )
            if response.returncode == 0:
                self._success_count += 1
            else:
                self._failure_count += 1
            return response
        except PersistentVerifierFatalError as exc:
            response = exc.response
            self._failure_count += 1
            self._service_time_total_s += max(0.0, response.service_time_s)
            self._service_time_max_s = max(
                self._service_time_max_s, max(0.0, response.service_time_s)
            )
            worker_owned = False
            cleanup_task = self._schedule_restart_and_requeue(worker, target_queue)
            try:
                await asyncio.shield(cleanup_task)
            except BaseException:
                pass
            return response
        except asyncio.CancelledError as cancel_exc:
            # Worker.execute's own cancellation handler has already
            # killed the subprocess and marked the worker as poisoned
            # (see PersistentVerifierWorker.execute — Fix 4). We must
            # restart the worker (fresh subprocess) rather than re-queue the
            # poisoned one. Run the restart in its own task so a second
            # cancellation of this caller cannot orphan the worker.
            worker_owned = False
            cleanup_task = self._schedule_restart_and_requeue(worker, target_queue)
            try:
                await asyncio.shield(cleanup_task)
            except asyncio.CancelledError:
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
                        await asyncio.shield(cleanup_task)
                    except BaseException:
                        pass
                else:
                    if not self._closing and self._started:
                        await target_queue.put(worker)
                    else:
                        await self._close_worker_best_effort(worker)

    async def close(self) -> None:
        self._closing = True
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
