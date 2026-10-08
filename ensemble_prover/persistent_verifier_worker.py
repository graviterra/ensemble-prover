"""Internal Lean LSP worker for the persistent verifier pool.

The pool manager starts this module with a private framed-JSON protocol. It is
not a user-facing CLI and should not be launched independently.
"""

from __future__ import annotations

import argparse
import asyncio
from collections import OrderedDict
import hashlib
import json
import logging
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Dict, List, Optional
from urllib.parse import unquote, urlparse

from .persistent_verifier import (
    PERSISTENT_VERIFIER_PROTOCOL,
    PERSISTENT_VERIFIER_VERSION,
    _protocol_major,
    DEFAULT_MAX_MESSAGE_BYTES,
    STDERR_TAIL_BYTES,
)
from .subprocess_cleanup import terminate_and_reap_process
from .local_inference.network_policy import prepare_owned_subprocess, restore_owned_worker_network_policy
from .utils import has_sorry_or_admit

logger = logging.getLogger(__name__)


def _timestamp_unix_s() -> float:
    return float(time.time())


def _uri_to_path(uri: str) -> Path:
    parsed = urlparse(str(uri or ""))
    if parsed.scheme != "file":
        raise ValueError(f"unsupported document uri: {uri!r}")
    return Path(unquote(parsed.path)).resolve()


def _severity_name(raw: Any) -> str:
    mapping = {1: "error", 2: "warning", 3: "info", 4: "info"}
    try:
        value = int(raw)
    except Exception:
        return "info"
    return mapping.get(value, "info")


def _canonicalize_diagnostics(uri: str, diagnostics: List[Dict[str, Any]]) -> str:
    file_path = str(_uri_to_path(uri))
    blocks: List[str] = []
    sortable: List[tuple[int, int, str, str]] = []
    for diag in diagnostics:
        rng = diag.get("range", {}) if isinstance(diag, dict) else {}
        start = rng.get("start", {}) if isinstance(rng, dict) else {}
        line = int(start.get("line", 0) or 0) + 1
        col = int(start.get("character", 0) or 0) + 1
        severity = _severity_name(diag.get("severity", 3) if isinstance(diag, dict) else 3)
        message = str(diag.get("message", "") if isinstance(diag, dict) else "").rstrip()
        sortable.append((line, col, severity, message))
    severity_order = {"error": 0, "warning": 1, "info": 2}
    for line, col, severity, message in sorted(
        sortable,
        key=lambda item: (
            int(item[0]),
            int(item[1]),
            int(severity_order.get(item[2], 99)),
            str(item[3]),
        ),
    ):
        if message:
            blocks.append(f"{file_path}:{line}:{col}: {severity}: {message}")
    if not blocks:
        return ""
    return "\n".join(blocks).rstrip() + "\n"


def _structured_diagnostics(uri: str, diagnostics: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    file_path = str(_uri_to_path(uri))
    structured: List[Dict[str, Any]] = []
    for diag in diagnostics:
        rng = diag.get("range", {}) if isinstance(diag, dict) else {}
        start = rng.get("start", {}) if isinstance(rng, dict) else {}
        structured.append(
            {
                "file": file_path,
                "line": int(start.get("line", 0) or 0) + 1,
                "col": int(start.get("character", 0) or 0) + 1,
                "severity": _severity_name(diag.get("severity", 3) if isinstance(diag, dict) else 3),
                "message": str(diag.get("message", "") if isinstance(diag, dict) else ""),
            }
        )
    return structured


class LeanLspError(RuntimeError):
    def __init__(self, message: str, failure_kind: str = "lean_backend_crash"):
        super().__init__(message)
        self.failure_kind = failure_kind


class LeanLspSession:
    def __init__(self, project_dir: Path):
        self.project_dir = Path(project_dir).resolve()
        self._proc: Optional[asyncio.subprocess.Process] = None
        self._stderr_task: Optional[asyncio.Task[None]] = None
        self._request_id: int = 1
        self._current_uri: Optional[str] = None
        self._current_version: int = 0
        self._documents: OrderedDict[str, int] = OrderedDict()
        self._document_version_counter = 0
        self.max_message_bytes = 32 * 1024 * 1024
        self._stderr_tail = b""

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
                    logger.debug("Lean LSP stderr: %s", text)
        except Exception:
            logger.debug("Lean LSP stderr drain failed", exc_info=True)

    async def _kill_proc(self) -> None:
        proc = self._proc
        stderr_task = self._stderr_task
        self._proc = None
        self._stderr_task = None
        self._documents.clear()
        self._current_uri = None
        self._current_version = 0
        if proc is None:
            return
        # The Lean server deliberately shares this worker's process group (see
        # start()), so proc.pid is not a process-group id here. Killing that
        # group with killpg(proc.pid) would be unsafe: it could address an
        # unrelated group that happens to reuse the id. Kill only the server
        # process and disconnect its pipes; the group sweep performed when the
        # worker itself is torn down reaps any remaining descendants.
        await terminate_and_reap_process(
            proc,
            auxiliary_tasks=(stderr_task,) if stderr_task is not None else (),
            kill_process_group=False,
            log=logger,
        )

    async def _write_frame(self, payload: Dict[str, Any]) -> None:
        proc = self._proc
        if proc is None or proc.stdin is None:
            raise LeanLspError("lean server stdin unavailable")
        body = json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode(
            "utf-8"
        )
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        proc.stdin.write(header + body)
        await proc.stdin.drain()

    async def _read_message(self, timeout_s: float = 60.0) -> Dict[str, Any]:
        proc = self._proc
        if proc is None or proc.stdout is None:
            raise LeanLspError("lean server stdout unavailable")
        deadline = time.monotonic() + max(0.1, float(timeout_s))
        remaining = deadline - time.monotonic()
        if remaining <= 0.0:
            raise asyncio.TimeoutError("timed out waiting for Lean LSP header")
        try:
            header_bytes = await asyncio.wait_for(
                proc.stdout.readuntil(b"\r\n\r\n"),
                timeout=remaining,
            )
        except asyncio.LimitOverrunError as exc:
            raise LeanLspError("Lean LSP header exceeds byte limit", "transport_oversized") from exc
        except asyncio.IncompleteReadError as exc:
            partial = bytes(exc.partial or b"")
            rc = proc.returncode if proc.returncode is not None else "unknown"
            if not partial:
                raise LeanLspError(
                    f"lean server exited before completing message header (returncode={rc})"
                ) from exc
            raise LeanLspError(
                f"lean server truncated message header (returncode={rc})", "transport_truncated"
            ) from exc
        if len(header_bytes) > 8192:
            raise LeanLspError("Lean LSP header exceeds byte limit", "transport_oversized")
        length = None
        for raw_line in header_bytes.decode("ascii", errors="replace").split("\r\n"):
            if raw_line.lower().startswith("content-length:"):
                if length is not None:
                    raise LeanLspError("Lean LSP message has duplicate content lengths", "transport_malformed")
                try:
                    length = int(raw_line.split(":", 1)[1].strip())
                except ValueError as exc:
                    raise LeanLspError("Lean LSP message has invalid content length", "transport_malformed") from exc
        if length is None:
            raise LeanLspError("Lean LSP message missing content length", "transport_malformed")
        if length < 0:
            raise LeanLspError("Lean LSP message has negative content length", "transport_malformed")
        if length > self.max_message_bytes:
            raise LeanLspError("Lean LSP message exceeds byte limit", "transport_oversized")
        try:
            body = await asyncio.wait_for(proc.stdout.readexactly(length), timeout=max(0.001, deadline - time.monotonic()))
        except asyncio.IncompleteReadError as exc:
            raise LeanLspError("Lean LSP message body truncated", "transport_truncated") from exc
        try:
            msg = json.loads(body.decode("utf-8"))
        except Exception as exc:
            raise LeanLspError("Lean LSP emitted invalid JSON", "transport_malformed") from exc
        if not isinstance(msg, dict):
            raise LeanLspError("Lean LSP emitted non-object JSON", "transport_malformed")
        return msg

    async def _handle_server_request(self, msg: Dict[str, Any]) -> None:
        if "id" not in msg or "method" not in msg:
            return
        response = {"jsonrpc": "2.0", "id": msg["id"], "result": None}
        await self._write_frame(response)

    async def _wait_for_response(self, request_id: int, timeout_s: float = 30.0) -> Dict[str, Any]:
        deadline = time.monotonic() + max(0.1, float(timeout_s))
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0.0:
                raise asyncio.TimeoutError("timed out waiting for Lean LSP response")
            msg = await self._read_message(remaining)
            if "method" in msg and "id" in msg:
                await self._handle_server_request(msg)
                continue
            if int(msg.get("id", -1)) == int(request_id):
                return msg

    async def start(self) -> None:
        if self._proc is not None:
            return
        # The Lean server intentionally inherits this worker's session and
        # process group (no start_new_session). The worker is itself a session
        # leader created by the host with start_new_session=True, so a host
        # forced kill of the worker's group sweeps the server too — the server
        # cannot outlive a SIGKILLed worker that is unable to run cleanup.
        # Giving the server its own session here would strand it as an orphan
        # in a group the host never signals.
        proc = await asyncio.create_subprocess_exec(
            "lake",
            "env",
            "lean",
            "--server",
            cwd=str(self.project_dir),
            env=prepare_owned_subprocess(("lake", "env", "lean", "--server"), project=self.project_dir),
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        self._proc = proc
        self._stderr_task = asyncio.create_task(self._drain_stderr())
        request_id = self._request_id
        self._request_id += 1
        await self._write_frame(
            {
                "jsonrpc": "2.0",
                "id": request_id,
                "method": "initialize",
                "params": {
                    "processId": None,
                    "rootUri": self.project_dir.as_uri(),
                    "capabilities": {},
                    "workspaceFolders": [
                        {"uri": self.project_dir.as_uri(), "name": self.project_dir.name}
                    ],
                },
            }
        )
        response = await self._wait_for_response(request_id, timeout_s=30.0)
        if "error" in response:
            raise LeanLspError(f"Lean LSP initialize failed: {response['error']!r}")
        await self._write_frame(
            {"jsonrpc": "2.0", "method": "initialized", "params": {}}
        )

    async def check_document(
        self,
        *,
        uri: str,
        text: str,
        timeout_s: float,
        require_completion: bool = False,
        context_slots: int = 1,
        completion_marker: str = "",
    ) -> tuple[List[Dict[str, Any]], int]:
        if self._proc is None:
            await self.start()
        path = _uri_to_path(uri)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        while uri not in self._documents and len(self._documents) >= max(1, context_slots):
            retired_uri, _ = self._documents.popitem(last=False)
            await self._write_frame(
                {
                    "jsonrpc": "2.0",
                    "method": "textDocument/didClose",
                    "params": {"textDocument": {"uri": retired_uri}},
                }
            )
        self._document_version_counter += 1
        version = self._document_version_counter
        if uri in self._documents:
            await self._write_frame(
                {
                    "jsonrpc": "2.0",
                    "method": "textDocument/didChange",
                    "params": {
                        "textDocument": {"uri": uri, "version": version},
                        "contentChanges": [{"text": text}],
                    },
                }
            )
        else:
            await self._write_frame(
                {
                    "jsonrpc": "2.0",
                    "method": "textDocument/didOpen",
                    "params": {
                        "textDocument": {
                            "uri": uri,
                            "languageId": "lean",
                            "version": version,
                            "text": text,
                        }
                    },
                }
            )
        self._documents[uri] = version
        self._documents.move_to_end(uri)
        self._current_uri = uri
        self._current_version = version
        await self._write_frame(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didSave",
                "params": {"textDocument": {"uri": uri}, "text": text},
            }
        )
        if require_completion:
            return await self._completed_diagnostics(
                uri=uri, version=version, timeout_s=timeout_s,
                completion_marker=completion_marker,
            ), version
        latest_diagnostics: Optional[List[Dict[str, Any]]] = None
        diagnostics_seen = False
        progress_seen = False
        progress_active: Optional[bool] = None
        progress_quiet_window_s = 0.10
        diagnostics_quiet_window_s = 0.35
        empty_diagnostics_quiet_window_s = 0.75
        settle_deadline: Optional[float] = None
        deadline = time.monotonic() + max(0.1, float(timeout_s))

        def _timeout_details() -> str:
            diagnostic_count = len(latest_diagnostics or [])
            return (
                "timed out waiting for Lean diagnostics "
                f"(uri={uri}, version={version}, progress_seen={progress_seen}, "
                f"progress_active={progress_active}, diagnostics_seen={diagnostics_seen}, "
                f"diagnostic_count={diagnostic_count}, settle_pending={settle_deadline is not None})"
            )

        while True:
            now = time.monotonic()
            if settle_deadline is not None and now >= settle_deadline:
                return list(latest_diagnostics or []), int(version)
            remaining = deadline - time.monotonic()
            if remaining <= 0.0:
                raise asyncio.TimeoutError(_timeout_details())
            read_timeout = remaining
            if settle_deadline is not None:
                read_timeout = min(
                    remaining,
                    max(0.05, settle_deadline - time.monotonic()),
                )
            try:
                msg = await self._read_message(read_timeout)
            except asyncio.TimeoutError:
                if (
                    settle_deadline is not None
                    and time.monotonic() >= settle_deadline
                ):
                    return list(latest_diagnostics or []), int(version)
                raise asyncio.TimeoutError(_timeout_details())
            if "method" in msg and "id" in msg:
                await self._handle_server_request(msg)
                continue
            method = str(msg.get("method", "") or "")
            if method == "$/lean/fileProgress":
                params = msg.get("params", {}) if isinstance(msg, dict) else {}
                text_document = (
                    params.get("textDocument", {}) if isinstance(params, dict) else {}
                )
                if str(text_document.get("uri", "") or "") != uri:
                    continue
                progress_version = text_document.get("version")
                if type(progress_version) is not int or progress_version != version:
                    continue
                processing = params.get("processing", [])
                if not isinstance(processing, list):
                    processing = []
                progress_seen = True
                progress_active = bool(processing)
                if progress_active:
                    settle_deadline = None
                else:
                    settle_deadline = time.monotonic() + progress_quiet_window_s
                continue
            if method != "textDocument/publishDiagnostics":
                continue
            params = msg.get("params", {}) if isinstance(msg, dict) else {}
            if str(params.get("uri", "") or "") != uri:
                continue
            msg_version = params.get("version")
            if type(msg_version) is not int or msg_version != version:
                continue
            diagnostics = params.get("diagnostics", [])
            if not isinstance(diagnostics, list):
                diagnostics = []
            latest_diagnostics = diagnostics
            diagnostics_seen = True
            if progress_seen:
                if progress_active is False:
                    settle_deadline = time.monotonic() + progress_quiet_window_s
                else:
                    settle_deadline = None
            else:
                # Empty diagnostics can be an early, provisional LSP snapshot.
                # Without fileProgress quiescence, accepting that snapshot as
                # success races delayed errors and can falsely validate a bad
                # proof. But some Lean server builds do not emit fileProgress
                # for quiet valid files, so empty diagnostics must eventually
                # settle after a longer conservative quiet window instead of
                # poisoning the worker as infrastructure timeout.
                settle_deadline = (
                    time.monotonic()
                    + (
                        diagnostics_quiet_window_s
                        if diagnostics
                        else empty_diagnostics_quiet_window_s
                    )
                )

    async def _completed_diagnostics(
        self, *, uri: str, version: int, timeout_s: float, completion_marker: str
    ) -> List[Dict[str, Any]]:
        """Await Lean's reporter and command/kernel tasks for this exact edit.

        Lean's waitForDiagnostics handler waits for both doc.reporter and
        cmdSnaps.waitAll. Sequential worker ownership prevents a later edit
        from satisfying this request with a different document version.
        """
        request_id = self._request_id
        self._request_id += 1
        await self._write_frame({
            "jsonrpc": "2.0", "id": request_id,
            "method": "textDocument/waitForDiagnostics",
            "params": {"uri": uri, "version": version},
        })
        deadline = time.monotonic() + max(0.001, timeout_s)
        diagnostics: Optional[List[Dict[str, Any]]] = None
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise asyncio.TimeoutError("timed out waiting for versioned Lean completion")
            msg = await self._read_message(remaining)
            if "method" in msg and "id" in msg:
                await self._handle_server_request(msg)
                continue
            if type(msg.get("id")) is int and msg["id"] == request_id:
                if "error" in msg or not isinstance(msg.get("result"), dict):
                    raise LeanLspError("Lean versioned completion request failed", "completion_unavailable")
                if diagnostics is None:
                    raise LeanLspError("Lean completion omitted matching-version diagnostics", "completion_unavailable")
                if completion_marker and not any(str(d.get("message", "")) == completion_marker for d in diagnostics):
                    raise LeanLspError("Lean completion omitted request marker", "completion_unavailable")
                return diagnostics
            if msg.get("method") != "textDocument/publishDiagnostics":
                continue
            params = msg.get("params", {})
            if not isinstance(params, dict) or params.get("uri") != uri:
                continue
            if type(params.get("version")) is not int or params["version"] != version:
                continue
            current = params.get("diagnostics")
            if not isinstance(current, list) or any(not isinstance(d, dict) for d in current):
                raise LeanLspError("Lean diagnostics have invalid shape", "transport_malformed")
            diagnostics = current

    async def close(self) -> None:
        try:
            for uri in list(self._documents):
                await self._write_frame(
                    {
                        "jsonrpc": "2.0",
                        "method": "textDocument/didClose",
                        "params": {"textDocument": {"uri": uri}},
                    }
                )
        except Exception:
            logger.debug("Lean LSP didClose failed during shutdown", exc_info=True)
        await self._kill_proc()


class PersistentVerifierServer:
    def __init__(self, worker_id: str, generation: int):
        self.worker_id = str(worker_id)
        self.generation = int(generation)
        self.session_id = f"sess-{uuid.uuid4().hex}"
        self.state = "cold"
        self.project_dir: Optional[Path] = None
        self.temp_root: Optional[Path] = None
        self._lsp: Optional[LeanLspSession] = None
        self._busy = False
        self.max_message_bytes = DEFAULT_MAX_MESSAGE_BYTES
        self.context_slots = 4

    def _message(self, msg_type: str, **extra: Any) -> Dict[str, Any]:
        return {
            "protocol": PERSISTENT_VERIFIER_PROTOCOL,
            "version": PERSISTENT_VERIFIER_VERSION,
            "type": str(msg_type or ""),
            "worker_id": self.worker_id,
            "worker_generation": int(self.generation),
            "timestamp_unix_s": _timestamp_unix_s(),
            **extra,
        }

    async def _read_host_message(self) -> Dict[str, Any]:
        raw = await asyncio.to_thread(sys.stdin.buffer.readline, self.max_message_bytes + 1)
        if not raw:
            raise EOFError("host closed stdin")
        if len(raw) > self.max_message_bytes:
            raise LeanLspError("host message exceeds byte limit", "transport_oversized")
        if not raw.endswith(b"\n"):
            raise LeanLspError("host message truncated", "transport_truncated")
        try:
            msg = json.loads(raw.decode("utf-8"))
        except Exception as exc:
            raise LeanLspError("host sent invalid JSON", "transport_malformed") from exc
        if not isinstance(msg, dict):
            raise LeanLspError("host message must be a JSON object")
        if str(msg.get("protocol", "")) != PERSISTENT_VERIFIER_PROTOCOL:
            raise LeanLspError("unexpected host protocol")
        if _protocol_major(str(msg.get("version", ""))) != _protocol_major(
            PERSISTENT_VERIFIER_VERSION
        ):
            raise LeanLspError("unexpected host protocol version")
        if str(msg.get("worker_id", "")) != self.worker_id:
            raise LeanLspError("unexpected worker_id on host message")
        if int(msg.get("worker_generation", -1)) != self.generation:
            raise LeanLspError("unexpected worker_generation on host message")
        return msg

    async def _send_host_message(self, payload: Dict[str, Any]) -> None:
        body = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
        if len(body.encode("utf-8")) + 1 > self.max_message_bytes:
            raise LeanLspError("worker response exceeds byte limit", "transport_oversized")
        await asyncio.to_thread(sys.stdout.write, body + "\n")
        await asyncio.to_thread(sys.stdout.flush)

    async def _send_hello(self) -> None:
        await self._send_host_message(
            self._message(
                "hello",
                session_id=self.session_id,
                capabilities={
                    "supports_progress": True,
                    "supports_cancel": False,
                    "supports_in_memory_docs": False,
                    "supports_temp_docs": True,
                    "supports_versioned_completion": True,
                    "supports_stable_contexts": True,
                },
                implementation={
                    "transport_impl": "python-worker-stdio",
                    "lean_backend_kind": "lean-lsp",
                },
            )
        )

    async def _initialize(self, msg: Dict[str, Any]) -> None:
        self.project_dir = Path(str(msg.get("project_dir", "") or "")).resolve()
        self.temp_root = Path(str(msg.get("temp_root", "") or "")).resolve()
        self.temp_root.mkdir(parents=True, exist_ok=True)
        self.state = "starting"
        self.max_message_bytes = max(1024, int(msg.get("max_message_bytes", DEFAULT_MAX_MESSAGE_BYTES)))
        self.context_slots = max(1, int(msg.get("context_slots", 4)))
        self._lsp = LeanLspSession(self.project_dir)
        self._lsp.max_message_bytes = max(1024, int(msg.get("lsp_max_message_bytes", 32 * 1024 * 1024)))
        await self._lsp.start()
        self.state = "idle"
        await self._send_host_message(
            self._message(
                "ready",
                session_id=self.session_id,
                state="idle",
            )
        )

    async def _handle_check(self, msg: Dict[str, Any]) -> bool:
        request_id = str(msg.get("request_id", "") or "")
        if not request_id:
            await self._send_host_message(
                self._message(
                    "fatal",
                    session_id=self.session_id,
                    request_id="",
                    failure_kind="protocol_desync",
                    returncode=1,
                    output="persistent verifier check missing request_id",
                    worker_state_after="poisoned",
                )
            )
            return False
        if self._busy or self._lsp is None:
            await self._send_host_message(
                self._message(
                    "failed",
                    session_id=self.session_id,
                    request_id=request_id,
                    failure_kind="request_rejected",
                    returncode=1,
                    output="worker rejected request: verifier not ready",
                    worker_state_after=self.state if self._busy else "idle",
                )
            )
            return True
        self._busy = True
        self.state = "busy"
        await self._send_host_message(
            self._message(
                "accepted",
                session_id=self.session_id,
                request_id=request_id,
                state="busy",
            )
        )
        service_started = time.monotonic()
        try:
            uri = str(msg.get("document_uri", "") or "")
            original_uri = uri
            content = str(msg.get("content", "") or "")
            timeout_s = float(msg.get("timeout_s", 45.0) or 45.0)
            metadata = msg.get("metadata", {})
            if not isinstance(metadata, dict):
                raise LeanLspError("request metadata must be an object", "transport_malformed")
            stable_context = bool(metadata.get("stable_context"))
            context_key = str(metadata.get("context_key", ""))
            context_family_key = str(metadata.get("context_family_key", context_key))
            if stable_context:
                if not context_key or not context_family_key or self.temp_root is None:
                    raise LeanLspError("stable context requires a context identity", "protocol_desync")
                identity = hashlib.sha256((str(msg.get("mode", "")) + "\0" + context_family_key).encode()).hexdigest()
                uri = (self.temp_root / f"context_{identity}.lean").resolve().as_uri()
            diagnostics, _version = await self._lsp.check_document(
                uri=uri,
                text=content,
                timeout_s=timeout_s,
                context_slots=self.context_slots,
                **({"require_completion": True,
                    "completion_marker": str(metadata.get("completion_marker", ""))} if stable_context else {}),
            )
            if has_sorry_or_admit(content) and not any(
                _severity_name(diag.get("severity", 3)) == "warning"
                and "declaration uses" in str(diag.get("message", "")).lower()
                and "sorry" in str(diag.get("message", "")).lower()
                for diag in diagnostics
                if isinstance(diag, dict)
            ):
                diagnostics = [
                    *diagnostics,
                    {
                        "severity": 2,
                        "message": "declaration uses `sorry`",
                        "range": {
                            "start": {"line": 0, "character": 0},
                            "end": {"line": 0, "character": 1},
                        },
                    },
                ]
            # Send the canonical output once. The caller does not consume the
            # duplicated structured diagnostics, and large frames are bounded
            # independently of this reduction in payload size.
            partial_output = _canonicalize_diagnostics(original_uri, diagnostics)
            has_error = any(diag.get("severity") == 1 for diag in diagnostics)
            # Match Lean CLI semantics: returncode is set by errors only.
            # The previous logic flipped returncode to 1 on any severity=2
            # diagnostic when `warning_as_error=True`, which silently failed
            # valid proofs whose only diagnostic was a benign linter warning
            # such as "unused variable". `lake env lean` returns 0 in that
            # case (verified empirically); the worker now matches it.
            # Sorry detection remains independent: `lean_runner.check()`
            # uses `parsed.sorry_count` (counted from `declaration uses
            # 'sorry'` warning text) to gate `ok`, so removing the severity
            # flip does not weaken sorry rejection.
            returncode = 1 if has_error else 0
            await self._send_host_message(
                self._message(
                    "completed",
                    session_id=self.session_id,
                    request_id=request_id,
                    ok=bool(returncode == 0),
                    returncode=int(returncode),
                    output=partial_output,
                    diagnostic_count=len(diagnostics),
                    document_version=_version,
                    context_key=context_key if stable_context else "",
                    context_family_key=context_family_key if stable_context else "",
                    request_completed=stable_context,
                    service_time_s=max(0.0, time.monotonic() - service_started),
                    worker_state_after="idle",
                )
            )
            self.state = "idle"
            self._busy = False
            return True
        except asyncio.TimeoutError as exc:
            timeout_details = str(exc or "").strip()
            output = "persistent verifier timed out waiting for Lean diagnostics"
            if timeout_details:
                output = f"{output}: {timeout_details}"
            try:
                await self._send_host_message(
                    self._message(
                        "fatal",
                        session_id=self.session_id,
                        request_id=request_id,
                        failure_kind="timeout_poison",
                        returncode=1,
                        output=output,
                        worker_state_after="poisoned",
                    )
                )
            finally:
                await self._close_lsp_best_effort()
        except Exception as exc:
            logger.exception("Persistent verifier worker request failed")
            try:
                await self._send_host_message(
                    self._message(
                        "fatal",
                        session_id=self.session_id,
                        request_id=request_id,
                        failure_kind=getattr(exc, "failure_kind", "lean_backend_crash"),
                        returncode=1,
                        output=f"persistent verifier worker crash: {exc}",
                        worker_state_after="poisoned",
                    )
                )
            finally:
                await self._close_lsp_best_effort()
        self.state = "poisoned"
        self._busy = False
        return False

    async def _close_lsp_best_effort(self) -> None:
        if self._lsp is None:
            return
        try:
            await self._lsp.close()
        except Exception:
            logger.debug("Persistent verifier LSP close failed", exc_info=True)
        finally:
            self._lsp = None

    async def run(self) -> int:
        try:
            return await self._run()
        finally:
            await self._close_lsp_best_effort()

    async def _run(self) -> int:
        await self._send_hello()
        while True:
            try:
                msg = await self._read_host_message()
            except EOFError:
                break
            except Exception as exc:
                logger.exception("Persistent verifier host transport failed")
                await self._close_lsp_best_effort()
                await self._send_host_message(
                    self._message(
                        "fatal",
                        session_id=self.session_id,
                        request_id="",
                        failure_kind="unrecoverable_transport_error",
                        returncode=1,
                        output=f"host transport failure: {exc}",
                        worker_state_after="poisoned",
                    )
                )
                return 1
            msg_type = str(msg.get("type", "") or "")
            if msg_type == "initialize":
                try:
                    await self._initialize(msg)
                except Exception as exc:
                    logger.exception("Persistent verifier initialization failed")
                    await self._close_lsp_best_effort()
                    await self._send_host_message(
                        self._message(
                            "fatal",
                            session_id=self.session_id,
                            request_id="",
                            failure_kind="worker_internal_corruption",
                            returncode=1,
                            output=f"persistent verifier initialization failed: {exc}",
                            worker_state_after="poisoned",
                        )
                    )
                    return 1
                continue
            if msg_type == "check":
                keep_running = await self._handle_check(msg)
                if not keep_running:
                    await self._close_lsp_best_effort()
                    return 1
                continue
            if msg_type == "shutdown":
                try:
                    await self._close_lsp_best_effort()
                finally:
                    await self._send_host_message(
                        self._message(
                            "shutdown_ack",
                            session_id=self.session_id,
                        )
                    )
                return 0
            await self._close_lsp_best_effort()
            await self._send_host_message(
                self._message(
                    "fatal",
                    session_id=self.session_id,
                    request_id=str(msg.get("request_id", "") or ""),
                    failure_kind="protocol_desync",
                    returncode=1,
                    output=f"unknown host message type: {msg_type!r}",
                    worker_state_after="poisoned",
                )
            )
            return 1
        await self._close_lsp_best_effort()
        return 0


def _parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Persistent Lean verifier worker")
    parser.add_argument("--worker-id", required=True)
    parser.add_argument("--generation", required=True, type=int)
    return parser.parse_args(argv)


async def _async_main(argv: Optional[List[str]] = None) -> int:
    args = _parse_args(argv)
    restore_owned_worker_network_policy()
    server = PersistentVerifierServer(args.worker_id, args.generation)
    return await server.run()


def main(argv: Optional[List[str]] = None) -> int:
    logging.basicConfig(level=logging.INFO, stream=sys.stderr)
    return asyncio.run(_async_main(argv))


if __name__ == "__main__":
    raise SystemExit(main())
