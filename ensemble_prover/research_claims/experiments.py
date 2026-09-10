"""Opt-in, ephemeral Python experiments with no host data or network mounts.

This is a bounded observation tool, never a theorem verifier. The operating
system's namespace sandbox is mandatory; no unsandboxed fallback exists.
"""

from __future__ import annotations

import asyncio
import base64
import math
import os
import signal
import secrets
from pathlib import Path
from typing import Any

from .model import positive_int, text


class PythonSandbox:
    def __init__(
        self,
        *,
        executable: str = "/usr/bin/bwrap",
        timeout_s: float = 20,
        output_bytes: int = 1_000_000,
        memory_bytes: int = 512 * 1024 * 1024,
    ):
        if not math.isfinite(timeout_s) or timeout_s <= 0:
            raise ValueError("experiment timeout must be finite and positive")
        self.executable = executable
        self.timeout_s = timeout_s
        self.output_bytes = positive_int(output_bytes, "experiment output bytes")
        self.memory_bytes = positive_int(memory_bytes, "experiment memory bytes")

    async def run(
        self, code: str, *, remaining_s: float | None = None
    ) -> dict[str, Any]:
        text(code, "Python source")
        result: dict[str, Any] = {
            "status": "tool_unavailable",
            "stdout": "",
            "stderr": "",
            "exit_code": None,
            "complete": False,
            "kernel_verified": False,
            "environment": {
                "isolation": "bubblewrap namespaces; read-only system runtime",
                "python": "/usr/bin/python3",
                "network": False,
                "per_process_memory_bytes": self.memory_bytes,
                "output_bytes": self.output_bytes,
                "timeout_s": self.timeout_s,
            },
        }
        for name in ("stdout", "stderr"):
            result.update(
                {f"{name}_base64": "", f"{name}_bytes": 0, f"{name}_text_lossy": False}
            )
        if os.geteuid() == 0:
            return {**result, "reason": "experiments require an unprivileged caller"}
        timeout = (
            min(self.timeout_s, remaining_s)
            if remaining_s is not None
            else self.timeout_s
        )
        if timeout <= 0:
            return {**result, "status": "timeout"}
        if (
            not Path(self.executable).is_file()
            or not Path("/usr/bin/python3").is_file()
        ):
            return result
        command = [
            self.executable,
            "--unshare-all",
            "--unshare-user",
            "--disable-userns",
            "--new-session",
            "--die-with-parent",
            "--cap-drop",
            "ALL",
            "--clearenv",
            "--ro-bind",
            "/usr",
            "/usr",
        ]
        for directory in ("/lib", "/lib64"):
            if Path(directory).exists():
                command += ["--ro-bind", directory, directory]
        command += [
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--tmpfs",
            "/tmp",
            "--remount-ro",
            "/tmp",
            "--remount-ro",
            "/dev",
            "--remount-ro",
            "/",
            "--chdir",
            "/tmp",
            "--setenv",
            "PATH",
            "/usr/bin",
            "/usr/bin/python3",
            "-I",
            "-B",
            "-",
        ]
        # Limits are set inside the sandbox, avoiding preexec_fn in an async,
        # potentially multithreaded parent process. The generated code receives
        # no writable host mounts, credentials, or inherited environment.
        startup_marker = ("ensemble-started-" + secrets.token_hex(24) + "\n").encode(
            "ascii"
        )
        wrapper = (
            "import resource\n"
            f"resource.setrlimit(resource.RLIMIT_AS, ({self.memory_bytes}, {self.memory_bytes}))\n"
            f"resource.setrlimit(resource.RLIMIT_CPU, ({math.ceil(timeout)}, {math.ceil(timeout) + 1}))\n"
            "resource.setrlimit(resource.RLIMIT_NPROC, (1, 1))\n"
            "resource.setrlimit(resource.RLIMIT_FSIZE, (1048576, 1048576))\n"
            "resource.setrlimit(resource.RLIMIT_NOFILE, (64, 64))\n"
            f"import os; os.write(2, {startup_marker!r})\n"
            f"exec(compile({code!r}, '<research-experiment>', 'exec'))\n"
        ).encode()
        try:
            process = await asyncio.create_subprocess_exec(
                *command,
                stdin=asyncio.subprocess.PIPE,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                start_new_session=True,
                env={},
            )
        except OSError:
            return result
        buffers = {"stdout": bytearray(), "stderr": bytearray()}
        total = 0
        startup_pending = bytearray()
        startup_checked = False
        runtime_started = False

        def capture(chunk: bytes, name: str) -> None:
            nonlocal total
            available = max(0, self.output_bytes - total)
            buffers[name].extend(chunk[:available])
            total += len(chunk)
            if total > self.output_bytes:
                raise OverflowError("experiment output limit reached")

        async def read(stream: asyncio.StreamReader, name: str) -> None:
            nonlocal startup_checked, runtime_started
            while chunk := await stream.read(16384):
                if name == "stderr" and not startup_checked:
                    startup_pending.extend(chunk)
                    if len(startup_pending) < len(
                        startup_marker
                    ) and startup_marker.startswith(startup_pending):
                        continue
                    startup_checked = True
                    runtime_started = startup_pending.startswith(startup_marker)
                    chunk = bytes(
                        startup_pending[len(startup_marker) :]
                        if runtime_started
                        else startup_pending
                    )
                    startup_pending.clear()
                capture(chunk, name)
            if name == "stderr" and startup_pending:
                capture(bytes(startup_pending), name)
                startup_pending.clear()

        async def write() -> None:
            assert process.stdin is not None
            try:
                process.stdin.write(wrapper)
                await process.stdin.drain()
            except (BrokenPipeError, ConnectionResetError):
                pass
            finally:
                process.stdin.close()

        assert process.stdout is not None and process.stderr is not None
        tasks = [
            asyncio.create_task(read(process.stdout, "stdout")),
            asyncio.create_task(read(process.stderr, "stderr")),
            asyncio.create_task(write()),
            asyncio.create_task(process.wait()),
        ]
        operation = asyncio.gather(*tasks)
        try:
            await asyncio.wait_for(operation, timeout=timeout)
            result["status"] = "completed" if process.returncode == 0 else "failed"
            result["complete"] = True
        except asyncio.TimeoutError:
            result["status"] = "timeout"
        except OverflowError:
            result["status"] = "output_limit"
        finally:
            # Bubblewrap's PID namespace init tears down descendants too. Kill
            # even if the leader exited but a descendant still owns pipe FDs.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            if process.returncode is None:
                try:
                    process.kill()
                except ProcessLookupError:
                    pass
            for task in tasks:
                task.cancel()
            await asyncio.gather(operation, *tasks, return_exceptions=True)

            # Drain remaining pipe buffers after killing. Waiting on the process
            # while a full StreamReader is paused can otherwise deadlock even
            # after the OS has reaped the child (notably on output-limit stops).
            async def drain(stream: asyncio.StreamReader) -> None:
                while await stream.read(16384):
                    pass

            await asyncio.gather(
                drain(process.stdout), drain(process.stderr), process.wait()
            )
        for name, value in buffers.items():
            raw = bytes(value)
            try:
                rendered = raw.decode("utf-8")
                lossy = False
            except UnicodeDecodeError:
                rendered, lossy = raw.decode("utf-8", errors="replace"), True
            result.update(
                {
                    name: rendered,
                    f"{name}_base64": base64.b64encode(raw).decode("ascii"),
                    f"{name}_bytes": len(raw),
                    f"{name}_text_lossy": lossy,
                }
            )
        result["exit_code"] = process.returncode
        result["runtime_started"] = runtime_started
        if not runtime_started and (
            result["status"] in {"completed", "failed"}
            or (result["status"] == "output_limit" and startup_checked)
        ):
            # A bounded startup diagnostic is not generated experiment output.
            # Do not infer failed startup while its marker is still unread.
            result.update(status="tool_unavailable", complete=False)
        return result
