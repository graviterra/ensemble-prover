"""Ready stdin with an explicit parent-controlled boundary before CLI exec."""

from __future__ import annotations

import asyncio
import errno
import os
import sys
import tempfile
from pathlib import Path


_EXEC_ERROR_PREFIX = b"EP_EXEC_ERROR:"


class ReadyStdinLaunch:
    """Own anonymous input and gate/status descriptors for a POSIX launch."""

    def __init__(self, input_data: bytes) -> None:
        self._fds: set[int] = set()
        self._loop = None
        self._status_future = None
        self._status_bytes = bytearray()
        self.gate_released = False
        self.stdin = tempfile.TemporaryFile(mode="w+b")
        try:
            self.stdin.write(input_data)
            self.stdin.seek(0)
            self.gate_read, self.gate_write = self._pipe()
            self.status_read, self.status_write = self._pipe()
        except BaseException:
            self.close()
            raise

    def _pipe(self) -> tuple[int, int]:
        pair = os.pipe()
        self._fds.update(pair)
        return pair

    def argv(self, command: list[str]) -> list[str]:
        return [
            sys.executable, "-I", "-S", str(Path(__file__).resolve()),
            str(self.gate_read), str(self.status_write), *command,
        ]

    @property
    def pass_fds(self) -> tuple[int, int]:
        return self.gate_read, self.status_write

    def observe_startup(self) -> None:
        """Drop parent copies and observe the private close-on-exec receipt."""
        self._close_fd(self.gate_read)
        self._close_fd(self.status_write)
        self._loop = asyncio.get_running_loop()
        self._status_future = self._loop.create_future()
        os.set_blocking(self.status_read, False)
        self._loop.add_reader(self.status_read, self._read_status)

    def _read_status(self) -> None:
        if self._status_future.done():
            return
        try:
            chunk = os.read(self.status_read, 128)
            self._status_bytes.extend(chunk)
            if len(self._status_bytes) > 128:
                raise RuntimeError("CLI bootstrap status exceeded its size limit")
            if chunk:
                return
            self._loop.remove_reader(self.status_read)
            self._status_future.set_result(bytes(self._status_bytes))
        except BlockingIOError:
            return
        except Exception as exc:
            self._loop.remove_reader(self.status_read)
            self._status_future.set_exception(exc)

    def release(self) -> None:
        """Release exec without yielding after the parent's admission checks."""
        if os.write(self.gate_write, b"1") != 1:
            raise OSError(errno.EIO, "CLI bootstrap gate was not released")
        self.gate_released = True
        self._close_fd(self.gate_write)

    async def exec_failure_errno(self) -> int | None:
        status = await self._status_future
        if not status:
            # EOF may mean exec succeeded or the bootstrap died. Neither is
            # authoritative evidence that generation could not have occurred.
            return None
        if status.startswith(_EXEC_ERROR_PREFIX) and status.endswith(b"\n"):
            value = status[len(_EXEC_ERROR_PREFIX):-1]
            if value.isdigit() and 0 < int(value) < 65536:
                return int(value)
        raise RuntimeError("CLI bootstrap returned an invalid exec receipt")

    def _close_fd(self, fd: int) -> None:
        if fd in self._fds:
            self._fds.remove(fd)
            os.close(fd)

    def close(self) -> None:
        if self._loop is not None:
            self._loop.remove_reader(self.status_read)
        if self._status_future is not None:
            if not self._status_future.done():
                self._status_future.cancel()
            elif not self._status_future.cancelled():
                self._status_future.exception()
        for fd in tuple(self._fds):
            self._close_fd(fd)
        self.stdin.close()


def _bootstrap() -> None:
    gate, status = int(sys.argv[1]), int(sys.argv[2])
    command = sys.argv[3:]
    # The actual CLI must never inherit the trusted exec-error channel.
    os.set_inheritable(status, False)
    allowed = os.read(gate, 1)
    os.close(gate)
    if allowed != b"1":
        os._exit(0)
    try:
        os.execvpe(command[0], command, os.environ)
    except OSError as exc:
        os.write(status, _EXEC_ERROR_PREFIX + str(exc.errno or errno.EIO).encode("ascii") + b"\n")
        os._exit(127)


if __name__ == "__main__":
    _bootstrap()
