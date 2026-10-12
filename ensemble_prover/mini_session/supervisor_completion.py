"""Positive cleanup evidence for private, process-owning supervisors."""

from __future__ import annotations

import os
import uuid
from dataclasses import dataclass
from typing import Any


_COMPLETION_FD_ENV = "ENSEMBLE_SUPERVISOR_COMPLETION_FD"
_COMPLETION_NONCE_ENV = "ENSEMBLE_SUPERVISOR_COMPLETION_NONCE"


class _WorkerCleanupIncomplete(RuntimeError):
    """The run directory may still have live writers; no handoff is permitted."""


@dataclass
class _WorkerCleanupState:
    """Carry cleanup authority independently of exception delivery."""

    complete: bool = False


def _completion_frame(nonce: str) -> bytes:
    return f"ensemble-supervisor-complete-v1:{nonce}\n".encode("ascii")


class SupervisorCompletionChannel:
    """Require a fresh supervisor receipt before consuming its outcome.

    Call ``begin_launch`` immediately before Popen and ``close_parent_writer``
    after acquiring its handle. Call ``finalize`` in the last parent finally,
    after all other resource release attempts. Pass any exception caught from
    that operation explicitly; a caller's handled exception is not ours.
    """

    def __init__(self) -> None:
        self._nonce = uuid.uuid4().hex
        self._read_fd, self._write_fd = os.pipe()
        self._launch_attempted = False
        try:
            os.set_blocking(self._read_fd, False)
        except BaseException:
            try:
                os.close(self._read_fd)
            finally:
                os.close(self._write_fd)
            raise

    @property
    def pass_fds(self) -> tuple[int, ...]:
        return (self._write_fd,)

    @property
    def environment(self) -> dict[str, str]:
        return {
            _COMPLETION_FD_ENV: str(self._write_fd),
            _COMPLETION_NONCE_ENV: self._nonce,
        }

    def begin_launch(self) -> None:
        self._launch_attempted = True

    def close_parent_writer(self) -> None:
        if self._write_fd >= 0:
            descriptor, self._write_fd = self._write_fd, -1
            os.close(descriptor)

    def finalize(
        self,
        proc: Any,
        *,
        local_cleanup_complete: bool = True,
        pending_error: BaseException | None = None,
    ) -> None:
        """Close transport and preserve cleanup authority over other failures."""
        confirmed = False
        try:
            if self._launch_attempted and local_cleanup_complete and proc is not None:
                returncode = proc.returncode
                if returncode is None:
                    returncode = proc.poll()
                if returncode is not None:
                    expected = _completion_frame(self._nonce)
                    confirmed = os.read(self._read_fd, len(expected) + 1) == expected
        except BaseException as exc:
            if pending_error is None:
                pending_error = exc
        finally:
            for attribute in ("_write_fd", "_read_fd"):
                descriptor = getattr(self, attribute)
                setattr(self, attribute, -1)
                if descriptor >= 0:
                    try:
                        os.close(descriptor)
                    except BaseException as exc:
                        if pending_error is None:
                            pending_error = exc
            if self._launch_attempted and not confirmed:
                raise _WorkerCleanupIncomplete(
                    "Private supervisor cleanup completion was not confirmed"
                ) from None
            if pending_error is not None:
                raise pending_error


class SupervisorCompletionWriter:
    """A supervisor-only descriptor, excluded from every worker subprocess."""

    def __init__(self, descriptor: int = -1, nonce: str = "") -> None:
        self._descriptor = descriptor
        self._nonce = nonce

    def finish(
        self,
        cleanup_state: _WorkerCleanupState,
        *,
        pending_error: BaseException | None = None,
    ) -> None:
        """Emit only an explicit completed cleanup; always close our writer."""
        if self._descriptor < 0:
            if pending_error is not None:
                raise pending_error
            return
        descriptor, self._descriptor = self._descriptor, -1
        try:
            if cleanup_state.complete is True:
                frame = _completion_frame(self._nonce)
                if os.write(descriptor, frame) != len(frame):
                    raise OSError("Incomplete supervisor completion receipt")
        except BaseException as exc:
            if pending_error is None:
                pending_error = exc
        finally:
            try:
                os.close(descriptor)
            except BaseException as exc:
                if pending_error is None:
                    pending_error = exc
            if pending_error is not None:
                raise pending_error


def adopt_supervisor_completion() -> SupervisorCompletionWriter:
    """Adopt the private launch capability without passing it to workers."""
    descriptor_text = os.environ.pop(_COMPLETION_FD_ENV, None)
    nonce = os.environ.pop(_COMPLETION_NONCE_ENV, None)
    if descriptor_text is None and nonce is None:
        return SupervisorCompletionWriter()
    if descriptor_text is None or nonce is None:
        raise ValueError("Incomplete supervisor completion transport")
    descriptor = int(descriptor_text)
    if descriptor < 3:
        raise ValueError("Invalid supervisor completion descriptor")
    try:
        os.set_inheritable(descriptor, False)
        if len(nonce) != 32 or any(character not in "0123456789abcdef" for character in nonce):
            raise ValueError("Invalid supervisor completion nonce")
        return SupervisorCompletionWriter(descriptor, nonce)
    except BaseException:
        os.close(descriptor)
        raise
