"""Owned process groups for synchronous Lean checks and export builds."""
from __future__ import annotations

import os
import signal
import subprocess
from collections.abc import Mapping, Sequence

from .subprocess_environment import sanitized_subprocess_environment

_DEFAULT_REAP_TIMEOUT_S = 5.0


def run_process_group(
    arguments: Sequence[str],
    *,
    cwd: str | os.PathLike[str],
    timeout: float,
    env: Mapping[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Capture a synchronous check and retire its descendants on interruption.

    Lake may start a compiler or parallel build workers. Killing only Lake on
    timeout leaves those workers running, including after Lake itself exited
    while a descendant still holds the output pipe open.
    """
    proc = subprocess.Popen(
        arguments, cwd=cwd, env=sanitized_subprocess_environment(env),
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    try:
        output, _ = proc.communicate(timeout=timeout)
        return subprocess.CompletedProcess(arguments, proc.returncode, output)
    except BaseException:
        # Signal the group even when communicate has already reaped its leader.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except OSError:
            try:
                proc.kill()
            except OSError:
                pass
        try:
            proc.wait(timeout=_DEFAULT_REAP_TIMEOUT_S)
        except (OSError, subprocess.TimeoutExpired):
            pass
        raise
    finally:
        if proc.stdout is not None:
            proc.stdout.close()
