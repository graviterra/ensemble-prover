"""Restore the caller's signal mask before executing an owned export command."""

from __future__ import annotations

import os
import signal
import sys


def main() -> None:
    # Popen runs with termination blocked until the embedding caller owns its
    # handle. Restore exactly the pre-launch mask, including intentional blocks,
    # in a fresh interpreter; no Python runs between fork and exec in the parent.
    mask = {int(value) for value in sys.argv[1].split(',') if value}
    command = sys.argv[2:]
    signal.pthread_sigmask(signal.SIG_SETMASK, mask)
    os.execvpe(command[0], command, os.environ)


if __name__ == '__main__':
    main()
