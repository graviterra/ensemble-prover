"""Bound source ingestion to regular files, including during replacement races."""

from __future__ import annotations

import os
import stat
from pathlib import Path


def read_source_bytes(path: Path) -> bytes:
    # Nonblocking open prevents a FIFO replacement from hanging before fstat.
    # Explicit symlink inputs are resolved once by the discovery boundary;
    # replacements at the captured source path must not redirect the request.
    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(descriptor, "rb") as handle:
        if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
            raise ValueError(f"Lean input is not a regular file: {path}")
        return handle.read()
