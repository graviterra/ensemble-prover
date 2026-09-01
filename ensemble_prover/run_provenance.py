"""Bounded source-checkout provenance for run artifacts."""

from __future__ import annotations

import hashlib
import os
import subprocess
from pathlib import Path
from typing import Any, Iterable

from .subprocess_environment import sanitized_subprocess_environment


_GIT_TIMEOUT_S = 5.0
_MAX_DIRTY_PATHS = 4096
_MAX_HASHED_CONTENT_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 1024 * 1024


def _git_bytes(cwd: Path, *args: str) -> bytes:
    completed = subprocess.run(
        ["git", *args],
        cwd=cwd,
        env=sanitized_subprocess_environment(),
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=_GIT_TIMEOUT_S,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(detail or f"git {' '.join(args)} failed")
    return bytes(completed.stdout)


def _dirty_paths(status: bytes) -> tuple[list[bytes], int, bool]:
    """Extract path bytes from porcelain-v1 -z, including rename pairs."""

    records = status.split(b"\0")
    paths: list[bytes] = []
    index = 0
    while index < len(records):
        record = records[index]
        index += 1
        if not record:
            continue
        if len(record) < 4:
            continue
        disposition = record[:2]
        paths.append(record[3:])
        if (b"R" in disposition or b"C" in disposition) and index < len(records):
            renamed_path = records[index]
            index += 1
            if renamed_path:
                paths.append(renamed_path)
    unique = sorted(dict.fromkeys(path for path in paths if path))
    return unique[:_MAX_DIRTY_PATHS], len(unique), len(unique) > _MAX_DIRTY_PATHS


def _hash_dirty_content(
    digest: Any,
    *,
    repository_root: Path,
    paths: Iterable[bytes],
) -> bool:
    remaining = _MAX_HASHED_CONTENT_BYTES
    truncated = False
    for raw_path in paths:
        digest.update(b"\0path\0")
        digest.update(raw_path)
        path_text = os.fsdecode(raw_path)
        candidate = repository_root / path_text
        try:
            if candidate.is_symlink():
                digest.update(b"\0symlink\0")
                digest.update(os.fsencode(os.readlink(candidate)))
                continue
            resolved = candidate.resolve(strict=False)
            if not resolved.is_relative_to(repository_root):
                digest.update(b"\0outside-root")
                continue
            if not candidate.is_file():
                digest.update(b"\0absent-or-nonfile")
                continue
            size = candidate.stat().st_size
            digest.update(f"\0size:{size}\0".encode("ascii"))
            if remaining <= 0:
                truncated = True
                continue
            with candidate.open("rb") as handle:
                while remaining > 0:
                    chunk = handle.read(min(_READ_CHUNK_BYTES, remaining))
                    if not chunk:
                        break
                    digest.update(chunk)
                    remaining -= len(chunk)
                if handle.read(1):
                    truncated = True
        except OSError as exc:
            digest.update(
                f"\0read-error:{type(exc).__name__}".encode(
                    "ascii", errors="replace"
                )
            )
    return truncated


def capture_repository_provenance(start_path: Path | str) -> dict[str, Any]:
    """Capture commit and a content-sensitive dirty-state fingerprint.

    The summary exposes no source contents or filenames. Hashing is bounded so
    an unexpectedly large untracked artifact cannot delay run startup without
    limit; ``content_hash_truncated`` makes that loss of precision explicit.
    """

    start = Path(start_path).resolve()
    cwd = start if start.is_dir() else start.parent
    base: dict[str, Any] = {
        "schema_version": 1,
        "capture_phase": "pre_output_allocation",
        "available": False,
        "repository_root": "",
        "git_commit": "",
        "git_branch": "",
        "worktree_dirty": False,
        "dirty_path_count": 0,
        "source_state_sha256": "",
        "content_hash_truncated": False,
        "capture_error": "",
    }
    try:
        root_text = _git_bytes(cwd, "rev-parse", "--show-toplevel").decode(
            "utf-8", errors="strict"
        ).strip()
        repository_root = Path(root_text).resolve()
        commit = _git_bytes(repository_root, "rev-parse", "HEAD").decode(
            "ascii", errors="strict"
        ).strip()
        try:
            branch = _git_bytes(
                repository_root,
                "symbolic-ref",
                "--quiet",
                "--short",
                "HEAD",
            ).decode("utf-8", errors="replace").strip()
        except RuntimeError:
            branch = ""
        status = _git_bytes(
            repository_root,
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
        )
        paths, dirty_path_count, paths_truncated = _dirty_paths(status)
        digest = hashlib.sha256()
        digest.update(b"ensemble-run-source-state-v1\0")
        digest.update(commit.encode("ascii", errors="replace"))
        digest.update(b"\0status\0")
        digest.update(status)
        content_truncated = _hash_dirty_content(
            digest,
            repository_root=repository_root,
            paths=paths,
        )
        base.update(
            available=True,
            repository_root=str(repository_root),
            git_commit=commit,
            git_branch=branch,
            worktree_dirty=bool(status),
            dirty_path_count=dirty_path_count,
            source_state_sha256=digest.hexdigest(),
            content_hash_truncated=bool(paths_truncated or content_truncated),
        )
    except (OSError, RuntimeError, subprocess.SubprocessError, UnicodeError) as exc:
        base["capture_error"] = f"{type(exc).__name__}: {exc}"[:500]
    return base
