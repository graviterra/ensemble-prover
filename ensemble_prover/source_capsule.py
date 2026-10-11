"""Opt-in private, bounded source blobs for reproducing local execution inputs."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import uuid
from pathlib import Path, PurePosixPath
from typing import Any

from .run_provenance import _git_bytes


_LOCKS = frozenset({"pyproject.toml", "uv.lock", "poetry.lock", "requirements.txt",
    "requirements-runtime.txt", "requirements-interface.txt", "requirements_mini_maybe.txt",
    "lean_project/lean-toolchain", "lean_project/lakefile.toml", "lean_project/lake-manifest.json"})
_SENSITIVE = ("secret", "credential", ".env", "private_key", "access_token")


def _source_paths(root: Path) -> list[str]:
    raw = _git_bytes(root, "ls-files", "-z", "--cached", "--others", "--exclude-standard",
                     "--", "ensemble_prover", *_LOCKS)
    result = set()
    for value in raw.split(b"\0"):
        if not value:
            continue
        name = os.fsdecode(value)
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or any(
            marker in part.lower() for part in path.parts for marker in _SENSITIVE
        ):
            continue
        if name in _LOCKS or (path.parts[0] == "ensemble_prover" and path.suffix == ".py"):
            result.add(name)
    return sorted(result)


def _read_source(root: Path, name: str, limit: int) -> tuple[dict[str, Any], bytes | None]:
    """Open each component without following symlinks, including ancestors."""
    parts = PurePosixPath(name).parts
    if not parts or PurePosixPath(name).is_absolute() or ".." in parts:
        raise ValueError("invalid source path")
    descriptor = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for part in parts[:-1]:
            next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = next_fd
        info = os.stat(parts[-1], dir_fd=descriptor, follow_symlinks=False)
        entry: dict[str, Any] = {"path": name, "mode": stat.S_IMODE(info.st_mode)}
        if stat.S_ISLNK(info.st_mode):
            return {**entry, "kind": "symlink", "target": os.readlink(parts[-1], dir_fd=descriptor)}, None
        if not stat.S_ISREG(info.st_mode):
            return {**entry, "kind": "omitted", "reason": "nonregular"}, None
        if info.st_size > limit:
            return {**entry, "kind": "omitted", "reason": "byte_limit", "size": info.st_size}, None
        fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=descriptor)
        with os.fdopen(fd, "rb") as handle:
            before = os.fstat(handle.fileno())
            if not stat.S_ISREG(before.st_mode):
                return {**entry, "kind": "omitted", "reason": "type_changed"}, None
            data = handle.read(limit + 1)
            after = os.fstat(handle.fileno())
        if len(data) > limit:
            return {**entry, "kind": "omitted", "reason": "byte_limit"}, None
        def identity(s: os.stat_result) -> tuple[int, ...]:
            return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_mode)

        if identity(info) != identity(before) or identity(before) != identity(after):
            return {**entry, "kind": "omitted", "reason": "changed_during_read"}, None
        return {**entry, "kind": "file", "size": len(data),
                "sha256": hashlib.sha256(data).hexdigest()}, data
    except FileNotFoundError:
        return {"path": name, "kind": "absent"}, None
    except OSError as error:
        return {"path": name, "kind": "omitted", "reason": type(error).__name__}, None
    finally:
        os.close(descriptor)


def _private_write(path: Path, data: bytes) -> None:
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())


def capture_source_capsule(repository_root: Path, output_dir: Path, *,
                           max_bytes: int = 64 * 1024 * 1024) -> dict[str, Any]:
    """Capture allowlisted source without claiming that execution is pinned.

    Blobs and names are private run artifacts. Environment variables, credentials,
    arbitrary untracked files, and outside-root symlink contents are excluded.
    """
    root = Path(repository_root).resolve()
    parent = Path(output_dir) / "source-capsule"
    parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    if parent.is_symlink():
        raise ValueError("source capsule directory must not be a symlink")
    destination = parent / uuid.uuid4().hex
    destination.mkdir(mode=0o700)
    blobs = destination / "blobs"
    blobs.mkdir(mode=0o700)
    commit = _git_bytes(root, "rev-parse", "HEAD").decode("ascii").strip()
    paths = _source_paths(root)
    entries = []
    remaining = max(0, int(max_bytes))
    for name in paths:
        entry, data = _read_source(root, name, remaining)
        entries.append(entry)
        if data is not None:
            blob = blobs / entry["sha256"]
            if not blob.exists():
                _private_write(blob, data)
            remaining -= len(data)
    stable = paths == _source_paths(root) and commit == _git_bytes(root, "rev-parse", "HEAD").decode("ascii").strip()
    for entry in entries:
        if entry["kind"] == "omitted":
            continue
        checked, _ = _read_source(root, entry["path"], max(0, int(max_bytes)))
        stable &= checked == entry
    omitted = sum(entry["kind"] == "omitted" for entry in entries)
    manifest = {
        "schema_version": 1, "git_commit": commit,
        "scope": "allowlisted_python_runtime_and_lock_files", "files": entries,
        "stable_capture": bool(stable), "complete_within_scope": bool(stable and not omitted),
        "omitted_count": omitted, "execution_pinned": False, "replay_complete": False,
        "excluded": ["environment", "credential_paths", "unrelated_untracked_files", "symlink_contents"],
    }
    encoded = json.dumps(manifest, ensure_ascii=True, sort_keys=True, indent=2).encode()
    manifest_path = destination / "manifest.json"
    _private_write(manifest_path, encoded)
    return {key: manifest[key] for key in (
        "scope", "stable_capture", "complete_within_scope", "omitted_count", "execution_pinned", "replay_complete",
    )} | {"manifest_path": str(manifest_path), "manifest_sha256": hashlib.sha256(encoded).hexdigest()}
