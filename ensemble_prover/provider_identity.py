"""Installation-scoped credential identifiers for persisted provider lanes."""

from __future__ import annotations

import fcntl
import hmac
import os
import stat
import threading
import time
from contextlib import ExitStack, contextmanager
from pathlib import Path
from typing import Iterator

_KEY_BYTES = 32
_KEY_NAME = "provider-identity.key"
_LOCK_NAME = "provider-identity.lock"
_INITIALIZED = b"ensemble-prover-provider-identity-v2\n"
_DOMAIN = b"ensemble-prover/provider-credential/v2\x00"
_KEY_CACHE: dict[Path, bytes] = {}
_KEY_CACHE_LOCK = threading.Lock()
_LOCK_TIMEOUT_SECONDS = 5.0


def _before_fork() -> None:
    # Inheriting a live flock descriptor can keep the parent's lock held even
    # after its operation finishes. Fork only once cold key I/O has closed.
    _KEY_CACHE_LOCK.acquire()


def _after_fork_parent() -> None:
    _KEY_CACHE_LOCK.release()


def _after_fork_child() -> None:
    global _KEY_CACHE_LOCK
    _KEY_CACHE_LOCK = threading.Lock()


os.register_at_fork(
    before=_before_fork,
    after_in_parent=_after_fork_parent,
    after_in_child=_after_fork_child,
)


class ProviderIdentityError(RuntimeError):
    """Protected provider identity state is unavailable or unsafe."""


def _state_directory() -> Path:
    configured = os.environ.get("XDG_STATE_HOME", "")
    root = Path(configured) if configured else Path.home() / ".local" / "state"
    if not root.is_absolute() or ".." in root.parts:
        raise ProviderIdentityError(
            "Provider identity state directory must be an absolute path without '..'"
        )
    return root / "ensemble-prover"


def _validate_private(fd: int, *, directory: bool = False) -> None:
    info = os.fstat(fd)
    expected_mode = 0o700 if directory else 0o600
    correct_type = (
        stat.S_ISDIR(info.st_mode) if directory else stat.S_ISREG(info.st_mode)
    )
    if (
        not correct_type
        or info.st_uid != os.getuid()
        or stat.S_IMODE(info.st_mode) != expected_mode
        or (not directory and info.st_nlink != 1)
    ):
        raise ProviderIdentityError(
            "Identity state must be owned by the current user, with directory mode 0700 and regular-file mode 0600"
        )


@contextmanager
def _open_state_directory(path: Path) -> Iterator[tuple[int, bool]]:
    # Resolve only ancestors on a cold load. The protected final directory
    # stays subject to O_NOFOLLOW, and cached identities need no path I/O.
    try:
        path = path.parent.resolve() / path.name
    except (OSError, RuntimeError) as exc:
        raise ProviderIdentityError(
            "Cannot resolve provider identity state root"
        ) from exc
    flags = os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
    skipped_parent_sync = False
    with ExitStack() as stack:
        current = os.open(path.anchor, os.O_PATH | flags)
        stack.callback(os.close, current)
        for index, component in enumerate(path.parts[1:], 1):
            final = index == len(path.parts) - 1
            try:
                os.stat(component, dir_fd=current, follow_symlinks=False)
                existing = True
            except FileNotFoundError:
                existing = False
            try:
                parent = os.open(".", os.O_RDONLY | flags, dir_fd=current)
            except PermissionError:
                if not existing:
                    raise
                # An unchanged ancestor requires search permission, not list
                # permission. No directory entry is created through this fd.
                parent = None
                skipped_parent_sync = True
            if parent is not None:
                try:
                    if not existing:
                        # Obtain a sync-capable parent before creating a child:
                        # a failed read-open must never leave an unsynced entry.
                        try:
                            os.mkdir(component, 0o700, dir_fd=current)
                        except FileExistsError:
                            pass
                    # Retry even for existing readable ancestors after a prior
                    # mkdir succeeded but its parent fsync failed.
                    os.fsync(parent)
                finally:
                    os.close(parent)
            current = os.open(
                component,
                (os.O_RDONLY if final else os.O_PATH) | flags,
                dir_fd=current,
            )
            stack.callback(os.close, current)
        _validate_private(current, directory=True)
        yield current, skipped_parent_sync


def _write_all(fd: int, data: bytes) -> None:
    remaining = memoryview(data)
    while remaining:
        written = os.write(fd, remaining)
        if written <= 0:
            raise OSError("Identity state write made no progress")
        remaining = remaining[written:]


def _read_bounded(fd: int, limit: int) -> bytes:
    content = bytearray()
    while len(content) <= limit:
        chunk = os.read(fd, limit + 1 - len(content))
        if not chunk:
            break
        content.extend(chunk)
    return bytes(content)


def _read_or_create_key(directory: int, initialized: bool) -> bytes:
    flags = os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK
    created = False
    try:
        key_fd = os.open(_KEY_NAME, os.O_RDONLY | flags, dir_fd=directory)
    except FileNotFoundError:
        if initialized:
            raise ProviderIdentityError(
                "Initialized provider identity key is missing; restore the original key"
            ) from None
        key_fd = os.open(
            _KEY_NAME,
            os.O_RDWR | os.O_CREAT | os.O_EXCL | flags,
            0o600,
            dir_fd=directory,
        )
        created = True
    with ExitStack() as stack:
        stack.callback(os.close, key_fd)
        _validate_private(key_fd)
        if created:
            key = os.urandom(_KEY_BYTES)
            _write_all(key_fd, key)
        else:
            key = _read_bounded(key_fd, _KEY_BYTES)
        if len(key) != _KEY_BYTES:
            raise ProviderIdentityError(
                "Provider identity key has invalid length; restore the original key"
            )
        # Do not remove partial or damaged files: a later call must report the
        # damage instead of assigning a new identity to existing receipts.
        os.fsync(key_fd)
        os.fsync(directory)
        return key


def _load_key(path: Path) -> bytes:
    with _open_state_directory(path) as (directory, skipped_parent_sync):
        flags = os.O_RDWR | os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK
        try:
            lock_fd = os.open(
                _LOCK_NAME,
                flags | os.O_CREAT | os.O_EXCL,
                0o600,
                dir_fd=directory,
            )
        except FileExistsError:
            lock_fd = os.open(_LOCK_NAME, flags, dir_fd=directory)
        with ExitStack() as stack:
            stack.callback(os.close, lock_fd)
            _validate_private(lock_fd)
            deadline = time.monotonic() + _LOCK_TIMEOUT_SECONDS
            while True:
                try:
                    fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise ProviderIdentityError(
                            "Provider identity initialization lock timed out; retry after the other process finishes"
                        ) from None
                    time.sleep(min(0.01, remaining))
            marker = _read_bounded(lock_fd, len(_INITIALIZED))
            if marker not in (b"", _INITIALIZED):
                raise ProviderIdentityError(
                    "Provider identity initialization record is invalid"
                )
            if skipped_parent_sync and marker != _INITIALIZED:
                raise ProviderIdentityError(
                    "Cannot initialize provider identity through an unreadable ancestor; "
                    "restore directory read permission and retry"
                )
            key = _read_or_create_key(directory, marker == _INITIALIZED)
            if not marker:
                os.lseek(lock_fd, 0, os.SEEK_SET)
                _write_all(lock_fd, _INITIALIZED)
            os.fsync(lock_fd)
            os.fsync(directory)
            return key


def credential_hmac_sha256(credential: str) -> str:
    """Identify a credential without exposing a reusable unkeyed verifier.

    The installation key is loaded lazily and cached by state location. Raw
    credentials are never cached or written to the identity state directory.
    """

    if not credential:
        return ""
    path = _state_directory()
    with _KEY_CACHE_LOCK:
        key = _KEY_CACHE.get(path)
        if key is None:
            try:
                key = _load_key(path)
            except (OSError, ProviderIdentityError) as exc:
                raise ProviderIdentityError(
                    f"Cannot use provider identity state at {path}: {exc}"
                ) from exc
            _KEY_CACHE[path] = key
        # Keep initial cryptographic backend setup inside the fork guard too.
        return hmac.digest(
            key, _DOMAIN + credential.encode("utf-8", errors="replace"), "sha256"
        ).hex()
