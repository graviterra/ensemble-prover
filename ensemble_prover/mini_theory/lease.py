"""Kernel-liveness ownership for crash-safe persistent Mini theory work."""

from __future__ import annotations

import fcntl
import uuid
from pathlib import Path
from typing import BinaryIO, Optional


def _release_file_handle(
    handle: BinaryIO,
    *,
    unlock: bool,
    label: str,
    primary: Optional[BaseException] = None,
) -> None:
    """Release a flock/file handle without replacing an earlier stop."""

    cleanup_errors: list[BaseException] = []
    cleanups = []
    if unlock:
        cleanups.append(lambda: fcntl.flock(handle.fileno(), fcntl.LOCK_UN))
    cleanups.append(handle.close)
    for cleanup in cleanups:
        try:
            cleanup()
        except BaseException as cleanup_error:
            cleanup_errors.append(cleanup_error)
    if primary is not None:
        for cleanup_error in cleanup_errors:
            primary.add_note(
                f"{label} also failed: {type(cleanup_error).__name__}: "
                f"{cleanup_error}"
            )
        return
    if cleanup_errors:
        first = next(
            (
                cleanup_error
                for cleanup_error in cleanup_errors
                if not isinstance(cleanup_error, Exception)
            ),
            cleanup_errors[0],
        )
        for cleanup_error in cleanup_errors:
            if cleanup_error is first:
                continue
            first.add_note(
                f"{label} also failed: {type(cleanup_error).__name__}: "
                f"{cleanup_error}"
            )
        raise first


class _ExclusiveFileLock:
    """Small flock guard whose cleanup cannot replace an active exception."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.handle: Optional[BinaryIO] = None

    def __enter__(self) -> "_ExclusiveFileLock":
        self.handle = self.path.open("a+b")
        try:
            fcntl.flock(self.handle.fileno(), fcntl.LOCK_EX)
        except BaseException as primary:
            _release_file_handle(
                self.handle,
                unlock=True,
                label="Mini theory owner cleanup-lock acquisition cleanup",
                primary=primary,
            )
            raise
        return self

    def __exit__(self, _exc_type, exc, _traceback) -> bool:
        assert self.handle is not None
        _release_file_handle(
            self.handle,
            unlock=True,
            label="Mini theory owner cleanup-lock cleanup",
            primary=exc,
        )
        return False


class TheoryLeaseOwner:
    """Hold a process-lifetime flock used to prove whether work was abandoned."""

    def __init__(self, root: Path, *, owner_id: str = "") -> None:
        self.root = Path(root).expanduser().resolve()
        self.owners_root = self.root / ".owners"
        self.owners_root.mkdir(parents=True, exist_ok=True)
        self.owner_id = str(owner_id or uuid.uuid4().hex)
        if not self._valid_owner_id(self.owner_id):
            raise ValueError(f"invalid theory lease owner id: {self.owner_id!r}")
        self.lock_path = self.owners_root / f"{self.owner_id}.lock"
        self._handle: Optional[BinaryIO] = None
        handle: Optional[BinaryIO] = None
        created_owner_path = False
        try:
            # Creating the owner path and taking its first lock must be one
            # cleanup-serialized operation. Otherwise an observer can open the
            # newly created but not-yet-locked inode and falsely prove death.
            with self._cleanup_lock():
                owner_path_preexisting = self.lock_path.exists()
                handle = self.lock_path.open("a+b")
                created_owner_path = not owner_path_preexisting
                try:
                    fcntl.flock(
                        handle.fileno(),
                        fcntl.LOCK_EX | fcntl.LOCK_NB,
                    )
                except BaseException as primary:
                    # Withdraw a freshly created pathname before releasing
                    # the cleanup lock.  Once that serialization is gone, a
                    # same-id replacement may legitimately lock this inode;
                    # an older failed creator must never unlink it afterward.
                    if created_owner_path:
                        try:
                            self.lock_path.unlink()
                        except FileNotFoundError:
                            pass
                        except BaseException as pathname_error:
                            primary.add_note(
                                "Mini theory owner failed-lock pathname "
                                "cleanup also failed: "
                                f"{type(pathname_error).__name__}: "
                                f"{pathname_error}"
                            )
                    _release_file_handle(
                        handle,
                        unlock=True,
                        label="Mini theory owner initialization cleanup",
                        primary=primary,
                    )
                    handle = None
                    raise
        except BaseException as primary:
            if handle is not None:
                if created_owner_path:
                    try:
                        self.lock_path.unlink()
                    except FileNotFoundError:
                        pass
                    except BaseException as pathname_error:
                        primary.add_note(
                            "Mini theory owner failed-lock pathname cleanup "
                            f"also failed: {type(pathname_error).__name__}: "
                            f"{pathname_error}"
                        )
                _release_file_handle(
                    handle,
                    unlock=True,
                    label="Mini theory owner initialization cleanup",
                    primary=primary,
                )
            raise
        self._handle = handle
        try:
            self.cleanup_abandoned_owner_files()
        except BaseException as primary:
            self._handle = None
            assert handle is not None
            try:
                # Construction never hands this owner to a caller, so its
                # unique pathname must be withdrawn while the acquired lease
                # is still held. Otherwise a failed startup leaves the exact
                # empty tombstone that clean close is designed to prevent.
                with self._cleanup_lock():
                    try:
                        self.lock_path.unlink()
                    except FileNotFoundError:
                        pass
            except BaseException as pathname_error:
                primary.add_note(
                    "Mini theory owner failed-construction pathname cleanup "
                    f"also failed: {type(pathname_error).__name__}: "
                    f"{pathname_error}"
                )
                try:
                    # The owner id is unique and its descriptor is still
                    # locked. If cleanup serialization itself is unavailable,
                    # direct withdrawal is the same safe fallback used by
                    # close/finalization.
                    self.lock_path.unlink()
                except FileNotFoundError:
                    pass
                except BaseException as fallback_error:
                    primary.add_note(
                        "Mini theory owner failed-construction pathname "
                        "fallback also failed: "
                        f"{type(fallback_error).__name__}: {fallback_error}"
                    )
            _release_file_handle(
                handle,
                unlock=True,
                label="Mini theory owner post-lock initialization cleanup",
                primary=primary,
            )
            raise

    def cleanup_abandoned_owner_files(self) -> tuple[str, ...]:
        """Remove stale owner files only after proving their locks are free.

        Owner identifiers are never reused.  A missing owner file is already
        defined as an abandoned owner, so removing a lock after acquiring it
        cannot weaken recovery correctness.  A dedicated cleanup lock prevents
        competing cleaners from unlinking the same inode concurrently.
        """

        removed: list[str] = []
        with self._cleanup_lock():
            for path in sorted(self.owners_root.glob("*.lock")):
                owner_id = path.stem
                if owner_id == self.owner_id or not self._valid_owner_id(owner_id):
                    continue
                try:
                    owner_handle = path.open("a+b")
                    try:
                        fcntl.flock(
                            owner_handle.fileno(),
                            fcntl.LOCK_EX | fcntl.LOCK_NB,
                        )
                    except BlockingIOError:
                        _release_file_handle(
                            owner_handle,
                            unlock=False,
                            label="Mini theory live-owner probe cleanup",
                        )
                        continue
                    except BaseException as primary:
                        _release_file_handle(
                            owner_handle,
                            unlock=True,
                            label="Mini theory abandoned-owner lock cleanup",
                            primary=primary,
                        )
                        raise
                    try:
                        path.unlink()
                        removed.append(owner_id)
                    except BaseException as primary:
                        _release_file_handle(
                            owner_handle,
                            unlock=True,
                            label="Mini theory abandoned-owner cleanup",
                            primary=primary,
                        )
                        raise
                    else:
                        _release_file_handle(
                            owner_handle,
                            unlock=True,
                            label="Mini theory abandoned-owner cleanup",
                        )
                except FileNotFoundError:
                    continue
        return tuple(removed)

    def close(self) -> None:
        # Finalizers may observe an instance whose construction was interrupted
        # before ``_handle`` was installed.  Treat it as already closed; there
        # is no owned descriptor to release in that state.
        handle = getattr(self, "_handle", None)
        if handle is None:
            return
        self._handle = None
        try:
            # Withdraw the unique owner pathname while its kernel lease is
            # still held and under the same serialization used by liveness
            # probes.  A clean shutdown must not leave a dead-owner tombstone
            # waiting for some future process to perform incidental cleanup.
            with self._cleanup_lock():
                try:
                    self.lock_path.unlink()
                except FileNotFoundError:
                    pass
        except BaseException as primary:
            try:
                # The unique pathname is owned only by this still-locked
                # descriptor. If serialization itself is interrupted, direct
                # withdrawal remains safe and avoids an unretryable tombstone.
                self.lock_path.unlink()
            except FileNotFoundError:
                pass
            except BaseException as pathname_error:
                primary.add_note(
                    "Mini theory owner close pathname fallback also failed: "
                    f"{type(pathname_error).__name__}: {pathname_error}"
                )
            try:
                _release_file_handle(
                    handle,
                    unlock=True,
                    label="Mini theory owner descriptor cleanup",
                )
            except BaseException as release_error:
                if (
                    not isinstance(release_error, Exception)
                    and isinstance(primary, Exception)
                ):
                    release_error.add_note(
                        "owner pathname cleanup also failed: "
                        f"{type(primary).__name__}: {primary}"
                    )
                    raise release_error
                primary.add_note(
                    "Mini theory owner descriptor cleanup also failed: "
                    f"{type(release_error).__name__}: {release_error}"
                )
            raise
        _release_file_handle(
            handle,
            unlock=True,
            label="Mini theory owner descriptor cleanup",
        )

    def owner_abandoned(self, owner_id: str) -> Optional[bool]:
        """Return true only when the owner's kernel lock is provably free."""

        clean = str(owner_id or "").strip()
        if not self._valid_owner_id(clean):
            return None
        try:
            with self._cleanup_lock():
                path = self.owners_root / f"{clean}.lock"
                if not path.is_file():
                    return True
                handle = path.open("a+b")
                try:
                    fcntl.flock(
                        handle.fileno(),
                        fcntl.LOCK_EX | fcntl.LOCK_NB,
                    )
                except BlockingIOError:
                    _release_file_handle(
                        handle,
                        unlock=False,
                        label="Mini theory live-owner abandonment probe cleanup",
                    )
                    return False
                except BaseException as primary:
                    _release_file_handle(
                        handle,
                        unlock=True,
                        label="Mini theory abandonment probe cleanup",
                        primary=primary,
                    )
                    raise
                _release_file_handle(
                    handle,
                    unlock=True,
                    label="Mini theory abandonment probe cleanup",
                )
                return True
        except OSError:
            return None

    def _cleanup_lock(self) -> _ExclusiveFileLock:
        return _ExclusiveFileLock(self.owners_root / ".cleanup.lock")

    @staticmethod
    def _valid_owner_id(owner_id: str) -> bool:
        clean = str(owner_id or "")
        return len(clean) == 32 and all(char in "0123456789abcdef" for char in clean)

    def __enter__(self) -> "TheoryLeaseOwner":
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def __del__(self) -> None:
        # GC/interpreter teardown must not enter flock/context-manager
        # machinery: test monkeypatch teardown and partially finalized modules
        # can make that path re-entrant or unsafe. Explicit ``close`` provides
        # the serialized, error-reporting lifecycle. Here the owner is already
        # unreachable, so withdraw its unique pathname and release the kernel
        # lease directly, suppressing every finalizer-time failure.
        handle = getattr(self, "_handle", None)
        if handle is None:
            return
        self._handle = None
        try:
            self.lock_path.unlink()
        except BaseException:
            pass
        try:
            _release_file_handle(
                handle,
                unlock=True,
                label="Mini theory owner finalizer cleanup",
            )
        except BaseException:
            pass
