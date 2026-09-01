"""Resolve and cache a caller-supplied Lean project's execution environment.

The cache avoids repeated Lake environment discovery while proof checks retain
their normal timeout and process-cleanup boundaries. Resolution failures fall
back to invoking Lean through the project's Lake environment.
"""

from __future__ import annotations

import asyncio
import concurrent.futures
import logging
import os
import threading
import time
from pathlib import Path
from typing import Awaitable, Callable, ClassVar, Dict, Optional, Tuple

from .subprocess_cleanup import (
    communicate_with_hard_timeout,
    terminate_and_reap_process,
)
from .subprocess_environment import sanitized_subprocess_environment

logger = logging.getLogger(__name__)

_LEAN_ENVIRONMENT_RESOLUTION_TIMEOUT_FLOOR_S = 300.0


def _captured_output_text(
    stdout_chunks: list[bytes], stderr_chunks: list[bytes]
) -> str:
    stdout_str = b"".join(stdout_chunks).decode(errors="replace")
    stderr_str = b"".join(stderr_chunks).decode(errors="replace")
    return stdout_str + ("\n" if stdout_str and stderr_str else "") + stderr_str


def _status_with_captured_output(
    status: str, stdout_chunks: list[bytes], stderr_chunks: list[bytes]
) -> str:
    detail = _captured_output_text(stdout_chunks, stderr_chunks).strip()
    if not detail:
        return status
    return f"{detail}\n{status}"


class LeanREPL:
    """Cached Lean environment for faster proof checking.

    On first use, resolves the lake environment (LEAN_PATH, lean binary)
    via ``lake env printenv`` and caches it.  Subsequent calls invoke
    ``lean`` directly, skipping the per-invocation ``lake`` overhead.

    Note that this is *not* a long-lived elaboration process: every check still
    runs in its own subprocess.  The cache only avoids repeating environment
    resolution.
    """

    _GLOBAL_ENV_CACHE: ClassVar[Dict[str, Tuple[str, str]]] = {}
    _GLOBAL_ENV_CACHE_LOCK: ClassVar[threading.Lock] = threading.Lock()
    _GLOBAL_ENV_EPOCH: ClassVar[Dict[str, int]] = {}
    _GLOBAL_ENV_CACHE_HITS: ClassVar[int] = 0
    _GLOBAL_ENV_CACHE_MISSES: ClassVar[int] = 0
    _GLOBAL_ENV_FAILURE_UNTIL: ClassVar[Dict[str, float]] = {}
    _GLOBAL_ENV_FAILURE_COOLDOWN_S: ClassVar[float] = 60.0
    _GLOBAL_ENV_ABANDONED: ClassVar[object] = object()
    _PROCESS_REAP_TIMEOUT_S: ClassVar[float] = 5.0
    _GLOBAL_ENV_INFLIGHT: ClassVar[
        Dict[str, concurrent.futures.Future[object]]
    ] = {}

    def __init__(
        self,
        project_dir: Path | str,
        timeout_s: int = 60,
        fast_fail_timeout_s: int = 20,
        fast_fail_enabled: bool = True,
        extra_lean_paths: tuple[str, ...] = (),
    ):
        self.project_dir = Path(project_dir).resolve()
        self.timeout_s = timeout_s
        self.fast_fail_timeout_s = fast_fail_timeout_s
        # fast_fail_enabled is accepted for API compatibility but not used:
        # direct lean invocations are normally silent on success, so
        # silence-based fast-fail would be counterproductive and could
        # prematurely terminate healthy runs.
        self._env: Optional[Dict[str, str]] = None
        self._lean_bin: Optional[str] = None
        self._lock = asyncio.Lock()
        self._lifecycle_lock = threading.Lock()
        self._lifecycle_generation = 0
        self._closed = False
        self._started = False
        self._failed = False
        self._environment_epoch: Optional[int] = None
        self._last_start_used_global_cache = False
        self._extra_lean_paths = tuple(
            dict.fromkeys(str(path) for path in extra_lean_paths if str(path).strip())
        )

    @property
    def project_cache_key(self) -> str:
        return str(self.project_dir)

    @classmethod
    def _get_global_env_cache(cls, key: str) -> Optional[Tuple[str, str]]:
        with cls._GLOBAL_ENV_CACHE_LOCK:
            cached = cls._GLOBAL_ENV_CACHE.get(key)
            if cached is not None:
                cls._GLOBAL_ENV_CACHE_HITS += 1
            else:
                cls._GLOBAL_ENV_CACHE_MISSES += 1
            return cached

    @classmethod
    def _set_global_env_cache(
        cls,
        key: str,
        lean_path: str,
        lean_bin: str,
        *,
        expected_epoch: Optional[int] = None,
    ) -> bool:
        with cls._GLOBAL_ENV_CACHE_LOCK:
            if (
                expected_epoch is not None
                and int(cls._GLOBAL_ENV_EPOCH.get(key, 0) or 0)
                != int(expected_epoch)
            ):
                return False
            cls._GLOBAL_ENV_CACHE[key] = (lean_path, lean_bin)
            cls._GLOBAL_ENV_FAILURE_UNTIL.pop(key, None)
            return True

    @classmethod
    def _clear_global_env_cache(cls, key: str) -> None:
        with cls._GLOBAL_ENV_CACHE_LOCK:
            cls._GLOBAL_ENV_CACHE.pop(key, None)
            cls._GLOBAL_ENV_FAILURE_UNTIL.pop(key, None)
            cls._GLOBAL_ENV_EPOCH[key] = (
                int(cls._GLOBAL_ENV_EPOCH.get(key, 0) or 0) + 1
            )
            stale_flight = cls._GLOBAL_ENV_INFLIGHT.pop(key, None)
            if stale_flight is not None and not stale_flight.done():
                stale_flight.set_result(cls._GLOBAL_ENV_ABANDONED)

    @classmethod
    def global_env_epoch(cls, key: str) -> int:
        """Return the publication epoch governing one project environment."""

        with cls._GLOBAL_ENV_CACHE_LOCK:
            return int(cls._GLOBAL_ENV_EPOCH.get(key, 0) or 0)

    @classmethod
    def environment_epoch_is_current(cls, key: str, epoch: int) -> bool:
        """Atomically admit use of coordinates bound to ``epoch``.

        The check is the linearization point for an environment-backed
        operation. An invalidation before admission rejects the stale
        coordinates; one after admission applies to subsequent operations.
        """

        with cls._GLOBAL_ENV_CACHE_LOCK:
            return int(cls._GLOBAL_ENV_EPOCH.get(key, 0) or 0) == int(epoch)

    @classmethod
    def _claim_global_resolution(
        cls, key: str
    ) -> tuple[bool, concurrent.futures.Future[object], int]:
        with cls._GLOBAL_ENV_CACHE_LOCK:
            epoch = int(cls._GLOBAL_ENV_EPOCH.get(key, 0) or 0)
            existing = cls._GLOBAL_ENV_INFLIGHT.get(key)
            if existing is not None:
                return False, existing, epoch
            future: concurrent.futures.Future[object] = (
                concurrent.futures.Future()
            )
            cls._GLOBAL_ENV_INFLIGHT[key] = future
            return True, future, epoch

    @classmethod
    def _finish_global_resolution(
        cls,
        key: str,
        future: concurrent.futures.Future[object],
        result: object,
    ) -> None:
        with cls._GLOBAL_ENV_CACHE_LOCK:
            if cls._GLOBAL_ENV_INFLIGHT.get(key) is future:
                cls._GLOBAL_ENV_INFLIGHT.pop(key, None)
            if not future.done():
                future.set_result(result)

    @classmethod
    def _global_resolution_in_cooldown(cls, key: str) -> bool:
        now = time.monotonic()
        with cls._GLOBAL_ENV_CACHE_LOCK:
            deadline = float(cls._GLOBAL_ENV_FAILURE_UNTIL.get(key, 0.0) or 0.0)
            if deadline <= now:
                cls._GLOBAL_ENV_FAILURE_UNTIL.pop(key, None)
                return False
            return True

    @classmethod
    def _record_global_resolution_failure(
        cls,
        key: str,
        *,
        expected_epoch: Optional[int] = None,
    ) -> bool:
        with cls._GLOBAL_ENV_CACHE_LOCK:
            if (
                expected_epoch is not None
                and int(cls._GLOBAL_ENV_EPOCH.get(key, 0) or 0)
                != int(expected_epoch)
            ):
                return False
            cls._GLOBAL_ENV_FAILURE_UNTIL[key] = (
                time.monotonic() + cls._GLOBAL_ENV_FAILURE_COOLDOWN_S
            )
            return True

    @classmethod
    def global_cache_stats(cls) -> Dict[str, int]:
        with cls._GLOBAL_ENV_CACHE_LOCK:
            return {
                "entries": len(cls._GLOBAL_ENV_CACHE),
                "hits": int(cls._GLOBAL_ENV_CACHE_HITS),
                "misses": int(cls._GLOBAL_ENV_CACHE_MISSES),
            }

    def _compose_env(self, lean_path: str) -> Dict[str, str]:
        combined = os.pathsep.join((*self._extra_lean_paths, lean_path))
        return {**os.environ, "LEAN_PATH": combined}

    def _publish_start_success(
        self,
        generation: int,
        lean_path: str,
        lean_bin: str,
        *,
        used_global_cache: bool,
        environment_epoch: int,
    ) -> bool:
        with self._lifecycle_lock:
            if self._lifecycle_generation != generation:
                return False
            self._lean_bin = lean_bin
            self._env = self._compose_env(lean_path)
            self._started = True
            self._failed = False
            self._environment_epoch = int(environment_epoch)
            self._last_start_used_global_cache = used_global_cache
            return True

    def _publish_start_from_global_cache(
        self,
        generation: int,
        *,
        expected_epoch: Optional[int] = None,
        expected_value: Optional[Tuple[str, str]] = None,
        used_global_cache: bool,
    ) -> tuple[Optional[Tuple[str, str]], bool]:
        """Publish one cache record without a read/invalidation race."""

        with self._GLOBAL_ENV_CACHE_LOCK:
            cache_type = type(self)
            epoch = int(
                cache_type._GLOBAL_ENV_EPOCH.get(self.project_cache_key, 0)
                or 0
            )
            cached = cache_type._GLOBAL_ENV_CACHE.get(self.project_cache_key)
            compatible = bool(
                cached is not None
                and (expected_epoch is None or int(expected_epoch) == epoch)
                and (expected_value is None or expected_value == cached)
            )
            if not compatible:
                if used_global_cache:
                    cache_type._GLOBAL_ENV_CACHE_MISSES += 1
                return None, False
            if used_global_cache:
                cache_type._GLOBAL_ENV_CACHE_HITS += 1
            assert cached is not None
            published = self._publish_start_success(
                generation,
                cached[0],
                cached[1],
                used_global_cache=used_global_cache,
                environment_epoch=epoch,
            )
            return cached, published

    def _publish_start_failure(self, generation: int) -> None:
        with self._lifecycle_lock:
            if self._lifecycle_generation != generation:
                return
            self._started = True
            self._failed = True
            self._env = None
            self._lean_bin = None
            self._environment_epoch = None

    def _reset_cancelled_start(self, generation: int) -> None:
        with self._lifecycle_lock:
            if self._lifecycle_generation != generation:
                return
            self._started = False
            self._failed = False
            self._env = None
            self._lean_bin = None
            self._environment_epoch = None

    def _lifecycle_active(self, generation: int) -> bool:
        with self._lifecycle_lock:
            return bool(
                not self._closed
                and self._lifecycle_generation == generation
            )

    def _admit_check_environment(
        self,
    ) -> Optional[tuple[str, Dict[str, str]]]:
        """Snapshot a locally current environment at dispatch admission."""

        with self._GLOBAL_ENV_CACHE_LOCK:
            current_epoch = int(
                self._GLOBAL_ENV_EPOCH.get(self.project_cache_key, 0) or 0
            )
            with self._lifecycle_lock:
                if (
                    not self._started
                    or self._failed
                    or self._lean_bin is None
                    or self._env is None
                    or self._environment_epoch != current_epoch
                ):
                    return None
                return self._lean_bin, dict(self._env)

    @property
    def available(self) -> bool:
        with self._lifecycle_lock:
            locally_available = bool(
                self._started
                and not self._failed
                and self._environment_epoch is not None
            )
            environment_epoch = self._environment_epoch
        return bool(
            locally_available
            and environment_epoch is not None
            and self.environment_epoch_is_current(
                self.project_cache_key,
                environment_epoch,
            )
        )

    @property
    def environment_epoch_stale(self) -> bool:
        """Whether an otherwise-live instance was revoked by invalidation."""

        with self._lifecycle_lock:
            epoch = self._environment_epoch
            locally_live = bool(
                self._started
                and not self._failed
                and not self._closed
                and epoch is not None
            )
        return bool(
            locally_live
            and epoch is not None
            and not self.environment_epoch_is_current(
                self.project_cache_key,
                epoch,
            )
        )

    async def start(self) -> bool:
        """Resolve and cache the Lean environment.

        Runs ``lake env printenv LEAN_PATH`` and ``lake env which lean``
        to discover the paths.  Returns *True* if successful.
        """
        async with self._lock:
            with self._lifecycle_lock:
                if self._closed:
                    return False
                if self._started:
                    already_failed = self._failed
                    started_epoch = self._environment_epoch
                else:
                    already_failed = False
                    started_epoch = None
                generation = self._lifecycle_generation
                self._last_start_used_global_cache = False
            if already_failed:
                return False
            if started_epoch is not None and self.environment_epoch_is_current(
                self.project_cache_key,
                started_epoch,
            ):
                return True
            if started_epoch is not None:
                self._reset_cancelled_start(generation)
            leader = False
            flight: Optional[concurrent.futures.Future[object]] = None
            resolution_epoch = 0
            try:
                while True:
                    leader = False
                    flight = None
                    cached, published = self._publish_start_from_global_cache(
                        generation,
                        used_global_cache=True,
                    )
                    if cached is not None:
                        if published:
                            logger.info(
                                "LeanREPL ready from global cache: lean=%s  "
                                "LEAN_PATH entries=%d",
                                cached[1],
                                len(cached[0].split(os.pathsep)),
                            )
                        return published
                    if self._global_resolution_in_cooldown(
                        self.project_cache_key
                    ):
                        self._publish_start_failure(generation)
                        logger.info(
                            "LeanREPL environment resolution cooling down; "
                            "using lake fallback"
                        )
                        return False

                    if not self._lifecycle_active(generation):
                        return False
                    leader, flight, resolution_epoch = self._claim_global_resolution(
                        self.project_cache_key
                    )
                    if not leader:
                        resolved = await asyncio.shield(
                            asyncio.wrap_future(flight)
                        )
                        if resolved is self._GLOBAL_ENV_ABANDONED:
                            if not self._lifecycle_active(generation):
                                return False
                            cached, published = (
                                self._publish_start_from_global_cache(
                                    generation,
                                    used_global_cache=True,
                                )
                            )
                            if cached is not None:
                                return published
                            if self._global_resolution_in_cooldown(
                                self.project_cache_key
                            ):
                                self._publish_start_failure(generation)
                                return False
                            continue
                        if resolved is None:
                            self._publish_start_failure(generation)
                            return False
                        resolved_value = tuple(resolved)
                        cached, published = self._publish_start_from_global_cache(
                            generation,
                            expected_epoch=resolution_epoch,
                            expected_value=resolved_value,
                            used_global_cache=True,
                        )
                        if cached is None:
                            continue
                        return published

                    # Cache/cooldown inspection and flight claiming use
                    # separate short critical sections so no thread lock is
                    # held across an await. Another event loop may have
                    # completed and removed its flight in that gap; recheck
                    # before this new leader spawns.
                    if not self._lifecycle_active(generation):
                        self._finish_global_resolution(
                            self.project_cache_key,
                            flight,
                            self._GLOBAL_ENV_ABANDONED,
                        )
                        return False
                    cached, published = self._publish_start_from_global_cache(
                        generation,
                        expected_epoch=resolution_epoch,
                        used_global_cache=True,
                    )
                    if cached is not None:
                        self._finish_global_resolution(
                            self.project_cache_key,
                            flight,
                            cached,
                        )
                        return published
                    if self._global_resolution_in_cooldown(
                        self.project_cache_key
                    ):
                        self._finish_global_resolution(
                            self.project_cache_key,
                            flight,
                            None,
                        )
                        self._publish_start_failure(generation)
                        return False

                    if not self._lifecycle_active(generation):
                        self._finish_global_resolution(
                            self.project_cache_key,
                            flight,
                            self._GLOBAL_ENV_ABANDONED,
                        )
                        return False
                    results = await asyncio.gather(
                        self._resolve_lean_path(),
                        self._resolve_lean_bin(),
                        return_exceptions=True,
                    )
                    lean_path, lean_bin = results
                    if isinstance(lean_path, BaseException):
                        logger.warning(
                            "LEAN_PATH resolution failed: %s", lean_path
                        )
                        lean_path = None
                    if isinstance(lean_bin, BaseException):
                        logger.warning(
                            "Lean binary resolution failed: %s", lean_bin
                        )
                        lean_bin = None
                    if lean_path is None or lean_bin is None:
                        failure_published = self._record_global_resolution_failure(
                            self.project_cache_key,
                            expected_epoch=resolution_epoch,
                        )
                        self._finish_global_resolution(
                            self.project_cache_key,
                            flight,
                            None
                            if failure_published
                            else self._GLOBAL_ENV_ABANDONED,
                        )
                        if not failure_published:
                            self._publish_start_failure(generation)
                            return False
                        self._publish_start_failure(generation)
                        return False

                    cache_published = self._set_global_env_cache(
                        self.project_cache_key,
                        lean_path,
                        lean_bin,
                        expected_epoch=resolution_epoch,
                    )
                    if not cache_published:
                        self._finish_global_resolution(
                            self.project_cache_key,
                            flight,
                            self._GLOBAL_ENV_ABANDONED,
                        )
                        self._publish_start_failure(generation)
                        return False
                    resolved_value = (lean_path, lean_bin)
                    self._finish_global_resolution(
                        self.project_cache_key,
                        flight,
                        resolved_value,
                    )
                    cached, published = self._publish_start_from_global_cache(
                        generation,
                        expected_epoch=resolution_epoch,
                        expected_value=resolved_value,
                        used_global_cache=False,
                    )
                    if cached is None:
                        self._publish_start_failure(generation)
                        return False
                    logger.info(
                        "LeanREPL ready: lean=%s  LEAN_PATH entries=%d",
                        lean_bin,
                        len(lean_path.split(os.pathsep)),
                    )
                    return published
            except asyncio.CancelledError:
                if leader and flight is not None:
                    self._finish_global_resolution(
                        self.project_cache_key,
                        flight,
                        self._GLOBAL_ENV_ABANDONED,
                    )
                self._reset_cancelled_start(generation)
                raise
            except Exception as exc:
                logger.warning("LeanREPL start failed: %s", exc)
                self._record_global_resolution_failure(
                    self.project_cache_key,
                    expected_epoch=(resolution_epoch if leader else None),
                )
                if leader and flight is not None:
                    self._finish_global_resolution(
                        self.project_cache_key,
                        flight,
                        None,
                    )
                self._publish_start_failure(generation)
                return False

    @staticmethod
    async def _kill_and_reap_resolution_process(
        proc: asyncio.subprocess.Process,
    ) -> None:
        await terminate_and_reap_process(
            proc,
            reap_timeout_s=LeanREPL._PROCESS_REAP_TIMEOUT_S,
            close_pipes=LeanREPL._close_child_pipes,
            log=logger,
        )

    @staticmethod
    def _close_child_pipes(proc: asyncio.subprocess.Process) -> None:
        """Disconnect our side of a dead child's pipes so exit waiters wake.

        ``proc.kill()`` ends the child and its exit *is* delivered (the
        transport's ``_returncode`` gets set), but exit waiters are woken only
        by ``_call_connection_lost``, which
        ``BaseSubprocessTransport._try_finish`` refuses to run while any pipe
        transport still reports connected.  When output is still buffered,
        cancelling a reader mid-``read()`` leaves that read transport alive, so
        every waiter registered before exit hangs forever -- pinning the Lean
        lock with no error and no log line.  A silent child closes its own
        write end on death and settles without this, which is why the failure
        only appears on children that produced output.
        """

        transport = getattr(proc, "_transport", None)
        if transport is None:
            return
        # fd 0 is present only for callers that pass ``stdin=PIPE``.
        for pipe_fd in (0, 1, 2):
            try:
                pipe = transport.get_pipe_transport(pipe_fd)
                if pipe is not None:
                    pipe.close()
            except Exception:
                # Best effort: a pipe already gone still counts as
                # disconnected, which is all the exit waiters need.  Log so a
                # transport that cannot be closed (uvloop, a future backend)
                # does not silently restore the hang.
                logger.debug(
                    "REPL: could not close pipe fd=%s during reap",
                    pipe_fd,
                    exc_info=True,
                )

    @staticmethod
    async def _finish_cleanup_despite_cancellation(
        cleanup: Awaitable[None],
    ) -> None:
        """Let owned subprocess cleanup finish under repeated cancellation.

        Operation timeout and runner shutdown can cancel the same caller in
        quick succession.  A bare ``await`` in a cancellation handler lets the
        second cancellation interrupt kill/reap and leak the child.  Keep the
        cleanup in its own task and consume every subsequent cancellation until
        that task has reached a terminal state; the caller then re-raises its
        original cancellation.
        """
        cleanup_task = asyncio.ensure_future(cleanup)
        while not cleanup_task.done():
            try:
                await asyncio.shield(cleanup_task)
            except asyncio.CancelledError:
                continue
        try:
            cleanup_task.result()
        except BaseException:
            # Cleanup is best-effort and must never replace the operation's
            # original CancelledError with a secondary reap failure.
            pass

    @classmethod
    async def _cancel_check_tasks_and_reap(
        cls,
        proc: asyncio.subprocess.Process,
        tasks: list[asyncio.Task],
        *,
        wait_task: Optional[asyncio.Task] = None,
    ) -> None:
        await terminate_and_reap_process(
            proc,
            wait_task=wait_task,
            auxiliary_tasks=tasks,
            reap_timeout_s=cls._PROCESS_REAP_TIMEOUT_S,
            close_pipes=cls._close_child_pipes,
            log=logger,
        )

    async def _resolve_lean_path(self) -> Optional[str]:
        proc = await asyncio.create_subprocess_exec(
            "lake",
            "env",
            "printenv",
            "LEAN_PATH",
            cwd=str(self.project_dir),
            env=sanitized_subprocess_environment(),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        try:
            stdout, stderr = await communicate_with_hard_timeout(
                proc,
                timeout_s=max(
                    _LEAN_ENVIRONMENT_RESOLUTION_TIMEOUT_FLOOR_S,
                    float(self.timeout_s),
                ),
                cleanup_timeout_s=self._PROCESS_REAP_TIMEOUT_S,
                close_pipes=self._close_child_pipes,
                log=logger,
            )
        except asyncio.CancelledError:
            raise
        except asyncio.TimeoutError:
            logger.warning("lake env printenv LEAN_PATH timed out")
            return None
        if proc.returncode != 0:
            logger.warning("lake env printenv LEAN_PATH failed: %s", stderr.decode())
            return None
        return stdout.decode().strip()

    async def _resolve_lean_bin(self) -> Optional[str]:
        proc = await asyncio.create_subprocess_exec(
            "lake",
            "env",
            "which",
            "lean",
            cwd=str(self.project_dir),
            env=sanitized_subprocess_environment(),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        try:
            stdout, stderr = await communicate_with_hard_timeout(
                proc,
                timeout_s=max(
                    _LEAN_ENVIRONMENT_RESOLUTION_TIMEOUT_FLOOR_S,
                    float(self.timeout_s),
                ),
                cleanup_timeout_s=self._PROCESS_REAP_TIMEOUT_S,
                close_pipes=self._close_child_pipes,
                log=logger,
            )
        except asyncio.CancelledError:
            raise
        except asyncio.TimeoutError:
            logger.warning("lake env which lean timed out")
            return None
        if proc.returncode != 0:
            logger.warning("lake env which lean failed: %s", stderr.decode())
            return None
        path = stdout.decode().strip()
        return path if path else None

    async def check(
        self,
        file_path: Path,
        *,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> Tuple[int, str]:
        """Check a Lean file using the cached environment.

        Returns ``(returncode, combined_output)``.
        Raises ``RuntimeError`` if the REPL is not available.

        Direct Lean subprocesses are normally silent on successful checks, so
        silence is not treated as a fast-fail condition here. The
        ``fast_fail_timeout_s`` argument is accepted for API compatibility, but
        this backend relies on the hard timeout instead of silence-based early
        termination.
        """
        admitted_environment = self._admit_check_environment()
        if admitted_environment is None:
            raise RuntimeError("LeanREPL not available")
        lean_bin, process_env = admitted_environment

        timeout = float(timeout_s) if timeout_s is not None else float(self.timeout_s)
        if timeout <= 0:
            timeout = 1.0

        proc = await asyncio.create_subprocess_exec(
            lean_bin,
            str(file_path),
            cwd=str(self.project_dir),
            env=sanitized_subprocess_environment(process_env),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        if dispatch_observer is not None:
            try:
                dispatch_observer()
            except Exception:
                pass

        # Incremental output reading with hard timeout.
        stdout_chunks: list[bytes] = []
        stderr_chunks: list[bytes] = []
        loop = asyncio.get_running_loop()
        start_time = loop.time()

        async def read_stream(
            stream: asyncio.StreamReader, chunks: list[bytes]
        ) -> None:
            while True:
                try:
                    chunk = await asyncio.wait_for(stream.read(4096), timeout=1.0)
                    if not chunk:
                        break
                    chunks.append(chunk)
                except asyncio.TimeoutError:
                    if loop.time() - start_time > timeout:
                        break

        read_tasks: list[asyncio.Task] = []
        wait_task: Optional[asyncio.Task] = None
        try:
            if proc.stdout is not None:
                read_tasks.append(
                    asyncio.create_task(read_stream(proc.stdout, stdout_chunks))
                )
            if proc.stderr is not None:
                read_tasks.append(
                    asyncio.create_task(read_stream(proc.stderr, stderr_chunks))
                )

            # Use proc.wait() task instead of polling proc.returncode
            wait_task = asyncio.create_task(proc.wait())

            while not wait_task.done():
                elapsed = loop.time() - start_time

                if elapsed > timeout:
                    logger.debug("REPL: total timeout after %.1fs", elapsed)
                    await self._cancel_check_tasks_and_reap(
                        proc,
                        read_tasks,
                        wait_task=wait_task,
                    )
                    return (
                        1,
                        _status_with_captured_output(
                            "Lean timeout", stdout_chunks, stderr_chunks
                        ),
                    )

                # Wait for process exit or next check interval
                check_interval = min(0.3, timeout - elapsed)
                await asyncio.wait({wait_task}, timeout=max(0.1, check_interval))

            # Polling ``done()`` establishes completion but does not join the
            # process-exit task or retrieve an exception.  Consume it here so
            # transactional callers correctly recognize this structured
            # child as settled.
            wait_task.result()

            # Wait for read tasks to finish
            for task in read_tasks:
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass

            # Drain remaining. A closed Lean that never EOFs used to park
            # the controller forever on a raw ``StreamReader.read()``.
            if proc.stdout:
                try:
                    remaining = await asyncio.wait_for(proc.stdout.read(), timeout=2.0)
                except asyncio.TimeoutError:
                    remaining = b""
                if remaining:
                    stdout_chunks.append(remaining)
            if proc.stderr:
                try:
                    remaining = await asyncio.wait_for(proc.stderr.read(), timeout=2.0)
                except asyncio.TimeoutError:
                    remaining = b""
                if remaining:
                    stderr_chunks.append(remaining)

            try:
                await asyncio.wait_for(proc.wait(), timeout=2.0)
            except asyncio.TimeoutError:
                pass

        except asyncio.CancelledError:
            await self._finish_cleanup_despite_cancellation(
                self._cancel_check_tasks_and_reap(
                    proc,
                    read_tasks,
                    wait_task=wait_task,
                )
            )
            raise
        except Exception as exc:
            await self._cancel_check_tasks_and_reap(
                proc,
                read_tasks,
                wait_task=wait_task,
            )
            return (
                1,
                _status_with_captured_output(
                    f"Lean subprocess error: {exc}",
                    stdout_chunks,
                    stderr_chunks,
                ),
            )

        out = _captured_output_text(stdout_chunks, stderr_chunks)
        return (proc.returncode if proc.returncode is not None else 1, out)

    async def restart(self) -> bool:
        """Reset and re-resolve the environment."""
        async with self._lock:
            with self._lifecycle_lock:
                if self._closed:
                    return False
                self._lifecycle_generation += 1
                self._started = False
                self._failed = False
                self._env = None
                self._lean_bin = None
                self._environment_epoch = None
                self._last_start_used_global_cache = False
        self._clear_global_env_cache(self.project_cache_key)
        return await self.start()

    async def refresh_current_environment(self) -> bool:
        """Reacquire current global coordinates without invalidating peers."""

        async with self._lock:
            with self._lifecycle_lock:
                if self._closed:
                    return False
                self._lifecycle_generation += 1
                self._started = False
                self._failed = False
                self._env = None
                self._lean_bin = None
                self._environment_epoch = None
                self._last_start_used_global_cache = False
        return await self.start()

    def close(self) -> None:
        """Clean up cached state.

        Sets _failed first to prevent new operations from starting,
        then clears remaining state. Safe to call from sync context.
        """
        with self._lifecycle_lock:
            self._lifecycle_generation += 1
            self._closed = True
            self._failed = True
            self._started = False
            self._env = None
            self._lean_bin = None
            self._environment_epoch = None
            self._last_start_used_global_cache = False
