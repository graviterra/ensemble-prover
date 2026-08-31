"""Run-local coordination for provider serving-lane capacity refusals.

The provider can expose one serving lane through several role clients.  A
retryable pre-generation 429 from that lane is therefore evidence about all of
those clients, not only the target which happened to observe it.  This module
keeps that evidence in a ContextVar-owned registry so copied scheduler tasks
share it while unrelated runs do not acquire process-global state.
"""

from __future__ import annotations

import contextvars
import functools
import math
import random
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Awaitable, Callable, Iterator, Optional, ParamSpec, TypeAlias, TypeVar

import httpx


@dataclass(frozen=True)
class ProviderLaneReceipt:
    fingerprint: str
    ready_at: float
    retry_after_s: float


@dataclass(frozen=True)
class ProviderLanePermit:
    fingerprint: str
    token: int
    observed_epoch: int
    half_open_probe: bool


@dataclass
class _LaneState:
    rejection_count: int = 0
    rejection_epoch: int = 0
    healthy_epoch_floor: int = 0
    ready_at: float = 0.0
    half_open_token: int = 0
    permanently_retired: bool = False


# Keep the concrete exception type identical to a provider 429.  The central
# error classifier intentionally recognizes exact httpx status errors by their
# defining module/name so a local subclass would silently become a non-retryable
# ``unknown`` failure.  The receipt attributes below distinguish this
# pre-dispatch case without inventing a parallel exception taxonomy.
ProviderLaneDeferred: TypeAlias = httpx.HTTPStatusError


def _provider_lane_deferred(
    receipt: ProviderLaneReceipt,
    *,
    permanently_retired: bool = False,
) -> httpx.HTTPStatusError:
    request = httpx.Request(
        "POST",
        "https://provider-lane.invalid/wait-for-capacity",
    )
    response = httpx.Response(
        429,
        request=request,
        json={
            "error": {
                "message": "provider serving lane is cooling down",
                "code": 429,
            }
        },
    )
    exc = httpx.HTTPStatusError(
        "provider serving lane is cooling down before dispatch",
        request=request,
        response=response,
    )
    exc.provider_defer_fingerprint = receipt.fingerprint  # type: ignore[attr-defined]
    exc.provider_defer_ready_at = receipt.ready_at  # type: ignore[attr-defined]
    exc.provider_defer_retry_after_s = receipt.retry_after_s  # type: ignore[attr-defined]
    exc.provider_lane_predispatch_defer = True  # type: ignore[attr-defined]
    exc.provider_lane_run_closed = permanently_retired  # type: ignore[attr-defined]
    return exc


class ProviderLaneHealthRegistry:
    """Coordinate retryable 429 evidence across one run's provider clients.

    Healthy lanes admit concurrent requests.  After a capacity refusal, the
    lane observes bounded exponential backoff.  Once the lease expires exactly
    one half-open request is admitted; all sibling clients retain a typed wait
    receipt until that request settles.
    """

    def __init__(
        self,
        *,
        clock: Callable[[], float] = time.time,
        base_backoff_s: float = 1.0,
        max_backoff_s: float = 300.0,
        half_open_poll_s: float = 0.25,
        jitter_fraction: float = 0.10,
    ) -> None:
        self._clock = clock
        self._base_backoff_s = max(0.01, float(base_backoff_s))
        self._max_backoff_s = max(
            self._base_backoff_s,
            float(max_backoff_s),
        )
        self._half_open_poll_s = max(0.01, float(half_open_poll_s))
        self._jitter_fraction = max(0.0, min(1.0, float(jitter_fraction)))
        self._states: dict[str, _LaneState] = {}
        self._next_token = 1
        self._lock = threading.Lock()

    def _now(self) -> float:
        now = float(self._clock())
        return now if math.isfinite(now) else time.time()

    def _permit_locked(
        self,
        fingerprint: str,
        *,
        epoch: int,
        half_open_probe: bool,
    ) -> ProviderLanePermit:
        token = self._next_token
        self._next_token += 1
        return ProviderLanePermit(
            fingerprint=fingerprint,
            token=token,
            observed_epoch=epoch,
            half_open_probe=half_open_probe,
        )

    def _deferred_locked(
        self,
        fingerprint: str,
        *,
        ready_at: float,
        now: float,
        permanently_retired: bool = False,
    ) -> ProviderLaneDeferred:
        bounded_ready_at = max(now + 0.001, float(ready_at))
        return _provider_lane_deferred(
            ProviderLaneReceipt(
                fingerprint=fingerprint,
                ready_at=bounded_ready_at,
                retry_after_s=max(0.0, bounded_ready_at - now),
            ),
            permanently_retired=permanently_retired,
        )

    def acquire(self, fingerprint: str) -> ProviderLanePermit:
        """Return a dispatch permit or raise a typed non-consuming wait."""

        lane = str(fingerprint or "").strip()
        if not lane:
            return ProviderLanePermit("", 0, 0, False)
        now = self._now()
        with self._lock:
            state = self._states.get(lane)
            if state is not None and state.permanently_retired:
                raise self._deferred_locked(
                    lane,
                    ready_at=max(state.ready_at, now + 0.001),
                    now=now,
                    permanently_retired=True,
                )
            if state is None or state.rejection_count <= 0:
                return self._permit_locked(
                    lane,
                    epoch=state.rejection_epoch if state is not None else 0,
                    half_open_probe=False,
                )
            if now < state.ready_at:
                raise self._deferred_locked(
                    lane,
                    ready_at=state.ready_at,
                    now=now,
                )
            if state.half_open_token:
                raise self._deferred_locked(
                    lane,
                    ready_at=now + self._half_open_poll_s,
                    now=now,
                )
            permit = self._permit_locked(
                lane,
                epoch=state.rejection_epoch,
                half_open_probe=True,
            )
            state.half_open_token = permit.token
            return permit

    def record_rate_limit(
        self,
        permit: ProviderLanePermit,
        *,
        provider_retry_after_s: float = 0.0,
    ) -> ProviderLaneReceipt:
        """Open or extend a lane after an authenticated retryable 429."""

        lane = str(permit.fingerprint or "").strip()
        if not lane:
            return ProviderLaneReceipt("", 0.0, 0.0)
        now = self._now()
        try:
            provider_hint = float(provider_retry_after_s)
        except (TypeError, ValueError, OverflowError):
            provider_hint = 0.0
        if not math.isfinite(provider_hint) or provider_hint < 0.0:
            provider_hint = 0.0
        with self._lock:
            state = self._states.setdefault(lane, _LaneState())
            if state.permanently_retired:
                return ProviderLaneReceipt(
                    fingerprint=lane,
                    ready_at=state.ready_at,
                    retry_after_s=max(0.0, state.ready_at - now),
                )
            if permit.observed_epoch < state.healthy_epoch_floor:
                # A successful half-open probe is newer authoritative lane
                # evidence. A slow refusal from a request admitted before that
                # success must not recreate the old epoch and reopen the lane.
                return ProviderLaneReceipt(
                    fingerprint=lane,
                    ready_at=state.ready_at,
                    retry_after_s=max(0.0, state.ready_at - now),
                )
            # Requests admitted together carry the same observed epoch. Their
            # responses are correlated evidence from one probe generation, so
            # they merge provider hints but advance the exponential ladder
            # only once. A failed half-open probe observes the current epoch
            # and therefore advances it exactly once.
            if permit.observed_epoch >= state.rejection_epoch:
                state.rejection_count = min(63, state.rejection_count + 1)
                state.rejection_epoch += 1
            exponential = min(
                self._max_backoff_s,
                self._base_backoff_s * (2.0 ** min(30, state.rejection_count - 1)),
            )
            delay = min(
                self._max_backoff_s,
                max(exponential, provider_hint),
            )
            if self._jitter_fraction:
                delay = min(
                    self._max_backoff_s,
                    delay * (1.0 + random.random() * self._jitter_fraction),
                )
            state.ready_at = max(state.ready_at, now + delay)
            if state.half_open_token == permit.token:
                state.half_open_token = 0
            return ProviderLaneReceipt(
                fingerprint=lane,
                ready_at=state.ready_at,
                retry_after_s=max(0.0, state.ready_at - now),
            )

    def record_success(self, permit: ProviderLanePermit) -> None:
        """Close a lane only when success is newer than its last refusal."""

        lane = str(permit.fingerprint or "").strip()
        if not lane:
            return
        with self._lock:
            state = self._states.get(lane)
            if state is None:
                return
            if state.permanently_retired:
                return
            if state.half_open_token == permit.token:
                state.half_open_token = 0
            # A request admitted before a newer refusal may finish afterward;
            # that stale success must not erase the newer capacity evidence.
            if permit.observed_epoch == state.rejection_epoch:
                if permit.half_open_probe:
                    # Retain a healthy tombstone with a monotonic generation.
                    # Removing the state would let a pre-recovery request with
                    # epoch zero recreate the lane and override this success.
                    state.rejection_epoch += 1
                    state.healthy_epoch_floor = state.rejection_epoch
                    state.rejection_count = 0
                    state.ready_at = 0.0
                    state.half_open_token = 0
                elif state.healthy_epoch_floor <= 0:
                    self._states.pop(lane, None)

    def record_unresolved_abandonment(
        self,
        permit: ProviderLanePermit,
        *,
        lease_s: float = 300.0,
    ) -> ProviderLaneReceipt:
        """Fence a half-open lane whose exact transport cannot be settled.

        Process cleanup may have to cancel the receipt observer while a
        cancellation-resistant HTTP task remains live. Releasing the token or
        expiring a timer at that point would admit duplicate provider work.
        Permanently retire this fingerprint in the closing run registry; a
        later theorem receives a fresh registry at its run boundary.
        """

        lane = str(permit.fingerprint or "").strip()
        if not lane:
            return ProviderLaneReceipt("", 0.0, 0.0)
        now = self._now()
        try:
            bounded_lease = float(lease_s)
        except (TypeError, ValueError, OverflowError):
            bounded_lease = self._max_backoff_s
        if not math.isfinite(bounded_lease) or bounded_lease <= 0.0:
            bounded_lease = self._max_backoff_s
        bounded_lease = min(
            self._max_backoff_s,
            max(self._base_backoff_s, bounded_lease),
        )
        with self._lock:
            state = self._states.setdefault(lane, _LaneState())
            if (
                permit.observed_epoch < state.healthy_epoch_floor
                or state.half_open_token != permit.token
            ):
                return ProviderLaneReceipt(
                    fingerprint=lane,
                    ready_at=state.ready_at,
                    retry_after_s=max(0.0, state.ready_at - now),
                )
            state.rejection_epoch += 1
            state.rejection_count = max(1, state.rejection_count)
            state.ready_at = max(state.ready_at, now + bounded_lease)
            state.half_open_token = 0
            state.permanently_retired = True
            return ProviderLaneReceipt(
                fingerprint=lane,
                ready_at=state.ready_at,
                retry_after_s=max(0.0, state.ready_at - now),
            )

    def release(self, permit: ProviderLanePermit) -> None:
        """Release a half-open permit after a non-rate-limit outcome."""

        lane = str(permit.fingerprint or "").strip()
        if not lane:
            return
        with self._lock:
            state = self._states.get(lane)
            if (
                state is not None
                and not state.permanently_retired
                and state.half_open_token == permit.token
            ):
                state.half_open_token = 0


class ProviderLanePermitOwnership:
    """Transfer a permit from a request owner to its detached observer."""

    def __init__(
        self,
        registry: ProviderLaneHealthRegistry,
        permit: ProviderLanePermit,
    ) -> None:
        self.registry = registry
        self.permit = permit
        self._lock = threading.Lock()
        self._observer_owns = False
        self._observer_settled = False
        self._released = False

    def _claim_release_locked(self) -> bool:
        if self._released:
            return False
        self._released = True
        return True

    def transfer_to_observer(self) -> None:
        release = False
        with self._lock:
            self._observer_owns = True
            if self._observer_settled:
                release = self._claim_release_locked()
        if release:
            self.registry.release(self.permit)

    def settle_owner(self) -> None:
        release = False
        with self._lock:
            if not self._observer_owns:
                release = self._claim_release_locked()
        if release:
            self.registry.release(self.permit)

    def settle_observer(self) -> None:
        release = False
        with self._lock:
            self._observer_settled = True
            if self._observer_owns:
                release = self._claim_release_locked()
        if release:
            self.registry.release(self.permit)


_CURRENT_PROVIDER_LANE_HEALTH: contextvars.ContextVar[
    Optional[ProviderLaneHealthRegistry]
] = contextvars.ContextVar("provider_lane_health_registry", default=None)


def bound_provider_lane_health_registry() -> Optional[ProviderLaneHealthRegistry]:
    """Return the registry explicitly bound to the current provider run."""

    return _CURRENT_PROVIDER_LANE_HEALTH.get()


def current_provider_lane_health_registry() -> ProviderLaneHealthRegistry:
    """Return the bound run registry, or a fresh caller-owned fallback.

    Only an explicit run binding is inherited by copied contexts.  An ambient
    lookup must not install mutable cooldown state that can leak into a later
    programmatic run created in the same task.
    """

    registry = bound_provider_lane_health_registry()
    return registry if registry is not None else ProviderLaneHealthRegistry()


@contextmanager
def bind_provider_lane_health_registry(
    registry: ProviderLaneHealthRegistry,
) -> Iterator[ProviderLaneHealthRegistry]:
    """Bind an explicit registry for one run or focused test."""

    token = _CURRENT_PROVIDER_LANE_HEALTH.set(registry)
    try:
        yield registry
    finally:
        _CURRENT_PROVIDER_LANE_HEALTH.reset(token)


_RunResult = TypeVar("_RunResult")
_RunParams = ParamSpec("_RunParams")


def fresh_provider_lane_health_run(
    function: Callable[_RunParams, Awaitable[_RunResult]],
) -> Callable[_RunParams, Awaitable[_RunResult]]:
    """Give one async provider-run entry point an isolated shared registry."""

    @functools.wraps(function)
    async def wrapped(
        *args: _RunParams.args,
        **kwargs: _RunParams.kwargs,
    ) -> _RunResult:
        with bind_provider_lane_health_registry(ProviderLaneHealthRegistry()):
            return await function(*args, **kwargs)

    return wrapped


__all__ = [
    "ProviderLaneDeferred",
    "ProviderLaneHealthRegistry",
    "ProviderLanePermitOwnership",
    "ProviderLanePermit",
    "ProviderLaneReceipt",
    "bind_provider_lane_health_registry",
    "bound_provider_lane_health_registry",
    "current_provider_lane_health_registry",
    "fresh_provider_lane_health_run",
]
