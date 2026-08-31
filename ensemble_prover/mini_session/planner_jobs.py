"""Session-owned runtime broker for long-running planner requests.

The broker deliberately contains no proof state.  A launch carries an immutable
request identity and an async operation; the eventual value is delivered once
to the session scheduler.  This lets provider work outlive an action quantum
without allowing a late or replayed request to publish twice.
"""

from __future__ import annotations

import asyncio
from collections.abc import Awaitable, Callable
from dataclasses import dataclass, field
from typing import Any, Mapping

from ensemble_prover.llm_usage import (
    ProviderDispatchExposureTracker,
    bind_llm_usage_context,
    bind_provider_dispatch_exposure_tracker,
)


@dataclass(frozen=True, slots=True)
class PlannerJobIdentity:
    """Immutable identity fence for one exact planner request."""

    job_id: str
    request_fingerprint: str
    stage: str
    pass_index: int
    root_statement_hash: str
    route_environment_hash: str
    proof_idea_cognition_hash: str
    planner_frontier_signature: str
    provider_lane_fingerprint: str
    owner_lane_id: str = ""
    stage_round: int = 0
    answer_visibility_policy_hash: str = ""
    active_target_statement_keys: tuple[str, ...] = ()
    helper_evidence_fingerprints: tuple[str, ...] = ()
    # Logical request material is durable authority. Runtime serving-lane
    # selection is deliberately separate: a composite client may resolve to
    # a concrete provider leaf only after the request has been prepared. It is
    # excluded from dataclass equality for legacy checkpoint compatibility;
    # every nonlegacy material change must rotate ``request_fingerprint``.
    request_material_fingerprint: str = field(default="", compare=False)
    request_io_policy_fingerprint: str = field(default="", compare=False)
    # Stable theorem/request policy, excluding monotone helper growth.  This
    # prevents an exact saved payload from crossing a changed problem shell or
    # visibility policy while still allowing useful concurrent proof progress.
    request_context_fingerprint: str = field(default="", compare=False)
    # Canonical JSON for the exact public provider request.  It is deliberately
    # excluded from equality/hash: the broker delivery fence remains the
    # immutable fingerprints above.  Persisting the request itself lets a new
    # process reconstruct a scheduler-owned job without rebuilding it from a
    # newer proof frontier or serializing any mutable proof state.
    request_material_json: str = field(
        default="",
        compare=False,
        repr=False,
    )

    def __post_init__(self) -> None:
        # Checkpoint JSON decoders reconstruct tuples as lists.  Normalize at
        # the boundary so restored identities remain immutable and hashable.
        object.__setattr__(
            self,
            "active_target_statement_keys",
            tuple(str(item) for item in self.active_target_statement_keys),
        )
        object.__setattr__(
            self,
            "helper_evidence_fingerprints",
            tuple(str(item) for item in self.helper_evidence_fingerprints),
        )


@dataclass(frozen=True, slots=True)
class PlannerJobLaunch:
    """A post-commit request for the session runtime to start planner work."""

    identity: PlannerJobIdentity
    run: Callable[[], Awaitable[Any]]
    usage_context: Mapping[str, Any] = field(
        default_factory=dict,
        compare=False,
        repr=False,
    )
    reconcile_provider_exposure: Callable[[int], None] | None = field(
        default=None,
        compare=False,
        repr=False,
    )


@dataclass(frozen=True, slots=True)
class PlannerJobResult:
    """The terminal value or failure of one exact planner request."""

    identity: PlannerJobIdentity
    value: Any = None
    exception: BaseException | None = None


class PlannerJobYield(BaseException):
    """Transfer a planner launch across the action transaction boundary.

    This derives from :class:`BaseException` so broad ``except Exception``
    recovery paths cannot accidentally turn the ownership transfer into an
    ordinary planner failure.
    """

    def __init__(self, launch: PlannerJobLaunch) -> None:
        super().__init__(launch.identity.job_id)
        self.launch = launch


class PlannerJobExecutionCancelled(RuntimeError):
    """A provider operation ended itself before producing a receipt."""


@dataclass(slots=True)
class _PlannerJobEntry:
    identity: PlannerJobIdentity
    task: asyncio.Task[None]
    result: PlannerJobResult | None = None


class PlannerJobBroker:
    """Own and deliver long planner operations for one running session."""

    def __init__(self) -> None:
        self._jobs: dict[tuple[str, str], _PlannerJobEntry] = {}
        self._quarantined: dict[tuple[str, str], _PlannerJobEntry] = {}
        self._launched: set[PlannerJobIdentity] = set()
        self._changed = asyncio.Event()
        self._owner_tasks: set[asyncio.Task[Any]] = set()
        self._session_owners: dict[int, asyncio.Task[Any] | None] = {}
        self._watched_session_tasks: set[asyncio.Task[Any]] = set()

    @staticmethod
    def _key(job_id: str, request_fingerprint: str) -> tuple[str, str]:
        return job_id, request_fingerprint

    def launch(self, launch: PlannerJobLaunch) -> bool:
        """Launch an exact request once; return false for a replay."""

        identity = launch.identity
        key = self._key(identity.job_id, identity.request_fingerprint)
        if (
            identity in self._launched
            or key in self._jobs
            or key in self._quarantined
        ):
            return False

        task = asyncio.create_task(self._run(key, launch))
        self._jobs[key] = _PlannerJobEntry(identity=identity, task=task)
        self._launched.add(identity)
        return True

    async def _run(
        self,
        key: tuple[str, str],
        launch: PlannerJobLaunch,
    ) -> None:
        owner_task = asyncio.current_task()
        exposure = ProviderDispatchExposureTracker()
        try:
            with (
                bind_llm_usage_context(launch.usage_context),
                bind_provider_dispatch_exposure_tracker(exposure),
            ):
                value = await launch.run()
        except asyncio.CancelledError:
            entry = self._jobs.get(key)
            if (
                entry is not None
                and entry.task is owner_task
                and entry.identity == launch.identity
            ):
                # Broker shutdown removes the entry before cancelling the
                # task.  A still-owned task therefore ended inside the
                # provider adapter. Publish a normal failure receipt so the
                # recursive controller can apply its bounded recovery policy
                # instead of either waiting forever or blindly reissuing the
                # same paid request.
                result = PlannerJobResult(
                    identity=launch.identity,
                    exception=PlannerJobExecutionCancelled(
                        "planner provider operation ended before completion"
                    ),
                )
            else:
                raise
        except Exception as exc:
            result = PlannerJobResult(
                identity=launch.identity,
                exception=exc.with_traceback(None),
            )
        else:
            result = PlannerJobResult(
                identity=launch.identity,
                value=value,
            )
        finally:
            reconcile = launch.reconcile_provider_exposure
            if callable(reconcile):
                try:
                    reconcile(exposure.provider_dispatches_started)
                except Exception:
                    # Accounting telemetry cannot change the mathematical
                    # value of an already completed provider receipt.
                    pass
            exposure.settle_all_current_exposure()

        entry = self._jobs.get(key)
        if (
            entry is None
            or entry.task is not owner_task
            or entry.identity != launch.identity
        ):
            return
        entry.result = result
        self._changed.set()

    def status(self, job_id: str, request_fingerprint: str) -> str:
        """Return ``missing``, ``pending``, or ``ready`` for an exact key."""

        key = self._key(job_id, request_fingerprint)
        entry = self._jobs.get(key)
        if entry is not None:
            return "pending" if entry.result is None else "ready"
        # A detached operation is fenced until it actually terminates. Even
        # if it had completed just before cancellation, its result is no
        # longer eligible for publication and must not appear consumable.
        if key in self._quarantined:
            return "pending"
        return "missing"

    async def wait_for_change(self) -> None:
        """Wait until a planner job becomes ready or jobs are cancelled."""

        await self._changed.wait()
        self._changed.clear()

    def has_pending(self) -> bool:
        return bool(self._quarantined) or any(
            entry.result is None for entry in self._jobs.values()
        )

    def has_ready(self) -> bool:
        return any(entry.result is not None for entry in self._jobs.values())

    def bind_owner_task(self, task: asyncio.Task[Any] | None) -> None:
        """Cancel runtime jobs synchronously when their session task stops."""

        if task is None or task in self._owner_tasks:
            return
        self._owner_tasks.add(task)

        def owner_done(done: asyncio.Task[Any]) -> None:
            self._owner_tasks.discard(done)
            stale_session_ids = tuple(
                owner_id
                for owner_id, owner_task in self._session_owners.items()
                if owner_task is done
            )
            for owner_id in stale_session_ids:
                self._session_owners.pop(owner_id, None)
            if (
                done.cancelled()
                and not self._owner_tasks
                and not self._session_owners
            ):
                self.cancel_all_nowait()

        task.add_done_callback(owner_done)

    def bind_session_owner(
        self,
        owner: Any,
        task: asyncio.Task[Any] | None,
    ) -> None:
        """Hold the broker for one live parent or nested MiniSession."""

        owner_id = id(owner)
        if owner_id in self._session_owners:
            return
        self._session_owners[owner_id] = task
        if task is None or task in self._watched_session_tasks:
            return
        self._watched_session_tasks.add(task)

        def session_task_done(done: asyncio.Task[Any]) -> None:
            self._watched_session_tasks.discard(done)
            stale_session_ids = tuple(
                session_id
                for session_id, session_task in self._session_owners.items()
                if session_task is done
            )
            for session_id in stale_session_ids:
                self._session_owners.pop(session_id, None)
            if (
                done.cancelled()
                and not self._session_owners
                and not self._owner_tasks
            ):
                self.cancel_all_nowait()

        task.add_done_callback(session_task_done)

    async def release_session_owner(self, owner: Any) -> None:
        """Release one session lease and clean up after the final owner."""

        self._session_owners.pop(id(owner), None)
        if self._session_owners or self._owner_tasks:
            return
        await self.cancel_all()

    def cancel_all_nowait(self) -> tuple[asyncio.Task[None], ...]:
        keyed_entries = tuple(self._jobs.items())
        entries = tuple(entry for _key, entry in keyed_entries)
        self._jobs.clear()
        for key, entry in keyed_entries:
            self._quarantined[key] = entry

            def release_quarantine(
                done: asyncio.Task[None],
                *,
                quarantined_key: tuple[str, str] = key,
                identity: PlannerJobIdentity = entry.identity,
            ) -> None:
                current = self._quarantined.get(quarantined_key)
                if current is None or current.task is not done:
                    return
                self._quarantined.pop(quarantined_key, None)
                self._launched.discard(identity)
                self._changed.set()

            entry.task.add_done_callback(release_quarantine)
            if not entry.task.done():
                entry.task.cancel()
        if entries:
            self._changed.set()
        return tuple(entry.task for entry in entries)

    def take(
        self,
        job_id: str,
        request_fingerprint: str,
    ) -> PlannerJobResult | None:
        """Consume a ready result exactly once."""

        key = self._key(job_id, request_fingerprint)
        entry = self._jobs.get(key)
        if entry is None or entry.result is None:
            return None
        del self._jobs[key]
        return entry.result

    def peek(
        self,
        job_id: str,
        request_fingerprint: str,
    ) -> PlannerJobResult | None:
        """Lease a ready result without retiring it before durable commit."""

        entry = self._jobs.get(self._key(job_id, request_fingerprint))
        return entry.result if entry is not None else None

    def acknowledge(
        self,
        identity: PlannerJobIdentity,
    ) -> bool:
        """Retire an exact ready result after its action outcome is durable."""

        key = self._key(identity.job_id, identity.request_fingerprint)
        entry = self._jobs.get(key)
        if (
            entry is None
            or entry.result is None
            or entry.identity != identity
        ):
            return False
        del self._jobs[key]
        # Publication is now durable. A later scheduler-authorized retry of
        # the same mathematical request is a new operation, not a replay of
        # this receipt; release its launch fence only at this commit boundary.
        self._launched.discard(entry.identity)
        return True

    async def cancel_all(self, *, drain_timeout_s: float = 1.0) -> None:
        """Cancel jobs with a finite drain and forbid late publication."""

        def observe_terminal(task: asyncio.Task[None]) -> None:
            if task.cancelled():
                return
            try:
                task.exception()
            except BaseException:
                return

        tasks = self.cancel_all_nowait()
        if not tasks:
            return
        done, pending = await asyncio.wait(
            tasks,
            timeout=max(0.0, float(drain_timeout_s or 0.0)),
        )
        for task in done:
            observe_terminal(task)
        for task in pending:
            # The broker entry was removed before cancellation, so even a
            # cancellation-resistant adapter cannot publish late.  Observe
            # its eventual terminal exception without blocking session stop.
            task.add_done_callback(observe_terminal)


__all__ = [
    "PlannerJobBroker",
    "PlannerJobExecutionCancelled",
    "PlannerJobIdentity",
    "PlannerJobLaunch",
    "PlannerJobResult",
    "PlannerJobYield",
]
