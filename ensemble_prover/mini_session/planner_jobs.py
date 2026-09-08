"""Session-owned runtime broker for long-running planner requests.

The broker deliberately contains no proof state.  A launch carries an immutable
request identity and an async operation; the eventual value is delivered once
to the session scheduler.  This lets provider work outlive an action quantum
without allowing a late or replayed request to publish twice.
"""

from __future__ import annotations

import asyncio
from collections.abc import Awaitable, Callable
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import asdict, dataclass, field
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


def planner_result_to_record(result: PlannerJobResult) -> dict[str, Any]:
    from ensemble_prover.state_data import clone_json_value
    error = None
    if result.exception is not None:
        from .planner_job_receipt import encode_planner_error
        error = encode_planner_error(result.exception)
    identity = asdict(result.identity)
    for name in ("active_target_statement_keys", "helper_evidence_fingerprints"):
        identity[name] = list(identity[name])
    return clone_json_value({"schema_version": 1, "identity": identity,
                             "value": result.value, "error": error})


def planner_result_from_record(record: dict[str, Any]) -> PlannerJobResult:
    from ensemble_prover.state_data import clone_json_value
    from dataclasses import fields
    data = clone_json_value(record)
    if (type(data) is not dict or set(data) != {"schema_version", "identity", "value", "error"}
            or type(data["schema_version"]) is not int or data["schema_version"] != 1):
        raise ValueError("Invalid durable planner receipt")
    identity = data["identity"]
    if type(identity) is not dict or set(identity) != {item.name for item in fields(PlannerJobIdentity)}:
        raise ValueError("Invalid durable planner identity")
    for name, value in identity.items():
        if name in {"pass_index", "stage_round"}:
            valid = type(value) is int and value >= 0
        elif name in {"active_target_statement_keys", "helper_evidence_fingerprints"}:
            valid = type(value) is list and all(type(item) is str for item in value)
        else:
            valid = type(value) is str
        if not valid:
            raise ValueError("Invalid durable planner identity field")
    if not identity["job_id"] or not identity["request_fingerprint"]:
        raise ValueError("Missing durable planner request identity")
    error = None
    if data["error"] is not None:
        from .planner_job_receipt import decode_planner_error
        error = decode_planner_error(data["error"])
        if data["value"] is not None:
            raise ValueError("Durable planner receipt has both value and error")
    return PlannerJobResult(PlannerJobIdentity(**identity), data["value"], error)


class PlannerJobYield(BaseException):
    """Transfer a planner launch across the action transaction boundary.

    This derives from :class:`BaseException` so broad ``except Exception``
    recovery paths cannot accidentally turn the ownership transfer into an
    ordinary planner failure.
    """

    def __init__(self, launch: PlannerJobLaunch) -> None:
        super().__init__(launch.identity.job_id)
        self.launch = launch


class PlannerJobEquivalentPending(BaseException):
    """Wait for another lane to publish before preparing this request again."""

    def __init__(self, owner_identity: PlannerJobIdentity) -> None:
        super().__init__(owner_identity.job_id)
        self.owner_identity = owner_identity


_equivalent_wait_guard: ContextVar[Callable[[PlannerJobIdentity], bool] | None] = ContextVar(
    "planner_equivalent_wait_guard", default=None,
)


@contextmanager
def bind_planner_equivalent_wait_guard(guard: Callable[[PlannerJobIdentity], bool]):
    """Opt a compatible controller into neutral waits for a live local owner."""
    token = _equivalent_wait_guard.set(guard)
    try:
        yield
    finally:
        _equivalent_wait_guard.reset(token)


def planner_equivalent_wait_allowed(identity: PlannerJobIdentity) -> bool:
    guard = _equivalent_wait_guard.get()
    return guard is not None and guard(identity)


class PlannerJobExecutionCancelled(RuntimeError):
    """A provider operation ended itself before producing a receipt."""


@dataclass(slots=True)
class _PlannerJobEntry:
    identity: PlannerJobIdentity
    task: asyncio.Task[None] | None
    result: PlannerJobResult | None = None


class PlannerJobBroker:
    """Own and deliver long planner operations for one running session."""

    def __init__(self, *, durable_result_sink: Any = None,
                 restored_receipts: tuple[dict[str, Any], ...] = ()) -> None:
        self._jobs: dict[tuple[str, str], _PlannerJobEntry] = {}
        self._quarantined: dict[tuple[str, str], _PlannerJobEntry] = {}
        self._launched: set[PlannerJobIdentity] = set()
        self._changed = asyncio.Event()
        self._owner_tasks: set[asyncio.Task[Any]] = set()
        self._session_owners: dict[int, asyncio.Task[Any] | None] = {}
        self._watched_session_tasks: set[asyncio.Task[Any]] = set()
        self._durable_result_sink = durable_result_sink
        self._durable_failure: BaseException | None = None
        self.durable_binding: tuple[int, str] | None = None
        self._acknowledged: dict[tuple[str, str], PlannerJobIdentity] = {}
        for record in restored_receipts:
            result = planner_result_from_record(record)
            key = self._key(result.identity.job_id, result.identity.request_fingerprint)
            if key in self._jobs:
                raise ValueError("Duplicate durable planner receipt")
            self._jobs[key] = _PlannerJobEntry(result.identity, None, result)
            self._launched.add(result.identity)

    def bind_durability(self, *, binding: tuple[int, str], sink: Any,
                        receipts: tuple[dict[str, Any], ...]) -> None:
        """Attach a previously idle broker without replacing bound owners."""
        if self.durable_binding == binding:
            return
        if (self.durable_binding is not None or self._durable_result_sink is not None
                or self._jobs or self._quarantined or self._launched or self._acknowledged
                or self._durable_failure is not None):
            raise ValueError("Cannot rebind an active or previously durable planner broker")
        staged = PlannerJobBroker(durable_result_sink=sink, restored_receipts=receipts)
        self._jobs = staged._jobs
        self._launched = staged._launched
        self._durable_result_sink = sink
        self.durable_binding = binding

    def _check_durable_failure(self) -> None:
        if self._durable_failure is not None:
            raise self._durable_failure

    def acknowledged_receipts(self) -> tuple[PlannerJobIdentity, ...]:
        return tuple(self._acknowledged.values())

    def unconsumed_request_identities(self) -> tuple[PlannerJobIdentity, ...]:
        """Expose pending/ready request identities without receipt authority."""
        self._check_durable_failure()
        return tuple(entry.identity for entry in (
            *self._jobs.values(), *self._quarantined.values(),
        ))

    def confirm_receipts_committed(self, identities: tuple[PlannerJobIdentity, ...]) -> None:
        for identity in identities:
            key = self._key(identity.job_id, identity.request_fingerprint)
            if self._acknowledged.get(key) == identity:
                self._acknowledged.pop(key)
                self._launched.discard(identity)

    @staticmethod
    def _key(job_id: str, request_fingerprint: str) -> tuple[str, str]:
        return job_id, request_fingerprint

    def launch(self, launch: PlannerJobLaunch) -> bool:
        """Launch an exact request once; return false for a replay."""

        self._check_durable_failure()
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
        result: PlannerJobResult | None = None
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
            if result is not None and result.exception is not None:
                # The callback can finish after its action quantum, and a
                # generic transport error need not carry dispatch metadata.
                # Capture authenticated exposure before retiring this tracker.
                prior = getattr(result.exception, "provider_dispatches_started", 0)
                prior = prior if type(prior) is int and prior >= 0 else 0
                try:
                    result.exception.provider_dispatches_started = max(
                        prior, exposure.provider_dispatches_started,
                    )
                except Exception:
                    pass
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
        if self._durable_result_sink is not None:
            def still_owned() -> bool:
                current = self._jobs.get(key)
                return current is entry and current.task is owner_task
            try:
                await self._durable_result_sink(result, publication_guard=still_owned)
            except BaseException as error:
                if still_owned():
                    self._durable_failure = error
                    self._changed.set()
                return
            if not still_owned():
                return
        entry.result = result
        self._changed.set()

    def status(self, job_id: str, request_fingerprint: str) -> str:
        """Return ``missing``, ``pending``, or ``ready`` for an exact key."""

        self._check_durable_failure()
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
        self._check_durable_failure()
        return bool(self._quarantined) or any(
            entry.result is None for entry in self._jobs.values()
        )

    def has_ready(self) -> bool:
        self._check_durable_failure()
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
        entries = tuple(entry for _key, entry in keyed_entries if entry.task is not None)
        self._jobs.clear()
        for key, entry in keyed_entries:
            if entry.task is None:
                self._launched.discard(entry.identity)
                continue
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

        self._check_durable_failure()
        key = self._key(job_id, request_fingerprint)
        entry = self._jobs.get(key)
        if entry is None or entry.result is None:
            return None
        del self._jobs[key]
        if self._durable_result_sink is not None:
            self._acknowledged[key] = entry.identity
        return entry.result

    def peek(
        self,
        job_id: str,
        request_fingerprint: str,
    ) -> PlannerJobResult | None:
        """Lease a ready result without retiring it before durable commit."""

        self._check_durable_failure()
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
        if self._durable_result_sink is not None:
            self._acknowledged[key] = entry.identity
        else:
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
