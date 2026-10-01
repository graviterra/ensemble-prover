"""A memory operation borrows one existing owner allocation."""

from __future__ import annotations

import asyncio
import math
import time
from dataclasses import dataclass, field
from typing import Any, Callable
from pathlib import Path
from contextlib import contextmanager
import json
import os
import uuid


@dataclass
class MemoryBudget:
    owner_id: str
    deadline_monotonic: float
    max_probes: int = 4
    max_heartbeats: int = 200_000
    memory_mb: int = 8192
    remaining_tokens: int | None = None
    remaining_cost: float | None = None
    provider_owner: Any = None
    concurrency: int = 1
    cancellation_event: Any = None
    probes_used: int = field(default=0, init=False)

    def __post_init__(self) -> None:
        if not self.owner_id or not math.isfinite(self.deadline_monotonic):
            raise ValueError("memory work requires a finite owner deadline")
        for value in (
            self.max_probes,
            self.max_heartbeats,
            self.memory_mb,
            self.concurrency,
        ):
            if type(value) is not int or value < 0:
                raise ValueError("memory resource limits must be nonnegative integers")
        if self.remaining_tokens is not None and (
            type(self.remaining_tokens) is not int or self.remaining_tokens < 0
        ):
            raise ValueError(
                "memory token allowance must be nonnegative when configured"
            )
        if self.remaining_cost is not None and (
            not math.isfinite(self.remaining_cost) or self.remaining_cost < 0
        ):
            raise ValueError(
                "memory cost allowance must be finite and nonnegative when configured"
            )

    def remaining_s(self) -> float:
        return max(0.0, self.deadline_monotonic - time.monotonic())

    def check_cancelled(self) -> None:
        if self.cancellation_event is not None and self.cancellation_event.is_set():
            raise asyncio.CancelledError
        if self.remaining_s() <= 0:
            raise TimeoutError("memory owner allocation exhausted")

    def claim_probe(self) -> None:
        self.check_cancelled()
        if self.probes_used >= self.max_probes:
            raise TimeoutError("memory operation coverage exhausted")
        self.probes_used += 1


class MemoryReservation(float):
    """An in-process reservation token; its numeric value is the time cap."""

    identity: str


class MemoryAllocation:
    """Conserve a container's allocation across recursive and parallel sessions.

    Reservations are charged durably before dispatch. A crash can lose unused
    allowance, but reconstructing a session never renews previously charged work.
    Monotonic deadlines stay local to the live operation.
    """

    def __init__(self, seconds: float, *, run_dir: Path | None = None) -> None:
        import threading

        self.run_dir = Path(run_dir) if run_dir is not None else None
        self.seconds = float(seconds)
        if not math.isfinite(self.seconds) or self.seconds < 0:
            raise ValueError("allocation requires finite nonnegative seconds")
        self._lock = threading.RLock()
        self._sessions: list[Any] = []
        self._spent = 0.0
        self._active = False
        self._reservation: MemoryReservation | None = None

    @contextmanager
    def _durable_ledger(self, *, write: bool = False):
        if self.run_dir is None:
            yield None
            return
        import fcntl
        from .evidence import contained_directory, read_contained, write_contained

        with contained_directory(
            self.run_dir, "memory_allocations", create=True
        ) as directory:
            lock = os.open(
                "lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600, dir_fd=directory
            )
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                deadline = time.monotonic() + 0.05
                try:
                    ledger = json.loads(
                        read_contained(directory, "allocation.json", 4096, deadline)
                    )
                except FileNotFoundError:
                    try:
                        read_contained(directory, "initialized", 64, deadline)
                    except FileNotFoundError:
                        # Mark the lifecycle before the first ledger write. A
                        # crash can lose allowance but cannot silently renew it.
                        write_contained(directory, "initialized", b"1", deadline)
                    else:
                        raise ValueError("memory allocation ledger is missing")
                    ledger = {
                        "schema": 1,
                        "total": self.seconds,
                        "spent": 0.0,
                        "active": "",
                    }
                    write_contained(
                        directory,
                        "allocation.json",
                        json.dumps(ledger, sort_keys=True).encode(),
                        deadline,
                    )
                else:
                    try:
                        read_contained(directory, "initialized", 64, deadline)
                    except FileNotFoundError:
                        write_contained(directory, "initialized", b"1", deadline)
                if (
                    ledger.get("schema") != 1
                    or not isinstance(ledger.get("active"), str)
                    or len(ledger["active"]) > 64
                    or any(
                        type(ledger.get(key)) not in (int, float)
                        or not math.isfinite(ledger[key])
                        or ledger[key] < 0
                        for key in ("total", "spent")
                    )
                ):
                    raise ValueError("memory allocation ledger is corrupt")
                self.seconds = min(self.seconds, ledger["total"])
                self._spent = max(self._spent, ledger["spent"])
                yield ledger
                if write:
                    write_contained(
                        directory,
                        "allocation.json",
                        json.dumps(ledger, sort_keys=True).encode(),
                        deadline,
                    )
            finally:
                os.close(lock)

    def attach(self, session: Any) -> None:
        import weakref

        with self._lock:
            self._sessions.append(weakref.ref(session))
            self._synchronize()

    def _synchronize(self) -> None:
        live = [reference for reference in self._sessions if reference() is not None]
        self._sessions = live
        for reference in live:
            saved_total = reference().mathematical_memory_state.get(
                "allocation_total_s", self.seconds
            )
            if (
                type(saved_total) not in (int, float)
                or not math.isfinite(saved_total)
                or saved_total < 0
            ):
                self.seconds = 0.0
            else:
                self.seconds = min(self.seconds, float(saved_total))
            saved = reference().mathematical_memory_state.get("allocation_spent_s", 0.0)
            if type(saved) not in (int, float) or not math.isfinite(saved) or saved < 0:
                self._spent = self.seconds
            else:
                self._spent = max(self._spent, float(saved))
        for reference in live:
            reference().mathematical_memory_state["allocation_spent_s"] = self._spent
            reference().mathematical_memory_state["allocation_total_s"] = self.seconds

    def available(self) -> float:
        with self._lock:
            try:
                with self._durable_ledger() as ledger:
                    self._synchronize()
                    if self._active or (ledger is not None and ledger["active"]):
                        return 0.0
                    return max(0.0, self.seconds - self._spent)
            except (OSError, ValueError, RuntimeError):
                return 0.0

    def reserve(self, limit: float) -> float:
        with self._lock:
            try:
                with self._durable_ledger(write=True) as ledger:
                    self._synchronize()
                    if self._active or (ledger is not None and ledger["active"]):
                        return 0.0
                    amount = min(max(0.0, limit), max(0.0, self.seconds - self._spent))
                    if amount <= 0:
                        return 0.0
                    token = MemoryReservation(amount)
                    token.identity = uuid.uuid4().hex
                    self._spent += amount
                    if ledger is not None:
                        ledger.update(
                            total=self.seconds,
                            spent=self._spent,
                            active=token.identity,
                            active_reserved_s=amount,
                        )
                # Publish live dispatch only after reservation fsync succeeds.
                self._active = True
                self._reservation = token
                self._synchronize()
                return token
            except (OSError, ValueError, RuntimeError):
                return 0.0

    def finish(self, reserved: float, elapsed: float) -> None:
        with self._lock:
            if reserved is not self._reservation or self._reservation is None:
                return
            try:
                with self._durable_ledger(write=True) as ledger:
                    if (
                        ledger is not None
                        and ledger["active"] != self._reservation.identity
                    ):
                        return
                    if not math.isfinite(elapsed) or elapsed < 0:
                        elapsed = float(reserved)
                    refund = max(0.0, float(reserved) - max(0.0, elapsed))
                    new_spent = max(0.0, self._spent - refund)
                    if ledger is not None:
                        ledger.update(spent=new_spent, active="", active_reserved_s=0.0)
                self._spent = new_spent
                for reference in self._sessions:
                    session = reference()
                    if session is not None:
                        session.mathematical_memory_state["allocation_spent_s"] = (
                            self._spent
                        )
            except (OSError, ValueError, RuntimeError):
                # Ambiguous settlement remains charged and blocks replay until
                # the owning controller reconciles the original dispatch.
                pass
            finally:
                self._reservation = None
                self._active = False

    def reconcile(self, authority: Callable[[str, float], float | None]) -> bool:
        """Settle a crashed dispatch through a live controller receipt validator.

        The callback must fence/join the original worker and establish its actual
        charged time for this exact token. A serialized completion flag is never
        sufficient. Missing, invalid, or unknown receipts leave work blocked.
        """
        if not callable(authority) or self.run_dir is None:
            return False
        with self._lock:
            if self._active:
                return False
            try:
                with self._durable_ledger(write=True) as ledger:
                    if not ledger or not ledger["active"]:
                        return False
                    reserved = ledger.get("active_reserved_s")
                    if (
                        not isinstance(reserved, (int, float))
                        or isinstance(reserved, bool)
                        or not math.isfinite(reserved)
                        or not 0 < reserved <= ledger["spent"]
                    ):
                        return False
                    actual = authority(ledger["active"], reserved)
                    if (
                        not isinstance(actual, (int, float))
                        or isinstance(actual, bool)
                        or not math.isfinite(actual)
                        or not 0 <= actual <= reserved
                    ):
                        return False
                    settled = max(0.0, ledger["spent"] - reserved + actual)
                    ledger.update(spent=settled, active="", active_reserved_s=0.0)
                self._spent = settled
                for reference in self._sessions:
                    session = reference()
                    if session is not None:
                        session.mathematical_memory_state["allocation_spent_s"] = (
                            settled
                        )
                return True
            except (OSError, ValueError, RuntimeError):
                return False
