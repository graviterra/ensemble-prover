"""Transactional buffering for speculative turn-recorder writes."""

from __future__ import annotations

from typing import Any


class QuarantinedTurnRecorder:
    """Buffer a speculative lane until its controller accepts the result.

    A strict asyncio deadline can detach an adapter that suppresses
    cancellation. Giving that task the parent recorder would let late events
    mutate the live run after the lane expired. Completed lanes commit their
    records; discarded lanes permanently ignore late writes.
    """

    def __init__(self, recorder: Any) -> None:
        self._recorder = recorder
        self._records: list[dict[str, Any]] = []
        self._active = True

    def record_turn(self, record: dict[str, Any]) -> None:
        if not self._active:
            return
        self._records.append(dict(record or {}))

    def commit(self) -> None:
        if not self._active:
            return
        self._active = False
        records = self._records
        self._records = []
        recorder = self._recorder
        if recorder is None or not hasattr(recorder, "record_turn"):
            return
        for record in records:
            recorder.record_turn(record)

    def discard(self) -> None:
        self._active = False
        self._records = []
