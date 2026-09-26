"""Bounded incremental reader for newline-delimited JSON traces.

The tailer commits only complete, newline-terminated records. It tracks the
file's device/inode and size so that replacement or truncation starts a new
generation instead of mixing bytes from two files. Rows larger than the
record limit are discarded through their next newline and reported as a
skipped byte range; they never grow memory. Reading is bounded per poll by
bytes and record count so an observer cannot stall on a huge backlog.
"""

from __future__ import annotations

import json
import os
import stat
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

DEFAULT_MAX_RECORD_BYTES = 4 * 1024 * 1024
DEFAULT_MAX_SLICE_BYTES = 4 * 1024 * 1024
DEFAULT_MAX_SLICE_RECORDS = 1000
_READ_CHUNK = 64 * 1024


@dataclass
class TailEvent:
    kind: str  # generation_reset | skipped_range | invalid_record | unavailable
    detail: str
    byte_start: int = 0
    byte_end: int = 0


@dataclass
class TailSlice:
    records: list[dict[str, Any]] = field(default_factory=list)
    events: list[TailEvent] = field(default_factory=list)
    offset: int = 0
    generation: int = 0
    size: int = 0
    has_more: bool = False


def _reject_constant(name: str) -> Any:
    raise ValueError(f"non-finite JSON constant {name!r} rejected")


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key {key!r}")
        result[key] = value
    return result


def parse_record(raw: bytes) -> dict[str, Any]:
    """Strictly parse one trace row: UTF-8, JSON object, finite numbers."""
    text = raw.decode("utf-8")
    value = json.loads(
        text, parse_constant=_reject_constant, object_pairs_hook=_reject_duplicate_keys
    )
    if not isinstance(value, dict):
        raise ValueError("trace row is not a JSON object")
    return value


class JsonlTailer:
    def __init__(
        self,
        path: str | os.PathLike[str],
        *,
        max_record_bytes: int = DEFAULT_MAX_RECORD_BYTES,
        max_slice_bytes: int = DEFAULT_MAX_SLICE_BYTES,
        max_slice_records: int = DEFAULT_MAX_SLICE_RECORDS,
    ) -> None:
        self.path = Path(path)
        self.max_record_bytes = int(max_record_bytes)
        self.max_slice_bytes = int(max_slice_bytes)
        self.max_slice_records = int(max_slice_records)
        self.offset = 0  # committed byte position
        self.generation = 0
        self.records_seen = 0
        self.bytes_skipped = 0
        self._identity: tuple[int, int] | None = None
        self._partial = b""
        self._discarding = False
        self._discard_start = 0

    # -- state helpers -----------------------------------------------------

    def _reset(self, events: list[TailEvent], detail: str) -> None:
        self.generation += 1
        events.append(TailEvent("generation_reset", detail, 0, self.offset))
        self.offset = 0
        self._partial = b""
        self._discarding = False
        self._discard_start = 0

    @property
    def read_position(self) -> int:
        return self.offset + len(self._partial)

    # -- polling -------------------------------------------------------------

    def poll(self) -> TailSlice:
        events: list[TailEvent] = []
        records: list[dict[str, Any]] = []
        try:
            fd = os.open(self.path, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC)
        except OSError as exc:
            events.append(TailEvent("unavailable", f"{exc.__class__.__name__}: {exc}"))
            return TailSlice([], events, self.offset, self.generation, 0, False)
        try:
            st = os.fstat(fd)
            if not stat.S_ISREG(st.st_mode):
                events.append(TailEvent("unavailable", "not a regular file"))
                return TailSlice([], events, self.offset, self.generation, 0, False)
            identity = (st.st_dev, st.st_ino)
            if self._identity is not None and identity != self._identity:
                self._reset(events, "trace file replaced (new device/inode)")
            elif st.st_size < self.read_position:
                self._reset(events, "trace file shrank below committed position")
            self._identity = identity
            os.lseek(fd, self.read_position, os.SEEK_SET)
            budget = self.max_slice_bytes
            if b"\n" in self._partial:
                # Complete records left unparsed by a previous record-capped slice.
                self._consume(b"", records, events)
            while budget > 0 and len(records) < self.max_slice_records:
                chunk = os.read(fd, min(_READ_CHUNK, budget))
                if not chunk:
                    break
                budget -= len(chunk)
                self._consume(chunk, records, events)
            size = os.fstat(fd).st_size
        finally:
            os.close(fd)
        has_more = size > self.read_position or b"\n" in self._partial
        return TailSlice(records, events, self.offset, self.generation, size, has_more)

    def _consume(
        self, chunk: bytes, records: list[dict[str, Any]], events: list[TailEvent]
    ) -> None:
        data = self._partial + chunk
        self._partial = b""
        start = 0
        while True:
            if len(records) >= self.max_slice_records and not self._discarding:
                # Record cap reached: keep the unparsed remainder (bounded by
                # one read chunk plus a partial row) for the next slice.
                self._partial = data[start:]
                return
            newline = data.find(b"\n", start)
            if newline < 0:
                rest = data[start:]
                if self._discarding:
                    self.offset += len(rest)
                    self.bytes_skipped += len(rest)
                elif len(rest) > self.max_record_bytes:
                    self._discarding = True
                    self._discard_start = self.offset
                    self.offset += len(rest)
                    self.bytes_skipped += len(rest)
                else:
                    self._partial = rest
                return
            line = data[start:newline]
            line_len = newline + 1 - start
            if self._discarding:
                self.offset += line_len
                self.bytes_skipped += line_len
                self._discarding = False
                events.append(
                    TailEvent(
                        "skipped_range",
                        "row exceeded record byte limit",
                        self._discard_start,
                        self.offset,
                    )
                )
            elif len(line) > self.max_record_bytes:
                events.append(
                    TailEvent(
                        "skipped_range",
                        "row exceeded record byte limit",
                        self.offset,
                        self.offset + line_len,
                    )
                )
                self.offset += line_len
                self.bytes_skipped += line_len
            else:
                byte_start = self.offset
                self.offset += line_len
                if line.strip():
                    try:
                        records.append(parse_record(line))
                        self.records_seen += 1
                    except (ValueError, UnicodeDecodeError) as exc:
                        events.append(
                            TailEvent("invalid_record", str(exc), byte_start, self.offset)
                        )
            start = newline + 1
