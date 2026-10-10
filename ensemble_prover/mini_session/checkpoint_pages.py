"""Authenticated immutable pages behind atomic checkpoint record envelopes."""
from __future__ import annotations

from contextlib import contextmanager
import hashlib
import os
from pathlib import Path
import stat
import tempfile
from typing import Any, Iterator
import zlib

from ..json_pages import PAGE_BYTES, decode_pages, encode_segments, strict_loads, string_pages

ENCODING = "checkpoint-json-pages-v1"
_DIRECTORY = ".checkpoint_pages"
_FANOUT = 128


def _digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _valid_digest(value: Any) -> bool:
    return (type(value) is str and len(value) == 64
            and all(c in "0123456789abcdef" for c in value))


def _pack(value: Any) -> bytes:
    import json
    return json.dumps(value, ensure_ascii=False, allow_nan=False,
                      sort_keys=True, separators=(",", ":")).encode("utf-8")


def decompress_page(data: bytes, expected: int, *, limit: int) -> bytes:
    if type(expected) is not int or not 0 < expected <= limit:
        raise ValueError("invalid checkpoint page size")
    try:
        decoder = zlib.decompressobj()
        raw = decoder.decompress(data, expected + 1)
    except zlib.error as error:
        raise ValueError("corrupt compressed checkpoint page") from error
    if len(raw) != expected or not decoder.eof or decoder.unused_data:
        raise ValueError("truncated or oversized checkpoint page")
    return raw


class PageStore:
    """Publish pages before their manifest; retain all referenced generations."""

    def __init__(self, parent: Path, *, parent_identity: tuple[int, int] | None = None) -> None:
        self.parent = parent
        self._parent_identity = parent_identity
        self._identity: tuple[int, int] | None = None
        self._durable: dict[str, tuple[int, int, int, int, int]] = {}
        # Only immutable exact strings are identity-cached. Mutable containers
        # are traversed on every save, including caller edits between saves.
        self._strings: dict[int, tuple[str, int, list[list[Any]]]] = {}

    def clear_string_hints(self) -> None:
        """Release bodies after a newer record no longer uses paged encoding."""
        self._strings.clear()

    @contextmanager
    def directory(self, *, create: bool, parent: Path | None = None) -> Iterator[tuple[int, int]]:
        parent = self.parent if parent is None else parent
        parent_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        directory_fd = None
        try:
            parent_original = os.fstat(parent_fd)
            if (self._parent_identity is not None
                    and (parent_original.st_dev, parent_original.st_ino) != self._parent_identity):
                raise ValueError("checkpoint page parent directory was replaced")
            flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
            try:
                directory_fd = os.open(_DIRECTORY, flags, dir_fd=parent_fd)
            except FileNotFoundError:
                if not create:
                    raise ValueError("missing checkpoint page directory") from None
                try:
                    os.mkdir(_DIRECTORY, mode=0o700, dir_fd=parent_fd)
                except FileExistsError:
                    pass
                os.fsync(parent_fd)
                directory_fd = os.open(_DIRECTORY, flags, dir_fd=parent_fd)
            except OSError as error:
                raise ValueError("invalid checkpoint page directory") from error
            identity_stat = os.fstat(directory_fd)
            identity = identity_stat.st_dev, identity_stat.st_ino
            if self._identity is not None and self._identity != identity:
                raise ValueError("checkpoint page directory was replaced")
            self._identity = identity
            yield parent_fd, directory_fd
            current = os.stat(_DIRECTORY, dir_fd=parent_fd, follow_symlinks=False)
            parent_current = parent.stat()
            if (not stat.S_ISDIR(current.st_mode)
                    or (current.st_dev, current.st_ino) != identity
                    or (parent_current.st_dev, parent_current.st_ino)
                    != (parent_original.st_dev, parent_original.st_ino)):
                raise ValueError("checkpoint page directory was replaced during IO")
        finally:
            if directory_fd is not None:
                os.close(directory_fd)
            os.close(parent_fd)

    @staticmethod
    def _stamp(info: os.stat_result) -> tuple[int, int, int, int, int]:
        return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns

    def _write(self, directory: int, raw: bytes) -> list[Any]:
        digest = _digest(raw)
        filename = f"{digest}.blob"
        try:
            info = os.stat(filename, dir_fd=directory, follow_symlinks=False)
        except FileNotFoundError:
            info = None
        if info is not None and stat.S_ISREG(info.st_mode) and self._durable.get(digest) == self._stamp(info):
            return [digest, len(raw)]
        sample = raw[:2048]
        compressed = (b"RAW1" + raw if len(sample) >= 1024
                      and len(zlib.compress(sample, level=1)) > len(sample) * 0.65
                      else zlib.compress(raw))
        descriptor, temporary = tempfile.mkstemp(prefix=".page-", suffix=".tmp",
                                                 dir=f"/proc/self/fd/{directory}")
        try:
            with os.fdopen(descriptor, "wb") as handle:
                handle.write(compressed)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, f"/proc/self/fd/{directory}/{filename}")
            # The containing directory is synced once after all new pages.
            self._durable[digest] = self._stamp(os.stat(filename, dir_fd=directory, follow_symlinks=False))
        finally:
            try:
                os.unlink(temporary)
            except FileNotFoundError:
                pass
        return [digest, len(raw)]

    @staticmethod
    def _read(directory: int, reference: Any, *, limit: int) -> bytes:
        if (type(reference) is not list or len(reference) != 2
                or not _valid_digest(reference[0]) or type(reference[1]) is not int
                or not 0 < reference[1] <= limit):
            raise ValueError("invalid checkpoint page reference")
        descriptor = None
        try:
            descriptor = os.open(f"{reference[0]}.blob",
                                 os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC,
                                 dir_fd=directory)
            if not stat.S_ISREG(os.fstat(descriptor).st_mode):
                raise ValueError("invalid checkpoint page file")
            with os.fdopen(descriptor, "rb") as handle:
                descriptor = None
                data = handle.read(limit + 1025)
            if len(data) > limit + 1024:
                raise ValueError("oversized compressed checkpoint page")
            if data.startswith(b"RAW1"):
                raw = data[4:]
                if len(raw) != reference[1]:
                    raise ValueError("invalid raw checkpoint page length")
            else:
                raw = decompress_page(data, reference[1], limit=limit)
            if _digest(raw) != reference[0]:
                raise ValueError("checkpoint page hash mismatch")
            return raw
        except OSError as error:
            raise ValueError("missing or invalid checkpoint page file") from error
        finally:
            if descriptor is not None:
                os.close(descriptor)

    def encode(self, value: dict[str, Any], *, limit: int,
               parent: Path | None = None) -> dict[str, Any]:
        try:
            return self._encode(value, limit=limit, parent=parent)
        except BaseException:
            # A partial batch has no directory durability acknowledgement.
            self._durable.clear()
            self._strings.clear()
            raise

    def _encode(self, value: dict[str, Any], *, limit: int,
                parent: Path | None = None) -> dict[str, Any]:
        page_limit = min(PAGE_BYTES, limit)
        # Index fanout follows the blob bound, never a total-state limit.
        fanout = min(_FANOUT, max(2, (page_limit - 128) // 90))
        references: list[list[Any]] = []
        used_strings: set[int] = set()
        with self.directory(create=True, parent=parent) as (_parent, directory):
            for segment in encode_segments(value, limit=page_limit):
                if isinstance(segment, bytes):
                    references.append(self._write(directory, segment))
                    continue
                used_strings.add(id(segment))
                cached = self._strings.get(id(segment))
                if cached is not None and cached[0] is segment and cached[1] == page_limit:
                    # Check file identities without decoding or serializing bodies.
                    saved = cached[2]
                    valid = True
                    for digest, _size in saved:
                        try:
                            info = os.stat(f"{digest}.blob", dir_fd=directory, follow_symlinks=False)
                        except FileNotFoundError:
                            valid = False
                            break
                        if not stat.S_ISREG(info.st_mode) or self._durable.get(digest) != self._stamp(info):
                            valid = False
                            break
                    if valid:
                        references.extend(saved)
                        continue
                saved = [self._write(directory, raw) for raw in string_pages(segment, limit=page_limit)]
                self._strings[id(segment)] = segment, page_limit, saved
                references.extend(saved)
            self._strings = {key: value for key, value in self._strings.items() if key in used_strings}
            count = len(references)
            level = 0
            nodes = [(index, index + 1, reference) for index, reference in enumerate(references)]
            while True:
                parents = []
                for offset in range(0, len(nodes), fanout):
                    group = nodes[offset:offset + fanout]
                    start, end = group[0][0], group[-1][1]
                    raw = _pack({"level": level, "start": start, "end": end,
                                 "children": [[a, b, ref] for a, b, ref in group]})
                    if len(raw) > page_limit:
                        raise ValueError("checkpoint index exceeds page size limit")
                    parents.append((start, end, self._write(directory, raw)))
                if len(parents) == 1:
                    os.fsync(directory)
                    return {"checkpoint_encoding": ENCODING, "root": parents[0][2],
                            "pages": count, "level": level}
                nodes = parents
                level += 1

    def references(self, envelope: dict[str, Any], directory: int, *,
                   limit: int) -> Iterator[tuple[bool, list[Any]]]:
        """Yield authenticated index coordinates and their bounded data references."""
        if (set(envelope) != {"checkpoint_encoding", "root", "pages", "level"}
                or envelope["checkpoint_encoding"] != ENCODING
                or type(envelope["pages"]) is not int or envelope["pages"] < 1
                or type(envelope["level"]) is not int or envelope["level"] < 0
                or envelope["level"] > envelope["pages"].bit_length()):
            raise ValueError("invalid checkpoint page envelope")
        pending = [(envelope["root"], envelope["level"], 0, envelope["pages"])]
        seen_indexes: set[str] = set()
        while pending:
            reference, level, start, end = pending.pop()
            if (type(reference) is not list or len(reference) != 2
                    or not _valid_digest(reference[0]) or type(reference[1]) is not int
                    or not 0 < reference[1] <= limit):
                raise ValueError("invalid checkpoint page reference")
            yield level == -1, reference
            if level == -1:
                continue
            raw = self._read(directory, reference, limit=limit)
            node = strict_loads(raw)
            if reference[0] in seen_indexes:
                raise ValueError("repeated checkpoint index")
            seen_indexes.add(reference[0])
            if (type(node) is not dict or set(node) != {"level", "start", "end", "children"}
                    or type(node["level"]) is not int or node["level"] != level
                    or type(node["start"]) is not int or node["start"] != start
                    or type(node["end"]) is not int or node["end"] != end
                    or type(node["children"]) is not list or not node["children"]):
                raise ValueError("invalid checkpoint index coordinates")
            cursor = start
            children = []
            for child in node["children"]:
                if (type(child) is not list or len(child) != 3
                        or type(child[0]) is not int or child[0] != cursor
                        or type(child[1]) is not int or not cursor < child[1] <= end
                        or (level == 0 and child[1] != cursor + 1)):
                    raise ValueError("invalid checkpoint index range")
                children.append((child[2], level - 1, child[0], child[1]))
                cursor = child[1]
            if cursor != end:
                raise ValueError("incomplete checkpoint index range")
            pending.extend(reversed(children))

    def decode(self, envelope: dict[str, Any], *, limit: int,
               parent: Path | None = None) -> dict[str, Any]:
        with self.directory(create=False, parent=parent) as (_parent, directory):
            value = decode_pages(self._read(directory, reference, limit=limit)
                                 for data, reference in self.references(envelope, directory, limit=limit)
                                 if data)
        if type(value) is not dict:
            raise ValueError("checkpoint JSON must be an object")
        return value

    def collect(self, *, record_limit: int, parent: Path | None = None) -> None:
        """Reclaim unreachable pages under the caller's exclusive registry lock.

        Every physical JSON receipt in this directory pins its pages, including
        failed-unlink snapshots and older archive receipts. Corrupt or unreadable
        receipts stop collection before any unlink. Temporary files are never
        published receipts. No live data payload is decompressed for collection.
        """
        with self.directory(create=False, parent=parent) as (parent_fd, directory):
            # A directory's ".." can change after it is opened. Keep receipt
            # enumeration on the parent descriptor that opened these pages.
            reachable: set[str] = set()
            for name in os.listdir(parent_fd):
                if not name.endswith(".json"):
                    continue
                descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC,
                                     dir_fd=parent_fd)
                with os.fdopen(descriptor, "rb") as handle:
                    if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
                        raise ValueError("invalid checkpoint collection receipt")
                    raw = handle.read(record_limit + 1)
                if len(raw) > record_limit:
                    raise ValueError("oversized checkpoint collection receipt")
                envelope = strict_loads(raw)
                if type(envelope) is not dict:
                    raise ValueError("invalid checkpoint collection receipt")
                if "checkpoint_encoding" in envelope:
                    reachable.update(ref[0] for _, ref in self.references(
                        envelope, directory, limit=min(PAGE_BYTES, record_limit),
                    ))
            for name in os.listdir(directory):
                if name.endswith(".blob") and _valid_digest(name[:-5]) and name[:-5] not in reachable:
                    os.unlink(name, dir_fd=directory)
                    self._durable.pop(name[:-5], None)
            os.fsync(directory)
        self._strings = {
            key: cached for key, cached in self._strings.items()
            if all(reference[0] in reachable for reference in cached[2])
        }
