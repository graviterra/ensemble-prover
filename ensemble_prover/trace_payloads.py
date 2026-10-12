"""Content-addressed storage for repeated diagnostic prompt/tool payloads."""

from __future__ import annotations

import hashlib
import json
import os
import re
from collections import OrderedDict
from pathlib import Path
from typing import Any, Mapping


_FIELDS = {"llm_response": str, "messages_sent": list, "tool_call_log": list}
_MAX_BYTES = 16 * 1024 * 1024
_MIN_BYTES = 4096


def _read_blob_bytes(
    directory: Path, digest: str, *, max_bytes: int = _MAX_BYTES,
) -> bytes:
    """Read authenticated payload bytes within the caller's remaining budget."""
    limit = min(_MAX_BYTES, max(0, max_bytes))
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("invalid trace payload identity")
    parent = directory / "trace_payloads"
    if parent.is_symlink():
        raise ValueError("trace payload directory is a symlink")
    descriptor = os.open(parent / (digest + ".json"), os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        import stat
        if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
            raise ValueError("trace payload is not a regular file")
        raw = stream.read(limit + 1)
    if len(raw) > limit or hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError("trace payload hash or size mismatch")
    return raw


def _read_blob(directory: Path, digest: str) -> Any:
    return json.loads(_read_blob_bytes(directory, digest))


def expand_trace_payloads(record: Mapping[str, Any], directory: Path) -> dict[str, Any]:
    result = dict(record)
    refs = result.get("_payload_refs", {})
    if not isinstance(refs, dict) or set(refs) - _FIELDS.keys():
        raise ValueError("invalid trace payload references")
    for field, digest in refs.items():
        if field in result or not isinstance(digest, str):
            raise ValueError("ambiguous trace payload reference")
        value = _read_blob(Path(directory), digest)
        if not isinstance(value, _FIELDS[field]):
            raise ValueError("trace payload type mismatch")
        result[field] = value
    result.pop("_payload_refs", None)
    return result


class TracePayloadStore:
    """Keep first occurrences inline; move only duplicate large values."""

    def __init__(self, directory: Path) -> None:
        self.directory = Path(directory)
        self.seen: OrderedDict[str, None] = OrderedDict()

    def encode(self, record: Mapping[str, Any]) -> dict[str, Any]:
        result = dict(record)
        result.pop("_payload_refs", None)
        identities = {}
        refs = {}
        for field, kind in _FIELDS.items():
            value = result.get(field)
            if not isinstance(value, kind):
                continue
            raw = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
                             allow_nan=False).encode()
            digest = hashlib.sha256(raw).hexdigest()
            identities[field] = digest
            if _MIN_BYTES <= len(raw) <= _MAX_BYTES:
                if digest in self.seen:
                    parent = self.directory / "trace_payloads"
                    try:
                        parent.mkdir(mode=0o700, exist_ok=True)
                        if parent.is_symlink():
                            raise ValueError("trace payload directory is a symlink")
                        path = parent / (digest + ".json")
                        try:
                            descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
                        except FileExistsError:
                            if _read_blob(self.directory, digest) != value:
                                raise ValueError("conflicting trace payload")
                        else:
                            with os.fdopen(descriptor, "wb") as stream:
                                stream.write(raw)
                                stream.flush()
                                os.fsync(stream.fileno())
                            directory_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY)
                            try:
                                os.fsync(directory_fd)
                            finally:
                                os.close(directory_fd)
                        refs[field] = digest
                        result.pop(field)
                    except (OSError, ValueError):
                        # Diagnostic compaction must never prevent the original
                        # record from being persisted when sidecar IO fails.
                        pass
                self.seen[digest] = None
                self.seen.move_to_end(digest)
                while len(self.seen) > 2048:
                    self.seen.popitem(last=False)
        if identities:
            result["payload_ids"] = identities
        if refs:
            result["_payload_refs"] = refs
        return result
