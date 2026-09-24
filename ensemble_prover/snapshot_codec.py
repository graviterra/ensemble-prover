"""Lossless, bounded JSON snapshot compression for durable diagnostic records."""

from __future__ import annotations

import base64
import binascii
import hashlib
import json
import math
import zlib
from typing import Any

from .state_data import StateDataError, clone_json_value

MAX_SNAPSHOT_BYTES = 256 * 1024 * 1024


def _validate_object_keys(value: Any) -> None:
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise ValueError("snapshot JSON object keys must be strings")
        for child in value.values():
            _validate_object_keys(child)
    elif type(value) in {list, tuple}:
        for child in value:
            _validate_object_keys(child)


def snapshot_bytes(value: Any) -> bytes:
    # Archive payloads become opaque strings to the durable writer, so enforce
    # its key contract before compression can conceal lossy JSON coercions.
    try:
        value = clone_json_value(value, label="snapshot")
    except StateDataError as error:
        raise ValueError(str(error)) from error
    _validate_object_keys(value)
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False).encode("utf-8")


def _hash(value: Any) -> str:
    return hashlib.sha256(snapshot_bytes(value)).hexdigest()


def compress_snapshot(value: Any) -> str:
    raw = snapshot_bytes(value)
    if len(raw) > MAX_SNAPSHOT_BYTES:
        raise ValueError("snapshot exceeds size limit")
    return base64.b64encode(zlib.compress(raw)).decode("ascii")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant: {value}")


def _finite_float(value: str) -> float:
    number = float(value)
    if not math.isfinite(number):
        raise ValueError("non-finite JSON number")
    return number


def decompress_snapshot(value: str, *, max_bytes: int | None = None) -> Any:
    """Decode strict JSON within both the per-record and caller's byte limits."""
    if max_bytes is not None and (type(max_bytes) is not int or max_bytes < 0):
        raise ValueError("invalid snapshot size limit")
    limit = MAX_SNAPSHOT_BYTES if max_bytes is None else min(MAX_SNAPSHOT_BYTES, max_bytes)
    try:
        compressed = base64.b64decode(value, validate=True)
        decoder = zlib.decompressobj()
        raw = decoder.decompress(compressed, limit + 1)
        if len(raw) > limit or not decoder.eof or decoder.unused_data:
            raise ValueError("invalid or oversized compressed snapshot")
        return json.loads(raw, object_pairs_hook=_unique_object,
                          parse_constant=_reject_constant, parse_float=_finite_float)
    except (TypeError, binascii.Error, zlib.error, UnicodeError,
            json.JSONDecodeError, RecursionError) as error:
        raise ValueError("invalid compressed snapshot") from error


def _delta(before: Any, after: Any) -> list[Any]:
    if snapshot_bytes(before) == snapshot_bytes(after):
        return ["keep"]
    if type(before) is dict and type(after) is dict:
        changes = {
            key: _delta(before[key], value) if key in before else ["replace", value]
            for key, value in after.items()
            if key not in before or snapshot_bytes(before[key]) != snapshot_bytes(value)
        }
        return ["dict", changes, [key for key in before if key not in after]]
    if type(before) is list and type(after) is list:
        prefix = 0
        while prefix < min(len(before), len(after)):
            if snapshot_bytes(before[prefix]) != snapshot_bytes(after[prefix]):
                break
            prefix += 1
        return ["list", prefix, after[prefix:]]
    return ["replace", after]


def _apply(before: Any, delta: Any) -> Any:
    """Build changed paths without repeatedly copying unchanged subtrees."""
    if type(delta) is not list or not delta:
        raise ValueError("invalid snapshot delta")
    if delta == ["keep"]:
        return before
    if len(delta) == 2 and delta[0] == "replace":
        return delta[1]
    if len(delta) == 3 and delta[0] == "dict" and type(before) is dict:
        changes, removed = delta[1:]
        if type(changes) is not dict or type(removed) is not list:
            raise ValueError("invalid snapshot dictionary delta")
        result = dict(before)
        for key in removed:
            if type(key) is not str or key not in result:
                raise ValueError("invalid snapshot removed key")
            del result[key]
        for key, change in changes.items():
            result[key] = _apply(before.get(key), change)
        return result
    if len(delta) == 3 and delta[0] == "list" and type(before) is list:
        prefix, suffix = delta[1:]
        if type(prefix) is not int or not 0 <= prefix <= len(before) or type(suffix) is not list:
            raise ValueError("invalid snapshot list delta")
        return before[:prefix] + suffix
    raise ValueError("invalid snapshot delta operation")


def encode_trace_snapshot(snapshot: dict[str, Any], previous: Any) -> dict[str, Any]:
    """Keep small snapshots readable; delta-encode large repetitive histories."""
    size = len(snapshot_bytes(snapshot))
    if size > MAX_SNAPSHOT_BYTES:
        raise ValueError("snapshot exceeds size limit")
    if size < 4096:
        return snapshot
    return {
        "snapshot_encoding": "json-delta-zlib-v1",
        "base_sha256": _hash(previous),
        "sha256": _hash(snapshot),
        "data": compress_snapshot(_delta(previous, snapshot)),
    }


def decode_trace_snapshot(snapshot: dict[str, Any], previous: Any) -> dict[str, Any]:
    if "snapshot_encoding" not in snapshot:
        return snapshot
    if (snapshot.get("snapshot_encoding") != "json-delta-zlib-v1"
            or set(snapshot) != {"snapshot_encoding", "base_sha256", "sha256", "data"}
            or snapshot["base_sha256"] != _hash(previous)):
        raise ValueError("snapshot encoding or predecessor mismatch")
    decoded = _apply(previous, decompress_snapshot(snapshot["data"]))
    if (type(decoded) is not dict or len(snapshot_bytes(decoded)) > MAX_SNAPSHOT_BYTES
            or _hash(decoded) != snapshot["sha256"]):
        raise ValueError("snapshot hash mismatch")
    # Applying a deep change must not copy the whole remaining predecessor at
    # every level. Detach unchanged branches once, after validation, so callers
    # can mutate decoded snapshots without modifying earlier trace events.
    try:
        return clone_json_value(decoded, label="decoded snapshot")
    except StateDataError as error:
        raise ValueError(str(error)) from error
