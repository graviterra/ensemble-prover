"""Strict JSON and YAML documents, canonical hashes, and durable file writes."""

from __future__ import annotations

from contextlib import contextmanager
import hashlib
import json
import math
import os
from pathlib import Path
import re
import tempfile
import threading
from typing import Any, Iterator

import yaml
from yaml.events import AliasEvent
from yaml.nodes import MappingNode

from .errors import LocalInferenceError

_MAX_DOCUMENT_BYTES = 1024 * 1024
_MAX_DEPTH = 32
_CODE = re.compile(r"^[a-z][a-z0-9_]{0,63}$")
_DROPPED_RESOLVERS = {
    "tag:yaml.org,2002:bool",
    "tag:yaml.org,2002:null",
    "tag:yaml.org,2002:timestamp",
    "tag:yaml.org,2002:merge",
    "tag:yaml.org,2002:value",
    "tag:yaml.org,2002:yaml",
}
_THREAD_LOCKS: dict[str, threading.Lock] = {}
_THREAD_GUARD = threading.Lock()


def canonical_json(value: Any) -> str:
    """Serialize inert JSON with sorted keys and no binary floats."""

    return json.dumps(
        _json_ready(value),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )


def content_hash(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def fingerprint(kind: str, payload: dict[str, Any]) -> str:
    if type(kind) is not str or _CODE.fullmatch(kind) is None:
        raise LocalInferenceError("invalid_fingerprint")
    if type(payload) is not dict:
        raise LocalInferenceError("invalid_fingerprint")
    return content_hash({"kind": kind, "schema": 1, "payload": payload})


def parse_json_text(text: str, *, max_bytes: int = _MAX_DOCUMENT_BYTES) -> Any:
    raw = _document_bytes(text, max_bytes=max_bytes, code="invalid_json")
    caught: LocalInferenceError | None = None
    value: Any = None
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except LocalInferenceError as exc:
        caught = exc
    except (UnicodeError, json.JSONDecodeError, RecursionError, ValueError):
        caught = LocalInferenceError("invalid_json")
    if caught is not None:
        raise caught from None
    _reject_exotic(value)
    return value


def parse_yaml_text(text: str, *, max_bytes: int = _MAX_DOCUMENT_BYTES) -> Any:
    raw = _document_bytes(text, max_bytes=max_bytes, code="invalid_yaml")
    loader: _StrictYAMLLoader | None = None
    caught: LocalInferenceError | None = None
    value: Any = None
    try:
        try:
            loader = _StrictYAMLLoader(raw.decode("utf-8"))
            value = loader.get_single_data()
        except LocalInferenceError as exc:
            caught = exc
        except Exception:
            caught = LocalInferenceError("invalid_yaml")
    finally:
        if loader is not None:
            try:
                loader.dispose()
            except Exception:
                if caught is None:
                    caught = LocalInferenceError("invalid_yaml")
    if caught is not None:
        raise caught from None
    if value is None:
        raise LocalInferenceError("invalid_yaml")
    _reject_exotic(value)
    return value


def atomic_write_json(path: Path, value: dict[str, Any], *, max_bytes: int) -> None:
    if path.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    payload = canonical_json(value).encode("utf-8")
    if len(payload) > max_bytes:
        raise LocalInferenceError("document_too_large")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=".local-inference-", suffix=".tmp", dir=path.parent,
    )
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temporary, 0o600)
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def read_json_object(path: Path, *, max_bytes: int, corrupt_code: str) -> dict[str, Any]:
    if path.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    try:
        raw = path.read_bytes()
    except OSError:
        raise LocalInferenceError(corrupt_code) from None
    if len(raw) > max_bytes:
        raise LocalInferenceError(corrupt_code)
    try:
        text = raw.decode("utf-8")
    except UnicodeError:
        raise LocalInferenceError(corrupt_code) from None
    try:
        value = parse_json_text(text, max_bytes=max_bytes)
    except LocalInferenceError:
        raise LocalInferenceError(corrupt_code) from None
    if type(value) is not dict:
        raise LocalInferenceError(corrupt_code)
    return value


@contextmanager
def durable_mutation(directory: Path) -> Iterator[None]:
    """Process-local lock plus an exclusive file lock around a ledger rewrite."""

    directory.mkdir(parents=True, exist_ok=True)
    lock_path = directory / ".mutation.lock"
    thread_lock = _thread_lock(lock_path)
    with thread_lock:
        descriptor = os.open(lock_path, os.O_RDWR | os.O_CREAT, 0o600)
        try:
            import fcntl

            fcntl.flock(descriptor, fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def copy_state(value: dict[str, Any]) -> dict[str, Any]:
    cloned = json.loads(canonical_json(value))
    if type(cloned) is not dict:
        raise LocalInferenceError("corrupt_json")
    return cloned


def _document_bytes(text: str, *, max_bytes: int, code: str) -> bytes:
    if type(text) is not str:
        raise LocalInferenceError(code)
    if text.startswith("\ufeff") or "\x00" in text:
        raise LocalInferenceError(code)
    try:
        raw = text.encode("utf-8")
    except UnicodeError:
        raise LocalInferenceError(code) from None
    if len(raw) > max_bytes:
        raise LocalInferenceError("document_too_large")
    return raw


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if type(key) is not str:
            raise LocalInferenceError("non_string_key")
        if key in result:
            raise LocalInferenceError("duplicate_key")
        result[key] = value
    return result


def _reject_constant(_name: str) -> None:
    raise LocalInferenceError("nonfinite_number")


def _json_ready(value: Any, depth: int = 0) -> Any:
    if depth > _MAX_DEPTH:
        raise LocalInferenceError("document_too_deep")
    if value is None or type(value) in {str, bool, int}:
        return value
    if type(value) is float:
        raise LocalInferenceError("float_not_canonical")
    if type(value) is list:
        return [_json_ready(item, depth + 1) for item in value]
    if type(value) is dict:
        ready: dict[str, Any] = {}
        for key, item in value.items():
            if type(key) is not str:
                raise LocalInferenceError("non_string_key")
            ready[key] = _json_ready(item, depth + 1)
        return ready
    raise LocalInferenceError("unsupported_scalar")


def _reject_exotic(value: Any, depth: int = 0) -> None:
    if depth > _MAX_DEPTH:
        raise LocalInferenceError("document_too_deep")
    if value is None or type(value) in {str, bool, int}:
        return
    if type(value) is float:
        if not math.isfinite(value):
            raise LocalInferenceError("nonfinite_number")
        return
    if type(value) is list:
        for item in value:
            _reject_exotic(item, depth + 1)
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                raise LocalInferenceError("non_string_key")
            _reject_exotic(item, depth + 1)
        return
    raise LocalInferenceError("unsupported_scalar")


def _construct_map(loader: yaml.SafeLoader, node: MappingNode) -> dict[str, Any]:
    if not isinstance(node, MappingNode):
        raise LocalInferenceError("mapping_required")
    mapping: dict[str, Any] = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=True)
        if type(key) is not str:
            raise LocalInferenceError("non_string_key")
        if key == "<<":
            raise LocalInferenceError("yaml_merge_forbidden")
        if key in mapping:
            raise LocalInferenceError("duplicate_key")
        mapping[key] = loader.construct_object(value_node, deep=True)
    return mapping


def _construct_int(loader: yaml.SafeLoader, node: Any) -> int:
    raw = loader.construct_scalar(node)
    if raw == "-0" or re.fullmatch(r"-?(?:0|[1-9][0-9]*)", raw) is None:
        raise LocalInferenceError("noncanonical_integer")
    return int(raw)


def _construct_float(loader: yaml.SafeLoader, node: Any) -> float:
    raw = loader.construct_scalar(node)
    if re.fullmatch(r"-?(?:0|[1-9][0-9]*)\.[0-9]+(?:[eE][-+]?[0-9]+)?", raw) is None:
        raise LocalInferenceError("nonfinite_number")
    value = float(raw)
    if not math.isfinite(value):
        raise LocalInferenceError("nonfinite_number")
    return value


class _StrictYAMLLoader(yaml.SafeLoader):
    def compose_node(self, parent: Any, index: Any) -> Any:
        if self.check_event(AliasEvent):
            raise LocalInferenceError("yaml_alias_forbidden")
        depth = getattr(self, "_local_depth", 0) + 1
        if depth > _MAX_DEPTH:
            raise LocalInferenceError("document_too_deep")
        self._local_depth = depth
        try:
            return super().compose_node(parent, index)
        finally:
            self._local_depth = depth - 1


def _install_loader() -> None:
    filtered: dict[Any, list[Any]] = {}
    for key, resolvers in yaml.SafeLoader.yaml_implicit_resolvers.items():
        kept = [item for item in resolvers if item[0] not in _DROPPED_RESOLVERS]
        if kept:
            filtered[key] = kept
    _StrictYAMLLoader.yaml_implicit_resolvers = filtered
    _StrictYAMLLoader.add_implicit_resolver(
        "tag:yaml.org,2002:bool",
        re.compile(r"^(?:true|True|TRUE|false|False|FALSE)$"),
        list("tTfF"),
    )
    _StrictYAMLLoader.add_implicit_resolver(
        "tag:yaml.org,2002:null",
        re.compile(r"^(?:~|null|Null|NULL)$"),
        list("~nN"),
    )
    _StrictYAMLLoader.add_constructor("tag:yaml.org,2002:map", _construct_map)
    _StrictYAMLLoader.add_constructor("tag:yaml.org,2002:int", _construct_int)
    _StrictYAMLLoader.add_constructor("tag:yaml.org,2002:float", _construct_float)


def _thread_lock(path: Path) -> threading.Lock:
    key = str(path.resolve())
    with _THREAD_GUARD:
        lock = _THREAD_LOCKS.get(key)
        if lock is None:
            lock = threading.Lock()
            _THREAD_LOCKS[key] = lock
        return lock


_install_loader()
