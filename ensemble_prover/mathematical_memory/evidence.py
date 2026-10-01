"""Authorized immutable evidence copies with descriptor-relative file access.

The registry is supplied by trusted runtime source adapters. Disk metadata and
browser identifiers cannot register a source or restore its permissions.
"""

from __future__ import annotations

import contextlib
import hashlib
import json
import os
import re
import stat
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterator


class EvidenceUnavailable(ValueError):
    """Evidence cannot safely be delivered under the current policy."""


def _deadline(deadline: float | None) -> None:
    if deadline is not None and time.monotonic() >= deadline:
        raise EvidenceUnavailable("deadline_exhausted")


@contextlib.contextmanager
def contained_directory(
    root: Path,
    child: str | None = None,
    *,
    create: bool = False,
    create_parents: bool = False,
) -> Iterator[int]:
    """Anchor all operations in opened directories, refusing symlink components."""
    if child is not None and not re.fullmatch(r"[a-z_]+", child):
        raise EvidenceUnavailable("invalid_directory")
    path = Path(root).absolute()
    fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in path.parts[1:]:
            if create_parents:
                try:
                    os.mkdir(part, 0o700, dir_fd=fd)
                    os.fsync(fd)
                except FileExistsError:
                    pass
            next_fd = os.open(
                part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd
            )
            os.close(fd)
            fd = next_fd
        if child is None:
            yield fd
            return
        if create:
            try:
                os.mkdir(child, 0o700, dir_fd=fd)
                os.fsync(fd)
            except FileExistsError:
                pass
        next_fd = os.open(
            child, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd
        )
        os.close(fd)
        fd = next_fd
        yield fd
    finally:
        os.close(fd)


def read_contained(
    fd: int, name: str, limit: int, deadline: float | None = None
) -> bytes:
    if not re.fullmatch(r"[a-zA-Z0-9_.-]+", name) or name in {".", ".."}:
        raise EvidenceUnavailable("invalid_artifact")
    _deadline(deadline)
    handle = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
    try:
        info = os.fstat(handle)
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit or info.st_nlink != 1:
            raise EvidenceUnavailable("invalid_artifact")
        chunks: list[bytes] = []
        remaining = limit + 1
        while remaining:
            _deadline(deadline)
            chunk = os.read(handle, min(65536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        data = b"".join(chunks)
        if len(data) > limit:
            raise EvidenceUnavailable("byte_limit")
        return data
    finally:
        os.close(handle)


def write_contained(
    fd: int, name: str, data: bytes, deadline: float | None = None
) -> None:
    if not re.fullmatch(r"[a-zA-Z0-9_.-]+", name) or name in {".", ".."}:
        raise EvidenceUnavailable("invalid_artifact")
    _deadline(deadline)
    temporary = f"tmp-{uuid.uuid4().hex}"
    handle = os.open(
        temporary,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
        0o600,
        dir_fd=fd,
    )
    try:
        remaining = memoryview(data)
        while remaining:
            _deadline(deadline)
            count = os.write(handle, remaining[:65536])
            if count <= 0:
                raise EvidenceUnavailable("write_failed")
            remaining = remaining[count:]
        os.fsync(handle)
        _deadline(deadline)
        os.replace(temporary, name, src_dir_fd=fd, dst_dir_fd=fd)
        os.fsync(fd)
    finally:
        os.close(handle)
        with contextlib.suppress(FileNotFoundError):
            os.unlink(temporary, dir_fd=fd)


@dataclass(frozen=True)
class EvidenceSource:
    reader: Callable[[int, float | None], bytes]
    provenance: Any
    validator: Callable[[Any, Any], bool]
    reconciled: Callable[[], bool]
    digest: str
    size: int
    store_id: str
    consumer_id: str = ""
    complete: bool = True


class EvidenceRegistry:
    def __init__(self) -> None:
        self._sources: dict[str, EvidenceSource] = {}

    def register(self, evidence_id: str, source: EvidenceSource) -> None:
        if not re.fullmatch(r"[a-zA-Z0-9_-]{1,128}", evidence_id):
            raise ValueError("invalid evidence identity")
        if (
            not re.fullmatch(r"[a-f0-9]{64}", source.digest)
            or type(source.size) is not int
            or source.size < 0
        ):
            raise ValueError("invalid evidence reference")
        existing = self._sources.get(evidence_id)
        if existing is not None and existing != source:
            raise ValueError("evidence identity conflict")
        self._sources[evidence_id] = source

    def resolve(self, evidence_id: str, policy: Any) -> EvidenceSource:
        if not isinstance(evidence_id, str) or not re.fullmatch(
            r"[a-zA-Z0-9_-]{1,128}", evidence_id
        ):
            raise EvidenceUnavailable("invalid_evidence_id")
        source = self._sources.get(evidence_id)
        if source is None:
            raise EvidenceUnavailable("unregistered_evidence")
        try:
            allowed = (
                source.complete
                and source.reconciled() is True
                and source.validator(source.provenance, policy) is True
            )
        except Exception as exc:
            raise EvidenceUnavailable("eligibility_unavailable") from exc
        if not allowed:
            raise EvidenceUnavailable("evidence_ineligible")
        return source


class MaterializedEvidenceStore:
    def __init__(self, run_dir: Path, registry: EvidenceRegistry) -> None:
        self.run_dir = Path(run_dir)
        self.registry = registry

    @staticmethod
    def _policy_id(policy: Any) -> str:
        value = policy.to_record() if hasattr(policy, "to_record") else policy
        return hashlib.sha256(
            json.dumps(
                value, sort_keys=True, separators=(",", ":"), default=str
            ).encode()
        ).hexdigest()

    def materialize(
        self,
        evidence_id: str,
        policy: Any,
        *,
        max_bytes: int = 2_000_000,
        max_count: int = 128,
        deadline_monotonic: float | None = None,
    ) -> dict[str, Any]:
        _deadline(deadline_monotonic)
        source = self.registry.resolve(evidence_id, policy)
        if source.size > max_bytes or max_count <= 0:
            raise EvidenceUnavailable("byte_or_count_limit")
        data = source.reader(max_bytes, deadline_monotonic)
        _deadline(deadline_monotonic)
        if (
            not isinstance(data, bytes)
            or len(data) != source.size
            or hashlib.sha256(data).hexdigest() != source.digest
        ):
            raise EvidenceUnavailable("source_integrity")
        # Revalidate after a potentially slow source read, before publication.
        self.registry.resolve(evidence_id, policy)
        provenance = (
            source.provenance.to_record()
            if hasattr(source.provenance, "to_record")
            else source.provenance
        )
        binding = {
            "schema_version": 1,
            "evidence_id": evidence_id,
            "digest": source.digest,
            "source_digest": source.digest,
            "size": source.size,
            "store_id": source.store_id,
            "consumer_id": source.consumer_id,
            "provenance": provenance,
            "policy_id": self._policy_id(policy),
            "complete": True,
            "destination_run": str(self.run_dir.absolute()),
        }
        artifact_id = hashlib.sha256(
            json.dumps(
                binding, sort_keys=True, separators=(",", ":"), default=str
            ).encode()
        ).hexdigest()
        binding["artifact_id"] = artifact_id
        with contained_directory(self.run_dir, "memory_evidence", create=True) as fd:
            import fcntl

            lock = os.open(
                "lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600, dir_fd=fd
            )
            try:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError as exc:
                    raise EvidenceUnavailable("store_busy") from exc
                names = os.listdir(fd)
                occupied = {
                    name.rsplit(".", 1)[0]
                    for name in names
                    if name.endswith((".json", ".blob"))
                }
                if artifact_id not in occupied and len(occupied) >= max_count:
                    raise EvidenceUnavailable("count_limit")
                try:
                    write_contained(fd, f"{artifact_id}.blob", data, deadline_monotonic)
                    write_contained(
                        fd,
                        f"{artifact_id}.json",
                        json.dumps(binding, sort_keys=True, default=str).encode(),
                        deadline_monotonic,
                    )
                except BaseException:
                    # A power loss can still leave an orphan, which counts
                    # against the cap. Normal failures remove newly made blobs
                    # under this same descriptor and lock, without extra time.
                    if (
                        f"{artifact_id}.blob" not in names
                        and f"{artifact_id}.json" not in os.listdir(fd)
                    ):
                        with contextlib.suppress(FileNotFoundError):
                            os.unlink(f"{artifact_id}.blob", dir_fd=fd)
                            os.fsync(fd)
                    raise
            finally:
                os.close(lock)
        return binding

    def read(
        self,
        artifact_id: str,
        policy: Any,
        *,
        max_bytes: int = 2_000_000,
        deadline_monotonic: float | None = None,
    ) -> tuple[dict[str, Any], bytes]:
        if not re.fullmatch(r"[a-f0-9]{64}", artifact_id):
            raise EvidenceUnavailable("invalid_artifact_id")
        with contained_directory(self.run_dir, "memory_evidence") as fd:
            binding = json.loads(
                read_contained(fd, f"{artifact_id}.json", 65536, deadline_monotonic)
            )
            if not isinstance(binding, dict):
                raise EvidenceUnavailable("invalid_binding")
            if binding.get("artifact_id") != artifact_id or binding.get(
                "destination_run"
            ) != str(self.run_dir.absolute()):
                raise EvidenceUnavailable("binding_mismatch")
            source = self.registry.resolve(binding.get("evidence_id", ""), policy)
            provenance = (
                source.provenance.to_record()
                if hasattr(source.provenance, "to_record")
                else source.provenance
            )
            if (
                binding.get("digest") != source.digest
                or binding.get("size") != source.size
                or binding.get("provenance") != provenance
                or binding.get("store_id") != source.store_id
                or binding.get("consumer_id") != source.consumer_id
                or binding.get("complete") is not True
            ):
                raise EvidenceUnavailable("source_binding_mismatch")
            data = read_contained(
                fd, f"{artifact_id}.blob", max_bytes, deadline_monotonic
            )
            if (
                len(data) != source.size
                or hashlib.sha256(data).hexdigest() != source.digest
            ):
                raise EvidenceUnavailable("copy_integrity")
            self.registry.resolve(binding["evidence_id"], policy)
            return binding, data
