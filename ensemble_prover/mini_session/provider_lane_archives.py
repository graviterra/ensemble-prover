"""Content-addressed storage for immutable parked provider payloads.

Only the attempt registry owns archive references. Runtime actions and exported
session records receive complete inert envelopes, with live authority checked
independently when a lane is activated. Ordinary checkpoint metadata and each
archive retain their existing storage bounds; cold bodies are never expanded
together to apply an additional aggregate provider limit.
"""

from __future__ import annotations

import hashlib
import os
import stat
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Iterator

from ensemble_prover.snapshot_codec import snapshot_bytes
from ensemble_prover.state_data import clone_json_value

from .durable_checkpoint import read_checkpoint_record, write_checkpoint_record
from .provider_lane_bank import copy_provider_envelope, decode_provider_lane
from .state_codec import StateSnapshotCompatibilityError


ARCHIVE_ENCODING = "provider-lane-archive-v1"
_ENVELOPE_KEYS = {"encoding", "sha256", "expanded_bytes", "header", "data"}


def _digest(value: Any) -> str:
    return hashlib.sha256(snapshot_bytes(value)).hexdigest()


def _is_digest(value: Any) -> bool:
    return (type(value) is str and len(value) == 64
            and all(character in "0123456789abcdef" for character in value))


def _banks(record: Any) -> Iterator[dict[str, Any]]:
    """Visit the explicit action-state field, never arbitrary matching text."""
    if type(record) is not dict:
        return
    scheduler = record.get("scheduler")
    if type(scheduler) is not dict:
        return
    actions = scheduler.get("action_runtime_states")
    if type(actions) is not dict:
        return
    for runtime in actions.values():
        state = runtime.get("state") if type(runtime) is dict else None
        if type(state) is not dict or "provider_quantum_parked" not in state:
            continue
        bank = state["provider_quantum_parked"]
        if type(bank) is not dict:
            raise ValueError("Invalid provider archive bank")
        yield bank


def session_has_provider_archives(record: Any) -> bool:
    return any(type(value) is dict and value.get("encoding") == ARCHIVE_ENCODING
               for bank in _banks(record) for value in bank.values())


def provider_archive_references(record: Any) -> Iterator[tuple[str, str]]:
    """Validate reference shapes without reading or admitting any payload."""
    for bank in _banks(record):
        for lane_id, envelope in bank.items():
            if type(envelope) is dict and envelope.get("encoding") == ARCHIVE_ENCODING:
                yield lane_id, ProviderLaneArchiveStore._reference_digest(lane_id, envelope)


def _checkpoint_shape(checkpoint: Any) -> dict[str, Any]:
    # The action's validator later establishes the complete runtime contract.
    # Storage only admits the exact inert container needed by the shared codec.
    if (type(checkpoint) is not dict or set(checkpoint) != {"state", "history", "binding"}
            or type(checkpoint["state"]) is not dict
            or type(checkpoint["history"]) is not list
            or type(checkpoint["binding"]) is not dict):
        raise ValueError("Invalid provider archive checkpoint")
    return checkpoint


class ProviderLaneArchiveStore:
    """Archive once per immutable envelope and hydrate at recovery boundaries."""

    def __init__(self, registry_root: Path, *,
                 write_record: Callable[[Path, dict[str, Any]], None] | None = None) -> None:
        self.directory = Path(registry_root) / "provider_lanes"
        self._directory_identity: tuple[int, int] | None = None
        self._registry_identity: tuple[int, int] | None = None
        self._write = write_record or write_checkpoint_record
        self._archives: dict[str, dict[str, Any]] = {}
        self._committed_references: set[tuple[str, str]] = set()
        self._created_archives: set[str] = set()
        # Holding the immutable string prevents id reuse. Cloning ordinary
        # session snapshots preserves this string object, so metadata-only
        # commits need neither payload hashing nor decompression.
        self._inline: dict[int, tuple[str, dict[str, Any], str]] = {}

    @contextmanager
    def _owned_directory(self, *, create: bool = False) -> Iterator[int]:
        """Pin archive IO to a real child directory, including during replacement.

        The registry root may itself be a configured symlink. Its archive
        child cannot redirect reads, writes or collection to another owner.
        Linux descriptor paths also keep an injected writer inside the opened
        child if its pathname is replaced while a durable write is in progress.
        Missing /proc descriptor access is an IO error, never an unsafe fallback.
        """
        if create:
            self.directory.parent.mkdir(parents=True, exist_ok=True)
        registry_fd = os.open(self.directory.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        directory_fd = None
        try:
            registry_stat = os.fstat(registry_fd)
            registry_identity = (registry_stat.st_dev, registry_stat.st_ino)
            if self._registry_identity not in {None, registry_identity}:
                raise ValueError("Provider archive registry directory was replaced")
            flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
            try:
                directory_fd = os.open("provider_lanes", flags, dir_fd=registry_fd)
            except FileNotFoundError:
                if not create:
                    raise
                os.mkdir("provider_lanes", mode=0o700, dir_fd=registry_fd)
                os.fsync(registry_fd)
                directory_fd = os.open("provider_lanes", flags, dir_fd=registry_fd)
            except OSError as error:
                raise ValueError("Missing or invalid provider archive directory") from error
            directory_stat = os.fstat(directory_fd)
            directory_identity = (directory_stat.st_dev, directory_stat.st_ino)
            if self._directory_identity not in {None, directory_identity}:
                raise ValueError("Provider archive directory was replaced")
            self._registry_identity = registry_identity
            self._directory_identity = directory_identity
            yield directory_fd
            current = os.stat("provider_lanes", dir_fd=registry_fd, follow_symlinks=False)
            current_registry = self.directory.parent.stat()
            if (
                not stat.S_ISDIR(current.st_mode)
                or (current.st_dev, current.st_ino) != directory_identity
                or (current_registry.st_dev, current_registry.st_ino) != registry_identity
            ):
                raise ValueError("Provider archive directory was replaced during IO")
        finally:
            if directory_fd is not None:
                os.close(directory_fd)
            os.close(registry_fd)

    def _check_directory(self) -> None:
        # Committed references remain cold even if their files are missing.
        # Reject redirects without forcing an archive read during publication.
        try:
            with self._owned_directory():
                pass
        except FileNotFoundError:
            if self._directory_identity is not None:
                raise ValueError("Provider archive directory disappeared") from None

    @staticmethod
    def _metadata(lane_id: str, envelope: Any) -> dict[str, Any]:
        if (not _is_digest(lane_id) or type(envelope) is not dict
                or set(envelope) != _ENVELOPE_KEYS
                or envelope["encoding"] != "json-zlib-v1"
                or not _is_digest(envelope["sha256"])
                or type(envelope["expanded_bytes"]) is not int
                or envelope["expanded_bytes"] < 0
                or type(envelope["data"]) is not str
                or type(envelope["header"]) is not dict
                or set(envelope["header"]) not in (
                    {"lane_id", "binding", "context_identity"},
                    {"lane_id", "binding", "context_identity", "has_pending_tool_replay"},
                )
                or ("has_pending_tool_replay" in envelope["header"]
                    and type(envelope["header"]["has_pending_tool_replay"]) is not bool)
                or envelope["header"]["lane_id"] != lane_id):
            raise ValueError("Invalid provider archive envelope")
        return clone_json_value(
            {key: value for key, value in envelope.items() if key != "data"},
            label="provider archive metadata",
        )

    def _admit(self, lane_id: str, envelope: Any) -> dict[str, Any]:
        self._metadata(lane_id, envelope)
        try:
            decode_provider_lane(lane_id, envelope, _checkpoint_shape)
        except StateSnapshotCompatibilityError as error:
            raise ValueError("Invalid provider archive payload") from error
        return copy_provider_envelope(envelope)

    def _remember(self, digest: str, envelope: dict[str, Any]) -> None:
        previous = self._archives.get(digest)
        if previous is not None:
            self._inline.pop(id(previous["data"]), None)
        clean = copy_provider_envelope(envelope)
        self._archives[digest] = clean
        metadata = self._metadata(clean["header"]["lane_id"], clean)
        self._inline[id(clean["data"])] = (clean["data"], metadata, digest)

    @staticmethod
    def _reference_digest(lane_id: str, reference: Any) -> str:
        if (not _is_digest(lane_id) or type(reference) is not dict
                or set(reference) != {"encoding", "sha256"}
                or reference["encoding"] != ARCHIVE_ENCODING
                or not _is_digest(reference["sha256"])):
            raise ValueError("Invalid provider archive reference")
        return reference["sha256"]

    def _load(self, lane_id: str, reference: Any) -> dict[str, Any]:
        digest = self._reference_digest(lane_id, reference)
        self._check_directory()
        cached = self._archives.get(digest)
        if cached is not None:
            if cached["header"]["lane_id"] != lane_id:
                raise ValueError("Provider archive belongs to another lane")
            return cached
        try:
            with self._owned_directory() as directory_fd:
                file_fd = os.open(
                    f"{digest}.json", os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW | os.O_CLOEXEC,
                    dir_fd=directory_fd,
                )
                try:
                    if not stat.S_ISREG(os.fstat(file_fd).st_mode):
                        raise ValueError("Missing or invalid provider archive file")
                    envelope = read_checkpoint_record(Path(f"/proc/self/fd/{file_fd}"))
                finally:
                    os.close(file_fd)
        except OSError as error:
            raise ValueError("Missing or invalid provider archive file") from error
        if _digest(envelope) != digest:
            raise ValueError("Provider archive hash mismatch")
        clean = self._admit(lane_id, envelope)
        self._remember(digest, clean)
        return self._archives[digest]

    def _archive(self, lane_id: str, envelope: Any) -> dict[str, str]:
        self._check_directory()
        if type(envelope) is dict and envelope.get("encoding") == ARCHIVE_ENCODING:
            digest = self._reference_digest(lane_id, envelope)
            if (lane_id, digest) not in self._committed_references:
                self._load(lane_id, envelope)
            return dict(envelope)
        metadata = self._metadata(lane_id, envelope)
        cached = self._inline.get(id(envelope["data"]))
        if (cached is not None and cached[0] is envelope["data"]
                and cached[1] == metadata):
            return {"encoding": ARCHIVE_ENCODING, "sha256": cached[2]}
        clean = self._admit(lane_id, envelope)
        digest = _digest(clean)
        if digest not in self._archives:
            # Existing files may be unacknowledged orphans after failed fsync.
            # Publish them again unless this writer verified a committed ref
            # or received its own complete durable write acknowledgement.
            with self._owned_directory(create=True) as directory_fd:
                path = Path(f"/proc/self/fd/{directory_fd}") / f"{digest}.json"
                existed = path.exists() or path.is_symlink()
                self._write(path, clean)
            if not existed:
                self._created_archives.add(digest)
        self._remember(digest, clean)
        return {"encoding": ARCHIVE_ENCODING, "sha256": digest}

    def compact_session(self, record: dict[str, Any]) -> dict[str, Any]:
        result = clone_json_value(record, label="archived provider session")
        for bank in _banks(result):
            for lane_id, envelope in tuple(bank.items()):
                bank[lane_id] = self._archive(lane_id, envelope)
        return result

    def validate_session(self, record: dict[str, Any]) -> None:
        """Admit reference shapes from an authenticated committed snapshot.

        The body remains cold until its session is requested. This does not
        grant runtime authority: hydration still checks the complete file and
        the action independently authenticates its execution context.
        """
        self._committed_references.update(provider_archive_references(record))

    def hydrate_session(self, record: dict[str, Any]) -> dict[str, Any]:
        """Return portable inert data; actions never receive archive handles."""
        result = clone_json_value(record, label="hydrated provider session")
        for bank in _banks(result):
            for lane_id, envelope in tuple(bank.items()):
                if type(envelope) is dict and envelope.get("encoding") == ARCHIVE_ENCODING:
                    bank[lane_id] = copy_provider_envelope(self._load(lane_id, envelope))
        return result

    def retain_sessions(self, sessions: dict[str, Any]) -> set[str]:
        """Release cached bytes after lanes retire, preserving archive files."""
        retained = {
            (lane_id, self._reference_digest(lane_id, reference))
            for session in sessions.values() for bank in _banks(session)
            for lane_id, reference in bank.items()
            if type(reference) is dict and reference.get("encoding") == ARCHIVE_ENCODING
        }
        digests = {digest for _lane, digest in retained}
        for digest in set(self._archives) - digests:
            previous = self._archives.pop(digest)
            self._inline.pop(id(previous["data"]), None)
        self._committed_references.intersection_update(retained)
        return digests

    def collect_unreferenced(self, retained_digests: set[str]) -> None:
        """Reclaim only this writer's new files after their snapshots retire.

        Preexisting archives can belong to older generation manifests and are
        never candidates. Unlink failures remain candidates for a later
        successful publication; optional cleanup cannot invalidate a commit.
        """
        candidates = self._created_archives - retained_digests
        if not candidates:
            return
        try:
            with self._owned_directory() as directory_fd:
                for digest in candidates:
                    try:
                        os.unlink(f"{digest}.json", dir_fd=directory_fd)
                    except FileNotFoundError:
                        pass
                    except OSError:
                        continue
                    self._created_archives.discard(digest)
        except (OSError, ValueError):
            # Optional cleanup cannot invalidate an otherwise durable commit.
            return
