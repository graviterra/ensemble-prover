"""Advisory use credit at the successful fresh-process export boundary.

The caller must be the live export process bridge. Historical summary flags or
export receipts never invoke this observer. Portable records additionally need
a controller-supplied live catalog authority; disk configuration cannot supply
one.
"""

from __future__ import annotations

import contextlib
import ctypes
import errno
import hashlib
import json
import os
import re
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

from .catalog import MemoryCatalog
from .config import MemoryConfig
from .evidence import EvidenceUnavailable, read_contained
from .model import (
    EligibilityPolicy,
    MemoryEvent,
    MemoryProvenance,
    canonical_json,
    content_digest,
    thaw,
)


@dataclass(frozen=True)
class ExportObserverContext:
    catalog: MemoryCatalog
    policy: EligibilityPolicy
    provenance_for_use: Callable[[MemoryEvent], MemoryProvenance | None] | None = None


ExportObserverFactory = Callable[
    [Path, MemoryConfig, EligibilityPolicy], ExportObserverContext
]
_factory: ExportObserverFactory | None = None


def configure_export_observer(factory: ExportObserverFactory | None) -> None:
    """Install an in-process controller authority, never a serialized callback."""
    global _factory
    if factory is not None and not callable(factory):
        raise TypeError("export observer factory must be callable")
    _factory = factory


def read_regular_file(path: Path, limit: int, deadline: float) -> bytes:
    """Read through anchored directory descriptors, rejecting special files."""
    path = Path(path).absolute()
    if time.monotonic() >= deadline:
        raise EvidenceUnavailable("deadline_exhausted")
    fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for component in path.parts[1:-1]:
            if time.monotonic() >= deadline:
                raise EvidenceUnavailable("deadline_exhausted")
            next_fd = os.open(
                component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd
            )
            os.close(fd)
            fd = next_fd
        return read_contained(fd, path.name, limit, deadline)
    finally:
        os.close(fd)


BINDING_NAME = "mathematical_memory_binding.json"


def persist_export_binding(run_dir: Path, catalog: MemoryCatalog) -> bool:
    """Pin this run to the first valid admitted catalog binding.

    Publication stages the complete bytes in a private temporary file and moves
    it onto the canonical name with a single atomic
    ``renameat2(RENAME_NOREPLACE)``. The move never replaces an existing
    destination and never creates a second link to the canonical inode, so an
    interrupted or concurrent publisher can neither truncate nor replace a
    binding that already exists, and no ambiguous two-name state needs to be
    reclaimed. When no-replace rename is unavailable the call fails closed
    rather than fall back to an overwriting ``os.replace``. A real crash can
    leave an orphaned unique staging file; it is deliberately never reclaimed
    by name or inode because no surviving process can prove ownership of it.
    """
    try:
        return _persist_export_binding(run_dir, catalog)
    except (OSError, ValueError, RuntimeError):
        return False


def _read_binding(directory: int, deadline: float) -> Any | None:
    """Return the parsed canonical binding, or None when the file is absent.

    Decoding errors surface instead of being repaired: a malformed canonical
    file cannot prove which catalog it belonged to, and replacing it would
    risk discarding a valid competing pin.
    """
    try:
        raw = read_contained(directory, BINDING_NAME, 65536, deadline)
    except FileNotFoundError:
        return None
    return json.loads(raw)


_RENAME_NOREPLACE = 1


def _rename_noreplace(src_fd: int, src: str, dst_fd: int, dst: str) -> bool:
    """Atomically rename ``src`` over ``dst`` only when ``dst`` does not exist.

    Returns True when the rename installed ``src`` as ``dst`` and False when
    ``dst`` already exists. Raises RuntimeError when the running kernel or libc
    cannot provide no-replace semantics: there is no portable rename that is
    both atomic and non-replacing, and falling back to ``os.replace`` could
    silently overwrite a competing pin.
    """
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = libc.renameat2
    except (AttributeError, OSError) as exc:
        raise RuntimeError("renameat2 unavailable") from exc
    renameat2.argtypes = [
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    result = renameat2(
        src_fd, os.fsencode(src), dst_fd, os.fsencode(dst), _RENAME_NOREPLACE
    )
    if result == 0:
        return True
    error_number = ctypes.get_errno()
    if error_number in (errno.EEXIST, errno.ENOTEMPTY):
        return False
    if error_number in (errno.ENOSYS, errno.EINVAL, errno.ENOTSUP):
        raise RuntimeError("renameat2 no-replace unsupported")
    raise OSError(error_number, os.strerror(error_number))


def _publish_binding(
    directory: int, raw: bytes, binding: Mapping[str, Any], deadline: float
) -> bool:
    """Install complete bytes atomically without clobbering a winning binding."""
    temporary = f"tmp-{uuid.uuid4().hex}"
    created = False
    try:
        handle = os.open(
            temporary,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o600,
            dir_fd=directory,
        )
        created = True
        try:
            remaining = memoryview(raw)
            while remaining:
                if time.monotonic() >= deadline:
                    raise EvidenceUnavailable("deadline_exhausted")
                count = os.write(handle, remaining)
                if count <= 0:
                    raise EvidenceUnavailable("write_failed")
                remaining = remaining[count:]
            os.fsync(handle)
        finally:
            os.close(handle)
        if not _rename_noreplace(directory, temporary, directory, BINDING_NAME):
            # A competing writer won the race. Its binding is authoritative and
            # is only read back for identity comparison, never rewritten. The
            # reader stays strict: a destination with extra links or a symlink
            # is rejected rather than repaired.
            return _read_binding(directory, deadline) == binding
        # The staged bytes were fsynced before the move, so the canonical name
        # now refers to a complete file. Syncing the directory makes the
        # rename durable; a crash before this cannot leave a partial file.
        os.fsync(directory)
        return True
    finally:
        # Remove only this call's own uniquely named staging file. A failed
        # exclusive open never created it, so a name collision or permission
        # error must not delete a pre-existing file that belongs to someone
        # else. A real crash can orphan this name, and it is deliberately never
        # reclaimed by name or inode because no surviving process can prove
        # ownership of it.
        if created:
            with contextlib.suppress(FileNotFoundError):
                os.unlink(temporary, dir_fd=directory)


def _persist_export_binding(run_dir: Path, catalog: MemoryCatalog) -> bool:
    """Pin the admitted catalog independently of mutable owner preferences.

    This protects against isolated owner replacement. Same-user replacement of
    both documents and database is outside local filesystem authentication.
    """
    from .evidence import contained_directory

    deadline = time.monotonic() + 0.05
    pin = catalog.generation(deadline_monotonic=deadline)
    binding = {
        "schema_version": 1,
        "run_id": str(Path(run_dir).absolute()),
        "catalog_root": str(catalog.root),
        "catalog_lineage": pin.lineage,
        "catalog_epoch": pin.epoch,
    }
    raw = canonical_json(binding).encode()
    with contained_directory(Path(run_dir)) as directory:
        existing = _read_binding(directory, deadline)
        if existing is not None:
            return existing == binding
        return _publish_binding(directory, raw, binding, deadline)


def _binding_matches(
    binding: Mapping[str, Any], catalog: MemoryCatalog, deadline: float
) -> bool:
    if binding.get("catalog_root") != str(catalog.root):
        return False
    pin = catalog.generation(deadline_monotonic=deadline)
    return (
        binding.get("catalog_lineage") == pin.lineage
        and binding.get("catalog_epoch") == pin.epoch
    )


def _context(run_dir: Path, deadline: float) -> ExportObserverContext | None:
    owner = json.loads(
        read_regular_file(run_dir / "mathematical_memory_owner.json", 65536, deadline)
    )
    if (
        not isinstance(owner, dict)
        or owner.get("schema_version") != 1
        or owner.get("request_owner") is not True
        or owner.get("run_id") not in {str(run_dir), str(run_dir.absolute())}
    ):
        return None
    binding = json.loads(
        read_regular_file(run_dir / "mathematical_memory_binding.json", 65536, deadline)
    )
    if (
        not isinstance(binding, dict)
        or binding.get("schema_version") != 1
        or binding.get("run_id") != str(run_dir.absolute())
    ):
        return None
    config = MemoryConfig.from_record(owner["mathematical_memory_config"])
    if binding.get("catalog_root") != config.root:
        return None
    if not config.enabled:
        return None
    policy = EligibilityPolicy.from_record(owner["mathematical_memory_policy"])
    if _factory is not None:
        context = _factory(run_dir, config, policy)
        if not isinstance(context, ExportObserverContext):
            raise TypeError("export observer requires a typed controller context")
        return context if _binding_matches(binding, context.catalog, deadline) else None
    # Without a live controller, only this run's incomplete local observations
    # may be read. Complete campaign/shared records stay fail closed.
    local_policy = EligibilityPolicy(
        visible_scopes=tuple(
            pair for pair in policy.visible_scopes if pair[0] == "session"
        ),
        allowed_source_record_ids=policy.allowed_source_record_ids,
        excluded_problem_ids=policy.excluded_problem_ids,
        excluded_family_ids=policy.excluded_family_ids,
        chronology_campaign_id=policy.chronology_campaign_id,
        chronology_cutoff=policy.chronology_cutoff,
        policy_version=policy.policy_version,
        allow_incomplete_session=policy.allow_incomplete_session,
    )
    catalog = MemoryCatalog(
        config.root,
        outbox_event_cap=config.outbox_event_cap,
        outbox_byte_cap=config.outbox_byte_cap,
        artifact_byte_cap=config.artifact_byte_cap,
        artifact_store_byte_cap=config.artifact_store_byte_cap,
        artifact_count_cap=config.artifact_count_cap,
        query_scan_cap=config.query_scan_cap,
        event_count_cap=config.event_count_cap,
        event_byte_cap=config.event_byte_cap,
        query_byte_cap=config.query_byte_cap,
    )
    return (
        ExportObserverContext(catalog, local_policy)
        if _binding_matches(binding, catalog, deadline)
        else None
    )


def observe_verified_export(run_dir: Path, fresh_result: Mapping[str, Any]) -> int:
    """Join a freshly verified export to existing exact accepted-root use.

    This is best effort and bounded to one second. The caller preserves ordinary
    export success even when memory or current source authority is unavailable.
    """
    if fresh_result.get("status") != "verified":
        return 0
    record = fresh_result.get("record")
    if not isinstance(record, Mapping):
        return 0
    source_digest = record.get("verified_source_digest")
    proof_hash = record.get("accepted_root_proof_hash")
    occurrence = record.get("export_occurrence_id")
    if (
        not isinstance(source_digest, str)
        or not re.fullmatch(r"[a-f0-9]{64}", source_digest)
        or not isinstance(proof_hash, str)
        or not re.fullmatch(r"[a-f0-9]{64}", proof_hash)
        or not isinstance(occurrence, str)
        or not re.fullmatch(r"[a-f0-9]{32}", occurrence)
    ):
        return 0
    deadline = time.monotonic() + 1.0
    run_dir = Path(run_dir)
    summary = json.loads(
        read_regular_file(run_dir / "summary.json", 2 * 1024 * 1024, deadline)
    )
    proof = summary.get("final_proof")
    if (
        not isinstance(proof, str)
        or hashlib.sha256(proof.strip().encode()).hexdigest() != proof_hash
    ):
        return 0
    output_path = Path(record.get("verified_output_path") or record["output_path"])
    if not output_path.is_absolute():
        output_path = Path(__file__).resolve().parents[2] / output_path
    source = read_regular_file(output_path, 2 * 1024 * 1024, deadline)
    if hashlib.sha256(source).hexdigest() != source_digest:
        return 0
    context = _context(run_dir, deadline)
    if context is None:
        return 0
    catalog, policy = context.catalog, context.policy
    view = catalog.query(
        policy, kind="use", limit=catalog.query_scan_cap, deadline_monotonic=deadline
    )
    observed = 0
    source_ref = None
    record_ref = None
    for prior in view.events:
        payload = prior.payload
        if (
            prior.provenance.run_id not in {str(run_dir), str(run_dir.absolute())}
            or payload.get("consumer_kind") != "root"
            or payload.get("proof_hash") != proof_hash
            or payload.get("usage") not in {"direct", "transitive"}
            or payload.get("root_export") is True
        ):
            continue
        # Quarantine, revocation, provenance and source evidence are rechecked
        # after the query, immediately before publishing this occurrence.
        if (
            catalog.get_event(prior.event_id, policy, deadline_monotonic=deadline)
            is None
        ):
            continue
        event_id = content_digest(
            {
                "export_use": prior.event_id,
                "source": source_digest,
                "proof": proof_hash,
                "occurrence": occurrence,
            }
        )
        if catalog.get_event(event_id, policy, deadline_monotonic=deadline) is not None:
            observed += 1
            continue
        if len(prior.evidence) > 61:
            continue
        provenance = (
            context.provenance_for_use(prior)
            if context.provenance_for_use is not None
            else prior.provenance
        )
        if provenance is None or (
            prior.provenance.complete and context.provenance_for_use is None
        ):
            continue
        if (
            provenance.source_record_ids != prior.provenance.source_record_ids
            or provenance.run_id != prior.provenance.run_id
            or not policy.permits(provenance)
        ):
            continue
        if source_ref is None:
            source_ref = catalog.put_artifact(
                source, kind="lean", deadline_monotonic=deadline
            )
            record_ref = catalog.put_artifact(
                canonical_json(dict(record)).encode(), deadline_monotonic=deadline
            )
        export_payload = {
            **thaw(payload),
            "root_export": True,
            "export_use_event_id": prior.event_id,
            "verified_source_digest": source_digest,
            "accepted_root_proof_hash": proof_hash,
            "export_record": dict(record),
        }
        payload_ref = catalog.put_artifact(
            canonical_json(export_payload).encode(), deadline_monotonic=deadline
        )
        event = MemoryEvent(
            event_id,
            prior.operation_id,
            prior.attempt_id,
            "use",
            export_payload,
            provenance,
            (*prior.evidence, source_ref, record_ref, payload_ref),
        )
        if (
            catalog.get_event(prior.event_id, policy, deadline_monotonic=deadline)
            is None
        ):
            continue
        result = catalog.append(
            event, deadline_monotonic=deadline, queue_on_failure=False
        )
        if result.status in {"stored", "duplicate"}:
            # Storing the session-local event is not by itself authority. The
            # owning live service must admit this exact id and payload digest,
            # and only when the referenced prior use was already admitted by a
            # live process for this catalog root. Restored or disk-only records
            # never populate that in-process admission map.
            try:
                from .service import admit_live_export_credit

                admit_live_export_credit(
                    catalog.root,
                    event,
                    prior_event_id=prior.event_id,
                    prior_payload_digest=prior.payload_digest,
                )
            except Exception:
                pass
            observed += 1
    return observed
