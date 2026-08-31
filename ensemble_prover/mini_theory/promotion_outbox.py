"""Crash-safe, fail-open staging for verified-helper theory promotion.

The proof search side of this module only writes a small immutable receipt.
Independent Lean compilation happens later, after proof-result selection.  A
receipt is content addressed and remains retryable across cancellation,
process loss, and dependency races.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import threading
import time
import uuid
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Callable, Iterator, Mapping, Optional, Sequence

from ..proof_dossier import VerifiedHelper, text_hash
from .model import THEORY_POLICY_VERSION, TheoryBundleCandidate


PROMOTION_OUTBOX_SCHEMA_VERSION = 2
_SUPPORTED_PROMOTION_OUTBOX_SCHEMA_VERSIONS = frozenset({1, 2})
PROMOTION_RESULT_POLICY_VERSION = 3
_HEX_32_RE = re.compile(r"^[0-9a-f]{32}$")
_HEX_64_RE = re.compile(r"^[0-9a-f]{64}$")
_NON_GENERIC_QUALITY_TAGS = frozenset(
    {
        "hollow_root_reducer",
        "negative_evidence_helper",
        "root_equivalent_helper",
        "structurally_vacuous_helper",
        "requires_unproved_premise",
    }
)
_NON_GENERIC_PROVENANCE_TAGS = frozenset(
    {
        "root_authoritative_helper",
        "root_exact_certificate",
        "root_finalization_certificate",
    }
)


def _canonical_json(payload: Mapping[str, Any]) -> str:
    return json.dumps(
        dict(payload),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )


def _sha256(payload: str | bytes) -> str:
    raw = payload.encode("utf-8") if isinstance(payload, str) else bytes(payload)
    return hashlib.sha256(raw).hexdigest()


def helper_is_promotable(helper: Any) -> tuple[bool, str]:
    """Return whether a dossier helper is generic reusable theory material."""

    name = str(getattr(helper, "name", "") or "").strip()
    source = str(getattr(helper, "source", "") or "").strip()
    if not name or not source:
        return False, "missing_helper_identity"
    render_policy = str(getattr(helper, "render_policy", "") or "").strip()
    if render_policy:
        return False, f"non_generic_render_policy:{render_policy}"
    quality_tags = {
        str(item or "").strip()
        for item in list(getattr(helper, "quality_tags", []) or ())
        if str(item or "").strip()
    }
    blocked_quality = sorted(quality_tags & _NON_GENERIC_QUALITY_TAGS)
    if blocked_quality:
        return False, "non_generic_quality:" + ",".join(blocked_quality)
    provenance_tags = {
        str(item or "").strip()
        for item in list(getattr(helper, "provenance_tags", []) or ())
        if str(item or "").strip()
    }
    blocked_provenance = sorted(
        provenance_tags & _NON_GENERIC_PROVENANCE_TAGS
    )
    if blocked_provenance:
        return False, "non_generic_provenance:" + ",".join(blocked_provenance)
    return True, "generic_verified_helper"


@dataclass(frozen=True)
class PromotionDependencyReceipt:
    helper_name: str
    source_hash: str
    source_sha256: str = ""
    source: str = ""

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "PromotionDependencyReceipt":
        return cls(
            helper_name=str(payload.get("helper_name") or "").strip(),
            source_hash=str(payload.get("source_hash") or "").strip(),
            source_sha256=str(payload.get("source_sha256") or "").strip(),
            source=str(payload.get("source") or ""),
        )


@dataclass(frozen=True)
class PromotionOutboxEntry:
    schema_version: int
    entry_id: str
    receipt_sha256: str
    helper_name: str
    source: str
    source_hash: str
    source_sha256: str
    support_receipts: tuple[PromotionDependencyReceipt, ...]
    domain: str
    imports: tuple[str, ...]
    owner_id: str
    origin_environment_key: str
    generated_by_run: str = ""
    generated_by_model: str = ""
    source_theorem: str = ""
    forbidden_problem_constants: tuple[str, ...] = ()
    policy_version: int = THEORY_POLICY_VERSION
    created_ts: float = 0.0
    workspace_id: str = ""
    supersedes_entry_id: str = ""

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "PromotionOutboxEntry":
        return cls(
            schema_version=int(payload.get("schema_version") or 0),
            entry_id=str(payload.get("entry_id") or "").strip(),
            receipt_sha256=str(payload.get("receipt_sha256") or "").strip(),
            helper_name=str(payload.get("helper_name") or "").strip(),
            source=str(payload.get("source") or ""),
            source_hash=str(payload.get("source_hash") or "").strip(),
            source_sha256=str(payload.get("source_sha256") or "").strip(),
            support_receipts=tuple(
                PromotionDependencyReceipt.from_dict(item)
                for item in list(payload.get("support_receipts") or ())
                if isinstance(item, Mapping)
            ),
            domain=str(payload.get("domain") or "").strip(),
            imports=tuple(
                str(item or "").strip()
                for item in list(payload.get("imports") or ())
                if str(item or "").strip()
            ),
            owner_id=str(payload.get("owner_id") or "").strip(),
            origin_environment_key=str(
                payload.get("origin_environment_key") or ""
            ).strip(),
            generated_by_run=str(payload.get("generated_by_run") or "").strip(),
            generated_by_model=str(payload.get("generated_by_model") or "").strip(),
            source_theorem=str(payload.get("source_theorem") or "").strip(),
            forbidden_problem_constants=tuple(
                str(item or "").strip()
                for item in list(payload.get("forbidden_problem_constants") or ())
                if str(item or "").strip()
            ),
            policy_version=int(payload.get("policy_version") or 0),
            created_ts=float(payload.get("created_ts") or 0.0),
            workspace_id=str(payload.get("workspace_id") or "").strip(),
            supersedes_entry_id=str(
                payload.get("supersedes_entry_id") or ""
            ).strip(),
        )

    def content_identity_payload(self) -> dict[str, Any]:
        payload = asdict(self)
        excluded = [
            "entry_id",
            "receipt_sha256",
            "created_ts",
            "origin_environment_key",
            "generated_by_run",
            "generated_by_model",
            "source_theorem",
        ]
        # Schema 1 deduplicated identical content across producer owners.
        # Schema 2 isolates owners so a completed run can be prioritized
        # without stealing or starving a duplicate receipt from a live run.
        if self.schema_version <= 1:
            excluded.append("owner_id")
            excluded.append("workspace_id")
            excluded.append("supersedes_entry_id")
        for key in excluded:
            payload.pop(key, None)
        return payload

    def receipt_payload(self) -> dict[str, Any]:
        payload = asdict(self)
        payload.pop("receipt_sha256", None)
        if self.schema_version <= 1:
            payload.pop("workspace_id", None)
            payload.pop("supersedes_entry_id", None)
        return payload


@dataclass(frozen=True)
class PromotionEnqueueResult:
    staged: bool
    entry_id: str = ""
    path: Path = Path()
    diagnostic: str = ""
    error_kind: str = ""
    error: str = ""


@dataclass
class PromotionDrainReport:
    attempted: int = 0
    published: int = 0
    rejected: int = 0
    deferred: int = 0
    skipped_live_owner: int = 0
    skipped_claimed: int = 0
    failures: int = 0
    retryable: int = 0
    recovered_claims: int = 0
    remaining: int = 0
    events: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["pending"] = max(
            self.remaining,
            self.deferred
            + self.skipped_live_owner
            + self.skipped_claimed
            + self.failures
            + self.retryable,
        )
        return payload


@dataclass
class _ResultValidationContext:
    """Invocation-scoped immutable indexes plus recursive-result memoization."""

    entries_by_id: dict[str, PromotionOutboxEntry]
    authoritative_ids: set[str]
    providers_by_identity: dict[
        tuple[str, str, str], tuple[PromotionOutboxEntry, ...]
    ]
    authority_owner_ids_by_entry: dict[str, frozenset[str]]
    cancellation_event: Any = None
    result_memo: dict[str, Optional[dict[str, Any]]] = field(default_factory=dict)
    visiting: set[str] = field(default_factory=set)


class PromotionOutbox:
    """Configured-root inbox whose entries can be reverified in any environment."""

    def __init__(self, library: Any) -> None:
        if str(getattr(library, "mode", "off") or "off") != "build":
            raise ValueError("promotion outbox requires Mini theory build mode")
        self.library = library
        raw_configured_root = getattr(library, "root", None)
        if raw_configured_root is None:
            store = getattr(library, "store", None)
            raw_configured_root = getattr(store, "root", None)
        if raw_configured_root is None:
            raise ValueError("promotion outbox requires a persistent theory root")
        configured_root = Path(raw_configured_root)
        configured_root = configured_root.expanduser().resolve()
        self.configured_root = configured_root
        self.root = configured_root / "promotion_inbox"
        self.entries_root = self.root / "entries"
        self.claims_root = self.root / "claims"
        self.results_root = self.root / "results"
        self.authorities_root = self.root / "authorities"
        self.environment_key = str(
            getattr(library, "environment_key", "") or _sha256(str(configured_root))[:16]
        )
        self.policy_version = int(
            getattr(library, "policy_version", THEORY_POLICY_VERSION)
            or THEORY_POLICY_VERSION
        )
        self.result_scope = (
            f"E_{self.environment_key}_P_{self.policy_version}"
            f"_R_{PROMOTION_RESULT_POLICY_VERSION}"
        )
        self._attested_bundle_cache: Optional[dict[str, Any]] = None
        self._legacy_schema2_lineage_index: Optional[
            dict[tuple[str, str, str, str], tuple[PromotionOutboxEntry, ...]]
        ] = None
        self._equivalent_work_index: Optional[
            dict[tuple[Any, ...], tuple[PromotionOutboxEntry, ...]]
        ] = None
        self._equivalent_work_entries_generation: Optional[
            tuple[int, int, int, int]
        ] = None
        self._active_authority_index: Optional[
            dict[str, tuple[dict[str, Any], ...]]
        ] = None
        self._active_authority_index_generation: Optional[
            tuple[int, int]
        ] = None

    def enqueue(
        self,
        helper: Any,
        *,
        domain: str,
        imports: Sequence[str],
        owner_id: str,
        generated_by_run: str = "",
        generated_by_model: str = "",
        source_theorem: str = "",
        forbidden_problem_constants: Sequence[str] = (),
        helper_lookup: Optional[Mapping[str, Any]] = None,
        workspace_id: str = "",
    ) -> PromotionEnqueueResult:
        """Persist one immutable receipt; ordinary I/O errors are fail-open."""

        eligible, diagnostic = helper_is_promotable(helper)
        if not eligible:
            try:
                revoked = self.revoke(
                    str(getattr(helper, "name", "") or "").strip(),
                    owner_id=owner_id,
                    workspace_id=workspace_id,
                    reason=diagnostic,
                )
            except Exception as exc:
                return PromotionEnqueueResult(
                    False,
                    diagnostic="promotion_receipt_persistence_failed",
                    error_kind=type(exc).__name__,
                    error=str(exc),
                )
            if not revoked and str(getattr(helper, "name", "") or "").strip():
                return PromotionEnqueueResult(
                    False,
                    diagnostic="promotion_receipt_persistence_failed",
                    error_kind="ValueError",
                    error="invalid promotion authority owner",
                )
            return PromotionEnqueueResult(False, diagnostic=diagnostic)
        try:
            name = str(getattr(helper, "name", "") or "").strip()
            workspace = str(workspace_id or owner_id).strip()
            with self._lock():
                # Durable authority, not process-local cache state, orders
                # replacements.  Holding the shared lock through the receipt
                # and authority writes also prevents a second outbox instance
                # or a concurrent drain from observing a half-committed
                # successful enqueue.
                authority = self._read_authority(
                    helper_name=name,
                    owner_id=str(owner_id),
                    workspace_id=workspace,
                    origin_environment_key=self.environment_key,
                )
                active = None
                if authority is not None and authority.get("promotable"):
                    try:
                        active = self._read_entry(
                            self._schema2_entry_path_for_id(
                                helper_name=name,
                                owner_id=str(owner_id),
                                workspace_id=workspace,
                                origin_environment_key=self.environment_key,
                                entry_id=str(
                                    authority.get("active_entry_id") or ""
                                ),
                            )
                        )
                    except (OSError, ValueError, json.JSONDecodeError):
                        active = None
                authority_path = self._authority_path(
                    helper_name=name,
                    owner_id=str(owner_id),
                    workspace_id=workspace,
                    origin_environment_key=self.environment_key,
                )
                if active is None and not os.path.lexists(authority_path):
                    current_lineage = self._schema2_lineage_entries(
                        helper_name=name,
                        owner_id=str(owner_id),
                        workspace_id=workspace,
                        origin_environment_key=self.environment_key,
                    )
                    # Schema-2 receipts written before lineage-prefixed names
                    # are adopted once on upgrade.  Do not mistake a durable
                    # implicit baseline for a brand-new lineage merely because
                    # its filename uses the earlier content-addressed layout.
                    lineage = current_lineage
                    if not lineage:
                        lineage = self._legacy_schema2_lineage_entries(
                            helper_name=name,
                            owner_id=str(owner_id),
                            workspace_id=workspace,
                            origin_environment_key=self.environment_key,
                        )
                    authoritative = self._authoritative_entry_ids(
                        lineage,
                        lock_held=True,
                    )
                    active = next(
                        (
                            item
                            for item in lineage
                            if item.entry_id in authoritative
                        ),
                        None,
                    )
                true_first_lineage = (
                    active is None and not os.path.lexists(authority_path)
                )
                legacy_unprefixed_active = bool(
                    active is not None
                    and self._legacy_schema2_entry_path(active.entry_id).is_file()
                    and not self._schema2_prefixed_entry_path(
                        helper_name=name,
                        owner_id=str(owner_id),
                        workspace_id=workspace,
                        origin_environment_key=self.environment_key,
                        entry_id=active.entry_id,
                    ).is_file()
                )
                helper_source_hash = str(
                    getattr(helper, "source_hash", "") or ""
                ).strip()
                supersedes_entry_id = ""
                if active is not None:
                    supersedes_entry_id = (
                        active.supersedes_entry_id
                        if active.source_hash == helper_source_hash
                        else active.entry_id
                    )
                entry = self._entry_for_helper(
                    helper,
                    domain=domain,
                    imports=imports,
                    owner_id=owner_id,
                    generated_by_run=generated_by_run,
                    generated_by_model=generated_by_model,
                    source_theorem=source_theorem,
                    forbidden_problem_constants=forbidden_problem_constants,
                    helper_lookup=helper_lookup,
                    workspace_id=workspace_id,
                    supersedes_entry_id=supersedes_entry_id,
                )
                if active is not None and entry.entry_id != active.entry_id:
                    # Equal Lean source is not equal receipt identity: support
                    # receipts, imports, and safety metadata can change.  Any
                    # distinct receipt must explicitly supersede the exact
                    # prior authority; only an identical entry is idempotent.
                    if entry.supersedes_entry_id != active.entry_id:
                        entry = self._entry_for_helper(
                            helper,
                            domain=domain,
                            imports=imports,
                            owner_id=owner_id,
                            generated_by_run=generated_by_run,
                            generated_by_model=generated_by_model,
                            source_theorem=source_theorem,
                            forbidden_problem_constants=(
                                forbidden_problem_constants
                            ),
                            helper_lookup=helper_lookup,
                            workspace_id=workspace_id,
                            supersedes_entry_id=active.entry_id,
                        )
                path = self._write_entry_locked(entry)
                exact_active_idempotent = bool(
                    active is not None
                    and entry.entry_id == active.entry_id
                )
                if not true_first_lineage and (
                    not exact_active_idempotent or legacy_unprefixed_active
                ):
                    self._write_authority_locked(
                        helper_name=entry.helper_name,
                        owner_id=entry.owner_id,
                        workspace_id=entry.workspace_id,
                        origin_environment_key=entry.origin_environment_key,
                        entry_id=entry.entry_id,
                        source_hash=entry.source_hash,
                        source_sha256=entry.source_sha256,
                        promotable=True,
                        reason="generic_verified_helper",
                    )
        except Exception as exc:
            return PromotionEnqueueResult(
                False,
                diagnostic="promotion_receipt_persistence_failed",
                error_kind=type(exc).__name__,
                error=str(exc),
            )
        # This cache is only an acceleration structure. Receipt persistence
        # already committed successfully and must never be reported as failed
        # because best-effort in-memory maintenance raced or ran out of room.
        try:
            self._index_equivalent_work(entry)
        except Exception:
            self._equivalent_work_index = None
            self._equivalent_work_entries_generation = None
        return PromotionEnqueueResult(
            True,
            entry_id=entry.entry_id,
            path=path,
            diagnostic="promotion_receipt_durable",
        )

    def reuse_equivalent_work(
        self,
        helper: Any,
        *,
        domain: str,
        imports: Sequence[str],
        owner_id: str,
        generated_by_run: str = "",
        generated_by_model: str = "",
        source_theorem: str = "",
        forbidden_problem_constants: Sequence[str] = (),
        helper_lookup: Optional[Mapping[str, Any]] = None,
        workspace_id: str = "",
    ) -> Optional[PromotionEnqueueResult]:
        """Reuse exact immutable work with workspace-scoped authority.

        This is intentionally narrower than ``enqueue``.  A newly proved
        helper still receives per-workspace crash authority.  Reuse keeps one
        immutable compilation receipt, but durably records that the consuming
        workspace also owns it; revoking one workspace therefore cannot erase
        another workspace's pending work.
        """

        promotable, _diagnostic = helper_is_promotable(helper)
        if not promotable:
            return None
        try:
            expected = self._entry_for_helper(
                helper,
                domain=domain,
                imports=imports,
                owner_id=owner_id,
                generated_by_run=generated_by_run,
                generated_by_model=generated_by_model,
                source_theorem=source_theorem,
                forbidden_problem_constants=forbidden_problem_constants,
                helper_lookup=helper_lookup,
                workspace_id=workspace_id,
            )
            expected_identity = self._compilation_policy_identity(expected)
            with self._lock():
                equivalent = next(
                    (
                        entry
                        for entry in self._equivalent_work_candidates_locked(
                            expected_identity
                        )
                        if bool(self._authority_token(entry, lock_held=True))
                        if entry.source_theorem == expected.source_theorem
                        or self._read_result(entry) is not None
                    ),
                    None,
                )
                if equivalent is None:
                    return None
                self._write_authority_locked(
                    helper_name=equivalent.helper_name,
                    owner_id=expected.owner_id,
                    workspace_id=expected.workspace_id,
                    origin_environment_key=equivalent.origin_environment_key,
                    entry_id=equivalent.entry_id,
                    source_hash=equivalent.source_hash,
                    source_sha256=equivalent.source_sha256,
                    promotable=True,
                    reason="equivalent_promotion_work_reused",
                )
                # The new reference cannot change compilation identity or add
                # an index candidate.  Advance the generation snapshot so a
                # second reuse can retain the one-scan lazy-index behavior.
                self._equivalent_work_entries_generation = (
                    self._entries_generation()
                )
            return PromotionEnqueueResult(
                True,
                entry_id=equivalent.entry_id,
                path=self._entry_path(equivalent),
                diagnostic="equivalent_promotion_work_reused",
            )
        except Exception:
            return None

    @staticmethod
    def _compilation_policy_identity(
        entry: PromotionOutboxEntry,
    ) -> tuple[Any, ...]:
        return (
            entry.helper_name,
            entry.source,
            entry.source_hash,
            entry.source_sha256,
            entry.support_receipts,
            entry.domain,
            entry.imports,
            entry.origin_environment_key,
            tuple(sorted(entry.forbidden_problem_constants)),
            entry.policy_version,
        )

    def _equivalent_work_candidates(
        self,
        identity: tuple[Any, ...],
    ) -> tuple[PromotionOutboxEntry, ...]:
        generation = self._entries_generation()
        if (
            self._equivalent_work_index is None
            or self._equivalent_work_entries_generation != generation
        ):
            # Serialize the refresh with enqueue/revoke. This gives the index
            # a real linearization point instead of allowing a receipt to land
            # between directory enumeration and cache publication.
            with self._lock():
                return self._equivalent_work_candidates_locked(identity)
        return self._equivalent_work_index.get(identity, ())

    def _equivalent_work_candidates_locked(
        self,
        identity: tuple[Any, ...],
    ) -> tuple[PromotionOutboxEntry, ...]:
        """Return indexed candidates while the shared outbox lock is held."""

        generation = self._entries_generation()
        if (
            self._equivalent_work_index is None
            or self._equivalent_work_entries_generation != generation
        ):
            entries = self._all_entries()
            authoritative_ids = self._authoritative_entry_ids(
                entries,
                lock_held=True,
            )
            index: dict[tuple[Any, ...], list[PromotionOutboxEntry]] = {}
            for entry in entries:
                # Legacy receipts have newest-entry authority without a
                # lineage token, so a cross-process addition can invalidate a
                # cached hit invisibly. Keep them out of this optimization;
                # the fallback writes a current schema-2 receipt.
                if (
                    entry.schema_version <= 1
                    or entry.entry_id not in authoritative_ids
                ):
                    continue
                index.setdefault(
                    self._compilation_policy_identity(entry), []
                ).append(entry)
            self._equivalent_work_index = {
                key: tuple(
                    sorted(
                        values,
                        key=lambda item: (item.created_ts, item.entry_id),
                    )
                )
                for key, values in index.items()
            }
            self._equivalent_work_entries_generation = generation
        return self._equivalent_work_index.get(identity, ())

    def _entries_generation(self) -> tuple[int, int, int, int]:
        """Cheap cross-process invalidation token for immutable receipts."""

        tokens: list[int] = []
        for root in (self.entries_root, self.authorities_root):
            try:
                stat = root.stat()
            except OSError:
                tokens.extend((0, 0))
            else:
                tokens.extend((int(stat.st_mtime_ns), int(stat.st_ctime_ns)))
        return (tokens[0], tokens[1], tokens[2], tokens[3])

    def _index_equivalent_work(self, entry: PromotionOutboxEntry) -> None:
        if self._equivalent_work_index is None:
            return
        identity = self._compilation_policy_identity(entry)
        current = self._equivalent_work_index.get(identity, ())
        if any(item.entry_id == entry.entry_id for item in current):
            return
        self._equivalent_work_index[identity] = tuple(
            sorted(
                (*current, entry),
                key=lambda item: (item.created_ts, item.entry_id),
            )
        )

    def revoke(
        self,
        helper_name: str,
        *,
        owner_id: str,
        workspace_id: str = "",
        origin_environment_key: str = "",
        reason: str,
    ) -> bool:
        """Durably supersede receipts for one producer/helper lineage."""

        name = str(helper_name or "").strip()
        if not name or not _HEX_32_RE.fullmatch(str(owner_id or "")):
            return False
        workspace = str(workspace_id or owner_id).strip()
        if not _HEX_32_RE.fullmatch(workspace):
            return False
        self._write_authority(
            helper_name=name,
            owner_id=owner_id,
            workspace_id=workspace,
            origin_environment_key=str(
                origin_environment_key or self.environment_key
            ),
            entry_id="",
            source_hash="",
            source_sha256="",
            promotable=False,
            reason=str(reason or "helper_removed"),
        )
        self._equivalent_work_index = None
        self._equivalent_work_entries_generation = None
        return True

    def durably_attested_helpers(
        self,
        helpers: Mapping[str, Any],
        *,
        domain: str,
        imports: Sequence[str],
        owner_id: str,
        source_theorem: str,
        forbidden_problem_constants: Sequence[str],
        workspace_id: str = "",
        allow_inherited_root_policy: bool = False,
    ) -> set[str]:
        """Return helpers with an authoritative compatible receipt in this root.

        Ordinary reconciliation requires an exact safety-policy match.  A
        recursive child may additionally reuse an inherited parent receipt:
        the helper source is immutable and predates the child obligation, so
        requiring the root theorem guards remains authoritative while avoiding
        a fresh receipt solely because the child adds its own theorem names.
        """

        expected: dict[str, tuple[Any, ...]] = {}
        helper_lookup = dict(helpers)
        for name, helper in helper_lookup.items():
            promotable, _diagnostic = helper_is_promotable(helper)
            source = str(getattr(helper, "source", "") or "").strip()
            source_hash = str(
                getattr(helper, "source_hash", "") or ""
            ).strip()
            if not promotable or source_hash != text_hash(source):
                continue
            support_hashes = {
                str(key or "").strip(): str(value or "").strip()
                for key, value in dict(
                    getattr(helper, "support_source_hashes", {}) or {}
                ).items()
                if str(key or "").strip()
            }
            support_receipts: list[PromotionDependencyReceipt] = []
            complete = True
            for support_name in tuple(
                dict.fromkeys(
                    str(item or "").strip()
                    for item in tuple(
                        getattr(helper, "support_names", ()) or ()
                    )
                    if str(item or "").strip()
                )
            ):
                dependency = helper_lookup.get(support_name)
                dependency_source = str(
                    getattr(dependency, "source", "") or ""
                ).strip()
                dependency_hash = support_hashes.get(support_name, "")
                if (
                    dependency is None
                    or not dependency_source
                    or dependency_hash != text_hash(dependency_source)
                    or dependency_hash
                    != str(getattr(dependency, "source_hash", "") or "")
                ):
                    complete = False
                    break
                support_receipts.append(
                    PromotionDependencyReceipt(
                        helper_name=support_name,
                        source_hash=dependency_hash,
                        source_sha256=_sha256(dependency_source),
                        source=dependency_source,
                    )
                )
            if not complete:
                continue
            expected[str(name)] = (
                source,
                source_hash,
                _sha256(source),
                tuple(support_receipts),
            )
        if not expected:
            return set()
        entries = self._all_entries()
        authoritative_ids = self._authoritative_entry_ids(entries)
        clean_imports = tuple(
            dict.fromkeys(
                str(item or "").strip()
                for item in imports
                if str(item or "").strip()
            )
        )
        clean_forbidden = tuple(
            dict.fromkeys(
                str(item or "").strip()
                for item in forbidden_problem_constants
                if str(item or "").strip()
            )
        )
        clean_source_theorem = str(source_theorem or "").strip()
        clean_owner_id = str(owner_id or "").strip()
        clean_workspace_id = str(workspace_id or "").strip()
        reference_workspace_id = (
            "" if allow_inherited_root_policy else clean_workspace_id
        )
        authority_index = self._active_authorities_by_entry_id()
        referenced_authority_ids: set[str] = set()
        for entry in entries:
            if any(
                authority.get("owner_id") == clean_owner_id
                and (
                    not reference_workspace_id
                    or authority.get("workspace_id")
                    == reference_workspace_id
                )
                for authority in self._active_authorities_for_entry(
                    entry,
                    authority_index=authority_index,
                )
            ):
                referenced_authority_ids.add(entry.entry_id)
        inherited_required_forbidden = (
            {
                clean_source_theorem,
                f"{clean_source_theorem}_solution",
            }
            if clean_source_theorem
            else set()
        )
        attested: set[str] = set()
        for entry in entries:
            identity = expected.get(entry.helper_name)
            if identity is None or entry.entry_id not in authoritative_ids:
                continue
            direct_workspace_authority = bool(
                entry.owner_id == clean_owner_id
                and (
                    allow_inherited_root_policy
                    or not clean_workspace_id
                    or (entry.workspace_id or entry.owner_id)
                    == clean_workspace_id
                )
            )
            referenced_workspace_authority = (
                entry.entry_id in referenced_authority_ids
            )
            forbidden_policy_matches = (
                entry.forbidden_problem_constants == clean_forbidden
            )
            if allow_inherited_root_policy and inherited_required_forbidden:
                forbidden_policy_matches = forbidden_policy_matches or (
                    inherited_required_forbidden.issubset(
                        set(entry.forbidden_problem_constants)
                    )
                )
            if (
                entry.origin_environment_key == self.environment_key
                and entry.policy_version == self.policy_version
                and (
                    direct_workspace_authority
                    or referenced_workspace_authority
                )
                and entry.domain == str(domain or "").strip()
                and entry.imports == clean_imports
                and entry.source_theorem == clean_source_theorem
                and forbidden_policy_matches
                and (
                    entry.source,
                    entry.source_hash,
                    entry.source_sha256,
                    entry.support_receipts,
                )
                == identity
            ):
                attested.add(entry.helper_name)
        return attested

    def pending_entries(
        self,
        *,
        source_theorems: Sequence[str] = (),
        cancellation_event: Any = None,
        _context: Optional[_ResultValidationContext] = None,
    ) -> tuple[PromotionOutboxEntry, ...]:
        # Resolve authority against the complete inbox before applying the
        # startup theorem filter.  In particular, schema-1 authority is the
        # newest receipt in a producer/name lineage; filtering first could
        # hide a newer receipt from another theorem and resurrect stale code.
        context = _context or self._result_validation_context(
            cancellation_event=cancellation_event,
        )
        entries = tuple(context.entries_by_id.values())
        authoritative_ids = context.authoritative_ids
        allowed = {
            str(item or "").strip()
            for item in source_theorems
            if str(item or "").strip()
        }
        pending = [
            entry
            for entry in entries
            if not (
                cancellation_event is not None
                and cancellation_event.is_set()
            )
            if entry.entry_id in authoritative_ids
            and (not allowed or entry.source_theorem in allowed)
            and self._read_result(entry, _context=context) is None
        ]
        return tuple(sorted(pending, key=lambda item: (item.created_ts, item.entry_id)))

    def status(self) -> dict[str, int]:
        """Return current-environment inbox counts without invoking Lean."""

        context = self._result_validation_context()
        entries = tuple(context.entries_by_id.values())
        owner_id = str(
            getattr(getattr(self.library, "lease_owner", None), "owner_id", "")
            or ""
        )
        published = 0
        rejected = 0
        authoritative_ids = context.authoritative_ids
        for entry in entries:
            if entry.entry_id not in authoritative_ids:
                continue
            result = self._read_result(entry, _context=context)
            status = str((result or {}).get("status") or "")
            if status == "published":
                published += 1
            elif status == "terminal_rejected":
                rejected += 1
        claimed = len(tuple(self._regular_json_files(self._claim_scope_root())))
        pending = max(0, len(authoritative_ids) - published - rejected)
        return {
            "created": sum(1 for entry in entries if entry.owner_id == owner_id),
            "receipts": len(entries),
            "pending": pending,
            "claimed": claimed,
            "published": published,
            "rejected": rejected,
        }

    def owner_ids_for_generated_run(
        self,
        generated_by_run: str,
        *,
        cancellation_event: Any = None,
    ) -> tuple[str, ...]:
        """Return receipt owners for one run so its maintenance gets priority."""

        run_id = str(generated_by_run or "").strip()
        if not run_id:
            return ()
        return tuple(
            dict.fromkeys(
                entry.owner_id
                for entry in self._all_entries(
                    cancellation_event=cancellation_event,
                )
                if not (
                    cancellation_event is not None
                    and cancellation_event.is_set()
                )
                if entry.generated_by_run == run_id
                and _HEX_32_RE.fullmatch(entry.owner_id)
            )
        )

    def drain(
        self,
        *,
        promoter: Any,
        current_owner_id: str,
        max_entries: int = 0,
        preferred_owner_ids: Sequence[str] = (),
        source_theorems: Sequence[str] = (),
        newest_first: bool = False,
        event_callback: Optional[Callable[[dict[str, Any]], Any]] = None,
        cancellation_event: Any = None,
    ) -> PromotionDrainReport:
        """Claim and publish ready receipts without holding the filesystem lock."""

        report = PromotionDrainReport()
        if not _HEX_32_RE.fullmatch(str(current_owner_id or "")):
            report.failures += 1
            self._event(
                report,
                event_callback,
                verdict="promotion_drain_invalid_owner",
            )
            return report
        report.recovered_claims = self._recover_abandoned_claims(
            cancellation_event=cancellation_event,
        )
        preferred = {
            str(item or "")
            for item in preferred_owner_ids
            if _HEX_32_RE.fullmatch(str(item or ""))
        }
        preferred.add(current_owner_id)
        allowed_source_theorems = {
            str(item or "").strip()
            for item in source_theorems
            if str(item or "").strip()
        }
        processed: set[str] = set()
        limit = max(0, int(max_entries or 0))
        while True:
            if cancellation_event is not None and cancellation_event.is_set():
                break
            if limit and report.attempted >= limit:
                break
            known_entries = self._all_entries(
                cancellation_event=cancellation_event,
            )
            validation_context = self._result_validation_context(
                known_entries,
                cancellation_event=cancellation_event,
            )
            candidates = sorted(
                [
                entry
                for entry in self.pending_entries(
                    source_theorems=tuple(allowed_source_theorems),
                    cancellation_event=cancellation_event,
                    _context=validation_context,
                )
                if entry.entry_id not in processed
                ],
                key=lambda entry: (
                    0 if entry.owner_id in preferred else 1,
                    -entry.created_ts if newest_first else entry.created_ts,
                    entry.entry_id,
                ),
            )
            if not candidates:
                break
            progressed = False
            deferred_ids: set[str] = set()
            for entry in candidates:
                if cancellation_event is not None and cancellation_event.is_set():
                    break
                if limit and report.attempted >= limit:
                    break
                current_owner_has_authority = current_owner_id in (
                    validation_context.authority_owner_ids_by_entry.get(
                        entry.entry_id,
                        frozenset(),
                    )
                )
                if (
                    entry.owner_id != current_owner_id
                    and not current_owner_has_authority
                ):
                    abandoned = self._producer_abandoned(
                        entry.owner_id,
                        environment_key=entry.origin_environment_key,
                    )
                    if abandoned is not True:
                        report.skipped_live_owner += 1
                        processed.add(entry.entry_id)
                        continue
                dependency_results: list[dict[str, Any]] = []
                dependency_ready = True
                for dependency in entry.support_receipts:
                    if not dependency.source_hash or not dependency.source_sha256:
                        dependency_ready = False
                        break
                    providers = validation_context.providers_by_identity.get(
                        (
                            dependency.helper_name,
                            dependency.source_hash,
                            dependency.source_sha256,
                        )
                    )
                    if not providers:
                        dependency_ready = False
                        break
                    result = next(
                        (
                            candidate_result
                            for provider in providers
                            if (
                                candidate_result := self._read_result(
                                    provider,
                                    _context=validation_context,
                                )
                            )
                            and candidate_result.get("status") == "published"
                        ),
                        None,
                    )
                    if result is None:
                        dependency_ready = False
                        break
                    dependency_results.append(result)
                if not dependency_ready:
                    deferred_ids.add(entry.entry_id)
                    continue
                claim = self._claim(
                    entry,
                    current_owner_id=current_owner_id,
                    require_current_owner_authority=(
                        entry.owner_id != current_owner_id
                        and current_owner_has_authority
                    ),
                    cancellation_event=cancellation_event,
                )
                if claim is None:
                    report.skipped_claimed += 1
                    processed.add(entry.entry_id)
                    continue
                report.attempted += 1
                progressed = True
                settled = False
                publication_settled = False
                try:
                    promoted_helper, dependency_ids, effective_imports = (
                        self._promotion_inputs(entry, dependency_results)
                    )
                    promotion_kwargs = {
                        "domain": entry.domain,
                        "imports": effective_imports,
                        "dependency_bundle_ids": dependency_ids,
                        "generated_by_run": entry.generated_by_run,
                        "generated_by_model": entry.generated_by_model,
                        "source_theorem": entry.source_theorem,
                        "forbidden_problem_constants": (
                            entry.forbidden_problem_constants
                        ),
                        "cancellation_event": cancellation_event,
                    }
                    prepare = getattr(promoter, "prepare", None)
                    publish_prepared = getattr(
                        promoter,
                        "publish_prepared",
                        None,
                    )
                    if callable(prepare) and callable(publish_prepared):
                        preparation = prepare(
                            promoted_helper,
                            **promotion_kwargs,
                        )
                        verification = getattr(
                            preparation,
                            "verification",
                            None,
                        )
                        if bool(getattr(verification, "accepted", False)):
                            # Lean compilation is complete. Hold the short
                            # outbox critical section across the immutable
                            # store commit so a replacement/tombstone cannot
                            # race between authority validation and publish.
                            with self._lock():
                                if not self._claim_is_current(
                                    entry,
                                    claim,
                                    lock_held=True,
                                ):
                                    result = SimpleNamespace(
                                        published=False,
                                        diagnostic="authority_changed_before_publish",
                                        retryable=True,
                                    )
                                else:
                                    result = publish_prepared(
                                        preparation,
                                        cancellation_event=cancellation_event,
                                    )
                                    if bool(getattr(result, "published", False)):
                                        publication = getattr(
                                            result,
                                            "publication",
                                            None,
                                        )
                                        bundle = getattr(
                                            publication,
                                            "bundle",
                                            None,
                                        )
                                        if bundle is None:
                                            raise RuntimeError(
                                                "published promotion has no immutable "
                                                "bundle receipt"
                                            )
                                        result_payload = self._published_result(
                                            entry,
                                            result,
                                            bundle,
                                        )
                                        self._attested_bundle_cache = None
                                        self._settle_locked(
                                            entry,
                                            result_payload,
                                            claim,
                                        )
                                        publication_settled = True
                                        validation_context.result_memo.pop(
                                            entry.entry_id,
                                            None,
                                        )
                        else:
                            result = publish_prepared(
                                preparation,
                                cancellation_event=cancellation_event,
                            )
                    else:
                        result = promoter.promote(
                            promoted_helper,
                            **promotion_kwargs,
                        )
                    diagnostic = str(getattr(result, "diagnostic", "") or "")
                    cancelled = bool(
                        cancellation_event is not None
                        and cancellation_event.is_set()
                    )
                    if bool(getattr(result, "published", False)):
                        publication = getattr(result, "publication", None)
                        bundle = getattr(publication, "bundle", None)
                        if bundle is None:
                            raise RuntimeError(
                                "published promotion has no immutable bundle receipt"
                            )
                        if publication_settled:
                            settled = True
                        else:
                            result_payload = self._published_result(
                                entry,
                                result,
                                bundle,
                            )
                            self._attested_bundle_cache = None
                            settled = self._settle(entry, result_payload, claim)
                            if settled:
                                validation_context.result_memo.pop(
                                    entry.entry_id,
                                    None,
                                )
                        if settled:
                            report.published += 1
                            verdict = "helper_promoted"
                        else:
                            report.retryable += 1
                            verdict = "helper_promotion_claim_lost_retryable"
                    elif (
                        cancelled
                        or bool(getattr(result, "retryable", False))
                        or self._retryable_diagnostic(diagnostic)
                    ):
                        report.retryable += 1
                        verdict = "helper_promotion_deferred_retryable"
                    else:
                        result_payload = {
                            "schema_version": PROMOTION_OUTBOX_SCHEMA_VERSION,
                            "result_policy_version": PROMOTION_RESULT_POLICY_VERSION,
                            "entry_id": entry.entry_id,
                            "status": "terminal_rejected",
                            "diagnostic": str(
                                getattr(result, "diagnostic", "") or ""
                            ),
                            "environment_key": self.environment_key,
                            "policy_version": self.policy_version,
                            "settled_ts": time.time(),
                        }
                        settled = self._settle(entry, result_payload, claim)
                        if settled:
                            validation_context.result_memo.pop(
                                entry.entry_id,
                                None,
                            )
                        if settled:
                            report.rejected += 1
                            verdict = "helper_not_promoted"
                        else:
                            report.retryable += 1
                            verdict = "helper_promotion_claim_lost_retryable"
                    self._event(
                        report,
                        event_callback,
                        phase="domain_theory_promotion",
                        helper_name=entry.helper_name,
                        diagnostic=str(getattr(result, "diagnostic", "") or ""),
                        published=bool(getattr(result, "published", False)),
                        verdict=verdict,
                    )
                except BaseException as exc:
                    if isinstance(exc, Exception):
                        report.failures += 1
                        self._event(
                            report,
                            event_callback,
                            phase="domain_theory_promotion",
                            helper_name=entry.helper_name,
                            error=f"{type(exc).__name__}: {exc}",
                            verdict="helper_promotion_failed_retryable",
                        )
                    else:
                        raise
                finally:
                    if not settled:
                        self._release_claim(entry.entry_id, claim)
                processed.add(entry.entry_id)
            if deferred_ids:
                # Providers may have been published later in this same pass.
                retryable = deferred_ids - processed
                if progressed and retryable:
                    continue
                report.deferred += len(retryable)
                processed.update(retryable)
            if not progressed:
                break
        report.remaining = len(
            self.pending_entries(
                source_theorems=tuple(allowed_source_theorems),
                cancellation_event=cancellation_event,
            )
        )
        return report

    @staticmethod
    def _retryable_diagnostic(diagnostic: str) -> bool:
        normalized = str(diagnostic or "").strip().lower()
        return any(
            marker in normalized
            for marker in (
                "cancel",
                "timeout",
                "timed_out",
                "executable",
                "environment",
                "infrastructure",
                "missing_artifact",
                "artifact_missing",
                "path_not_found",
                "no_such_file",
                "permission_denied",
                "lean_project_missing",
                "missing_dependency_bundle",
            )
        )

    def _entry_for_helper(
        self,
        helper: Any,
        *,
        domain: str,
        imports: Sequence[str],
        owner_id: str,
        generated_by_run: str,
        generated_by_model: str,
        source_theorem: str,
        forbidden_problem_constants: Sequence[str],
        helper_lookup: Optional[Mapping[str, Any]],
        workspace_id: str = "",
        supersedes_entry_id: str = "",
    ) -> PromotionOutboxEntry:
        if not _HEX_32_RE.fullmatch(str(owner_id or "")):
            raise ValueError("invalid promotion receipt owner id")
        workspace = str(workspace_id or owner_id).strip()
        if not _HEX_32_RE.fullmatch(workspace):
            raise ValueError("invalid promotion receipt workspace id")
        source = str(getattr(helper, "source", "") or "").strip()
        source_hash = str(getattr(helper, "source_hash", "") or "").strip()
        if source_hash != text_hash(source):
            raise ValueError("verified helper source hash mismatch")
        support_hashes = {
            str(name or "").strip(): str(value or "").strip()
            for name, value in dict(
                getattr(helper, "support_source_hashes", {}) or {}
            ).items()
            if str(name or "").strip()
        }
        support_names = tuple(
            dict.fromkeys(
                str(item or "").strip()
                for item in list(getattr(helper, "support_names", []) or ())
                if str(item or "").strip()
            )
        )
        lookup = dict(helper_lookup or {})
        receipts: list[PromotionDependencyReceipt] = []
        for support_name in support_names:
            dependency = lookup.get(support_name)
            dependency_source = str(
                getattr(dependency, "source", "") or ""
            ).strip()
            dependency_hash = support_hashes.get(support_name, "")
            if dependency is not None and dependency_hash:
                current_hash = str(
                    getattr(dependency, "source_hash", "") or ""
                ).strip()
                if current_hash != dependency_hash:
                    dependency_source = ""
            receipts.append(
                PromotionDependencyReceipt(
                    helper_name=support_name,
                    source_hash=dependency_hash,
                    source_sha256=(
                        _sha256(dependency_source) if dependency_source else ""
                    ),
                    source=dependency_source,
                )
            )
        entry = PromotionOutboxEntry(
            schema_version=PROMOTION_OUTBOX_SCHEMA_VERSION,
            entry_id="",
            receipt_sha256="",
            helper_name=str(getattr(helper, "name", "") or "").strip(),
            source=source,
            source_hash=source_hash,
            source_sha256=_sha256(source),
            support_receipts=tuple(receipts),
            domain=str(domain or "").strip(),
            imports=tuple(
                dict.fromkeys(
                    str(item or "").strip()
                    for item in imports
                    if str(item or "").strip()
                )
            ),
            owner_id=str(owner_id),
            origin_environment_key=self.environment_key,
            generated_by_run=str(generated_by_run or "").strip(),
            generated_by_model=str(generated_by_model or "").strip(),
            source_theorem=str(source_theorem or "").strip(),
            forbidden_problem_constants=tuple(
                dict.fromkeys(
                    str(item or "").strip()
                    for item in forbidden_problem_constants
                    if str(item or "").strip()
                )
            ),
            policy_version=self.policy_version,
            created_ts=time.time(),
            workspace_id=workspace,
            supersedes_entry_id=str(supersedes_entry_id or "").strip(),
        )
        entry_id = _sha256(_canonical_json(entry.content_identity_payload()))
        entry = replace(entry, entry_id=entry_id)
        return replace(
            entry,
            receipt_sha256=_sha256(_canonical_json(entry.receipt_payload())),
        )

    def _write_entry(self, entry: PromotionOutboxEntry) -> Path:
        self._ensure_safe_directory(self.entries_root)
        with self._lock():
            return self._write_entry_locked(entry)

    def _write_entry_locked(self, entry: PromotionOutboxEntry) -> Path:
        self._ensure_safe_directory(self.entries_root)
        path = self._entry_path(entry)
        if path.is_file():
            existing = self._read_entry(path)
            if (
                existing.content_identity_payload()
                != entry.content_identity_payload()
            ):
                raise ValueError("promotion receipt identity conflict")
            return path
        self._atomic_json(path, asdict(entry))
        return path

    def _entry_path(self, entry: PromotionOutboxEntry) -> Path:
        if entry.schema_version <= 1:
            return self.entries_root / f"{entry.entry_id}.json"
        lineage_key = self._authority_key(
            helper_name=entry.helper_name,
            owner_id=entry.owner_id,
            workspace_id=entry.workspace_id or entry.owner_id,
            origin_environment_key=entry.origin_environment_key,
        )
        return self.entries_root / (
            f"L_{lineage_key}_E_{entry.entry_id}.json"
        )

    def _schema2_entry_path_for_id(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
        entry_id: str,
    ) -> Path:
        if not _HEX_64_RE.fullmatch(entry_id):
            raise ValueError("invalid promotion entry id")
        prefixed = self._schema2_prefixed_entry_path(
            helper_name=helper_name,
            owner_id=owner_id,
            workspace_id=workspace_id,
            origin_environment_key=origin_environment_key,
            entry_id=entry_id,
        )
        if prefixed.is_file() and not prefixed.is_symlink():
            return prefixed
        legacy = self._legacy_schema2_entry_path(entry_id)
        if legacy.is_file() and not legacy.is_symlink():
            return legacy
        return prefixed

    def _schema2_prefixed_entry_path(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
        entry_id: str,
    ) -> Path:
        lineage_key = self._authority_key(
            helper_name=helper_name,
            owner_id=owner_id,
            workspace_id=workspace_id,
            origin_environment_key=origin_environment_key,
        )
        return self.entries_root / f"L_{lineage_key}_E_{entry_id}.json"

    def _legacy_schema2_entry_path(self, entry_id: str) -> Path:
        return self.entries_root / f"{entry_id}.json"

    def _schema2_lineage_entries(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
    ) -> tuple[PromotionOutboxEntry, ...]:
        lineage_key = self._authority_key(
            helper_name=helper_name,
            owner_id=owner_id,
            workspace_id=workspace_id,
            origin_environment_key=origin_environment_key,
        )
        entries: list[PromotionOutboxEntry] = []
        if not self.entries_root.is_dir() or self.entries_root.is_symlink():
            return ()
        for path in sorted(
            self.entries_root.glob(f"L_{lineage_key}_E_*.json")
        ):
            if path.is_symlink() or not path.is_file():
                continue
            try:
                entry = self._read_entry(path)
            except (OSError, ValueError, json.JSONDecodeError):
                continue
            entries.append(entry)
        return tuple(entries)

    def _legacy_schema2_lineage_entries(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
    ) -> tuple[PromotionOutboxEntry, ...]:
        """Return pre-prefix schema-2 receipts from one upgrade-only scan."""

        if self._legacy_schema2_lineage_index is None:
            index: dict[
                tuple[str, str, str, str], list[PromotionOutboxEntry]
            ] = {}
            if self.entries_root.is_dir() and not self.entries_root.is_symlink():
                for path in self._regular_json_files(self.entries_root):
                    if re.fullmatch(r"[0-9a-f]{64}\.json", path.name) is None:
                        continue
                    try:
                        entry = self._read_entry(path)
                    except (OSError, ValueError, json.JSONDecodeError):
                        continue
                    if entry.schema_version != 2:
                        continue
                    key = (
                        entry.origin_environment_key,
                        entry.owner_id,
                        entry.workspace_id or entry.owner_id,
                        entry.helper_name,
                    )
                    index.setdefault(key, []).append(entry)
            self._legacy_schema2_lineage_index = {
                key: tuple(values) for key, values in index.items()
            }
        return self._legacy_schema2_lineage_index.get(
            (
                origin_environment_key,
                owner_id,
                workspace_id,
                helper_name,
            ),
            (),
        )

    def _read_entry(self, path: Path) -> PromotionOutboxEntry:
        if path.is_symlink() or not path.is_file():
            raise ValueError("promotion inbox entry must be a regular file")
        payload = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(payload, Mapping):
            raise ValueError("promotion receipt must be an object")
        entry = PromotionOutboxEntry.from_dict(payload)
        if entry.schema_version not in _SUPPORTED_PROMOTION_OUTBOX_SCHEMA_VERSIONS:
            raise ValueError("unsupported promotion receipt schema")
        if not _HEX_64_RE.fullmatch(entry.entry_id):
            raise ValueError("invalid promotion receipt id")
        if entry.source_hash != text_hash(entry.source):
            raise ValueError("promotion receipt helper hash mismatch")
        if entry.source_sha256 != _sha256(entry.source):
            raise ValueError("promotion receipt sha256 mismatch")
        if (
            _sha256(_canonical_json(entry.content_identity_payload()))
            != entry.entry_id
        ):
            raise ValueError("promotion receipt identity mismatch")
        if (
            _sha256(_canonical_json(entry.receipt_payload()))
            != entry.receipt_sha256
        ):
            raise ValueError("promotion receipt integrity mismatch")
        for dependency in entry.support_receipts:
            if dependency.source:
                if dependency.source_sha256 != _sha256(dependency.source):
                    raise ValueError("promotion dependency snapshot hash mismatch")
                if dependency.source_hash != text_hash(dependency.source):
                    raise ValueError("promotion dependency source receipt mismatch")
        return entry

    def _all_entries(
        self,
        *,
        source_theorems: Sequence[str] = (),
        cancellation_event: Any = None,
    ) -> tuple[PromotionOutboxEntry, ...]:
        entries_by_id: dict[str, PromotionOutboxEntry] = {}
        entry_paths: dict[str, Path] = {}
        conflicted_ids: set[str] = set()
        allowed = {
            str(item or "").strip()
            for item in source_theorems
            if str(item or "").strip()
        }
        for path in self._regular_json_files(self.entries_root):
            if cancellation_event is not None and cancellation_event.is_set():
                break
            try:
                entry = self._read_entry(path)
            except (OSError, ValueError, json.JSONDecodeError):
                continue
            if entry.entry_id in conflicted_ids:
                continue
            existing = entries_by_id.get(entry.entry_id)
            if (
                existing is not None
                and existing.content_identity_payload()
                != entry.content_identity_payload()
            ):
                # A content-address collision or hand-edited duplicate cannot
                # confer authority. Fail closed for that id instead of
                # selecting whichever directory entry happened to sort first.
                entries_by_id.pop(entry.entry_id, None)
                entry_paths.pop(entry.entry_id, None)
                conflicted_ids.add(entry.entry_id)
                continue
            existing_path = entry_paths.get(entry.entry_id)
            if (
                existing is None
                or existing_path is None
                or (
                    path.name.startswith("L_")
                    and not existing_path.name.startswith("L_")
                )
            ):
                entries_by_id[entry.entry_id] = entry
                entry_paths[entry.entry_id] = path
        return tuple(
            entry
            for entry in entries_by_id.values()
            if not allowed or entry.source_theorem in allowed
        )

    def _promotion_inputs(
        self,
        entry: PromotionOutboxEntry,
        dependency_results: Sequence[Mapping[str, Any]],
    ) -> tuple[VerifiedHelper, tuple[str, ...], tuple[str, ...]]:
        source = entry.source
        dependency_ids: list[str] = []
        imports = list(entry.imports)
        for dependency, result in zip(entry.support_receipts, dependency_results):
            bundle_id = str(result.get("bundle_id") or "").strip()
            module_name = str(result.get("module_name") or "").strip()
            fq_name = str(result.get("fq_name") or "").strip()
            if not bundle_id or not module_name or not fq_name:
                raise RuntimeError("published dependency receipt is incomplete")
            dependency_ids.append(bundle_id)
            if module_name not in imports:
                imports.append(module_name)
        namespaces = tuple(
            dict.fromkeys(
                str(result.get("namespace") or "").strip()
                for result in dependency_results
                if str(result.get("namespace") or "").strip()
            )
        )
        if namespaces:
            source = "\n".join([*(f"open {item}" for item in namespaces), source])
        helper = VerifiedHelper(
            name=entry.helper_name,
            source=source,
            source_hash=text_hash(source),
            phase="mini_theory_promotion_outbox",
            turn_index=0,
            support_names=[item.helper_name for item in entry.support_receipts],
            support_source_hashes={
                item.helper_name: item.source_hash for item in entry.support_receipts
            },
        )
        return helper, tuple(dependency_ids), tuple(imports)

    def _published_result(self, entry: PromotionOutboxEntry, result: Any, bundle: Any):
        declarations = tuple(getattr(bundle, "declarations", ()) or ())
        exact_names = [
            str(getattr(item, "fq_name", "") or "").strip()
            for item in declarations
            if str(getattr(item, "fq_name", "") or "").strip().split(".")[-1]
            == entry.helper_name
        ]
        fq_name = exact_names[0] if len(exact_names) == 1 else ""
        if not fq_name:
            raise RuntimeError(
                "published helper manifest does not attest one exact declaration"
            )
        return {
            "schema_version": PROMOTION_OUTBOX_SCHEMA_VERSION,
            "result_policy_version": PROMOTION_RESULT_POLICY_VERSION,
            "entry_id": entry.entry_id,
            "status": "published",
            "diagnostic": str(getattr(result, "diagnostic", "") or ""),
            "bundle_id": str(getattr(bundle, "bundle_id", "") or ""),
            "module_name": str(getattr(bundle, "module_name", "") or ""),
            "namespace": str(getattr(bundle, "namespace", "") or ""),
            "fq_name": fq_name,
            "environment_key": self.environment_key,
            "policy_version": self.policy_version,
            "settled_ts": time.time(),
        }

    def _claim(
        self,
        entry: PromotionOutboxEntry,
        *,
        current_owner_id: str,
        require_current_owner_authority: bool = False,
        cancellation_event: Any = None,
    ) -> Optional[dict[str, Any]]:
        path = self._claim_path(entry.entry_id)
        with self._lock():
            if cancellation_event is not None and cancellation_event.is_set():
                return None
            if require_current_owner_authority and not any(
                authority.get("owner_id") == current_owner_id
                for authority in self._active_authorities_for_entry(
                    entry,
                    lock_held=True,
                )
            ):
                # A consumer may drain shared immutable work while its own
                # authority is live. Recheck that ownership at the exact claim
                # linearization point; an invocation snapshot is only a cheap
                # eligibility filter and cannot grant stale publication rights.
                return None
            authority_token = self._authority_token(entry, lock_held=True)
            if not authority_token:
                return None
            if self._read_result(
                entry,
                cancellation_event=cancellation_event,
            ) is not None:
                return None
            self._quarantine_invalid_sidecar(self._result_path(entry.entry_id))
            if path.is_file():
                if self._read_claim(path, entry.entry_id) is not None:
                    return None
                self._quarantine_invalid_sidecar(path)
            claim = {
                "schema_version": PROMOTION_OUTBOX_SCHEMA_VERSION,
                "result_policy_version": PROMOTION_RESULT_POLICY_VERSION,
                "entry_id": entry.entry_id,
                "claim_id": uuid.uuid4().hex,
                "claim_owner_id": current_owner_id,
                "required_authority_owner_id": (
                    current_owner_id if require_current_owner_authority else ""
                ),
                "environment_key": self.environment_key,
                "claimed_ts": time.time(),
                "authority_token": authority_token,
            }
            if not claim["authority_token"]:
                return None
            self._atomic_json(path, claim)
        return claim

    def _settle(
        self,
        entry: PromotionOutboxEntry,
        result: Mapping[str, Any],
        claim: Mapping[str, Any],
    ) -> bool:
        with self._lock():
            return self._settle_locked(entry, result, claim)

    def _settle_locked(
        self,
        entry: PromotionOutboxEntry,
        result: Mapping[str, Any],
        claim: Mapping[str, Any],
    ) -> bool:
        if not self._claim_is_current(entry, claim, lock_held=True):
            return False
        self._atomic_json(self._result_path(entry.entry_id), result)
        self._unlink_and_fsync(self._claim_path(entry.entry_id))
        return True

    def _claim_is_current(
        self,
        entry: PromotionOutboxEntry,
        claim: Mapping[str, Any],
        *,
        lock_held: bool = False,
    ) -> bool:
        if not lock_held:
            with self._lock():
                return self._claim_is_current(
                    entry,
                    claim,
                    lock_held=True,
                )
        required_authority_owner_id = str(
            claim.get("required_authority_owner_id") or ""
        )
        return bool(
            self._read_claim(
                self._claim_path(entry.entry_id), entry.entry_id
            )
            == dict(claim)
            and self._authority_token(entry, lock_held=True)
            == str(claim.get("authority_token") or "")
            and (
                not required_authority_owner_id
                or any(
                    authority.get("owner_id")
                    == required_authority_owner_id
                    for authority in self._active_authorities_for_entry(
                        entry,
                        lock_held=True,
                    )
                )
            )
        )

    def _release_claim(
        self,
        entry_id: str,
        claim: Mapping[str, Any],
    ) -> bool:
        with self._lock():
            if self._read_claim(
                self._claim_path(entry_id), entry_id
            ) != dict(claim):
                return False
            self._unlink_and_fsync(self._claim_path(entry_id))
        return True

    def _recover_abandoned_claims(self, *, cancellation_event: Any = None) -> int:
        recovered = 0
        for path in self._regular_json_files(self._claim_scope_root()):
            if cancellation_event is not None and cancellation_event.is_set():
                break
            try:
                payload = self._read_claim(path, path.stem)
                if payload is None:
                    with self._lock():
                        if self._read_claim(path, path.stem) is None:
                            self._quarantine_invalid_sidecar(path)
                    continue
                owner_id = str(payload.get("claim_owner_id") or "")
            except (OSError, ValueError, json.JSONDecodeError, AttributeError):
                continue
            if self._producer_abandoned(
                owner_id,
                environment_key=self.environment_key,
            ) is not True:
                continue
            with self._lock():
                current = self._read_claim(path, path.stem)
                if current == payload:
                    self._unlink_and_fsync(path)
                    recovered += 1
        return recovered

    def _authority_key(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
    ) -> str:
        return _sha256(
            _canonical_json(
                {
                    "origin_environment_key": origin_environment_key,
                    "owner_id": owner_id,
                    "workspace_id": workspace_id,
                    "helper_name": helper_name,
                }
            )
        )

    def _authority_path(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
    ) -> Path:
        return self.authorities_root / (
            self._authority_key(
                helper_name=helper_name,
                owner_id=owner_id,
                workspace_id=workspace_id,
                origin_environment_key=origin_environment_key,
            )
            + ".json"
        )

    def _write_authority(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
        entry_id: str,
        source_hash: str,
        source_sha256: str,
        promotable: bool,
        reason: str,
    ) -> None:
        with self._lock():
            self._write_authority_locked(
                helper_name=helper_name,
                owner_id=owner_id,
                workspace_id=workspace_id,
                origin_environment_key=origin_environment_key,
                entry_id=entry_id,
                source_hash=source_hash,
                source_sha256=source_sha256,
                promotable=promotable,
                reason=reason,
            )

    def _write_authority_locked(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
        entry_id: str,
        source_hash: str,
        source_sha256: str,
        promotable: bool,
        reason: str,
    ) -> None:
        payload = {
            "schema_version": PROMOTION_OUTBOX_SCHEMA_VERSION,
            "origin_environment_key": origin_environment_key,
            "owner_id": owner_id,
            "workspace_id": workspace_id,
            "helper_name": helper_name,
            "authority_id": uuid.uuid4().hex,
            "active_entry_id": entry_id if promotable else "",
            "source_hash": source_hash if promotable else "",
            "source_sha256": source_sha256 if promotable else "",
            "promotable": bool(promotable),
            "reason": str(reason or ""),
            "updated_ts": time.time(),
        }
        self._atomic_json(
            self._authority_path(
                helper_name=helper_name,
                owner_id=owner_id,
                workspace_id=workspace_id,
                origin_environment_key=origin_environment_key,
            ),
            payload,
        )
        self._active_authority_index = None
        self._active_authority_index_generation = None

    def _read_authority(
        self,
        *,
        helper_name: str,
        owner_id: str,
        workspace_id: str,
        origin_environment_key: str,
    ) -> Optional[dict[str, Any]]:
        path = self._authority_path(
            helper_name=helper_name,
            owner_id=owner_id,
            workspace_id=workspace_id,
            origin_environment_key=origin_environment_key,
        )
        payload = self._read_authority_path(path)
        if payload is None:
            return None
        if (
            payload.get("origin_environment_key") != origin_environment_key
            or payload.get("owner_id") != owner_id
            or payload.get("workspace_id") != workspace_id
            or payload.get("helper_name") != helper_name
        ):
            return None
        return payload

    def _read_authority_path(self, path: Path) -> Optional[dict[str, Any]]:
        """Read one self-addressed workspace authority sidecar."""

        if path.is_symlink() or not path.is_file():
            return None
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError, json.JSONDecodeError):
            return None
        if not isinstance(payload, dict):
            return None
        origin_environment_key = str(
            payload.get("origin_environment_key") or ""
        ).strip()
        owner_id = str(payload.get("owner_id") or "").strip()
        workspace_id = str(payload.get("workspace_id") or "").strip()
        helper_name = str(payload.get("helper_name") or "").strip()
        if (
            payload.get("schema_version")
            not in _SUPPORTED_PROMOTION_OUTBOX_SCHEMA_VERSIONS
            or not origin_environment_key
            or not _HEX_32_RE.fullmatch(owner_id)
            or not _HEX_32_RE.fullmatch(workspace_id)
            or not helper_name
            or not isinstance(payload.get("promotable"), bool)
            or not _HEX_32_RE.fullmatch(str(payload.get("authority_id") or ""))
            or path
            != self._authority_path(
                helper_name=helper_name,
                owner_id=owner_id,
                workspace_id=workspace_id,
                origin_environment_key=origin_environment_key,
            )
        ):
            return None
        if payload.get("promotable") and (
            not _HEX_64_RE.fullmatch(str(payload.get("active_entry_id") or ""))
            or not str(payload.get("source_hash") or "").strip()
            or not _HEX_64_RE.fullmatch(
                str(payload.get("source_sha256") or "")
            )
        ):
            return None
        return payload

    def _all_authorities(self) -> tuple[dict[str, Any], ...]:
        return tuple(
            authority
            for path in self._regular_json_files(self.authorities_root)
            if (authority := self._read_authority_path(path)) is not None
        )

    def _authority_generation(self) -> tuple[int, int]:
        try:
            stat = self.authorities_root.stat()
        except OSError:
            return (0, 0)
        return (int(stat.st_mtime_ns), int(stat.st_ctime_ns))

    def _active_authorities_by_entry_id_locked(
        self,
    ) -> dict[str, tuple[dict[str, Any], ...]]:
        generation = self._authority_generation()
        if (
            self._active_authority_index is None
            or self._active_authority_index_generation != generation
        ):
            index: dict[str, list[dict[str, Any]]] = {}
            for authority in self._all_authorities():
                if not authority.get("promotable"):
                    continue
                entry_id = str(authority.get("active_entry_id") or "")
                if not _HEX_64_RE.fullmatch(entry_id):
                    continue
                index.setdefault(entry_id, []).append(authority)
            self._active_authority_index = {
                entry_id: tuple(
                    sorted(
                        authorities,
                        key=lambda item: (
                            str(item.get("owner_id") or ""),
                            str(item.get("workspace_id") or ""),
                            str(item.get("authority_id") or ""),
                        ),
                    )
                )
                for entry_id, authorities in index.items()
            }
            self._active_authority_index_generation = generation
        return self._active_authority_index

    def _active_authorities_by_entry_id(
        self,
    ) -> dict[str, tuple[dict[str, Any], ...]]:
        generation = self._authority_generation()
        if (
            self._active_authority_index is not None
            and self._active_authority_index_generation == generation
        ):
            return self._active_authority_index
        with self._lock():
            return self._active_authorities_by_entry_id_locked()

    def _active_authorities_for_entry(
        self,
        entry: PromotionOutboxEntry,
        *,
        lock_held: bool = False,
        authority_index: Optional[
            Mapping[str, Sequence[dict[str, Any]]]
        ] = None,
    ) -> tuple[dict[str, Any], ...]:
        index = authority_index
        if index is None:
            index = (
                self._active_authorities_by_entry_id_locked()
                if lock_held
                else self._active_authorities_by_entry_id()
            )
        return tuple(
            authority
            for authority in index.get(entry.entry_id, ())
            if authority.get("origin_environment_key")
            == entry.origin_environment_key
            and authority.get("helper_name") == entry.helper_name
            and authority.get("active_entry_id") == entry.entry_id
            and authority.get("source_hash") == entry.source_hash
            and authority.get("source_sha256") == entry.source_sha256
        )

    def _entry_is_authoritative(
        self,
        entry: PromotionOutboxEntry,
        *,
        lock_held: bool = False,
    ) -> bool:
        return entry.entry_id in self._authoritative_entry_ids(
            self._all_entries(),
            lock_held=lock_held,
        )

    def _authority_token(
        self,
        entry: PromotionOutboxEntry,
        *,
        lock_held: bool = False,
    ) -> str:
        if entry.schema_version <= 1:
            return (
                f"legacy:{entry.entry_id}"
                if self._entry_is_authoritative(entry, lock_held=lock_held)
                else ""
            )
        if self._active_authorities_for_entry(entry, lock_held=lock_held):
            # The immutable receipt, rather than any one workspace reference,
            # is the claim authority. Removing one reference must not cancel a
            # claim while another workspace still owns the exact same work.
            return f"authority:{entry.entry_id}"
        workspace_id = entry.workspace_id or entry.owner_id
        path = self._authority_path(
            helper_name=entry.helper_name,
            owner_id=entry.owner_id,
            workspace_id=workspace_id,
            origin_environment_key=entry.origin_environment_key,
        )
        return (
            f"authority:{entry.entry_id}"
            if not os.path.lexists(path) and not entry.supersedes_entry_id
            else ""
        )

    def _authoritative_entry_ids(
        self,
        entries: Sequence[PromotionOutboxEntry],
        *,
        cancellation_event: Any = None,
        lock_held: bool = False,
    ) -> set[str]:
        authoritative: set[str] = set()
        legacy_lineages: dict[
            tuple[str, str, str], list[PromotionOutboxEntry]
        ] = {}
        lineages: dict[
            tuple[str, str, str, str], list[PromotionOutboxEntry]
        ] = {}
        for entry in entries:
            if cancellation_event is not None and cancellation_event.is_set():
                return authoritative
            if entry.schema_version <= 1:
                legacy_lineages.setdefault(
                    (
                        entry.origin_environment_key,
                        entry.owner_id,
                        entry.helper_name,
                    ),
                    [],
                ).append(entry)
                continue
            lineages.setdefault(
                (
                    entry.origin_environment_key,
                    entry.owner_id,
                    entry.workspace_id or entry.owner_id,
                    entry.helper_name,
                ),
                [],
            ).append(entry)
        for lineage in legacy_lineages.values():
            if cancellation_event is not None and cancellation_event.is_set():
                return authoritative
            authoritative.add(
                max(
                    lineage,
                    key=lambda item: (item.created_ts, item.entry_id),
                ).entry_id
            )
        for (
            origin_environment_key,
            owner_id,
            workspace_id,
            helper_name,
        ), lineage in lineages.items():
            if cancellation_event is not None and cancellation_event.is_set():
                return authoritative
            authority = self._read_authority(
                helper_name=helper_name,
                owner_id=owner_id,
                workspace_id=workspace_id,
                origin_environment_key=origin_environment_key,
            )
            if authority is None:
                authority_path = self._authority_path(
                    helper_name=helper_name,
                    owner_id=owner_id,
                    workspace_id=workspace_id,
                    origin_environment_key=origin_environment_key,
                )
                # A missing authority file can only be the narrow crash gap
                # after one complete immutable entry was renamed into place.
                # A present-but-invalid authority is never approval.
                if not os.path.lexists(authority_path):
                    # The first immutable entry is intentionally its own
                    # authority (one proof-path fsync). If a replacement
                    # crashes after its entry rename but before its authority
                    # replace, preserve that earlier fully durable baseline.
                    # A completed replacement writes an explicit authority
                    # token and supersedes it on the next read.
                    baselines = [
                        item for item in lineage if not item.supersedes_entry_id
                    ]
                    if baselines:
                        # Workspace staging is serialized by the session; the
                        # deterministic tie-break is only for malformed or
                        # legacy hand-authored schema-2 fixtures.
                        authoritative.add(
                            min(baselines, key=lambda item: item.entry_id).entry_id
                        )
                continue
            if not authority.get("promotable"):
                continue
            active_id = str(authority.get("active_entry_id") or "")
            active = next(
                (item for item in lineage if item.entry_id == active_id),
                None,
            )
            if (
                active is not None
                and authority.get("source_hash") == active.source_hash
                and authority.get("source_sha256") == active.source_sha256
            ):
                authoritative.add(active.entry_id)
        entries_by_id = {entry.entry_id: entry for entry in entries}
        authority_index = (
            self._active_authorities_by_entry_id_locked()
            if lock_held
            else self._active_authorities_by_entry_id()
        )
        for active_id, authorities in authority_index.items():
            if cancellation_event is not None and cancellation_event.is_set():
                return authoritative
            active = entries_by_id.get(active_id)
            if active is None:
                continue
            if any(
                authority.get("origin_environment_key")
                == active.origin_environment_key
                and authority.get("helper_name") == active.helper_name
                and authority.get("source_hash") == active.source_hash
                and authority.get("source_sha256") == active.source_sha256
                for authority in authorities
            ):
                # An authority may intentionally reference an immutable entry
                # from another producer/workspace. This is how equivalent work
                # remains one compilation receipt while ownership is shared.
                authoritative.add(active.entry_id)
        return authoritative

    def _producer_abandoned(
        self,
        owner_id: str,
        *,
        environment_key: str,
    ) -> Optional[bool]:
        if not _HEX_32_RE.fullmatch(str(owner_id or "")):
            return None
        lease_owner = getattr(self.library, "lease_owner", None)
        probe = getattr(lease_owner, "owner_abandoned", None)
        if environment_key == self.environment_key and callable(probe):
            try:
                return probe(owner_id)
            except OSError:
                return None
        owners_root = (
            self.configured_root
            / "environments"
            / f"E_{environment_key}"
            / ".owners"
        )
        lock_path = owners_root / f"{owner_id}.lock"
        if lock_path.is_symlink():
            return None
        if not lock_path.is_file():
            return True
        try:
            with lock_path.open("a+b") as handle:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    return False
                finally:
                    try:
                        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
                    except OSError:
                        pass
            return True
        except OSError:
            return None

    def _result_validation_context(
        self,
        entries: Optional[Sequence[PromotionOutboxEntry]] = None,
        *,
        cancellation_event: Any = None,
    ) -> _ResultValidationContext:
        """Build one authority/provider index for a result-validation pass."""

        known_entries = tuple(entries) if entries is not None else self._all_entries(
            cancellation_event=cancellation_event,
        )
        authoritative_ids = self._authoritative_entry_ids(
            known_entries,
            cancellation_event=cancellation_event,
        )
        authority_index = self._active_authorities_by_entry_id()
        authority_owner_ids_by_entry = {
            entry.entry_id: frozenset(
                str(authority.get("owner_id") or "")
                for authority in self._active_authorities_for_entry(
                    entry,
                    authority_index=authority_index,
                )
                if _HEX_32_RE.fullmatch(
                    str(authority.get("owner_id") or "")
                )
            )
            for entry in known_entries
        }
        providers: dict[
            tuple[str, str, str], list[PromotionOutboxEntry]
        ] = {}
        for entry in known_entries:
            if cancellation_event is not None and cancellation_event.is_set():
                break
            if entry.entry_id not in authoritative_ids:
                continue
            providers.setdefault(
                (entry.helper_name, entry.source_hash, entry.source_sha256),
                [],
            ).append(entry)
        return _ResultValidationContext(
            entries_by_id={entry.entry_id: entry for entry in known_entries},
            authoritative_ids=authoritative_ids,
            providers_by_identity={
                key: tuple(
                    sorted(value, key=lambda item: (item.created_ts, item.entry_id))
                )
                for key, value in providers.items()
            },
            authority_owner_ids_by_entry=authority_owner_ids_by_entry,
            cancellation_event=cancellation_event,
        )

    def _read_result(
        self,
        entry_or_id: PromotionOutboxEntry | str,
        *,
        _context: Optional[_ResultValidationContext] = None,
        cancellation_event: Any = None,
    ) -> Optional[dict[str, Any]]:
        entry_id = (
            entry_or_id.entry_id
            if isinstance(entry_or_id, PromotionOutboxEntry)
            else str(entry_or_id or "")
        )
        event = (
            _context.cancellation_event
            if _context is not None
            else cancellation_event
        )
        if event is not None and event.is_set():
            return None
        path = self._result_path(entry_id)
        # Most pending receipts have no result.  Avoid building a full inbox
        # index during the claim's fresh under-lock recheck in that common
        # case.
        if path.is_symlink() or not path.is_file():
            return None
        context = _context or self._result_validation_context(
            cancellation_event=event,
        )
        if entry_id in context.result_memo:
            return context.result_memo[entry_id]
        entry = (
            entry_or_id
            if isinstance(entry_or_id, PromotionOutboxEntry)
            else context.entries_by_id.get(entry_id)
        )
        if entry_id in context.visiting:
            context.result_memo[entry_id] = None
            return None
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError, json.JSONDecodeError):
            context.result_memo[entry_id] = None
            return None
        context.visiting.add(entry_id)
        try:
            valid = self._valid_result_payload(
                entry,
                payload,
                _context=context,
            )
        finally:
            context.visiting.discard(entry_id)
        if not valid:
            context.result_memo[entry_id] = None
            return None
        context.result_memo[entry_id] = payload
        return payload

    def _valid_result_payload(
        self,
        entry: Optional[PromotionOutboxEntry],
        payload: Any,
        *,
        _context: Optional[_ResultValidationContext] = None,
    ) -> bool:
        if entry is None or not isinstance(payload, dict):
            return False
        if (
            payload.get("schema_version")
            not in _SUPPORTED_PROMOTION_OUTBOX_SCHEMA_VERSIONS
            or payload.get("result_policy_version")
            != PROMOTION_RESULT_POLICY_VERSION
            or payload.get("entry_id") != entry.entry_id
            or payload.get("environment_key") != self.environment_key
            or payload.get("policy_version") != self.policy_version
            or payload.get("status") not in {"published", "terminal_rejected"}
        ):
            return False
        if payload.get("status") == "terminal_rejected":
            return True
        context = _context or self._result_validation_context()
        cancellation_event = context.cancellation_event
        if cancellation_event is not None and cancellation_event.is_set():
            return False
        bundle_id = str(payload.get("bundle_id") or "")
        module_name = str(payload.get("module_name") or "")
        namespace = str(payload.get("namespace") or "")
        fq_name = str(payload.get("fq_name") or "")
        if not bundle_id or not module_name or not namespace or not fq_name:
            return False
        iterator = getattr(getattr(self.library, "store", None), "iter_bundles", None)
        if not callable(iterator):
            return fq_name == f"{namespace}.{entry.helper_name}"
        try:
            if cancellation_event is not None and cancellation_event.is_set():
                return False
            if self._attested_bundle_cache is None:
                refreshed = self._cancellable_bundle_snapshot(
                    iterator,
                    cancellation_event=cancellation_event,
                )
                if refreshed is None:
                    return False
                self._attested_bundle_cache = refreshed
            bundle = self._attested_bundle_cache.get(bundle_id)
            if bundle is None:
                # Another maintenance process may have published since this
                # instance populated its immutable-bundle cache.
                refreshed = self._cancellable_bundle_snapshot(
                    iterator,
                    cancellation_event=cancellation_event,
                )
                if refreshed is None:
                    return False
                self._attested_bundle_cache = refreshed
                bundle = self._attested_bundle_cache.get(bundle_id)
            if bundle is None:
                return False
            exact = [
                str(getattr(item, "fq_name", "") or "")
                for item in tuple(getattr(bundle, "declarations", ()) or ())
                if str(getattr(item, "fq_name", "") or "").split(".")[-1]
                == entry.helper_name
            ]
            if (
                bundle.domain != entry.domain
                or bundle.module_name != module_name
                or bundle.namespace != namespace
                or tuple(exact) != (fq_name,)
            ):
                return False
            dependency_ids = tuple(bundle.dependency_bundle_ids or ())
            if len(dependency_ids) != len(entry.support_receipts):
                return False
            dependency_results: list[dict[str, Any]] = []
            for receipt, dependency_id in zip(
                entry.support_receipts,
                dependency_ids,
            ):
                if cancellation_event is not None and cancellation_event.is_set():
                    return False
                dependency_bundle = self._attested_bundle_cache.get(dependency_id)
                if dependency_bundle is None:
                    return False
                providers = context.providers_by_identity.get(
                    (
                        receipt.helper_name,
                        receipt.source_hash,
                        receipt.source_sha256,
                    ),
                    [],
                )
                provider_result = next(
                    (
                        candidate
                        for provider in providers
                        if (
                            candidate := self._read_result(
                                provider,
                                _context=context,
                            )
                        )
                        and candidate.get("status") == "published"
                        and candidate.get("bundle_id") == dependency_id
                    ),
                    None,
                )
                if provider_result is None:
                    return False
                dependency_results.append(provider_result)
            body = entry.source
            namespaces = [
                str(item.get("namespace") or "")
                for item in dependency_results
            ]
            if namespaces:
                body = "\n".join([*(f"open {item}" for item in namespaces), body])
            expected_imports = list(entry.imports)
            for item in dependency_results:
                dependency_module = str(item.get("module_name") or "")
                if dependency_module and dependency_module not in expected_imports:
                    expected_imports.append(dependency_module)
            if tuple(bundle.imports or ()) != tuple(expected_imports):
                return False
            expected = TheoryBundleCandidate.create(
                domain=entry.domain,
                source=body,
                imports=tuple(expected_imports),
                dependency_bundle_ids=dependency_ids,
            )
            return (
                expected.bundle_id == bundle.bundle_id
                and expected.source_hash == bundle.source_hash
            )
        except Exception:
            return False

    @staticmethod
    def _cancellable_bundle_snapshot(
        iterator: Callable[[], Iterator[Any]],
        *,
        cancellation_event: Any = None,
    ) -> Optional[dict[str, Any]]:
        bundles: dict[str, Any] = {}
        for bundle in iterator():
            if cancellation_event is not None and cancellation_event.is_set():
                return None
            bundles[str(getattr(bundle, "bundle_id", "") or "")] = bundle
        return bundles

    def _read_claim(self, path: Path, entry_id: str) -> Optional[dict[str, Any]]:
        if path.is_symlink() or not path.is_file():
            return None
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError, json.JSONDecodeError):
            return None
        if not isinstance(payload, dict):
            return None
        required_authority_owner_id = str(
            payload.get("required_authority_owner_id") or ""
        )
        if (
            payload.get("schema_version")
            not in _SUPPORTED_PROMOTION_OUTBOX_SCHEMA_VERSIONS
            or payload.get("result_policy_version")
            != PROMOTION_RESULT_POLICY_VERSION
            or payload.get("entry_id") != entry_id
            or payload.get("environment_key") != self.environment_key
            or not _HEX_32_RE.fullmatch(str(payload.get("claim_owner_id") or ""))
            or not _HEX_32_RE.fullmatch(str(payload.get("claim_id") or ""))
            or not str(payload.get("authority_token") or "")
            or (
                required_authority_owner_id
                and (
                    not _HEX_32_RE.fullmatch(required_authority_owner_id)
                    or required_authority_owner_id
                    != str(payload.get("claim_owner_id") or "")
                )
            )
        ):
            return None
        return payload

    def _quarantine_invalid_sidecar(self, path: Path) -> None:
        if path.is_symlink() or not path.exists():
            return
        quarantine = path.with_name(
            f".{path.name}.invalid.{os.getpid()}.{uuid.uuid4().hex}"
        )
        os.replace(path, quarantine)
        self._fsync_dir(path.parent)

    def _claim_scope_root(self) -> Path:
        return self.claims_root / self.result_scope

    def _result_scope_root(self) -> Path:
        return self.results_root / self.result_scope

    def _claim_path(self, entry_id: str) -> Path:
        if not _HEX_64_RE.fullmatch(entry_id):
            raise ValueError("invalid promotion entry id")
        return self._claim_scope_root() / f"{entry_id}.json"

    def _result_path(self, entry_id: str) -> Path:
        if not _HEX_64_RE.fullmatch(entry_id):
            raise ValueError("invalid promotion entry id")
        return self._result_scope_root() / f"{entry_id}.json"

    @staticmethod
    def _regular_json_files(root: Path) -> Iterator[Path]:
        if not root.is_dir() or root.is_symlink():
            return iter(())
        return iter(
            path
            for path in sorted(root.glob("*.json"))
            if path.is_file() and not path.is_symlink()
        )

    @contextmanager
    def _lock(self):
        self._ensure_safe_directory(self.root)
        lock_path = self.root / ".lock"
        with lock_path.open("a+b") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

    def _atomic_json(self, path: Path, payload: Mapping[str, Any]) -> None:
        self._ensure_safe_directory(path.parent)
        temporary = path.parent / f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
        encoded = json.dumps(
            dict(payload), ensure_ascii=False, sort_keys=True, indent=2
        ) + "\n"
        try:
            with temporary.open("x", encoding="utf-8") as handle:
                handle.write(encoded)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
            PromotionOutbox._fsync_dir(path.parent)
        finally:
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass

    def _ensure_safe_directory(self, path: Path) -> None:
        candidate = Path(path)
        try:
            candidate.relative_to(self.configured_root)
        except ValueError as exc:
            raise ValueError("promotion inbox path escapes configured root") from exc
        if not self.configured_root.exists():
            self.configured_root.mkdir(parents=True, exist_ok=True)
            self._fsync_dir(self.configured_root.parent)
            self._fsync_dir(self.configured_root)
        if self.configured_root.is_symlink() or not self.configured_root.is_dir():
            raise ValueError("configured theory root must be a regular directory")
        current = self.configured_root
        for segment in candidate.relative_to(self.configured_root).parts:
            current = current / segment
            if current.is_symlink():
                raise ValueError("promotion inbox directories must not be symlinks")
        current = self.configured_root
        for segment in candidate.relative_to(self.configured_root).parts:
            child = current / segment
            if not child.exists():
                child.mkdir()
                self._fsync_dir(current)
                self._fsync_dir(child)
            current = child
        if candidate.is_symlink() or not candidate.is_dir():
            raise ValueError("promotion inbox directory is not a regular directory")
        try:
            candidate.resolve().relative_to(self.configured_root)
        except ValueError as exc:
            raise ValueError("promotion inbox directory escaped configured root") from exc

    @staticmethod
    def _unlink_and_fsync(path: Path) -> None:
        try:
            path.unlink()
        except FileNotFoundError:
            return
        PromotionOutbox._fsync_dir(path.parent)

    @staticmethod
    def _fsync_dir(path: Path) -> None:
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)

    @staticmethod
    def _event(
        report: PromotionDrainReport,
        callback: Optional[Callable[[dict[str, Any]], Any]],
        **payload: Any,
    ) -> None:
        record = dict(payload)
        report.events.append(record)
        if callback is None:
            return
        try:
            callback(record)
        except Exception:
            pass


def run_verified_helper_promotion_maintenance(
    library: Any,
    *,
    max_entries: int = 8,
    wall_budget_s: float = 60.0,
    preferred_owner_ids: Sequence[str] = (),
    source_theorems: Sequence[str] = (),
    newest_first: bool = False,
    event_callback: Optional[Callable[[dict[str, Any]], Any]] = None,
    cancellation_event: Any = None,
) -> PromotionDrainReport:
    """Run bounded, explicitly invoked publication maintenance.

    Programmatic proof callers can use this after committing their proof
    outcome.  The timer is advisory to the Lean verifier and also bounds new
    admissions: no additional receipt starts after the wall budget expires.
    """

    from .promotion import VerifiedHelperPromoter

    outbox = PromotionOutbox(library)
    owns_cancellation_event = cancellation_event is None
    if cancellation_event is None:
        cancellation_event = threading.Event()
    timer: Optional[threading.Timer] = None
    if owns_cancellation_event and float(wall_budget_s or 0.0) > 0.0:
        timer = threading.Timer(float(wall_budget_s), cancellation_event.set)
        timer.daemon = True
        timer.start()
    try:
        return outbox.drain(
            promoter=VerifiedHelperPromoter(library),
            current_owner_id=str(library.lease_owner.owner_id),
            max_entries=max(1, int(max_entries or 1)),
            preferred_owner_ids=preferred_owner_ids,
            source_theorems=source_theorems,
            newest_first=newest_first,
            event_callback=event_callback,
            cancellation_event=cancellation_event,
        )
    finally:
        if timer is not None:
            timer.cancel()
