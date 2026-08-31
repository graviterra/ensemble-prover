"""Governed facade for reading, verifying, and publishing Mini theory."""

from __future__ import annotations

import json
import subprocess
from functools import wraps
from dataclasses import dataclass, replace
from pathlib import Path
from threading import Event, RLock
from typing import Any, Callable, Iterable, Literal, Mapping, Optional, TypeVar

from .context import TheoryContextPair
from .environment import dependency_environment_fingerprint
from .lease import TheoryLeaseOwner
from .model import (
    MINI_THEORY_SCHEMA_VERSION,
    THEORY_POLICY_VERSION,
    PublishedTheoryBundle,
    TheoryBundleCandidate,
    TheoryVerificationReceipt,
    content_hash,
)
from .need_store import TheoryNeedStore
from .retrieval import MiniTheoryRetriever, TheorySearchHit
from .store import (
    ReadOnlyTheoryStore,
    TheoryStore,
    TheoryStoreError,
    TheoryStorePublicationCommitted,
)
from .verifier import TheoryBundleVerifier, TheoryVerificationResult


TheoryMode = Literal["off", "read", "build"]
_T = TypeVar("_T")


def _serialized_library_operation(
    method: Callable[..., _T],
) -> Callable[..., _T]:
    """Serialize refresh plus every consumer of its mutable indexes."""

    @wraps(method)
    def wrapped(self: "MiniTheoryLibrary", *args: Any, **kwargs: Any) -> _T:
        with self.operation_lock:
            return method(self, *args, **kwargs)

    return wrapped


@dataclass(frozen=True)
class TheoryPublishResult:
    verification: TheoryVerificationResult
    bundle: Optional[PublishedTheoryBundle] = None

    @property
    def published(self) -> bool:
        return self.bundle is not None


class MiniTheoryLibrary:
    """Single policy boundary for persistent theory state.

    ``off`` never reads or writes theory, ``read`` may retrieve/import already
    verified bundles, and ``build`` additionally permits verify-and-publish.
    No caller can publish a candidate without an accepted independent Lean
    receipt from this library's verifier.
    """

    schema_version = MINI_THEORY_SCHEMA_VERSION
    policy_version = THEORY_POLICY_VERSION

    def __init__(
        self,
        *,
        root: Path,
        lean_project_dir: Path,
        mode: TheoryMode = "read",
        verifier_timeout_s: float = 180.0,
        attempt_scope_id: str = "",
    ) -> None:
        if mode not in {"off", "read", "build"}:
            raise ValueError(f"unsupported Mini theory mode: {mode!r}")
        self.mode: TheoryMode = mode
        requested_root = Path(root).expanduser()
        # ``Path.resolve`` consults the filesystem to resolve symlinks.  Off
        # mode must not even read the configured theory path, so use purely
        # lexical absolutization until a persistent mode is selected.
        self.root = (
            requested_root.absolute()
            if self.mode == "off"
            else requested_root.resolve()
        )
        # ``off`` is a true subsystem boundary, not merely a runtime policy
        # checked after persistent resources have already been opened.  Keep
        # the public no-op/fail-closed methods usable while avoiding even the
        # environment fingerprint and store/lease constructors: each of those
        # reads or creates theory state.
        self.environment_key = ""
        self.lease_owner: Optional[TheoryLeaseOwner] = None
        self._store: Optional[TheoryStore] = None
        self.store: Optional[ReadOnlyTheoryStore] = None
        self.needs: Optional[TheoryNeedStore] = None
        self.verifier: Optional[TheoryBundleVerifier] = None
        self.retriever: Optional[MiniTheoryRetriever] = None
        self._bound_lean_toolchain = ""
        self._bound_environment_fingerprint = ""
        self.operation_lock = RLock()
        if self.mode == "off":
            return
        project = Path(lean_project_dir).expanduser().resolve()
        self._bound_lean_toolchain = self._read_toolchain(project)
        self._bound_environment_fingerprint = dependency_environment_fingerprint(
            project
        )
        self.environment_key = self._environment_storage_key(
            lean_toolchain=self._bound_lean_toolchain,
            environment_fingerprint=self._bound_environment_fingerprint,
        )
        environment_root = self.root / "environments" / f"E_{self.environment_key}"
        self.lease_owner = TheoryLeaseOwner(environment_root)
        try:
            self._store = TheoryStore(
                environment_root,
                lease_owner=self.lease_owner,
            )
            self.store = ReadOnlyTheoryStore(self._store)
            self.needs = TheoryNeedStore(
                self.store.root,
                lease_owner=self.lease_owner,
                attempt_scope_id=attempt_scope_id,
            )
            self.verifier = TheoryBundleVerifier(
                lean_project_dir=Path(lean_project_dir),
                store=self._store,
                timeout_s=verifier_timeout_s,
            )
            self.retriever = MiniTheoryRetriever(self._store)
            self.recover_abandoned_build_attempts()
            self.reconcile_need_contexts()
        except BaseException as primary_error:
            try:
                self.lease_owner.close()
            except BaseException as cleanup_error:
                primary_error.add_note(
                    "mini theory library lease cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise

    def close(self) -> None:
        if self.lease_owner is not None:
            self.lease_owner.close()

    def recover_abandoned_build_attempts(self, *, need_id: str = "") -> int:
        """CAS-reconcile build leases whose owner process is provably dead."""

        if self.mode == "off":
            return 0
        assert self.needs is not None
        assert self.store is not None
        recovered = 0
        for record in self.needs.abandoned_build_attempts(need_id=need_id):
            bundle = None
            if record.active_attempt_bundle_id:
                try:
                    bundle = self.store.load(
                        record.active_attempt_bundle_id,
                        domain=record.need.domain,
                    )
                except TheoryStoreError:
                    bundle = None
            if bundle is not None:
                _, applied = self.needs.settle_build_attempt(
                    record.need.need_id,
                    record.active_attempt_id,
                    status="context_available",
                    diagnostic="recovered_verified_publication_after_owner_exit",
                    bundle_id=bundle.bundle_id,
                )
            else:
                _, applied = self.needs.release_build_attempt(
                    record.need.need_id,
                    record.active_attempt_id,
                    diagnostic="recovered_abandoned_theory_build_attempt",
                )
            recovered += int(applied)
        return recovered

    @_serialized_library_operation
    def search(self, query_text: str, **kwargs: object) -> list[TheorySearchHit]:
        if self.mode == "off":
            return []
        assert self.retriever is not None
        snapshot = self._environment_bundle_snapshot()
        self._refresh_retriever_from_bundles(snapshot[2].values())
        hits = self.retriever.search(query_text, **kwargs)  # type: ignore[arg-type]
        compatible: list[TheorySearchHit] = []
        # The environment/store view is hit-independent: every bundle in this
        # env-keyed bucket was publish-gated against the same bound
        # environment.  Snapshot once for the whole result set.
        for hit in hits:
            try:
                self._require_environment_compatible(
                    (hit.bundle_id,),
                    snapshot=snapshot,
                )
            except TheoryStoreError:
                continue
            compatible.append(hit)
        return compatible

    @_serialized_library_operation
    def search_partitions(
        self,
        query_text: str,
        *,
        partitions: Mapping[str, Iterable[str]],
        **kwargs: object,
    ) -> dict[str, object]:
        """Score independent partitions from one live verified store snapshot."""

        if self.mode == "off":
            return {"hits": {}, "bundle_snapshots": {}, "bundle_ids": {}}
        assert self.retriever is not None
        environment_snapshot = self._environment_bundle_snapshot()
        bundles = environment_snapshot[2]
        self._refresh_retriever_from_bundles(bundles.values())
        normalized = {
            str(name): {
                str(item or "").strip()
                for item in bundle_ids
                if str(item or "").strip()
            }
            for name, bundle_ids in partitions.items()
        }
        baseline = normalized.get("baseline", set())
        recovered = normalized.get("recovered", set())
        recovered.difference_update(baseline)
        concurrent = normalized.setdefault("concurrent", set())
        concurrent.difference_update(baseline, recovered)
        concurrent.update(set(bundles).difference(baseline, recovered))
        hits_by_partition: dict[str, list[TheorySearchHit]] = {}
        snapshots_by_bundle: dict[str, tuple[dict[str, object], ...]] = {}
        for name, eligible in normalized.items():
            hits = self.retriever.search(
                query_text,
                **kwargs,  # type: ignore[arg-type]
                eligible_bundle_ids=tuple(eligible),
            )
            compatible: list[TheorySearchHit] = []
            for hit in hits:
                try:
                    self._require_environment_compatible(
                        (hit.bundle_id,),
                        snapshot=environment_snapshot,
                    )
                except TheoryStoreError:
                    continue
                compatible.append(hit)
                snapshots_by_bundle[hit.bundle_id] = (
                    self._provenance_snapshot(
                        (hit.bundle_id,),
                        environment_snapshot=environment_snapshot,
                    )
                )
            hits_by_partition[name] = compatible
        return {
            "hits": hits_by_partition,
            "bundle_snapshots": snapshots_by_bundle,
            "bundle_ids": {
                name: tuple(sorted(bundle_ids))
                for name, bundle_ids in normalized.items()
            },
        }

    @_serialized_library_operation
    def prepare_context(
        self,
        context: TheoryContextPair,
        *,
        bundle_ids: Iterable[str],
    ) -> tuple[TheoryContextPair, tuple[dict[str, object], ...]]:
        """Select and attest one context from a single store snapshot."""

        selected_ids = tuple(
            dict.fromkeys(
                str(item or "").strip()
                for item in bundle_ids
                if str(item or "").strip()
            )
        )
        if self.mode == "off":
            return context, ()
        active_ids = tuple(context.lean.bundle_ids)
        if not selected_ids and not active_ids:
            return context, ()
        assert self.retriever is not None
        environment_snapshot = self._environment_bundle_snapshot()
        self._refresh_retriever_from_bundles(environment_snapshot[2].values())
        if not selected_ids:
            self._require_environment_compatible(
                active_ids,
                snapshot=environment_snapshot,
            )
            return context, self._provenance_snapshot(
                active_ids,
                environment_snapshot=environment_snapshot,
            )
        modules = self.retriever.required_modules(selected_ids)
        bundles_by_module = {
            bundle.module_name: bundle
            for bundle in environment_snapshot[2].values()
        }
        active_bundle_ids = tuple(
            bundles_by_module[module].bundle_id for module in modules
        )
        inventory = tuple(
            f"{declaration.fq_name} : {declaration.type_text}"
            for module in modules
            for declaration in bundles_by_module[module].declarations
        )
        selected = context.with_theory(
            modules=modules,
            bundle_ids=active_bundle_ids,
            inventory=inventory,
        )
        self._require_environment_compatible(
            selected.lean.bundle_ids,
            snapshot=environment_snapshot,
        )
        return selected, self._provenance_snapshot(
            selected.lean.bundle_ids,
            environment_snapshot=environment_snapshot,
        )

    @_serialized_library_operation
    def select_context(
        self,
        context: TheoryContextPair,
        *,
        bundle_ids: Iterable[str],
    ) -> TheoryContextPair:
        selected = tuple(dict.fromkeys(str(item).strip() for item in bundle_ids if str(item).strip()))
        if not selected or self.mode == "off":
            return context
        assert self.retriever is not None
        assert self.store is not None
        snapshot = self._environment_bundle_snapshot()
        self._refresh_retriever_from_bundles(snapshot[2].values())
        self._require_environment_compatible(selected, snapshot=snapshot)
        modules = self.retriever.required_modules(selected)
        # Reuse the single snapshot for the module map: a second disk scan
        # here could observe a different store state than the compatibility
        # check just used.
        bundles_by_module = {
            bundle.module_name: bundle for bundle in snapshot[2].values()
        }
        active_bundle_ids = tuple(
            bundles_by_module[module].bundle_id for module in modules
        )
        inventory = tuple(
            f"{declaration.fq_name} : {declaration.type_text}"
            for module in modules
            for declaration in bundles_by_module[module].declarations
        )
        return context.with_theory(
            modules=modules,
            # `modules` is dependency-closed.  Availability must use the same
            # closure or imported dependency declarations are falsely hidden.
            bundle_ids=active_bundle_ids,
            inventory=inventory,
        )

    def verify_and_publish(
        self,
        candidate: TheoryBundleCandidate,
        *,
        cancellation_event: Optional[Event] = None,
    ) -> TheoryPublishResult:
        if self.mode != "build":
            raise TheoryStoreError("theory publication requires mode='build'")
        verification = self.verify_candidate(
            candidate,
            cancellation_event=cancellation_event,
        )
        return self.publish_verified(
            candidate,
            verification,
            cancellation_event=cancellation_event,
        )

    def verify_candidate(
        self,
        candidate: TheoryBundleCandidate,
        *,
        cancellation_event: Optional[Event] = None,
        forbidden_target_statements: Iterable[str] = (),
    ) -> TheoryVerificationResult:
        if self.mode != "build":
            raise TheoryStoreError("theory verification requires mode='build'")
        assert self.verifier is not None
        environment_error = self._bound_environment_error()
        if environment_error:
            return TheoryVerificationResult(
                receipt=self.verifier._rejected(
                    candidate,
                    environment_error,
                ).receipt
            )
        verify_kwargs: dict[str, Any] = {
            "cancellation_event": cancellation_event,
        }
        clean_forbidden_targets = tuple(
            str(statement or "").strip()
            for statement in forbidden_target_statements
            if str(statement or "").strip()
        )
        if clean_forbidden_targets:
            verify_kwargs["forbidden_target_statements"] = clean_forbidden_targets
        verification = self.verifier.verify(candidate, **verify_kwargs)
        if not verification.accepted:
            return verification
        if (
            not verification.receipt.lean_toolchain
            or not verification.receipt.mathlib_revision
        ):
            return replace(
                verification,
                receipt=replace(
                    verification.receipt,
                    accepted=False,
                    diagnostic="verification_environment_fingerprint_unavailable",
                ),
                compiled_artifact=b"",
            )
        return verification

    @_serialized_library_operation
    def reuse_published_candidate(
        self,
        candidate: TheoryBundleCandidate,
        *,
        helper_name: str,
        cancellation_event: Optional[Event] = None,
    ) -> Optional[TheoryPublishResult]:
        """Return an exact durable bundle without invoking Lean again."""

        if self.mode != "build":
            raise TheoryStoreError("theory publication requires mode='build'")
        assert self.store is not None
        assert self.retriever is not None
        if cancellation_event is not None and cancellation_event.is_set():
            raise TheoryStoreError("theory publication cancelled")
        if self.publication_preflight_error():
            return None
        bundle = self.store.load(candidate.bundle_id, domain=candidate.domain)
        if bundle is None:
            return None
        declarations = tuple(bundle.declarations)
        exact_declarations = tuple(
            declaration
            for declaration in declarations
            if declaration.fq_name.rsplit(".", 1)[-1] == helper_name
        )
        if not (
            bundle.bundle_id == candidate.bundle_id
            and bundle.domain == candidate.domain
            and bundle.module_name == candidate.module_name
            and bundle.namespace == candidate.namespace
            and bundle.source_hash == candidate.source_hash
            and bundle.imports == candidate.imports
            and bundle.dependency_bundle_ids == candidate.dependency_bundle_ids
            and bundle.policy_version == THEORY_POLICY_VERSION
            and bundle.lean_toolchain == self._bound_lean_toolchain
            and bundle.mathlib_revision == self._bound_environment_fingerprint
            and exact_declarations == declarations
            and len(declarations) == 1
            and bool(bundle.compiled_artifact_hash)
        ):
            return None
        try:
            self.retriever.required_modules((bundle.bundle_id,))
        except TheoryStoreError:
            # The bundle may have been published by another process after
            # this library initialized. Refresh the consumer index before
            # reporting it as reusable.
            self._refresh_retriever()
            self.retriever.required_modules((bundle.bundle_id,))
        if cancellation_event is not None and cancellation_event.is_set():
            raise TheoryStoreError("theory publication cancelled")
        if self.publication_preflight_error():
            return None
        verification = TheoryVerificationResult(
            receipt=TheoryVerificationReceipt(
                accepted=True,
                bundle_id=candidate.bundle_id,
                module_name=candidate.module_name,
                source_hash=candidate.source_hash,
                declarations=declarations,
                lean_toolchain=bundle.lean_toolchain,
                mathlib_revision=bundle.mathlib_revision,
                policy_version=bundle.policy_version,
                verification_output_hash=bundle.verification_output_hash,
                compiled_artifact_hash=bundle.compiled_artifact_hash,
                diagnostic="verified_existing_bundle",
            )
        )
        return TheoryPublishResult(verification=verification, bundle=bundle)

    @_serialized_library_operation
    def publish_verified(
        self,
        candidate: TheoryBundleCandidate,
        verification: TheoryVerificationResult,
        *,
        cancellation_event: Optional[Event] = None,
    ) -> TheoryPublishResult:
        if self.mode != "build":
            raise TheoryStoreError("theory publication requires mode='build'")
        assert self.verifier is not None
        assert self._store is not None
        assert self.retriever is not None
        if not verification.accepted:
            return TheoryPublishResult(verification=verification)
        if cancellation_event is not None and cancellation_event.is_set():
            raise TheoryStoreError("theory publication cancelled")
        if not self.verifier.validates_publication(candidate, verification):
            raise TheoryStoreError(
                "theory verification result was not issued by this library"
            )
        environment_error = self._bound_environment_error()
        if environment_error:
            raise TheoryStoreError(environment_error)
        if (
            verification.receipt.lean_toolchain != self._bound_lean_toolchain
            or verification.receipt.mathlib_revision
            != self._bound_environment_fingerprint
        ):
            raise TheoryStoreError(
                "theory verification environment does not match library storage bucket"
            )
        try:
            bundle = self._store.publish_verified(
                candidate,
                verification,
                verifier=self.verifier,
            )
        except TheoryStorePublicationCommitted as exc:
            raise TheoryStorePublicationCommitted(
                exc.bundle,
                str(exc),
                cause=exc.cause,
                verification=verification,
            ) from exc
        try:
            self.retriever.refresh()
        except BaseException as exc:
            raise TheoryStorePublicationCommitted(
                bundle,
                "theory publication committed before retrieval index refresh "
                f"failed: {type(exc).__name__}: {exc}",
                cause=exc,
                verification=verification,
            ) from exc
        return TheoryPublishResult(verification=verification, bundle=bundle)

    @staticmethod
    def _read_toolchain(project: Path) -> str:
        try:
            return (project / "lean-toolchain").read_text(
                encoding="utf-8"
            ).strip()
        except OSError:
            return ""

    @staticmethod
    def _environment_storage_key(
        *,
        lean_toolchain: str,
        environment_fingerprint: str,
    ) -> str:
        payload = json.dumps(
            {
                "schema_version": MINI_THEORY_SCHEMA_VERSION,
                "policy_version": THEORY_POLICY_VERSION,
                "lean_toolchain": lean_toolchain,
                "mathlib_revision": environment_fingerprint,
            },
            sort_keys=True,
            separators=(",", ":"),
        )
        return content_hash(payload, length=16)

    def _bound_environment_error(self) -> str:
        if self.mode == "off":
            return "theory_library_disabled"
        assert self.verifier is not None
        project = self.verifier.lean_project_dir
        current_toolchain = self._read_toolchain(project)
        current_fingerprint = dependency_environment_fingerprint(project)
        if not self._bound_lean_toolchain or not self._bound_environment_fingerprint:
            return "theory_library_environment_unresolved_at_initialization"
        if (
            current_toolchain != self._bound_lean_toolchain
            or current_fingerprint != self._bound_environment_fingerprint
        ):
            return "theory_library_environment_changed_since_initialization"
        return ""

    def publication_preflight_error(self) -> str:
        """Return why a build is guaranteed to reject before spending LLM cost."""

        if self.mode != "build":
            return "theory_publication_requires_build_mode"
        return self._bound_environment_error()

    def activate_lean_runner(self, lean: object) -> None:
        """Expose verified store artifacts to every subsequent Lean check."""

        if self.mode == "off":
            return
        assert self.store is not None
        assert self.verifier is not None
        cfg = getattr(lean, "cfg", None)
        if cfg is None:
            raise TheoryStoreError("Lean runner has no mutable configuration")
        configured_backend = str(getattr(cfg, "backend_mode", "") or "").strip()
        if configured_backend == "persistent_process":
            if getattr(lean, "_persistent_pool", None) is not None:
                raise TheoryStoreError(
                    "activate Mini theory before starting persistent Lean workers"
                )
            # Persistent workers do not accept dynamic module roots. Theory
            # runs use the supported cached subprocess backend so every check
            # shares the exact verified LEAN_PATH.
            setattr(cfg, "backend_mode", "env_cached_subprocess")
        configured = list(getattr(cfg, "module_search_paths", ()) or ())
        modules_root = str(self.store.modules_root.resolve())
        if modules_root not in configured:
            if getattr(lean, "_repl", None) is not None:
                raise TheoryStoreError(
                    "activate Mini theory before initializing the Lean REPL"
                )
            configured.append(modules_root)
            setattr(cfg, "module_search_paths", configured)
        if not str(getattr(cfg, "resolved_lean_path", "") or "").strip():
            project = self.verifier.lean_project_dir
            try:
                lean_path_run = subprocess.run(
                    ["lake", "env", "printenv", "LEAN_PATH"],
                    cwd=project,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    check=False,
                )
                lean_bin_run = subprocess.run(
                    ["lake", "env", "which", "lean"],
                    cwd=project,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    check=False,
                )
            except OSError as exc:
                raise TheoryStoreError(
                    f"could not resolve Lean environment for theory activation: {exc}"
                ) from exc
            lean_path = lean_path_run.stdout.strip()
            lean_bin = lean_bin_run.stdout.strip()
            if (
                lean_path_run.returncode != 0
                or lean_bin_run.returncode != 0
                or not lean_path
                or not lean_bin
            ):
                diagnostic = (
                    lean_path_run.stderr.strip()
                    or lean_bin_run.stderr.strip()
                    or "Lake environment resolution failed"
                )
                raise TheoryStoreError(
                    "could not resolve Lean environment for theory activation: "
                    + diagnostic
                )
            bind_environment = getattr(
                lean,
                "bind_resolved_lean_environment",
                None,
            )
            if callable(bind_environment):
                bind_environment(lean_path, lean_bin)
            else:
                setattr(cfg, "resolved_lean_path", lean_path)
                setattr(cfg, "resolved_lean_executable", lean_bin)

    @_serialized_library_operation
    def snapshot(self, bundle_ids: Iterable[str]) -> tuple[dict[str, object], ...]:
        """Return exact immutable provenance for a dependency-closed selection."""

        if self.mode == "off":
            return ()
        assert self.store is not None
        assert self.retriever is not None
        selected = tuple(dict.fromkeys(str(item).strip() for item in bundle_ids if str(item).strip()))
        if not selected:
            return ()
        environment_snapshot = self._environment_bundle_snapshot()
        self._refresh_retriever_from_bundles(environment_snapshot[2].values())
        self._require_environment_compatible(
            selected,
            snapshot=environment_snapshot,
        )
        return self._provenance_snapshot(
            selected,
            environment_snapshot=environment_snapshot,
        )

    def _provenance_snapshot(
        self,
        bundle_ids: Iterable[str],
        *,
        environment_snapshot: tuple[
            str,
            str,
            dict[str, PublishedTheoryBundle],
        ],
    ) -> tuple[dict[str, object], ...]:
        """Build dependency-closed provenance from an existing store view."""

        assert self.retriever is not None
        ordered_modules = self.retriever.required_modules(bundle_ids)
        by_module = {
            bundle.module_name: bundle
            for bundle in environment_snapshot[2].values()
        }
        return tuple(
            {
                "bundle_id": by_module[module].bundle_id,
                "module_name": module,
                "source_hash": by_module[module].source_hash,
                "compiled_artifact_hash": by_module[module].compiled_artifact_hash,
                "lean_toolchain": by_module[module].lean_toolchain,
                "mathlib_revision": by_module[module].mathlib_revision,
                "policy_version": by_module[module].policy_version,
            }
            for module in ordered_modules
        )

    def _refresh_retriever(self) -> None:
        if self.mode == "off":
            return
        assert self.retriever is not None
        try:
            self.retriever.refresh()
        except TheoryStoreError:
            raise
        except Exception as exc:
            raise TheoryStoreError(
                "could not refresh Mini theory retrieval index: "
                f"{type(exc).__name__}: {exc}"
            ) from exc

    def _refresh_retriever_from_bundles(
        self,
        bundles: Iterable[PublishedTheoryBundle],
    ) -> None:
        """Refresh from a caller-owned snapshot with the public error contract."""

        if self.mode == "off":
            return
        assert self.retriever is not None
        try:
            self.retriever.refresh_from_bundles(bundles)
        except TheoryStoreError:
            raise
        except Exception as exc:
            raise TheoryStoreError(
                "could not refresh Mini theory retrieval index: "
                f"{type(exc).__name__}: {exc}"
            ) from exc

    def integrity_issues(self) -> tuple[dict[str, str], ...]:
        if self.mode == "off":
            return ()
        assert self.store is not None
        assert self.needs is not None
        return tuple(
            {"area": "bundle", **issue} for issue in self.store.integrity_issues()
        ) + tuple(
            {"area": "need", **issue} for issue in self.needs.integrity_issues()
        )

    def reconcile_need_contexts(self) -> tuple[str, ...]:
        """Reopen needs whose consumer-validated bundle closure is unusable."""

        if self.mode == "off":
            return ()
        assert self.needs is not None
        invalidated: list[str] = []
        for record in tuple(self.needs.iter_records()):
            if record.status not in {"resolved", "context_available"}:
                continue
            bundle_ids = tuple(record.validated_bundle_ids or ()) or (
                (record.bundle_id,) if record.bundle_id else ()
            )
            try:
                if not bundle_ids:
                    raise TheoryStoreError("need has no validated theory bundles")
                self.snapshot(bundle_ids)
            except TheoryStoreError as exc:
                _reopened, changed = self.needs.invalidate_context(
                    record.need.need_id,
                    diagnostic=f"validated_theory_context_unusable:{exc}",
                    expected_record=record,
                )
                if changed:
                    invalidated.append(record.need.need_id)
        return tuple(invalidated)

    def _environment_bundle_snapshot(
        self,
    ) -> tuple[str, str, dict[str, PublishedTheoryBundle]]:
        """One point-in-time view of the live environment and store contents.

        Environment fingerprinting spawns git subprocesses per Lake package
        and the store scan re-verifies every bundle's hashes, so public
        operations must compute this once and reuse it for every bundle they
        check — never once per hit.  The snapshot is intentionally scoped to a
        single serialized operation; it is never cached across operations, so
        every public call still observes the live environment.
        """

        assert self.verifier is not None
        assert self.store is not None
        current_toolchain = self.verifier._lean_toolchain()
        current_mathlib = self.verifier._mathlib_revision()
        bundles = {bundle.bundle_id: bundle for bundle in self.store.iter_bundles()}
        return current_toolchain, current_mathlib, bundles

    def _require_environment_compatible(
        self,
        bundle_ids: Iterable[str],
        *,
        snapshot: Optional[
            tuple[str, str, dict[str, PublishedTheoryBundle]]
        ] = None,
    ) -> None:
        if self.mode == "off":
            return
        if snapshot is None:
            snapshot = self._environment_bundle_snapshot()
        current_toolchain, current_mathlib, bundles = snapshot
        pending = list(bundle_ids)
        seen: set[str] = set()
        while pending:
            bundle_id = str(pending.pop() or "").strip()
            if not bundle_id or bundle_id in seen:
                continue
            bundle = bundles.get(bundle_id)
            if bundle is None:
                raise TheoryStoreError(f"missing theory bundle {bundle_id}")
            if not bundle.lean_toolchain or bundle.lean_toolchain != current_toolchain:
                raise TheoryStoreError(
                    f"incompatible Lean toolchain for theory bundle {bundle_id}"
                )
            if not bundle.mathlib_revision or bundle.mathlib_revision != current_mathlib:
                raise TheoryStoreError(
                    f"incompatible Mathlib revision for theory bundle {bundle_id}"
                )
            if bundle.policy_version != THEORY_POLICY_VERSION:
                raise TheoryStoreError(
                    f"incompatible theory policy for bundle {bundle_id}"
                )
            seen.add(bundle_id)
            pending.extend(bundle.dependency_bundle_ids)
