"""Content-addressed, atomic storage for verified Mini theory bundles."""

from __future__ import annotations

import fcntl
import json
import os
import re
import shutil
import tempfile
import time
from dataclasses import replace
from pathlib import Path
from typing import TYPE_CHECKING, Any, BinaryIO, Iterator, Optional

from .lease import TheoryLeaseOwner
from .model import (
    MINI_THEORY_SCHEMA_VERSION,
    THEORY_POLICY_VERSION,
    PublishedTheoryBundle,
    TheoryBundleCandidate,
    TheoryVerificationReceipt,
    content_hash,
)

if TYPE_CHECKING:
    from .verifier import TheoryBundleVerifier, TheoryVerificationResult


class TheoryStoreError(RuntimeError):
    pass


class TheoryStoreConflict(TheoryStoreError):
    pass


class TheoryStorePublicationCommitted(TheoryStoreError):
    """Publication became durable before a later operation failed."""

    def __init__(
        self,
        bundle: PublishedTheoryBundle,
        detail: str,
        *,
        cause: Optional[BaseException] = None,
        verification: Optional[Any] = None,
    ) -> None:
        super().__init__(detail)
        self.bundle = bundle
        self.cause = cause
        self.verification = verification


class _ExclusiveStoreLock:
    """Exclusive store flock whose cleanup preserves a body BaseException."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.handle: Optional[BinaryIO] = None

    @staticmethod
    def _release(
        handle: BinaryIO,
        *,
        primary: Optional[BaseException] = None,
    ) -> None:
        cleanup_errors: list[BaseException] = []
        for cleanup in (
            lambda: fcntl.flock(handle.fileno(), fcntl.LOCK_UN),
            handle.close,
        ):
            try:
                cleanup()
            except BaseException as cleanup_error:
                cleanup_errors.append(cleanup_error)
        if primary is not None:
            for cleanup_error in cleanup_errors:
                primary.add_note(
                    "Mini theory store-lock cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            return
        if cleanup_errors:
            first = next(
                (
                    cleanup_error
                    for cleanup_error in cleanup_errors
                    if not isinstance(cleanup_error, Exception)
                ),
                cleanup_errors[0],
            )
            for cleanup_error in cleanup_errors:
                if cleanup_error is first:
                    continue
                first.add_note(
                    "Mini theory store-lock cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise first

    def __enter__(self) -> "_ExclusiveStoreLock":
        self.handle = self.path.open("a+b")
        try:
            fcntl.flock(self.handle.fileno(), fcntl.LOCK_EX)
        except BaseException as primary:
            self._release(self.handle, primary=primary)
            raise
        return self

    def __exit__(self, _exc_type, exc, _traceback) -> bool:
        assert self.handle is not None
        self._release(self.handle, primary=exc)
        return False


class ReadOnlyTheoryStore:
    """Read-only store surface exposed outside the governed library."""

    def __init__(self, store: "TheoryStore") -> None:
        self.__store = store

    @property
    def root(self) -> Path:
        return self.__store.root

    @property
    def modules_root(self) -> Path:
        return self.__store.modules_root

    def bundle_dir(self, *args: object, **kwargs: object) -> Path:
        return self.__store.bundle_dir(*args, **kwargs)  # type: ignore[arg-type]

    def source_path(self, bundle: PublishedTheoryBundle) -> Path:
        return self.__store.source_path(bundle)

    def manifest_path(self, bundle: PublishedTheoryBundle) -> Path:
        return self.__store.manifest_path(bundle)

    def artifact_path(self, bundle: PublishedTheoryBundle) -> Path:
        return self.__store.artifact_path(bundle)

    def load(
        self,
        bundle_id: str,
        *,
        domain: str,
    ) -> Optional[PublishedTheoryBundle]:
        return self.__store.load(bundle_id, domain=domain)

    def iter_bundles(self) -> Iterator[PublishedTheoryBundle]:
        return self.__store.iter_bundles()

    def integrity_issues(self) -> tuple[dict[str, str], ...]:
        return self.__store.integrity_issues()


class TheoryStore:
    """Persist verified bundles as immutable, atomically visible directories."""

    SOURCE_FILENAME = "Theory.lean"
    ARTIFACT_FILENAME = "Theory.olean"
    MANIFEST_FILENAME = "manifest.json"

    def __init__(
        self,
        root: Path,
        *,
        lease_owner: Optional[TheoryLeaseOwner] = None,
    ) -> None:
        self.root = Path(root).expanduser().resolve()
        self.modules_root = self.root / "modules"
        self.staging_root = self.root / "staging"
        self.lock_path = self.root / ".publish.lock"
        self.modules_root.mkdir(parents=True, exist_ok=True)
        self.staging_root.mkdir(parents=True, exist_ok=True)
        owns_lease_owner = lease_owner is None
        self.lease_owner = lease_owner or TheoryLeaseOwner(self.root)
        try:
            self.owner_staging_root = self.staging_root / self.lease_owner.owner_id
            self.recover_abandoned_staging()
            self.owner_staging_root.mkdir(parents=True, exist_ok=True)
        except BaseException as primary_error:
            if owns_lease_owner:
                try:
                    self.lease_owner.close()
                except BaseException as cleanup_error:
                    primary_error.add_note(
                        "theory store lease cleanup also failed: "
                        f"{type(cleanup_error).__name__}: {cleanup_error}"
                    )
            raise

    def recover_abandoned_staging(self) -> tuple[str, ...]:
        """Remove only staging owned by a provably dead process."""

        recovered: list[str] = []
        with self._publish_lock():
            for path in tuple(self.staging_root.iterdir()):
                if not path.is_dir() or path.is_symlink():
                    continue
                if not TheoryLeaseOwner._valid_owner_id(path.name):
                    continue
                if self.lease_owner.owner_abandoned(path.name) is not True:
                    continue
                shutil.rmtree(path, ignore_errors=True)
                if not path.exists():
                    recovered.append(path.name)
            if recovered:
                self._fsync_dir(self.staging_root)
        return tuple(recovered)

    def bundle_dir(self, candidate_or_bundle: TheoryBundleCandidate | PublishedTheoryBundle | str, *, domain: str = "") -> Path:
        if isinstance(candidate_or_bundle, str):
            bundle_id = candidate_or_bundle
            if re.fullmatch(r"[0-9a-f]{16}", bundle_id) is None:
                raise ValueError(f"invalid theory bundle id: {bundle_id!r}")
            if not domain:
                raise ValueError("domain is required when looking up a bundle id")
            from .model import sanitize_module_segment

            domain_segment = sanitize_module_segment(domain)
        else:
            bundle_id = candidate_or_bundle.bundle_id
            from .model import sanitize_module_segment

            domain_segment = sanitize_module_segment(candidate_or_bundle.domain)
        return (
            self.modules_root
            / "MiniTheory"
            / "Domains"
            / domain_segment
            / "Bundles"
            / f"B_{bundle_id}"
        )

    def source_path(self, bundle: PublishedTheoryBundle) -> Path:
        return self.bundle_dir(bundle) / self.SOURCE_FILENAME

    def manifest_path(self, bundle: PublishedTheoryBundle) -> Path:
        return self.bundle_dir(bundle) / self.MANIFEST_FILENAME

    def artifact_path(self, bundle: PublishedTheoryBundle) -> Path:
        return self.bundle_dir(bundle) / self.ARTIFACT_FILENAME

    def publish_verified(
        self,
        candidate: TheoryBundleCandidate,
        verification: "TheoryVerificationResult",
        *,
        verifier: "TheoryBundleVerifier",
        created_ts: Optional[float] = None,
    ) -> PublishedTheoryBundle:
        """Persist only a result sealed by the exact independent verifier."""

        from .verifier import TheoryBundleVerifier

        if (
            type(verifier) is not TheoryBundleVerifier
            or verifier.store is not self
            or not verifier.validates_publication(candidate, verification)
        ):
            raise TheoryStoreError(
                "theory verification result lacks verifier-issued authority"
            )
        return self.__persist_verified(
            candidate,
            verification.receipt,
            compiled_artifact=verification.compiled_artifact,
            created_ts=created_ts,
        )

    def __persist_verified(
        self,
        candidate: TheoryBundleCandidate,
        receipt: TheoryVerificationReceipt,
        *,
        compiled_artifact: Optional[Path | bytes] = None,
        created_ts: Optional[float] = None,
    ) -> PublishedTheoryBundle:
        self._validate_receipt(candidate, receipt)
        published = PublishedTheoryBundle(
            schema_version=MINI_THEORY_SCHEMA_VERSION,
            bundle_id=candidate.bundle_id,
            domain=candidate.domain,
            module_name=candidate.module_name,
            namespace=candidate.namespace,
            source_hash=candidate.source_hash,
            imports=candidate.imports,
            dependency_bundle_ids=candidate.dependency_bundle_ids,
            # Need satisfaction is consumer-validated mutable state in
            # TheoryNeedStore, not a self-asserted property of immutable Lean
            # content.  Identical content therefore has one stable manifest.
            satisfies_need_ids=(),
            declarations=receipt.declarations,
            lean_toolchain=receipt.lean_toolchain,
            mathlib_revision=receipt.mathlib_revision,
            policy_version=receipt.policy_version,
            verification_output_hash=receipt.verification_output_hash,
            compiled_artifact_hash=receipt.compiled_artifact_hash,
            generated_by_run=candidate.generated_by_run,
            generated_by_model=candidate.generated_by_model,
            source_theorem=candidate.source_theorem,
            created_ts=float(created_ts if created_ts is not None else time.time()),
        )
        published = replace(
            published,
            manifest_hash=published.computed_manifest_hash(),
        )
        final_dir = self.bundle_dir(published)
        self.recover_abandoned_staging()
        self.owner_staging_root.mkdir(parents=True, exist_ok=True)
        staging_dir = Path(
            tempfile.mkdtemp(
                prefix=f"{candidate.bundle_id}.",
                dir=str(self.owner_staging_root),
            )
        )
        primary: Optional[BaseException] = None
        try:
            source_path = staging_dir / self.SOURCE_FILENAME
            artifact_path = staging_dir / self.ARTIFACT_FILENAME
            manifest_path = staging_dir / self.MANIFEST_FILENAME
            source_path.write_text(candidate.source.rstrip() + "\n", encoding="utf-8")
            if compiled_artifact is None:
                raise TheoryStoreError("verified compiled artifact is required")
            if isinstance(compiled_artifact, bytes):
                artifact_path.write_bytes(compiled_artifact)
            else:
                artifact_source = Path(compiled_artifact)
                if not artifact_source.is_file():
                    raise TheoryStoreError("verified compiled artifact is required")
                shutil.copyfile(artifact_source, artifact_path)
            artifact_hash = content_hash(artifact_path.read_bytes(), length=64)
            if artifact_hash != receipt.compiled_artifact_hash:
                raise TheoryStoreError("compiled artifact hash mismatch")
            manifest_path.write_text(
                json.dumps(published.to_dict(), ensure_ascii=False, sort_keys=True, indent=2)
                + "\n",
                encoding="utf-8",
            )
            self._fsync_file(source_path)
            self._fsync_file(artifact_path)
            self._fsync_file(manifest_path)
            self._fsync_dir(staging_dir)
            final_dir.parent.mkdir(parents=True, exist_ok=True)
            committed_candidate: Optional[PublishedTheoryBundle] = None
            try:
                with self._publish_lock():
                    if final_dir.exists():
                        existing = self.load(
                            candidate.bundle_id,
                            domain=candidate.domain,
                        )
                        # ``verification_output_hash`` is provenance, not
                        # content identity: Lean warning diagnostics embed the
                        # per-run verification tempdir path, so byte-identical
                        # content independently re-verified by another run
                        # hashes differently.  Requiring it here would turn
                        # every cross-run re-publication of identical content
                        # into a permanent conflict.
                        immutable_receipt = (
                            existing is not None
                            and existing.source_hash == candidate.source_hash
                            and existing.compiled_artifact_hash
                            == receipt.compiled_artifact_hash
                            and existing.lean_toolchain == receipt.lean_toolchain
                            and existing.mathlib_revision == receipt.mathlib_revision
                            and existing.policy_version == receipt.policy_version
                            and existing.declarations == receipt.declarations
                        )
                        if not immutable_receipt:
                            raise TheoryStoreConflict(
                                f"bundle {candidate.bundle_id} already exists "
                                "with different verification identity"
                            )
                        committed_candidate = existing
                    else:
                        committed_candidate = published
                        os.replace(staging_dir, final_dir)
                        self._fsync_dir(final_dir.parent)
                        staging_dir = Path()
            except BaseException as exc:
                # Inspect committed state around the whole publish-lock scope,
                # including file-context __exit__/close. A caller must receive
                # exact commit provenance whenever the immutable bundle became
                # durable before that scope returned cleanly.
                committed = None
                try:
                    committed = self.load(
                        candidate.bundle_id,
                        domain=candidate.domain,
                    )
                except (OSError, TheoryStoreError):
                    pass
                if (
                    committed_candidate is not None
                    and committed == committed_candidate
                ):
                    raise TheoryStorePublicationCommitted(
                        committed,
                        "theory publication committed before publish-lock "
                        f"scope returned cleanly: {type(exc).__name__}: {exc}",
                        cause=exc,
                    ) from exc
                raise
            assert committed_candidate is not None
            return committed_candidate
        except BaseException as exc:
            primary = exc
            raise
        finally:
            cleanup_errors: list[BaseException] = []
            try:
                if str(staging_dir) not in {"", "."} and staging_dir.exists():
                    shutil.rmtree(staging_dir, ignore_errors=True)
            except BaseException as cleanup_error:
                cleanup_errors.append(cleanup_error)
            try:
                self.owner_staging_root.rmdir()
            except OSError:
                pass
            except BaseException as cleanup_error:
                cleanup_errors.append(cleanup_error)
            if primary is not None:
                for cleanup_error in cleanup_errors:
                    primary.add_note(
                        "Mini theory staging cleanup also failed: "
                        f"{type(cleanup_error).__name__}: {cleanup_error}"
                    )
            elif cleanup_errors:
                first = next(
                    (
                        cleanup_error
                        for cleanup_error in cleanup_errors
                        if not isinstance(cleanup_error, Exception)
                    ),
                    cleanup_errors[0],
                )
                for cleanup_error in cleanup_errors:
                    if cleanup_error is first:
                        continue
                    first.add_note(
                        "Mini theory staging cleanup also failed: "
                        f"{type(cleanup_error).__name__}: {cleanup_error}"
                    )
                raise first

    def load(self, bundle_id: str, *, domain: str) -> Optional[PublishedTheoryBundle]:
        directory = self.bundle_dir(str(bundle_id or ""), domain=domain)
        manifest_path = directory / self.MANIFEST_FILENAME
        source_path = directory / self.SOURCE_FILENAME
        artifact_path = directory / self.ARTIFACT_FILENAME
        if (
            not manifest_path.is_file()
            or not source_path.is_file()
            or not artifact_path.is_file()
        ):
            return None
        try:
            payload = json.loads(manifest_path.read_text(encoding="utf-8"))
            bundle = PublishedTheoryBundle.from_dict(payload)
        except Exception as exc:
            raise TheoryStoreError(f"invalid theory manifest {manifest_path}: {exc}") from exc
        source = source_path.read_text(encoding="utf-8").strip()
        from .model import sanitize_module_segment

        expected_segment = sanitize_module_segment(domain)
        expected_module = (
            f"MiniTheory.Domains.{expected_segment}.Bundles.B_{bundle_id}.Theory"
        )
        expected_namespace = f"MiniTheory.Domains.{expected_segment}.B_{bundle_id}"
        if (
            bundle.schema_version != MINI_THEORY_SCHEMA_VERSION
            or bundle.bundle_id != bundle_id
            or bundle.domain != domain
            or bundle.module_name != expected_module
            or bundle.namespace != expected_namespace
        ):
            raise TheoryStoreError(f"manifest identity mismatch for bundle {bundle_id}")
        if (
            not bundle.manifest_hash
            or bundle.manifest_hash != bundle.computed_manifest_hash()
        ):
            raise TheoryStoreError(f"manifest hash mismatch for bundle {bundle_id}")
        if content_hash(source, length=64) != bundle.source_hash:
            raise TheoryStoreError(f"source hash mismatch for bundle {bundle.bundle_id}")
        if not self._manifest_matches_content_identity(bundle, source):
            raise TheoryStoreError(
                f"manifest content identity mismatch for bundle {bundle_id}"
            )
        if content_hash(artifact_path.read_bytes(), length=64) != bundle.compiled_artifact_hash:
            raise TheoryStoreError(f"compiled artifact hash mismatch for bundle {bundle.bundle_id}")
        return bundle

    def iter_bundles(self) -> Iterator[PublishedTheoryBundle]:
        for directory in self._bundle_directories():
            manifest_path = directory / self.MANIFEST_FILENAME
            try:
                expected_id = self._bundle_id_from_directory(directory)
                payload = json.loads(manifest_path.read_text(encoding="utf-8"))
                bundle = PublishedTheoryBundle.from_dict(payload)
                loaded = self.load(expected_id, domain=bundle.domain)
                if loaded is None:
                    continue
            except Exception:
                continue
            yield loaded

    def integrity_issues(self) -> tuple[dict[str, str], ...]:
        """Return explicit diagnostics for every non-loadable bundle directory."""

        issues: list[dict[str, str]] = []
        for directory in self._bundle_directories():
            manifest_path = directory / self.MANIFEST_FILENAME
            try:
                expected_id = self._bundle_id_from_directory(directory)
                missing = [
                    filename
                    for filename in (
                        self.MANIFEST_FILENAME,
                        self.SOURCE_FILENAME,
                        self.ARTIFACT_FILENAME,
                    )
                    if not (directory / filename).is_file()
                ]
                if missing:
                    raise TheoryStoreError(
                        "missing bundle files: " + ",".join(missing)
                    )
                payload = json.loads(manifest_path.read_text(encoding="utf-8"))
                bundle = PublishedTheoryBundle.from_dict(payload)
                loaded = self.load(expected_id, domain=bundle.domain)
                if loaded is None:
                    raise TheoryStoreError("bundle could not be loaded")
            except Exception as exc:
                issues.append(
                    {
                        "path": str(manifest_path),
                        "error": f"{type(exc).__name__}: {exc}",
                    }
                )
        for path in sorted(self.staging_root.iterdir()):
            if path == self.owner_staging_root:
                continue
            if not path.is_dir() or not TheoryLeaseOwner._valid_owner_id(path.name):
                issues.append(
                    {
                        "path": str(path),
                        "error": "legacy_or_unowned_theory_staging_preserved",
                    }
                )
            elif self.lease_owner.owner_abandoned(path.name) is True:
                issues.append(
                    {
                        "path": str(path),
                        "error": "abandoned_theory_staging_pending_recovery",
                    }
                )
        return tuple(issues)

    def _bundle_directories(self) -> tuple[Path, ...]:
        return tuple(
            path
            for path in sorted(
                self.modules_root.glob("MiniTheory/Domains/*/Bundles/B_*")
            )
            if path.is_dir()
        )

    @staticmethod
    def _bundle_id_from_directory(directory: Path) -> str:
        match = re.fullmatch(r"B_([0-9a-f]{16})", directory.name)
        if match is None:
            raise TheoryStoreError(f"invalid bundle directory name: {directory.name}")
        return match.group(1)

    @staticmethod
    def _manifest_matches_content_identity(
        bundle: PublishedTheoryBundle,
        source: str,
    ) -> bool:
        import_block = "\n".join(f"import {module}" for module in bundle.imports)
        prefix = "\n\n".join(
            part
            for part in (
                import_block,
                "set_option autoImplicit false",
                f"namespace {bundle.namespace}",
            )
            if part
        ) + "\n\n"
        suffix = f"\n\nend {bundle.namespace}"
        if not source.startswith(prefix) or not source.endswith(suffix):
            return False
        body = source[len(prefix) : -len(suffix)]
        try:
            reconstructed = TheoryBundleCandidate.create(
                domain=bundle.domain,
                source=body,
                imports=bundle.imports,
                dependency_bundle_ids=bundle.dependency_bundle_ids,
            )
        except (TypeError, ValueError):
            return False
        return bool(
            reconstructed.bundle_id == bundle.bundle_id
            and reconstructed.module_name == bundle.module_name
            and reconstructed.namespace == bundle.namespace
            and reconstructed.source == source
        )

    @staticmethod
    def _validate_receipt(
        candidate: TheoryBundleCandidate,
        receipt: TheoryVerificationReceipt,
    ) -> None:
        if not receipt.accepted:
            raise TheoryStoreError("cannot publish a rejected theory candidate")
        for field_name in ("bundle_id", "module_name", "source_hash"):
            if getattr(candidate, field_name) != getattr(receipt, field_name):
                raise TheoryStoreError(f"verification receipt {field_name} mismatch")
        if not receipt.declarations:
            raise TheoryStoreError("verified theory bundle contains no declarations")
        if not receipt.lean_toolchain or not receipt.mathlib_revision:
            raise TheoryStoreError(
                "verification receipt has no compatible Lean environment fingerprint"
            )
        if receipt.policy_version != THEORY_POLICY_VERSION:
            raise TheoryStoreError("verification receipt policy version mismatch")
        if not receipt.compiled_artifact_hash:
            raise TheoryStoreError("verification receipt has no compiled artifact hash")

    @staticmethod
    def _fsync_file(path: Path) -> None:
        handle = path.open("rb")
        try:
            os.fsync(handle.fileno())
        except BaseException as primary:
            try:
                handle.close()
            except BaseException as cleanup_error:
                primary.add_note(
                    "Mini theory file descriptor cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise
        else:
            handle.close()

    @staticmethod
    def _fsync_dir(path: Path) -> None:
        descriptor = os.open(path, os.O_RDONLY)
        try:
            os.fsync(descriptor)
        except BaseException as primary:
            try:
                os.close(descriptor)
            except BaseException as cleanup_error:
                primary.add_note(
                    "Mini theory directory descriptor cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise
        else:
            os.close(descriptor)

    def _publish_lock(self) -> _ExclusiveStoreLock:
        return _ExclusiveStoreLock(self.lock_path)
