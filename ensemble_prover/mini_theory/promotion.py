"""Safe promotion of run-local verified helpers into durable theory bundles."""

from __future__ import annotations

import re
import threading
from dataclasses import dataclass
from typing import Any, Iterable, Optional, Sequence
from ..math_utils import _strip_lean_comments_and_strings as _executable_lean_code

from .library import MiniTheoryLibrary, TheoryPublishResult
from .model import TheoryBundleCandidate
from .store import TheoryStorePublicationCommitted
from .promotion_context import (
    _DOTTED_IDENT,
    _mask_lean_noncode,
    helper_promotion_context,
    is_promotion_context_command,
    lean_name_components,
    split_promotion_context,
)


_DECLARATION_HEAD_RE = re.compile(
    r"^(?:@\[[^\]\n]+\]\s*)*(?:protected\s+)?"
    rf"(?P<kind>theorem|lemma)(?=\s|«)\s*(?P<name>{_DOTTED_IDENT})(?=\.\{{|\s|:|\(|\{{|⦃|\[|$)"
)
# Quoted identifiers delimit themselves and may immediately follow a keyword
# or another token. Greedy token consumption preserves entire ordinary names
# and quoted components without imposing Python-style word boundaries.
_IDENTIFIER_RE = re.compile(_DOTTED_IDENT)
_ATTRIBUTE_LINE_RE = re.compile(r"^@\[[^\]\n]+\]$")

# Persisted refusals predating complete Lean-name extraction can be retried
# without invalidating independently verified publications or other refusals.
DECLARATION_EXTRACTION_POLICY_VERSION = 2


def _lean_code_without_comments_or_strings(source: str) -> str:
    """Mask non-code text before conservative identifier policy checks."""

    return _mask_lean_noncode(str(source or ""))


def _problem_constant_name_components(name: str) -> tuple[str, ...]:
    """Absolute and relative spellings identify the same protected constant."""

    components = lean_name_components(name)
    if len(components) > 1 and components[0] == "_root_":
        return components[1:]
    return components


def _used_problem_constants(source: str, forbidden_constants: Iterable[str]) -> tuple[str, ...]:
    """Apply the same protected-name check to fresh and persisted helpers."""

    forbidden = {
        str(item or "").strip()
        for item in forbidden_constants
        if str(item or "").strip()
    }
    if not forbidden:
        return ()
    # Interpolation bodies elaborate as Lean terms. Strip literal text while
    # retaining executable bodies, including nested interpolations.
    executable_source, _lexically_complete = _executable_lean_code(source)
    referenced_names = {
        _problem_constant_name_components(identifier)
        for identifier in _IDENTIFIER_RE.findall(
            executable_source
        )
    }
    forbidden_names = {
        name: _problem_constant_name_components(name) for name in forbidden
    }
    return tuple(sorted(
        forbidden_name
        for forbidden_name, forbidden_components in forbidden_names.items()
        if forbidden_components
        if any(
            identifier == forbidden_components
            or len(forbidden_components) == 1
            and identifier[-1:] == forbidden_components
            for identifier in referenced_names
        )
    ))


@dataclass(frozen=True)
class HelperPromotionResult:
    helper_name: str
    candidate: Optional[TheoryBundleCandidate]
    publication: Optional[TheoryPublishResult]
    diagnostic: str
    retryable: bool = False

    @property
    def published(self) -> bool:
        return bool(self.publication and self.publication.published)


@dataclass(frozen=True)
class HelperPromotionPreparation:
    helper_name: str
    candidate: Optional[TheoryBundleCandidate]
    verification: Any
    diagnostic: str
    retryable: bool = False
    existing_publication: Optional[TheoryPublishResult] = None


class VerifiedHelperPromoter:
    """Promote only helpers that survive independent package verification."""

    def __init__(self, library: MiniTheoryLibrary) -> None:
        self.library = library

    def promote(
        self,
        helper: Any,
        *,
        domain: str,
        imports: Sequence[str],
        dependency_bundle_ids: Sequence[str] = (),
        satisfies_need_ids: Sequence[str] = (),
        generated_by_run: str = "",
        generated_by_model: str = "",
        source_theorem: str = "",
        forbidden_problem_constants: Iterable[str] = (),
        cancellation_event: Optional[threading.Event] = None,
        deadline_monotonic: float | None = None,
        max_heartbeats: int | None = None,
        memory_mb: int | None = None,
    ) -> HelperPromotionResult:
        preparation = self.prepare(
            helper,
            domain=domain,
            imports=imports,
            dependency_bundle_ids=dependency_bundle_ids,
            satisfies_need_ids=satisfies_need_ids,
            generated_by_run=generated_by_run,
            generated_by_model=generated_by_model,
            source_theorem=source_theorem,
            forbidden_problem_constants=forbidden_problem_constants,
            cancellation_event=cancellation_event,
            **{
                key: value
                for key, value in {
                    "deadline_monotonic": deadline_monotonic,
                    "max_heartbeats": max_heartbeats,
                    "memory_mb": memory_mb,
                }.items()
                if value is not None
            },
        )
        from ensemble_prover.lean_runner import _check_lean_owner_deadline

        _check_lean_owner_deadline(deadline_monotonic)
        return self.publish_prepared(
            preparation,
            cancellation_event=cancellation_event,
            **(
                {"deadline_monotonic": deadline_monotonic}
                if deadline_monotonic is not None
                else {}
            ),
        )

    def prepare(
        self,
        helper: Any,
        *,
        domain: str,
        imports: Sequence[str],
        dependency_bundle_ids: Sequence[str] = (),
        satisfies_need_ids: Sequence[str] = (),
        generated_by_run: str = "",
        generated_by_model: str = "",
        source_theorem: str = "",
        forbidden_problem_constants: Iterable[str] = (),
        cancellation_event: Optional[threading.Event] = None,
        deadline_monotonic: float | None = None,
        max_heartbeats: int | None = None,
        memory_mb: int | None = None,
    ) -> HelperPromotionPreparation:
        helper_name = str(getattr(helper, "name", "") or "").strip()
        source = str(getattr(helper, "source", "") or "").strip()
        try:
            context = helper_promotion_context(source, ())
        except ValueError:
            context = ()
        source = "\n".join((*context, source))
        declaration = self._extract_declaration(source, helper_name)
        if not helper_name or declaration is None:
            return HelperPromotionPreparation(
                helper_name=helper_name,
                candidate=None,
                verification=None,
                diagnostic="helper_declaration_not_extractable",
            )
        used_forbidden = _used_problem_constants(
            declaration, forbidden_problem_constants,
        )
        if used_forbidden:
            return HelperPromotionPreparation(
                helper_name=helper_name,
                candidate=None,
                verification=None,
                diagnostic="problem_local_constants:" + ",".join(used_forbidden),
            )
        replay_context, declaration_body = split_promotion_context(declaration)
        candidate = TheoryBundleCandidate.create(
            domain=domain,
            source=declaration_body,
            context_commands=replay_context,
            imports=imports,
            dependency_bundle_ids=dependency_bundle_ids,
            satisfies_need_ids=satisfies_need_ids,
            generated_by_run=generated_by_run,
            generated_by_model=generated_by_model,
            source_theorem=source_theorem,
        )
        reuse_published = getattr(
            self.library,
            "reuse_published_candidate",
            None,
        )
        existing_publication = (
            reuse_published(
                candidate,
                helper_name=helper_name,
                cancellation_event=cancellation_event,
            )
            if callable(reuse_published)
            else None
        )
        if existing_publication is not None:
            return HelperPromotionPreparation(
                helper_name=helper_name,
                candidate=candidate,
                verification=existing_publication.verification,
                diagnostic="verified_existing_bundle",
                existing_publication=existing_publication,
            )
        verification = self.library.verify_candidate(
            candidate,
            cancellation_event=cancellation_event,
            **{
                key: value
                for key, value in {
                    "deadline_monotonic": deadline_monotonic,
                    "max_heartbeats": max_heartbeats,
                    "memory_mb": memory_mb,
                }.items()
                if value is not None
            },
        )
        diagnostic = str(verification.receipt.diagnostic or "")
        return HelperPromotionPreparation(
            helper_name=helper_name,
            candidate=candidate,
            verification=verification,
            diagnostic=diagnostic,
            retryable=self._verification_is_retryable(verification),
        )

    def publish_prepared(
        self,
        preparation: HelperPromotionPreparation,
        *,
        cancellation_event: Optional[threading.Event] = None,
        deadline_monotonic: float | None = None,
    ) -> HelperPromotionResult:
        candidate = preparation.candidate
        verification = preparation.verification
        if candidate is None or verification is None:
            return HelperPromotionResult(
                helper_name=preparation.helper_name,
                candidate=candidate,
                publication=None,
                diagnostic=preparation.diagnostic,
                retryable=preparation.retryable,
            )
        committed_error = None
        if preparation.existing_publication is not None:
            publication = preparation.existing_publication
        else:
            try:
                publication = self.library.publish_verified(
                    candidate,
                    verification,
                    cancellation_event=cancellation_event,
                    **(
                        {"deadline_monotonic": deadline_monotonic}
                        if deadline_monotonic is not None
                        else {}
                    ),
                )
            except TheoryStorePublicationCommitted as exc:
                if exc.verification is None:
                    raise
                publication = TheoryPublishResult(
                    verification=exc.verification,
                    bundle=exc.bundle,
                )
                committed_error = exc
        if publication.published and publication.bundle is not None:
            for need_id in candidate.satisfies_need_ids:
                if self.library.needs.get(need_id) is None:
                    continue
                self.library.needs.record_outcome(
                    need_id,
                    status="context_available",
                    diagnostic="verified_helper_promoted_pending_consumer",
                    bundle_id=publication.bundle.bundle_id,
                    count_attempt=False,
                )
        if (
            committed_error is not None
            and committed_error.cause is not None
            and not isinstance(committed_error.cause, Exception)
        ):
            raise committed_error.cause
        diagnostic = publication.verification.receipt.diagnostic
        return HelperPromotionResult(
            helper_name=preparation.helper_name,
            candidate=candidate,
            publication=publication,
            diagnostic=diagnostic,
            retryable=self._verification_failure_is_retryable(publication),
        )

    @staticmethod
    def _verification_failure_is_retryable(publication: TheoryPublishResult) -> bool:
        if publication.published:
            return False
        return VerifiedHelperPromoter._verification_is_retryable(
            publication.verification
        )

    @staticmethod
    def _verification_is_retryable(verification: Any) -> bool:
        # Process status is supplied by the verifier; output may contain arbitrary
        # theorem names or diagnostics and cannot establish an infrastructure error.
        if bool(getattr(verification, "retryable", False)):
            return True
        reason = str(verification.receipt.diagnostic or "").partition(":")[0]
        return reason.strip().lower() in {
            "lean_executable_unavailable",
            "lean_path_unavailable",
            "lean_project_missing",
            "verification_environment_fingerprint_unavailable",
            "theory_library_environment_unresolved_at_initialization",
            "theory_library_environment_changed_since_initialization",
            "missing_dependency_bundles",
            "missing_dependency_bundle_artifact",
        }

    @staticmethod
    def _extract_declaration(source: str, helper_name: str) -> Optional[str]:
        declaration = str(source or "").strip()
        # Split physical lines identically before and after masking. Python's
        # splitlines also treats Unicode separators inside comments/literals
        # as line breaks, but masking replaces those characters with spaces.
        lines = declaration.split("\n")
        masked_lines = _lean_code_without_comments_or_strings(declaration).split("\n")
        if not lines:
            return None
        declaration_index = 0
        while declaration_index < len(lines):
            stripped = masked_lines[declaration_index].strip()
            if (
                not stripped
                or is_promotion_context_command(stripped)
                or _ATTRIBUTE_LINE_RE.fullmatch(stripped)
            ):
                declaration_index += 1
                continue
            break
        if declaration_index >= len(lines):
            return None
        head = _DECLARATION_HEAD_RE.match(masked_lines[declaration_index].lstrip())
        if head is None or head.group("name") != helper_name:
            return None
        # A promoted helper must be exactly one top-level declaration. Lean
        # continuation/tactic lines are indented; any later unindented content
        # is another command and is rejected instead of being guessed at by a
        # partial command regex.
        for line in lines[declaration_index + 1 :]:
            if line.strip() and not line[:1].isspace():
                return None
        return declaration
