"""Safe promotion of run-local verified helpers into durable theory bundles."""

from __future__ import annotations

import re
import threading
from dataclasses import dataclass
from typing import Any, Iterable, Optional, Sequence

from .library import MiniTheoryLibrary, TheoryPublishResult
from .model import TheoryBundleCandidate
from .store import TheoryStorePublicationCommitted


_DECLARATION_HEAD_RE = re.compile(
    r"^(?:@\[[^\]\n]+\]\s*)*(?:protected\s+)?"
    r"(?P<kind>theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
_OPEN_COMMAND_RE = re.compile(
    r"^open\s+[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
_IDENTIFIER_RE = re.compile(
    r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\b"
)
_ATTRIBUTE_LINE_RE = re.compile(r"^@\[[^\]\n]+\]$")


def _lean_code_without_comments_or_strings(source: str) -> str:
    """Mask non-code text before conservative identifier policy checks."""

    text = str(source or "")
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            if char == "\\" and index + 1 < len(text):
                output.extend("  ")
                index += 2
            else:
                if char == '"':
                    in_string = False
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if pair == "--":
            end = text.find("\n", index)
            if end < 0:
                output.extend(" " * (len(text) - index))
                break
            output.extend(" " * (end - index))
            output.append("\n")
            index = end + 1
        elif pair == "/-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    return "".join(output)


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
        )
        return self.publish_prepared(
            preparation,
            cancellation_event=cancellation_event,
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
    ) -> HelperPromotionPreparation:
        helper_name = str(getattr(helper, "name", "") or "").strip()
        source = str(getattr(helper, "source", "") or "").strip()
        declaration = self._extract_declaration(source, helper_name)
        if not helper_name or declaration is None:
            return HelperPromotionPreparation(
                helper_name=helper_name,
                candidate=None,
                verification=None,
                diagnostic="helper_declaration_not_extractable",
            )
        forbidden = {
            str(item or "").strip()
            for item in forbidden_problem_constants
            if str(item or "").strip()
        }
        referenced_identifiers = set(
            _IDENTIFIER_RE.findall(
                _lean_code_without_comments_or_strings(declaration)
            )
        )
        used_forbidden = sorted(
            forbidden_name
            for forbidden_name in forbidden
            if any(
                identifier == forbidden_name
                or identifier.rsplit(".", 1)[-1] == forbidden_name
                for identifier in referenced_identifiers
            )
        )
        if used_forbidden:
            return HelperPromotionPreparation(
                helper_name=helper_name,
                candidate=None,
                verification=None,
                diagnostic="problem_local_constants:" + ",".join(used_forbidden),
            )
        candidate = TheoryBundleCandidate.create(
            domain=domain,
            source=declaration,
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
        diagnostic = str(verification.receipt.diagnostic or "").lower()
        output = "\n".join(
            (
                str(getattr(verification, "compile_output", "") or ""),
                str(getattr(verification, "audit_output", "") or ""),
            )
        ).lower()
        if diagnostic in {
            "lean_executable_unavailable",
            "lean_path_unavailable",
        }:
            return True
        return any(
            marker in output
            for marker in (
                "cancelled",
                "timeout after",
                "timeoutexpired",
                "filenotfounderror",
                "permissionerror",
                "oserror",
                "no such file or directory",
            )
        )

    @staticmethod
    def _extract_declaration(source: str, helper_name: str) -> Optional[str]:
        declaration = str(source or "").strip()
        lines = declaration.splitlines()
        if not lines:
            return None
        declaration_index = 0
        while declaration_index < len(lines):
            stripped = lines[declaration_index].strip()
            if (
                not stripped
                or stripped.startswith("--")
                or _OPEN_COMMAND_RE.fullmatch(stripped)
                or _ATTRIBUTE_LINE_RE.fullmatch(stripped)
            ):
                declaration_index += 1
                continue
            if stripped.startswith("/-"):
                depth = 0
                while declaration_index < len(lines):
                    comment_line = lines[declaration_index].strip()
                    depth += comment_line.count("/-")
                    depth -= comment_line.count("-/")
                    declaration_index += 1
                    if depth <= 0:
                        # Accept only comment-only leading lines. Code after a
                        # closing delimiter would widen the parser boundary.
                        if comment_line.rsplit("-/", 1)[-1].strip():
                            return None
                        break
                if depth != 0:
                    return None
                continue
            break
        if declaration_index >= len(lines):
            return None
        head = _DECLARATION_HEAD_RE.match(lines[declaration_index])
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
