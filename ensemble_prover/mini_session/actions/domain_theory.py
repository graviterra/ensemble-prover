"""MiniSession action for persistent domain-theory retrieval/construction."""

from __future__ import annotations

import inspect
import hashlib
import json
import re
import threading
import time
from dataclasses import dataclass, replace
from typing import Any, ClassVar, FrozenSet, Optional

from ensemble_prover.llm_error_policy import classify_llm_exception
from ensemble_prover.mini_theory import (
    TheoryCandidateOutputUnavailable,
    TheoryNeed,
    TheoryStoreError,
    TheoryStorePublicationCommitted,
)
from ensemble_prover.mini_theory.worker import run_cancellable_worker
from ensemble_prover.proof_dossier import (
    StaleProofIdeaContextProjectionError,
    selected_work_has_explicit_cognition,
)
from ensemble_prover.proof_graph import (
    graph_statement_closed_premises,
    graph_statement_leading_telescope_is_universal,
    graph_statement_key,
    graph_statement_root_equivalent,
    graph_text_hash,
)
from ensemble_prover.lean_decl_parser import find_decl_header_end
from ensemble_prover.theorem_project import _mask_noncode, scan_lean_declarations

from ..action import MiniOutcome


_THEORY_GENERIC_IDENTIFIERS = frozenset(
    {
        "a", "b", "c", "f", "g", "h", "i", "j", "k", "m", "n", "x", "y", "z",
        "forall", "exists", "true", "false", "prop", "type",
        "fin", "nat", "int", "real", "set", "finset",
        "theorem", "lemma", "def", "abbrev", "structure", "class",
        "inductive", "instance", "notation", "where",
        "general", "mathematics",
    }
)

_THEORY_SUPPORT_DECLARATION_HEAD_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]\r\n]*\][ \t]*)*"
    r"(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>def|abbrev|structure|class|inductive|instance|notation)\b"
)


class SelectedTheoryProofIdeaContextError(RuntimeError):
    """Selected theory work carried cognition that no longer resolves exactly."""

    mini_selected_proof_idea_context_error = True


def _theory_support_declaration_surfaces(source: str) -> tuple[tuple[str, str], ...]:
    """Return non-theorem declaration names and headers for relevance checks."""

    text = str(source or "")
    masked = _mask_noncode(text)
    surfaces: list[tuple[str, str]] = []
    for match in _THEORY_SUPPORT_DECLARATION_HEAD_RE.finditer(masked):
        header_end = find_decl_header_end(
            text,
            match.end("kind"),
            allow_where=True,
            allow_equations=False,
        )
        if header_end is None:
            continue
        header = masked[match.start("kind") : header_end].strip()
        tail = masked[match.end("kind") : header_end].lstrip()
        name_match = re.match(
            r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b",
            tail,
        )
        surfaces.append(
            (
                str(name_match.group("name") or "") if name_match else "",
                header,
            )
        )
    return tuple(surfaces)


def _theory_semantic_identifiers(text: str) -> set[str]:
    return {
        token
        for token in re.findall(r"[A-Za-z][A-Za-z0-9_']*", str(text or "").lower())
        if len(token) > 1 and token not in _THEORY_GENERIC_IDENTIFIERS
    }


def _theory_statement_advances_need(
    statement: str,
    need: TheoryNeed,
    *,
    candidate_name: str = "",
) -> bool:
    candidate = str(statement or "").strip()
    targets = tuple(
        text
        for text in (
            str(need.consumer_statement or "").strip(),
            str(need.target_statement or "").strip(),
        )
        if text
    )
    if not candidate or not targets:
        return False
    if any(
        graph_statement_root_equivalent(
            candidate,
            target,
            active_target_statements=(target,),
        )
        for target in targets
    ):
        return True
    candidate_tokens = _theory_semantic_identifiers(
        f"{candidate_name} {candidate}"
    )
    target_tokens = set().union(*(_theory_semantic_identifiers(item) for item in targets))
    required_name_tokens = _theory_semantic_identifiers(
        str(getattr(need, "required_name_hint", "") or "")
    )
    if required_name_tokens and required_name_tokens.issubset(candidate_tokens):
        return True
    # Generic Lean/type tokens were removed above, so one remaining shared
    # mathematical identifier is substantive. Requiring two would discard
    # narrow but useful declarations such as lemmas whose only shared concept
    # with the consumer is ``Prime`` or ``Collinear``.
    return bool(candidate_tokens & target_tokens)


def _first_text(record: dict[str, Any], *keys: str) -> str:
    for key in keys:
        value = str(record.get(key) or "").strip()
        if value:
            return value
    return ""


def _string_tuple(value: Any) -> tuple[str, ...]:
    """Normalize scalar/sequence graph metadata without splitting strings."""
    if value is None:
        return ()
    items = (value,) if isinstance(value, str) else value
    if not isinstance(items, (list, tuple, set, frozenset)):
        items = (items,)
    return tuple(
        dict.fromkeys(
            text
            for item in items
            if (text := str(item or "").strip())
        )
    )


def _candidate_need_forbidden_targets(
    need: TheoryNeed,
    *,
    root_statement: str = "",
) -> tuple[str, ...]:
    evidence = dict(need.evidence_payload or {})
    return tuple(
        dict.fromkeys(
            text
            for text in (
                str(need.consumer_statement or "").strip(),
                str(need.target_statement or "").strip(),
                str(root_statement or "").strip(),
                _first_text(
                    evidence,
                    "formalization_bridge_parent_statement",
                    "parent_repair_target_statement",
                    "materialization_parent_statement",
                    "root_contract_statement",
                ),
            )
            if text
        )
    )


def _candidate_need_contract_rejection(
    candidate: Any,
    need: TheoryNeed,
    *,
    root_statement: str = "",
) -> dict[str, Any]:
    """Reject a candidate that assumes the contract it claims to satisfy.

    Independent Lean compilation proves the implication exported by a bundle;
    it does not prove that the implication advances the selected theory need.
    This need-relative gate prevents a stronger/root target from being hidden as
    a proof premise of a weaker conclusion.
    """

    forbidden_targets = _candidate_need_forbidden_targets(
        need,
        root_statement=root_statement,
    )
    try:
        declarations = scan_lean_declarations(
            str(getattr(candidate, "source", "") or "")
        )
    except (TypeError, ValueError) as exc:
        return {
            "rejected": True,
            "reason": "candidate_declaration_scan_failed",
            "diagnostic": str(exc),
        }
    relevant_declaration_found = False
    declaration_found = False
    for declaration in declarations:
        statement = str(declaration.statement_type or "").strip()
        if not statement:
            continue
        declaration_found = True
        relevant_declaration_found = bool(
            relevant_declaration_found
            or _theory_statement_advances_need(
                statement,
                need,
                candidate_name=declaration.canonical_name,
            )
        )
        if declaration.kind not in {"theorem", "lemma"}:
            continue
        for premise in graph_statement_closed_premises(statement):
            for forbidden in forbidden_targets:
                if graph_statement_root_equivalent(
                    premise,
                    forbidden,
                    active_target_statements=(forbidden,),
                ):
                    return {
                        "rejected": True,
                        "reason": "candidate_assumes_need_or_root_target",
                        "declaration_name": declaration.canonical_name,
                        "declaration_statement": statement,
                        "forbidden_premise": premise,
                        "forbidden_target": forbidden,
                        "forbidden_target_hash": graph_text_hash(
                            graph_statement_key(forbidden) or forbidden
                        ),
                    }
        if not graph_statement_leading_telescope_is_universal(statement):
            # The loop above clears a candidate by finding NOTHING in its closed
            # premises, but the premise walker only sees a universal telescope:
            # for an existential-headed one an empty result means "cannot analyze",
            # so the candidate would be admitted on evidence never computed.
            # Checked AFTER the loop so a premise the walker did reach still
            # yields the specific assumes-target reason.
            return {
                "rejected": True,
                "reason": "candidate_premises_not_analyzable",
                "declaration_name": declaration.canonical_name,
                "declaration_statement": statement,
            }
    for declaration_name, declaration_surface in _theory_support_declaration_surfaces(
        candidate.source
    ):
        declaration_found = True
        relevant_declaration_found = bool(
            relevant_declaration_found
            or _theory_statement_advances_need(
                declaration_surface,
                need,
                candidate_name=declaration_name,
            )
        )
    if not declaration_found or not relevant_declaration_found:
        return {
            "rejected": True,
            "reason": "candidate_not_relevant_to_need",
        }
    return {"rejected": False}


@dataclass
class DomainTheoryAction:
    candidate_builder: Optional[Any] = None
    stage: str = "build"
    max_search_results: int = 5
    min_retrieval_score: float = 4.0
    default_imports: tuple[str, ...] = ("Mathlib",)
    max_attempts_per_need: int = 2

    id: str = "domain_theory"
    priority: int = 24
    cost_estimate_s: float = 120.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"conv", "theory_state"})
    # Retrieval is once per need and construction is bounded by the durable
    # need record. A session-global action-id counter must not suppress later,
    # mathematically independent needs.
    BUDGET_SCOPE: ClassVar[str] = "theory_need"

    @staticmethod
    def _durable_attempt_count(library: Any, record: Any) -> int:
        scoped_count = getattr(
            getattr(library, "needs", None),
            "attempts_for_current_scope",
            None,
        )
        if callable(scoped_count):
            return max(0, int(scoped_count(record) or 0))
        return max(0, int(getattr(record, "attempts", 0) or 0))

    def request_config(self) -> dict[str, Any]:
        """Project builder semantics for build-request identity."""

        builder = self.candidate_builder
        builder_config: Optional[dict[str, Any]] = None
        if builder is not None:
            manifest = getattr(builder, "request_config", None)
            if callable(manifest):
                raw = manifest()
                if not isinstance(raw, dict):
                    raise TypeError(
                        "theory candidate builder request_config must return a dict"
                    )
                builder_config = dict(raw)
            else:
                builder_config = {
                    "schema_version": 1,
                    "class": f"{type(builder).__module__}.{type(builder).__qualname__}",
                }
        return {
            "schema_version": 1,
            "candidate_builder": builder_config,
        }


    def _build_request_fingerprint(
        self,
        need: TheoryNeed,
        *,
        imports: tuple[str, ...],
        dependency_bundle_ids: tuple[str, ...],
        dependency_declarations: tuple[str, ...],
        proof_idea_context_digest: str = "",
    ) -> str:
        payload = {
            "schema_version": 1,
            "need": need.to_dict(),
            "imports": imports,
            "dependency_bundle_ids": dependency_bundle_ids,
            "dependency_declarations": dependency_declarations,
            "action": self.request_config(),
        }
        clean_context_digest = str(proof_idea_context_digest or "").strip()
        if clean_context_digest:
            # Preserve legacy execution-only request identity while making a
            # selected strategy revision a first-class semantic input.
            payload["proof_idea_context_digest"] = clean_context_digest
        return hashlib.sha256(
            json.dumps(
                payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=True,
            ).encode("utf-8")
        ).hexdigest()

    @staticmethod
    def _selected_theory_prompt_context(
        session: Any,
        selected_work: dict[str, Any],
    ) -> tuple[str, str]:
        """Resolve one selected lifecycle for theory without global fallback."""

        dossier = getattr(session, "dossier", None)
        resolver = getattr(dossier, "resolve_proof_idea_context", None)
        projector = getattr(dossier, "project_proof_idea_context", None)
        if not callable(resolver) or not callable(projector):
            return "", ""
        record = dict(selected_work or {})
        explicit_cognition = selected_work_has_explicit_cognition(record)
        resolution = resolver(record, policy="exact_selected")
        status = str(getattr(resolution, "status", "") or "").strip()
        if status != "resolved":
            if explicit_cognition:
                reason = str(
                    getattr(resolution, "reason", "") or status or "unbound"
                )
                raise SelectedTheoryProofIdeaContextError(
                    "selected theory cognition could not be resolved exactly: "
                    f"{status or 'unknown'}: {reason}"
                )
            return "", ""
        try:
            projection = projector(resolution, audience="theory")
        except StaleProofIdeaContextProjectionError as exc:
            raise SelectedTheoryProofIdeaContextError(
                "selected theory cognition changed before projection: "
                f"{exc}"
            ) from exc
        render = getattr(projection, "render", None)
        if not callable(render):
            raise TypeError("theory proof-idea context projection has no renderer")
        resolution_digest = str(
            getattr(resolution, "context_digest", "") or ""
        ).strip()
        projection_digest = str(
            getattr(projection, "context_digest", "") or ""
        ).strip()
        if projection_digest != resolution_digest:
            raise SelectedTheoryProofIdeaContextError(
                "theory proof-idea projection digest does not match its resolution"
            )
        return str(render() or ""), resolution_digest

    def is_applicable(self, session: Any) -> bool:
        library = getattr(session, "theory_library", None)
        if library is None or getattr(library, "mode", "off") == "off":
            return False
        record = dict(getattr(session, "selected_work_item_record", {}) or {})
        if not record or not bool(record.get("formalization_required")):
            return False
        if selected_work_has_explicit_cognition(record):
            dossier = getattr(session, "dossier", None)
            resolver = getattr(dossier, "resolve_proof_idea_context", None)
            if callable(resolver):
                try:
                    resolution = resolver(record, policy="exact_selected")
                except Exception:
                    # Applicability is a read-only probe. Unexpected resolver
                    # failures remain authoritative in ``run`` where they can
                    # be typed and settled without silently retiring work.
                    pass
                else:
                    if str(getattr(resolution, "status", "") or "").strip() != (
                        "resolved"
                    ):
                        return False
        # Applicability is a read-only scheduler probe.  Derive the current
        # executable contract without superseding durable needs or rewriting
        # graph/frontier bindings; adoption belongs to ``run`` after its
        # authoritative selected-context freshness check.
        need = self._derive_need_from_record(session, record)
        if self.stage == "retrieve":
            return need.need_id not in getattr(
                session, "theory_context_hit_need_ids", set()
            )
        if self.stage != "build" or getattr(library, "mode", "off") != "build":
            return False
        durable_record = library.needs.get(need.need_id)
        durable_diagnostic = str(
            getattr(durable_record, "diagnostic", "") or ""
        )
        if durable_diagnostic.startswith("theory_candidate_not_emitted:"):
            try:
                dependency_records = tuple(
                    library.needs.get(dependency_need_id)
                    for dependency_need_id in need.dependency_need_ids
                )
                dependency_bundle_ids = tuple(
                    dict.fromkeys(
                        bundle_id
                        for dependency_record in dependency_records
                        if dependency_record is not None
                        and dependency_record.status == "resolved"
                        for bundle_id in self._record_bundle_ids(dependency_record)
                    )
                )
                dependency_plan_complete = len(dependency_records) == len(
                    need.dependency_need_ids
                ) and all(
                    dependency_record is not None
                    and dependency_record.status == "resolved"
                    and self._record_bundle_ids(dependency_record)
                    for dependency_record in dependency_records
                )
                bundles = tuple(
                    library.store.load(bundle_id, domain=need.domain)
                    for bundle_id in dependency_bundle_ids
                )
                if dependency_plan_complete and all(bundle is not None for bundle in bundles):
                    dependency_modules = tuple(
                        bundle.module_name for bundle in bundles if bundle is not None
                    )
                    dependency_declarations = tuple(
                        f"{declaration.fq_name} : {declaration.type_text}"
                        for bundle in bundles
                        if bundle is not None
                        for declaration in bundle.declarations
                    )
                    _, proof_idea_context_digest = (
                        self._selected_theory_prompt_context(session, record)
                    )
                    current_fingerprint = self._build_request_fingerprint(
                        need,
                        imports=tuple(
                            dict.fromkeys(
                                (
                                    *(need.required_imports or self.default_imports),
                                    *dependency_modules,
                                )
                            )
                        ),
                        dependency_bundle_ids=dependency_bundle_ids,
                        dependency_declarations=dependency_declarations,
                        proof_idea_context_digest=proof_idea_context_digest,
                    )
                    if durable_diagnostic == (
                        f"theory_candidate_not_emitted:{current_fingerprint}"
                    ):
                        return False
            except SelectedTheoryProofIdeaContextError:
                return False
            except (AttributeError, OSError, TheoryStoreError, TypeError, ValueError):
                # Applicability must stay conservative when durable dependency
                # state cannot be reconstructed. The run path performs the
                # authoritative comparison before claiming a lease.
                pass
        durable_bundle_ids = self._record_bundle_ids(durable_record)
        attempted = getattr(session, "theory_attempted_need_ids", set())
        bound_bundle_ids = set(
            getattr(session, "theory_consumer_bundle_ids_by_need_id", {}).get(
                need.need_id,
                (),
            )
            or ()
        )
        if (
            durable_record is not None
            and durable_record.status in {"context_available", "resolved"}
            and durable_bundle_ids
            and need.need_id not in attempted
            and (
                not set(durable_bundle_ids).issubset(
                    set(getattr(session, "theory_imported_bundle_ids", ()) or ())
                )
                or not set(durable_bundle_ids).issubset(bound_bundle_ids)
            )
        ):
            return True
        if durable_record is not None and durable_record.status in {
            "resolved",
            "superseded",
        }:
            return False
        if durable_record is not None and getattr(
            durable_record,
            "active_attempt_id",
            "",
        ):
            abandoned_attempts = getattr(
                library.needs,
                "abandoned_build_attempts",
                None,
            )
            if not callable(abandoned_attempts):
                return False
            try:
                if not abandoned_attempts(need_id=need.need_id):
                    return False
            except TheoryStoreError:
                return False
        if not self._dependencies_ready(library, need):
            return False
        if (
            durable_record is not None
            and self._durable_attempt_count(library, durable_record)
            >= self.max_attempts_per_need
        ):
            return False
        attempts = int(
            getattr(session, "theory_need_attempt_counts", {}).get(need.need_id, 0)
        )
        return need.need_id not in attempted and attempts < self.max_attempts_per_need

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Theory availability probe; never adopts or mutates a theory need."""

        return self.is_applicable(session)

    async def run(self, session: Any) -> MiniOutcome:
        started = time.monotonic()
        record = dict(getattr(session, "selected_work_item_record", {}) or {})
        proof_idea_context = ""
        proof_idea_context_digest = ""
        if self.stage == "build" or selected_work_has_explicit_cognition(record):
            try:
                proof_idea_context, proof_idea_context_digest = (
                    self._selected_theory_prompt_context(session, record)
                )
            except SelectedTheoryProofIdeaContextError as exc:
                # A selected packet can become stale after the applicability
                # probe when helper/environment state changes. Return the
                # typed zero-provider invalidation before deriving/upserting a
                # need so MiniSession can retire only this action generation.
                return MiniOutcome.from_exception(
                    self,
                    exc,
                    cost_seconds=time.monotonic() - started,
                )
            except Exception as exc:
                # Resolver/projector infrastructure can fail after the
                # read-only applicability probe as well. Preserve that typed
                # retryable outcome before any durable theory mutation;
                # letting it escape would trigger dispatch-generation recycle.
                return MiniOutcome.from_exception(
                    self,
                    exc,
                    cost_seconds=time.monotonic() - started,
                )
        need = self._derive_need_from_record(session, record)
        try:
            self._adopt_need_for_record(session, record, need)
        except Exception as exc:
            # Adoption can touch the durable supersession store.  Keep an
            # ordinary persistence failure inside the optional theory lane;
            # escaping here would recycle the whole dispatch generation and
            # immediately select the same work again.
            if self.stage == "retrieve":
                return self._optional_retrieval_deferred(
                    session,
                    need,
                    started,
                    boundary="need_adoption",
                    exc=exc,
                )
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="need_adoption",
                exc=exc,
            )
        library = session.theory_library
        if self.stage == "retrieve":
            try:
                need = library.needs.upsert(need).need
                # Observational prompt evidence is intentionally frozen at the
                # first durable contract version. Only executable identity
                # changes open a fresh bounded attempt set.
                session.theory_needs[need.need_id] = need
                recover_attempts = getattr(
                    library,
                    "recover_abandoned_build_attempts",
                    None,
                )
                if callable(recover_attempts):
                    recover_attempts(need_id=need.need_id)
                durable_record = library.needs.get(need.need_id)
                adopted = self._adopt_durable_context(
                    session,
                    need,
                    durable_record,
                    started,
                )
                if adopted is not None:
                    session.theory_context_hit_need_ids.add(need.need_id)
                    return self._with_outcome_metadata(
                        adopted,
                        semantic_budget_step_consumed=True,
                    )
                if (
                    durable_record is not None
                    and durable_record.status in {"context_available", "resolved"}
                    and self._record_bundle_ids(durable_record)
                ):
                    session.theory_context_hit_need_ids.add(need.need_id)
                    return self._no_progress(
                        started,
                        need,
                        "durable_theory_context_already_bound",
                        preserve_frontier_work=True,
                        consume_selected_frontier_action=True,
                    )
                return await self._retrieve(session, need, started)
            except Exception as exc:
                return self._optional_retrieval_deferred(
                    session,
                    need,
                    started,
                    boundary="retrieval_bookkeeping",
                    exc=exc,
                )
        try:
            need = library.needs.upsert(need).need
            session.theory_needs[need.need_id] = need
        except Exception as exc:
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="need_upsert",
                exc=exc,
            )
        if self.stage != "build":
            session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(started, need, "invalid_domain_theory_stage")
        if getattr(library, "mode", "off") != "build":
            session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(started, need, "theory_build_mode_disabled")
        recover_attempts = getattr(library, "recover_abandoned_build_attempts", None)
        try:
            if callable(recover_attempts):
                recover_attempts(need_id=need.need_id)
            durable_record = library.needs.get(need.need_id)
            adopted = self._adopt_durable_context(
                session,
                need,
                durable_record,
                started,
            )
        except Exception as exc:
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="durable_context",
                exc=exc,
            )
        if adopted is not None:
            if not adopted.progress:
                session.theory_attempted_need_ids.add(need.need_id)
                return self._with_outcome_metadata(
                    adopted,
                    consume_selected_frontier_action=True,
                    semantic_budget_step_consumed=True,
                )
            return self._with_outcome_metadata(
                adopted,
                semantic_budget_step_consumed=True,
            )
        if durable_record is not None and durable_record.status in {
            "resolved",
            "superseded",
        }:
            session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(
                started,
                need,
                "theory_build_need_terminal",
                semantic_budget_step_consumed=True,
            )
        if self.candidate_builder is None:
            session.theory_attempted_need_ids.add(need.need_id)
            try:
                library.needs.record_outcome(
                    need.need_id,
                    status="blocked",
                    diagnostic="theory_candidate_builder_unavailable",
                )
            except Exception as exc:
                return self._optional_build_deferred(
                    session,
                    need,
                    started,
                    boundary="builder_unavailable_record",
                    exc=exc,
                )
            return self._no_progress(
                started,
                need,
                "theory_candidate_builder_unavailable",
                semantic_budget_step_consumed=True,
            )
        publication_preflight = getattr(
            library,
            "publication_preflight_error",
            None,
        )
        try:
            preflight_error = (
                str(publication_preflight() or "")
                if callable(publication_preflight)
                else ""
            )
        except Exception as exc:
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="publication_preflight",
                exc=exc,
            )
        if preflight_error:
            session.theory_attempted_need_ids.add(need.need_id)
            try:
                library.needs.record_outcome(
                    need.need_id,
                    status="blocked",
                    diagnostic=preflight_error,
                    count_attempt=False,
                )
            except Exception as exc:
                return self._optional_build_deferred(
                    session,
                    need,
                    started,
                    boundary="preflight_record",
                    exc=exc,
                )
            return self._no_progress(
                started,
                need,
                f"theory_build_preflight_rejected:{preflight_error}",
                semantic_budget_step_consumed=True,
            )
        try:
            dependency_records = tuple(
                library.needs.get(dependency_need_id)
                for dependency_need_id in need.dependency_need_ids
            )
        except Exception as exc:
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="dependency_need_read",
                exc=exc,
            )
        unresolved_dependencies = tuple(
            dependency_need_id
            for dependency_need_id, dependency_record in zip(
                need.dependency_need_ids,
                dependency_records,
            )
            if dependency_record is None
            or dependency_record.status != "resolved"
            or not (
                tuple(getattr(dependency_record, "validated_bundle_ids", ()) or ())
                or dependency_record.bundle_id
            )
        )
        if unresolved_dependencies:
            diagnostic = "unresolved_theory_prerequisites:" + ",".join(
                unresolved_dependencies
            )
            try:
                library.needs.record_outcome(
                    need.need_id,
                    status="blocked",
                    diagnostic=diagnostic,
                    count_attempt=False,
                )
            except Exception as exc:
                return self._optional_build_deferred(
                    session,
                    need,
                    started,
                    boundary="unresolved_dependency_record",
                    exc=exc,
                )
            return self._no_progress(
                started,
                need,
                diagnostic,
                preserve_frontier_work=True,
            )
        dependency_bundle_ids = tuple(
            dict.fromkeys(
                bundle_id
                for dependency_record in dependency_records
                if dependency_record is not None
                for bundle_id in (
                    tuple(
                        getattr(
                            dependency_record,
                            "validated_bundle_ids",
                            (),
                        )
                        or ()
                    )
                    or (dependency_record.bundle_id,)
                )
                if bundle_id
            )
        )
        try:
            bundles_by_id = (
                {bundle.bundle_id: bundle for bundle in library.store.iter_bundles()}
                if dependency_bundle_ids
                else {}
            )
        except Exception as exc:
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="dependency_bundle_read",
                exc=exc,
            )
        missing_dependency_bundles = tuple(
            bundle_id
            for bundle_id in dependency_bundle_ids
            if bundle_id not in bundles_by_id
        )
        if missing_dependency_bundles:
            diagnostic = "missing_current_environment_prerequisites:" + ",".join(
                missing_dependency_bundles
            )
            try:
                library.needs.record_outcome(
                    need.need_id,
                    status="blocked",
                    diagnostic=diagnostic,
                    count_attempt=False,
                )
            except Exception as exc:
                return self._optional_build_deferred(
                    session,
                    need,
                    started,
                    boundary="missing_dependency_record",
                    exc=exc,
                )
            session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(
                started,
                need,
                diagnostic,
                preserve_frontier_work=True,
                consume_selected_frontier_action=True,
                semantic_budget_step_consumed=True,
            )
        dependency_modules = tuple(
            bundles_by_id[bundle_id].module_name
            for bundle_id in dependency_bundle_ids
        )
        dependency_declarations = tuple(
            f"{declaration.fq_name} : {declaration.type_text}"
            for bundle_id in dependency_bundle_ids
            for declaration in bundles_by_id[bundle_id].declarations
        )
        build_imports = tuple(
            dict.fromkeys(
                (
                    *(need.required_imports or self.default_imports),
                    *dependency_modules,
                )
            )
        )
        build_request_fingerprint = self._build_request_fingerprint(
            need,
            imports=build_imports,
            dependency_bundle_ids=dependency_bundle_ids,
            dependency_declarations=dependency_declarations,
            proof_idea_context_digest=proof_idea_context_digest,
        )
        terminal_request_diagnostic = (
            f"theory_candidate_not_emitted:{build_request_fingerprint}"
        )
        if (
            durable_record is not None
            and str(getattr(durable_record, "diagnostic", "") or "")
            == terminal_request_diagnostic
        ):
            session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(
                started,
                need,
                "theory_identical_terminal_request_suppressed",
                semantic_budget_step_consumed=True,
            )
        claim_with_reason = getattr(
            library.needs,
            "claim_build_attempt_with_reason",
            None,
        )
        try:
            if callable(claim_with_reason):
                claimed_attempt, claim_reason = claim_with_reason(
                    need.need_id,
                    max_attempts=self.max_attempts_per_need,
                )
            else:
                claimed_attempt = library.needs.claim_build_attempt(
                    need.need_id,
                    max_attempts=self.max_attempts_per_need,
                )
                claim_reason = (
                    "claimed" if claimed_attempt is not None else "exhausted"
                )
        except Exception as exc:
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="attempt_claim",
                exc=exc,
            )
        if claimed_attempt is None:
            if claim_reason == "active_elsewhere":
                return self._no_progress(
                    started,
                    need,
                    "theory_build_in_progress_elsewhere",
                    preserve_frontier_work=True,
                    preserve_action_budget=True,
                )
            session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(
                started,
                need,
                (
                    "theory_build_need_terminal"
                    if claim_reason == "terminal"
                    else "theory_build_attempts_exhausted"
                ),
                semantic_budget_step_consumed=True,
            )
        attempt_id = str(getattr(claimed_attempt, "active_attempt_id", "") or "")
        leased_claim = bool(
            attempt_id
            and callable(getattr(library.needs, "settle_build_attempt", None))
        )

        def settle_attempt(*, status: str, diagnostic: str, bundle_id: str = ""):
            if leased_claim:
                return library.needs.settle_build_attempt(
                    need.need_id,
                    attempt_id,
                    status=status,
                    diagnostic=diagnostic,
                    bundle_id=bundle_id,
                )
            return (
                library.needs.record_outcome(
                    need.need_id,
                    status=status,
                    diagnostic=diagnostic,
                    bundle_id=bundle_id,
                ),
                True,
            )

        def release_attempt(diagnostic: str) -> None:
            if leased_claim:
                library.needs.release_build_attempt(
                    need.need_id,
                    attempt_id,
                    diagnostic=diagnostic,
                )

        def defer_claimed_attempt(
            boundary: str,
            exc: Exception,
        ) -> MiniOutcome:
            try:
                release_attempt(f"{boundary}_failed")
            except Exception as bookkeeping_error:
                exc.add_note(
                    "Mini theory lease release also failed: "
                    f"{type(bookkeeping_error).__name__}: {bookkeeping_error}"
                )
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary=boundary,
                exc=exc,
            )

        def release_claimed_after_external_stop(
            diagnostic: str,
            primary: BaseException,
        ) -> None:
            """Best-effort CAS-release while preserving an external stop."""

            try:
                release_attempt(diagnostic)
            except BaseException as bookkeeping_error:
                primary.add_note(
                    "Mini theory lease release also failed: "
                    f"{type(bookkeeping_error).__name__}: {bookkeeping_error}"
                )

        attempt_count = self._durable_attempt_count(
            library,
            claimed_attempt,
        ) + int(leased_claim)
        session.theory_need_attempt_counts[need.need_id] = attempt_count
        exhausted = attempt_count >= self.max_attempts_per_need
        try:
            build_kwargs: dict[str, Any] = {
                "imports": build_imports,
                "dependency_bundle_ids": dependency_bundle_ids,
                "dependency_declarations": dependency_declarations,
            }
            build_parameters = inspect.signature(
                self.candidate_builder.build
            ).parameters.values()
            accepts_arbitrary_keywords = any(
                parameter.kind is inspect.Parameter.VAR_KEYWORD
                for parameter in build_parameters
            )
            parameter_names = {
                parameter.name for parameter in build_parameters
            }
            if accepts_arbitrary_keywords or "proof_idea_context" in parameter_names:
                build_kwargs["proof_idea_context"] = proof_idea_context
            if (
                accepts_arbitrary_keywords
                or "proof_idea_context_digest" in parameter_names
            ):
                build_kwargs["proof_idea_context_digest"] = (
                    proof_idea_context_digest
                )
            candidate = await self.candidate_builder.build(need, **build_kwargs)
        except TheoryCandidateOutputUnavailable as exc:
            attempt_released = False
            try:
                release_attempt("theory_candidate_output_unavailable")
                attempt_released = True
            except Exception as bookkeeping_error:
                exc.add_note(
                    "Mini theory lease release also failed: "
                    f"{type(bookkeeping_error).__name__}: {bookkeeping_error}"
                )
            # The lease represented an in-flight claim, not a completed build
            # attempt. Keep the session-local mirror aligned with the durable
            # counter so max-attempt gating cannot retire work that emitted no
            # usable candidate.
            if attempt_released:
                durable_attempts = self._durable_attempt_count(
                    library,
                    claimed_attempt,
                )
                if durable_attempts > 0:
                    session.theory_need_attempt_counts[need.need_id] = (
                        durable_attempts
                    )
                else:
                    session.theory_need_attempt_counts.pop(need.need_id, None)
            return self._no_progress(
                started,
                need,
                f"theory_candidate_output_deferred:{exc.reason}",
                preserve_frontier_work=True,
                consume_selected_frontier_action=True,
                preserve_action_budget=True,
                semantic_budget_step_consumed=False,
            )
        except Exception as exc:
            try:
                release_attempt("theory_candidate_build_failed")
            except Exception as bookkeeping_error:
                exc.add_note(
                    "Mini theory lease release also failed: "
                    f"{type(bookkeeping_error).__name__}: {bookkeeping_error}"
                )
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="candidate_build",
                exc=exc,
            )
        except BaseException as primary:
            release_claimed_after_external_stop(
                "theory_candidate_build_interrupted",
                primary,
            )
            raise
        if candidate is None:
            try:
                _, applied = settle_attempt(
                    status="pending",
                    diagnostic=terminal_request_diagnostic,
                )
            except Exception as exc:
                return defer_claimed_attempt("candidate_settlement", exc)
            except BaseException as primary:
                release_claimed_after_external_stop(
                    "candidate_settlement_interrupted",
                    primary,
                )
                raise
            if not applied:
                return self._no_progress(
                    started,
                    need,
                    "theory_build_attempt_lease_lost",
                    preserve_frontier_work=True,
                )
            if exhausted:
                session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(
                started,
                need,
                "theory_candidate_not_emitted",
                preserve_frontier_work=False,
                semantic_budget_step_consumed=True,
            )
        contract_rejection = _candidate_need_contract_rejection(
            candidate,
            need,
            root_statement=str(
                getattr(getattr(session, "dossier", None), "root_statement", "")
                or ""
            ),
        )
        if bool(contract_rejection.get("rejected")):
            diagnostic = str(
                contract_rejection.get("reason")
                or "candidate_assumes_need_or_root_target"
            )
            try:
                _, applied = settle_attempt(
                    status="rejected",
                    diagnostic=diagnostic,
                )
            except Exception as exc:
                return defer_claimed_attempt("contract_rejection_settlement", exc)
            except BaseException as primary:
                release_claimed_after_external_stop(
                    "contract_rejection_settlement_interrupted",
                    primary,
                )
                raise
            if not applied:
                return self._no_progress(
                    started,
                    need,
                    "theory_build_attempt_lease_lost",
                    preserve_frontier_work=True,
                )
            if exhausted:
                session.theory_attempted_need_ids.add(need.need_id)
            record_event = getattr(session, "_record_event", None)
            if callable(record_event):
                record_event({
                    "phase": "domain_theory_build",
                    "need_id": need.need_id,
                    "candidate_bundle_id": str(candidate.bundle_id or ""),
                    "candidate_contract_rejection": dict(contract_rejection),
                    "verdict": "theory_candidate_contract_rejected",
                })
            return self._no_progress(
                started,
                need,
                "theory_candidate_rejected:" + diagnostic,
                preserve_frontier_work=not exhausted,
                semantic_budget_step_consumed=True,
            )
        if leased_claim:
            try:
                _, marked = library.needs.mark_build_attempt_candidate(
                    need.need_id,
                    attempt_id,
                    bundle_id=candidate.bundle_id,
                )
            except Exception as exc:
                try:
                    release_attempt("theory_candidate_identity_journal_failed")
                except Exception as bookkeeping_error:
                    exc.add_note(
                        "Mini theory lease release also failed: "
                        f"{type(bookkeeping_error).__name__}: {bookkeeping_error}"
                    )
                return self._optional_build_deferred(
                    session,
                    need,
                    started,
                    boundary="candidate_identity_journal",
                    exc=exc,
                )
            except BaseException as primary:
                release_claimed_after_external_stop(
                    "theory_candidate_identity_journal_interrupted",
                    primary,
                )
                raise
            if not marked:
                return self._no_progress(
                    started,
                    need,
                    "theory_build_attempt_lease_lost",
                )
        verification_cancel = threading.Event()
        publication = None
        committed_bundle = None
        try:
            verify_kwargs: dict[str, Any] = {
                "cancellation_event": verification_cancel,
            }
            verify_parameters = inspect.signature(
                library.verify_candidate
            ).parameters.values()
            if any(
                parameter.name == "forbidden_target_statements"
                or parameter.kind is inspect.Parameter.VAR_KEYWORD
                for parameter in verify_parameters
            ):
                verify_kwargs["forbidden_target_statements"] = (
                    _candidate_need_forbidden_targets(
                        need,
                        root_statement=str(
                            getattr(
                                getattr(session, "dossier", None),
                                "root_statement",
                                "",
                            )
                            or ""
                        ),
                    )
                )
            verification = await run_cancellable_worker(
                library.verify_candidate,
                candidate,
                **verify_kwargs,
            )
            publication = library.publish_verified(
                candidate,
                verification,
                cancellation_event=verification_cancel,
            )
        except TheoryStorePublicationCommitted as exc:
            committed_bundle = exc.bundle
            if exc.cause is not None and not isinstance(exc.cause, Exception):
                try:
                    settle_attempt(
                        status="context_available",
                        diagnostic="publication_committed_before_external_stop",
                        bundle_id=exc.bundle.bundle_id,
                    )
                except BaseException as bookkeeping_error:
                    exc.cause.add_note(
                        "Mini theory committed-publication settlement also failed: "
                        f"{type(bookkeeping_error).__name__}: {bookkeeping_error}"
                    )
                    release_claimed_after_external_stop(
                        "committed_publication_settlement_interrupted",
                        exc.cause,
                    )
                raise exc.cause
        except Exception as exc:
            try:
                release_attempt("theory_verification_or_publication_failed")
            except Exception as bookkeeping_error:
                exc.add_note(
                    "Mini theory lease release also failed: "
                    f"{type(bookkeeping_error).__name__}: {bookkeeping_error}"
                )
            return self._optional_build_deferred(
                session,
                need,
                started,
                boundary="verification_or_publication",
                exc=exc,
            )
        except BaseException as primary:
            release_claimed_after_external_stop(
                "theory_verification_or_publication_interrupted",
                primary,
            )
            raise
        if committed_bundle is None and (
            publication is None
            or not publication.published
            or publication.bundle is None
        ):
            try:
                _, applied = settle_attempt(
                    status="rejected",
                    diagnostic=publication.verification.receipt.diagnostic,
                )
            except Exception as exc:
                return defer_claimed_attempt("rejection_settlement", exc)
            except BaseException as primary:
                release_claimed_after_external_stop(
                    "rejection_settlement_interrupted",
                    primary,
                )
                raise
            if not applied:
                return self._no_progress(
                    started,
                    need,
                    "theory_build_attempt_lease_lost",
                    preserve_frontier_work=True,
                )
            if exhausted:
                session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(
                started,
                need,
                "theory_candidate_rejected:" + publication.verification.receipt.diagnostic,
                preserve_frontier_work=not exhausted,
                semantic_budget_step_consumed=True,
            )
        published_bundle = committed_bundle or publication.bundle
        try:
            _, applied = settle_attempt(
                status="context_available",
                diagnostic=(
                    "recovered_publication_after_publish_exception"
                    if committed_bundle is not None
                    else "theory_built_verified_published_pending_local_import"
                ),
                bundle_id=published_bundle.bundle_id,
            )
        except Exception as exc:
            return defer_claimed_attempt("publication_settlement", exc)
        except BaseException as primary:
            release_claimed_after_external_stop(
                "publication_settlement_interrupted",
                primary,
            )
            raise
        if not applied:
            return self._no_progress(
                started,
                need,
                "theory_build_attempt_lease_lost",
                preserve_frontier_work=True,
            )
        try:
            session.install_theory_bundles((published_bundle.bundle_id,))
        except Exception as exc:
            session.theory_attempted_need_ids.add(need.need_id)
            return self._no_progress(
                started,
                need,
                f"theory_import_rejected:{exc}",
                preserve_frontier_work=True,
                consume_selected_frontier_action=True,
                semantic_budget_step_consumed=True,
            )
        self._tell_conversation(
            session,
            module_name=published_bundle.module_name,
            declarations=tuple(
                (declaration.fq_name, declaration.type_text)
                for declaration in published_bundle.declarations
            ),
        )
        if exhausted:
            session.theory_attempted_need_ids.add(need.need_id)
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=False,
            cost_seconds=time.monotonic() - started,
            metadata={
                "theory_need_id": need.need_id,
                "theory_verdict": "theory_built_verified_published_imported",
                "theory_bundle_id": published_bundle.bundle_id,
                "theory_module": published_bundle.module_name,
                "theory_progress": True,
                "theory_context_progress": True,
                "theory_context_changed": True,
                "preserve_frontier_work": True,
                "preserve_selected_frontier_action": True,
                "consume_selected_frontier_action": True,
                "semantic_budget_step_consumed": True,
                "strong_progress": False,
            },
        )

    async def _retrieve(
        self,
        session: Any,
        need: TheoryNeed,
        started: float,
    ) -> MiniOutcome:
        library = session.theory_library
        # Retrieval is a bounded, optional lane. Mark this semantic need before
        # touching the store so a storage fault cannot repeatedly pre-empt the
        # unchanged mathematical frontier.
        session.theory_context_hit_need_ids.add(need.need_id)
        search_kwargs = {
            "goal_state": " ".join(
                item
                for item in (
                    need.mathematical_description,
                    need.required_name_hint,
                )
                if item
            ),
            "domain": need.domain,
            "max_results": self.max_search_results,
            "admission_predicate": lambda hit: _theory_statement_advances_need(
                str(getattr(hit, "type_text", "") or ""),
                need,
                candidate_name=str(getattr(hit, "fq_name", "") or ""),
            ),
        }
        partition_bundle_snapshots: dict[
            str, tuple[dict[str, object], ...]
        ] = {}
        try:
            baseline_ids = getattr(
                library,
                "pre_worker_retrieval_baseline_bundle_ids",
                None,
            )
            recovered_ids = getattr(
                library,
                "pre_worker_recovered_bundle_ids",
                None,
            )
            concurrent_ids = getattr(
                library,
                "pre_worker_concurrent_bundle_ids",
                None,
            )
            if baseline_ids is None or recovered_ids is None:
                hits = library.search(
                    need.consumer_statement or need.target_statement,
                    **search_kwargs,
                )
            else:
                partitioned_search = getattr(library, "search_partitions", None)
                if callable(partitioned_search):
                    result = partitioned_search(
                        need.consumer_statement or need.target_statement,
                        partitions={
                            "baseline": tuple(baseline_ids),
                            "recovered": tuple(recovered_ids),
                            "concurrent": tuple(concurrent_ids or ()),
                        },
                        **search_kwargs,
                    )
                    partition_hits = dict(result.get("hits") or {})
                    partition_ids = dict(result.get("bundle_ids") or {})
                    partition_bundle_snapshots = dict(
                        result.get("bundle_snapshots") or {}
                    )
                    library.pre_worker_concurrent_bundle_ids = frozenset(
                        partition_ids.get("concurrent") or ()
                    )
                    hits = [
                        *list(partition_hits.get("baseline") or ())[:1],
                        *list(partition_hits.get("recovered") or ())[:1],
                        *list(partition_hits.get("concurrent") or ())[:1],
                    ]
                else:
                    # Compatibility libraries without the atomic partitioned
                    # operation retain the same semantics. The production
                    # library performs this inventory and all three searches
                    # from one serialized integrity-checked snapshot.
                    live_concurrent_ids = set(concurrent_ids or ())
                    try:
                        current_ids = {
                            str(getattr(bundle, "bundle_id", "") or "")
                            for bundle in library.store.iter_bundles()
                            if str(getattr(bundle, "bundle_id", "") or "")
                        }
                        live_concurrent_ids.update(
                            current_ids.difference(baseline_ids, recovered_ids)
                        )
                        library.pre_worker_concurrent_bundle_ids = frozenset(
                            live_concurrent_ids
                        )
                    except Exception:
                        pass
                    baseline_hits = library.search(
                        need.consumer_statement or need.target_statement,
                        **search_kwargs,
                        eligible_bundle_ids=tuple(baseline_ids),
                    )
                    recovered_hits = library.search(
                        need.consumer_statement or need.target_statement,
                        **search_kwargs,
                        eligible_bundle_ids=tuple(recovered_ids),
                    )
                    concurrent_hits = (
                        library.search(
                            need.consumer_statement or need.target_statement,
                            **search_kwargs,
                            eligible_bundle_ids=tuple(live_concurrent_ids),
                        )
                        if live_concurrent_ids
                        else ()
                    )
                    hits = [
                        *baseline_hits[:1],
                        *recovered_hits[:1],
                        *concurrent_hits[:1],
                    ]
        except Exception as exc:
            return self._optional_retrieval_deferred(
                session,
                need,
                started,
                boundary="search",
                exc=exc,
            )
        hits = [
            hit
            for hit in hits
            if hit.score >= self.min_retrieval_score
            and _theory_statement_advances_need(
                str(getattr(hit, "type_text", "") or ""),
                need,
                candidate_name=str(getattr(hit, "fq_name", "") or ""),
            )
        ]
        if hits:
            chosen = hits[0]
            chosen_hits = tuple(
                dict.fromkeys(hit.bundle_id for hit in hits)
            )
            try:
                changed = session.install_theory_bundles(chosen_hits)
            except Exception as exc:
                return self._optional_retrieval_deferred(
                    session,
                    need,
                    started,
                    boundary="context_install",
                    exc=exc,
                )
            validated_bundle_ids = chosen_hits
            if partition_bundle_snapshots:
                records_by_id: dict[str, dict[str, object]] = {}
                for bundle_id in chosen_hits:
                    for item in partition_bundle_snapshots.get(bundle_id, ()):
                        record_id = str(item.get("bundle_id") or "").strip()
                        if record_id:
                            records_by_id.setdefault(record_id, item)
                validated_bundle_ids = tuple(records_by_id) or chosen_hits
            else:
                snapshot = getattr(library, "snapshot", None)
            if not partition_bundle_snapshots and callable(snapshot):
                try:
                    validated_bundle_ids = tuple(
                        str(item.get("bundle_id") or "").strip()
                        for item in snapshot(chosen_hits)
                        if isinstance(item, dict)
                        and str(item.get("bundle_id") or "").strip()
                    ) or chosen_hits
                except Exception:
                    # Installation already validated the exact selection; a
                    # snapshot observability failure must not discard useful
                    # context or narrow its durable receipt.
                    validated_bundle_ids = chosen_hits
            self._tell_conversation(
                session,
                module_name=chosen.module_name,
                declarations=tuple(
                    (hit.fq_name, hit.type_text) for hit in hits
                ),
            )
            if getattr(library, "mode", "off") != "build":
                session.theory_attempted_need_ids.add(need.need_id)
            library.needs.record_outcome(
                need.need_id,
                status="context_available",
                diagnostic="published_theory_context_retrieved",
                bundle_id=chosen.bundle_id,
                bundle_ids=validated_bundle_ids,
            )
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "theory_need_id": need.need_id,
                    "theory_verdict": "published_theory_retrieved",
                    "theory_bundle_id": chosen.bundle_id,
                    "theory_context_bundle_ids": list(validated_bundle_ids),
                    "theory_declaration": chosen.fq_name,
                    "theory_context_declarations": [
                        hit.fq_name for hit in hits
                    ],
                    "theory_context_progress": bool(changed),
                    "theory_context_changed": bool(changed),
                    "preserve_frontier_work": True,
                    "preserve_selected_frontier_action": True,
                    "consume_selected_frontier_action": True,
                    "semantic_budget_step_consumed": True,
                    "strong_progress": False,
                },
            )
        if getattr(library, "mode", "off") != "build":
            session.theory_attempted_need_ids.add(need.need_id)
            library.needs.record_outcome(
                need.need_id,
                status="pending",
                diagnostic="published_theory_zero_hit_read_only",
            )
            return self._no_progress(
                started,
                need,
                "published_theory_zero_hit_read_only",
                preserve_frontier_work=True,
                consume_selected_frontier_action=True,
            )
        library.needs.record_outcome(
            need.need_id,
            status="pending",
            diagnostic="published_theory_zero_hit_build_available",
        )
        return self._no_progress(
            started,
            need,
            "published_theory_zero_hit_build_available",
            preserve_frontier_work=True,
            consume_selected_frontier_action=True,
        )

    @staticmethod
    def _record_bundle_ids(record: Any) -> tuple[str, ...]:
        if record is None:
            return ()
        return tuple(getattr(record, "validated_bundle_ids", ()) or ()) or (
            (record.bundle_id,) if getattr(record, "bundle_id", "") else ()
        )

    def _adopt_durable_context(
        self,
        session: Any,
        need: TheoryNeed,
        durable_record: Any,
        started: float,
    ) -> Optional[MiniOutcome]:
        if durable_record is None or durable_record.status not in {
            "context_available",
            "resolved",
        }:
            return None
        durable_bundle_ids = self._record_bundle_ids(durable_record)
        if not durable_bundle_ids:
            return None
        imported_bundle_ids = set(
            getattr(session, "theory_imported_bundle_ids", ()) or ()
        )
        bound_bundle_ids = set(
            getattr(session, "theory_consumer_bundle_ids_by_need_id", {}).get(
                need.need_id,
                (),
            )
            or ()
        )
        import_needed = not set(durable_bundle_ids).issubset(imported_bundle_ids)
        binding_needed = not set(durable_bundle_ids).issubset(bound_bundle_ids)
        if not import_needed and not binding_needed:
            return None
        library = session.theory_library
        try:
            changed = session.install_theory_bundles(durable_bundle_ids)
            durable_bundles = tuple(
                bundle
                for bundle_id in durable_bundle_ids
                if (
                    bundle := library.store.load(
                        bundle_id,
                        domain=need.domain,
                    )
                )
                is not None
            )
        except TheoryStoreError as exc:
            return self._no_progress(
                started,
                need,
                f"published_theory_import_rejected:{exc}",
                preserve_frontier_work=True,
            )
        for bundle in durable_bundles:
            self._tell_conversation(
                session,
                module_name=bundle.module_name,
                declarations=tuple(
                    (declaration.fq_name, declaration.type_text)
                    for declaration in bundle.declarations
                ),
            )
        context_progress = bool(changed or binding_needed)
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=False,
            cost_seconds=time.monotonic() - started,
            metadata={
                "theory_need_id": need.need_id,
                "theory_verdict": "durable_theory_context_imported",
                "theory_bundle_id": durable_bundle_ids[-1],
                "theory_bundle_ids": durable_bundle_ids,
                "theory_progress": False,
                "theory_context_progress": context_progress,
                "theory_context_changed": context_progress,
                "preserve_selected_frontier_action": True,
                "preserve_frontier_work": True,
                "consume_selected_frontier_action": True,
                "strong_progress": False,
            },
        )

    @staticmethod
    def _derive_need_from_record(
        session: Any,
        record: dict[str, Any],
    ) -> TheoryNeed:
        """Derive a theory need without mutating scheduler or durable state."""

        graph_record = record.get("graph_record")
        merged = {**(graph_record if isinstance(graph_record, dict) else {}), **record}
        consumer_statement = _first_text(
            merged,
            "target_statement",
            "parent_repair_target_statement",
            "formalization_bridge_parent_statement",
            "materialization_parent_statement",
            "decomposition_request_statement",
            "materialization_seed",
            "obligation_reason",
        )
        if not consumer_statement:
            consumer_statement = str(getattr(session.dossier, "root_statement", "") or "")
        root_contract_statement = str(
            getattr(getattr(session, "dossier", None), "root_statement", "") or ""
        ).strip()
        merged["consumer_contract_hash"] = graph_text_hash(
            graph_statement_key(consumer_statement) or consumer_statement
        )
        if root_contract_statement:
            merged["root_contract_statement"] = root_contract_statement
            merged["root_contract_hash"] = graph_text_hash(
                graph_statement_key(root_contract_statement)
                or root_contract_statement
            )
        consumer_node = _first_text(
            merged,
            "node_id",
            "graph_node_id",
            "obligation_id",
            "claim_id",
        ) or "root"
        root_name = str(getattr(session.problem, "theorem_name", "") or "root")
        domain = str(getattr(session, "theory_domain", "") or "general mathematics")
        required_name = _first_text(
            merged,
            "required_declaration_name",
            "formalization_required_declaration_name",
        )
        requested_kind = str(
            merged.get("theory_need_kind")
            or merged.get("formalization_need_kind")
            or DomainTheoryAction._infer_need_kind(merged)
        ).strip()
        if requested_kind not in {
            "definition",
            "structure",
            "instance",
            "notation",
            "bridge_lemma",
            "theorem_family",
        }:
            requested_kind = "bridge_lemma"
        description = _first_text(
            merged,
            "mathematical_description",
            "obligation_reason",
            "blocker",
            "reason",
        ) or consumer_statement
        graph = getattr(getattr(session, "dossier", None), "proof_graph", None)
        nodes = getattr(graph, "nodes", {}) if graph is not None else {}
        # ``source_node_id`` identifies the parent that *requires* this
        # obligation (source -> obligation in ProofGraph), not a prerequisite
        # of the obligation.  Only explicit dependency nodes point upstream.
        dependency_node_ids = tuple(
            dict.fromkeys(
                (
                    *_string_tuple(merged.get("dependencies")),
                    *_string_tuple(merged.get("dependency_node_ids")),
                )
            )
        )
        inferred_dependency_need_ids = tuple(
            str(getattr(nodes.get(node_id), "metadata", {}).get("theory_need_id") or "").strip()
            for node_id in dependency_node_ids
            if nodes.get(node_id) is not None
            and str(
                getattr(nodes.get(node_id), "metadata", {}).get("theory_need_id")
                or ""
            ).strip()
        )
        dependency_need_ids = tuple(
            dict.fromkeys(
                (
                    *_string_tuple(merged.get("explicit_dependency_need_ids")),
                    *inferred_dependency_need_ids,
                )
            )
        )
        library = getattr(session, "theory_library", None)
        canonical_need_id = getattr(
            getattr(library, "needs", None),
            "canonical_need_id",
            None,
        )
        if callable(canonical_need_id):
            dependency_need_ids = tuple(
                sorted(
                    dict.fromkeys(
                        canonical_need_id(dependency_need_id)
                        for dependency_need_id in dependency_need_ids
                    )
                )
            )
        # A dependency-plan extension is a new executable need version.  This
        # prevents a need already attempted under a weaker graph from being
        # permanently suppressed when later graph evidence adds prerequisites.
        need_id = TheoryNeed.derive_need_id(
            originating_root=root_name,
            domain=domain,
            consumer_node_id=consumer_node,
            consumer_statement=consumer_statement,
            required_name_hint=required_name,
            need_kind=requested_kind,
            required_imports=tuple(
                getattr(session, "theory_default_imports", ("Mathlib",))
            ),
            dependency_need_ids=dependency_need_ids,
        )
        need = TheoryNeed(
            need_id=need_id,
            domain=domain,
            target_statement=consumer_statement,
            need_kind=requested_kind,
            mathematical_description=description,
            originating_root=root_name,
            consumer_node_id=consumer_node,
            consumer_statement=consumer_statement,
            required_name_hint=required_name,
            evidence_kind=str(merged.get("work_type") or "formalization_required"),
            evidence_payload=merged,
            required_imports=tuple(getattr(session, "theory_default_imports", ("Mathlib",))),
            dependency_need_ids=dependency_need_ids,
        )
        return need

    @staticmethod
    def _adopt_need_for_record(
        session: Any,
        record: dict[str, Any],
        need: TheoryNeed,
    ) -> None:
        """Publish one already-validated need contract to durable/session state."""

        graph_record = record.get("graph_record")
        merged = {**(graph_record if isinstance(graph_record, dict) else {}), **record}
        graph = getattr(getattr(session, "dossier", None), "proof_graph", None)
        nodes = getattr(graph, "nodes", {}) if graph is not None else {}
        consumer_node = need.consumer_node_id
        library = getattr(session, "theory_library", None)
        node = nodes.get(consumer_node) if isinstance(nodes, dict) else None
        previous_need_id = ""
        if node is not None and isinstance(getattr(node, "metadata", None), dict):
            previous_need_id = str(
                node.metadata.get("theory_need_id") or ""
            ).strip()
        if not previous_need_id:
            previous_need_id = _first_text(merged, "theory_need_id")
        if (
            previous_need_id
            and previous_need_id != need.need_id
            and library is not None
            and hasattr(library.needs, "supersede_need")
        ):
            affected_need_ids = library.needs.supersede_need(
                previous_need_id,
                need,
            )
            getattr(session, "theory_attempted_need_ids", set()).difference_update(
                affected_need_ids
            )
            attempt_counts = getattr(session, "theory_need_attempt_counts", {})
            for affected_need_id in affected_need_ids:
                attempt_counts.pop(affected_need_id, None)
            frontier_map = getattr(
                session,
                "theory_need_ids_by_frontier_key",
                {},
            )
            for frontier_key, mapped_need_id in tuple(frontier_map.items()):
                if mapped_need_id in affected_need_ids:
                    frontier_map.pop(frontier_key, None)
        for target in (
            record,
            getattr(session, "selected_work_item_record", None),
        ):
            if isinstance(target, dict):
                target["theory_need_id"] = need.need_id
                target["theory_need_kind"] = need.need_kind
                target["mathematical_description"] = need.mathematical_description
                target["resolved_dependency_need_ids"] = list(
                    need.dependency_need_ids
                )
        if node is not None and isinstance(getattr(node, "metadata", None), dict):
            node.metadata.update(
                {
                    "theory_need_id": need.need_id,
                    "theory_need_kind": need.need_kind,
                    "mathematical_description": need.mathematical_description,
                    "resolved_dependency_need_ids": list(
                        need.dependency_need_ids
                    ),
                }
            )
        selected_work_item = getattr(session, "selected_work_item", None)
        frontier_key_getter = getattr(session, "_frontier_work_key", None)
        need_ids_by_frontier = getattr(
            session,
            "theory_need_ids_by_frontier_key",
            None,
        )
        if (
            selected_work_item is not None
            and callable(frontier_key_getter)
            and isinstance(need_ids_by_frontier, dict)
        ):
            need_ids_by_frontier[frontier_key_getter(selected_work_item)] = need.need_id

    @staticmethod
    def _need_from_record(session: Any, record: dict[str, Any]) -> TheoryNeed:
        """Derive and adopt a theory need after authoritative validation."""

        need = DomainTheoryAction._derive_need_from_record(session, record)
        DomainTheoryAction._adopt_need_for_record(session, record, need)
        return need

    @staticmethod
    def _infer_need_kind(record: dict[str, Any]) -> str:
        evidence = " ".join(
            str(record.get(key) or "")
            for key in (
                "error_type",
                "lean_error_type",
                "obligation_reason",
                "reason",
                "blocker",
                "mathematical_description",
            )
        ).lower()
        if "failed to synthesize" in evidence or "typeclass" in evidence:
            return "instance"
        if "notation" in evidence or "parser" in evidence:
            return "notation"
        if "structure" in evidence:
            return "structure"
        if "unknown identifier" in evidence or "unknown constant" in evidence:
            return "definition"
        return "bridge_lemma"

    @staticmethod
    def _dependencies_ready(library: Any, need: TheoryNeed) -> bool:
        for dependency_need_id in need.dependency_need_ids:
            record = library.needs.get(dependency_need_id)
            if (
                record is None
                or record.status != "resolved"
                or not (
                    tuple(getattr(record, "validated_bundle_ids", ()) or ())
                    or record.bundle_id
                )
            ):
                return False
        return True

    def _no_progress(
        self,
        started: float,
        need: TheoryNeed,
        verdict: str,
        *,
        preserve_frontier_work: bool = False,
        consume_selected_frontier_action: bool = False,
        preserve_action_budget: bool = False,
        semantic_budget_step_consumed: Optional[bool] = None,
    ) -> MiniOutcome:
        if semantic_budget_step_consumed is None:
            semantic_budget_step_consumed = self.stage == "retrieve"
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=False,
            cost_seconds=time.monotonic() - started,
            metadata={
                "theory_need_id": need.need_id,
                "theory_verdict": verdict,
                "preserve_frontier_work": preserve_frontier_work,
                "consume_selected_frontier_action": consume_selected_frontier_action,
                "preserve_action_budget": preserve_action_budget,
                "semantic_budget_step_consumed": bool(
                    semantic_budget_step_consumed
                ),
            },
        )

    def _optional_retrieval_deferred(
        self,
        session: Any,
        need: TheoryNeed,
        started: float,
        *,
        boundary: str,
        exc: Exception,
    ) -> MiniOutcome:
        """Isolate an ordinary persistence failure to the retrieval lane."""

        if classify_llm_exception(exc).terminal:
            raise exc
        session.theory_context_hit_need_ids.add(need.need_id)
        return self._no_progress(
            started,
            need,
            (
                "published_theory_retrieval_deferred:"
                f"{boundary}:{type(exc).__name__}:{exc}"
            ),
            preserve_frontier_work=True,
            consume_selected_frontier_action=True,
            semantic_budget_step_consumed=True,
        )

    def _optional_build_deferred(
        self,
        session: Any,
        need: TheoryNeed,
        started: float,
        *,
        boundary: str,
        exc: Exception,
    ) -> MiniOutcome:
        """Isolate ordinary build-infrastructure failure from math search."""

        if classify_llm_exception(exc).terminal:
            raise exc
        session.theory_attempted_need_ids.add(need.need_id)
        return self._no_progress(
            started,
            need,
            (
                "domain_theory_build_deferred:"
                f"{boundary}:{type(exc).__name__}:{exc}"
            ),
            preserve_frontier_work=True,
            consume_selected_frontier_action=True,
            semantic_budget_step_consumed=True,
        )

    @staticmethod
    def _with_outcome_metadata(
        outcome: MiniOutcome,
        **metadata: Any,
    ) -> MiniOutcome:
        return replace(
            outcome,
            metadata={**dict(outcome.metadata or {}), **metadata},
        )

    @staticmethod
    def _tell_conversation(
        session: Any,
        *,
        module_name: str,
        declarations: tuple[tuple[str, str], ...],
    ) -> None:
        append_user = getattr(getattr(session, "conv", None), "append_user", None)
        if not callable(append_user):
            return
        declaration_text = "\n".join(
            f"- `{name}` : `{type_text}`" for name, type_text in declarations
        )
        append_user(
            "A Mini-owned theory bundle was independently Lean-verified and is "
            f"now imported as `{module_name}`. Its reusable declarations are:\n"
            f"{declaration_text}\nUse them only when they satisfy the current goal."
        )
