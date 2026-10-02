"""Session-owned memory orchestration over existing retrieval and proof gates."""

from __future__ import annotations

import logging
import contextlib
import re
import time
import uuid
import sqlite3
import weakref
from collections import OrderedDict
from threading import RLock
from dataclasses import replace
from pathlib import Path
from typing import Any, Mapping

from .budget import MemoryAllocation, MemoryBudget
from .config import MemoryConfig
from .model import (
    EligibilityPolicy,
    GenerationPin,
    MemoryEvent,
    MemoryProvenance,
    canonical_json,
    content_digest,
)

_LOG = logging.getLogger(__name__)
_SESSIONS: dict[int, weakref.ReferenceType[Any]] = {}
_LOCAL_EVENTS: dict[str, OrderedDict[str, str]] = {}
_LOCAL_EVENTS_LOCK = RLock()


def default_memory_root() -> Path:
    return Path.home() / ".local" / "share" / "ensemble-prover" / "mathematical-memory"


def session_for_dossier(dossier: Any) -> Any:
    reference = _SESSIONS.get(id(dossier))
    session = reference() if reference is not None else None
    return session if session is not None and session.dossier is dossier else None


def observe_application(dossier: Any, **payload: Any) -> None:
    session = session_for_dossier(dossier)
    service = getattr(session, "mathematical_memory", None)
    if service is not None:
        service.record_legacy_application(payload)


def observe_use(dossier: Any, payload: Mapping[str, Any]) -> None:
    session = session_for_dossier(dossier)
    service = getattr(session, "mathematical_memory", None)
    if service is not None:
        service.record_use(payload)


class MathematicalMemoryService:
    def __init__(
        self,
        session: Any,
        config: MemoryConfig,
        policy: EligibilityPolicy | None = None,
        *,
        allocation: MemoryAllocation | None = None,
        request_owner: bool = True,
        provenance_registry: Any = None,
    ) -> None:
        from .catalog import MemoryCatalog

        self.session = weakref.ref(session)
        self.provenance_registry = provenance_registry
        self.request_owner = request_owner
        self.config = config
        output = getattr(getattr(session, "recorder", None), "output_dir", None)
        self.allocation = allocation or MemoryAllocation(
            config.action_seconds, run_dir=Path(output) if output is not None else None
        )
        self.allocation.attach(session)
        self.known_declarations: dict[str, Any] = {}
        self.known_candidate_ids: dict[str, str] = {}
        self.profile_bundle_bindings: dict[str, tuple[str, ...]] = {}
        self._local_context_sources: dict[int, tuple[Any, str, str]] = {}
        self._event_deliveries: dict[str, tuple[MemoryEvent, str]] = {}
        self._pending_solution: dict[str, Any] | None = None
        self._reduction_bindings: dict[str, tuple[Any, str, str]] = {}
        self._memory_support_names: dict[str, str] = {}
        self._memory_import_owners: set[str] = set()
        self._local_order = 0
        self.candidate_coverage: dict[str, Any] = {}
        self.catalog = MemoryCatalog(
            config.root,
            outbox_event_cap=config.outbox_event_cap,
            outbox_byte_cap=config.outbox_byte_cap,
            artifact_byte_cap=config.artifact_byte_cap,
            query_scan_cap=config.query_scan_cap,
            event_count_cap=config.event_count_cap,
            event_byte_cap=config.event_byte_cap,
            query_byte_cap=config.query_byte_cap,
            artifact_store_byte_cap=config.artifact_store_byte_cap,
            artifact_count_cap=config.artifact_count_cap,
            current_authority=self._event_authority,
            event_authority=self._event_integrity,
        )
        self.run_id = str(
            getattr(getattr(session, "recorder", None), "output_dir", "")
            or session.session_activation_id
        )
        self.scope_id = content_digest(
            {
                "run": self.run_id,
                "scope": session.scope,
                "target": str(getattr(session.problem, "statement_type", "")),
            }
        )
        self.policy = policy or EligibilityPolicy(
            visible_scopes=(("session", self.scope_id),)
            + ((("campaign", config.campaign_id),) if config.campaign_id else ()),
            allow_incomplete_session=True,
        )
        self.policy_id = content_digest(self.policy.to_record())
        self.health = "ready"
        self.last_view: dict[str, Any] = {}
        self.request_store: Any = None
        output = getattr(getattr(session, "recorder", None), "output_dir", None)
        if output is not None and request_owner and session.parent is None:
            from .requests import MemoryRequestStore

            self.request_store = MemoryRequestStore(Path(output))
            self.request_store.reconcile_inflight()
            if not getattr(self.request_store, "owns_dispatch", True):
                self.request_owner = False
                self.request_store = None

    def _event_authority(self, provenance: MemoryProvenance, event_id: str) -> bool:
        registry = self.provenance_registry
        if provenance.complete:
            return bool(
                registry is not None
                and registry.current_authority(provenance, event_id)
            )
        if provenance.scope != "session" or provenance.scope_id != self.scope_id:
            return False
        with _LOCAL_EVENTS_LOCK:
            admitted = event_id in _LOCAL_EVENTS.get(
                str(Path(self.config.root).absolute()), {}
            )
        return admitted and (
            registry is None or registry.current_authority(provenance, event_id)
        )

    def _event_integrity(self, event: MemoryEvent) -> bool:
        if event.provenance.complete:
            return True
        with _LOCAL_EVENTS_LOCK:
            return (
                _LOCAL_EVENTS.get(str(Path(self.config.root).absolute()), {}).get(
                    event.event_id
                )
                == event.payload_digest
            )

    def check_budget(self, budget: MemoryBudget) -> None:
        budget.check_cancelled()
        if (
            budget.max_heartbeats <= 0
            or budget.memory_mb <= 0
            or budget.concurrency <= 0
        ):
            raise TimeoutError("memory checker resource allowance exhausted")
        session = self.session()
        if session is None:
            raise RuntimeError("memory session expired")
        dispatch = str(getattr(session, "_inflight_action_dispatch_id", "") or "")
        if dispatch and dispatch != budget.owner_id:
            from ensemble_prover.deadline_guard import DispatchScopeDetached

            raise DispatchScopeDetached("memory action dispatch changed")

    def context(self) -> tuple[str, str, tuple[str, ...]]:
        from ensemble_prover.proof_dossier import active_root_target_statement

        session = self.session()
        if session is None:
            raise RuntimeError("memory session expired")
        statement = str(getattr(session.conv, "goal_statement", "") or "")
        if getattr(session, "scope", "problem") == "problem":
            statement = (
                active_root_target_statement(
                    session.dossier,
                    require_single=True,
                    require_no_hypotheses=False,
                    include_hypotheses=True,
                )
                or statement
            )
        preamble = str(session.acceptance_preamble())
        lemmas = tuple(session.dossier.verified_helper_blocks())
        return statement, preamble, lemmas

    def context_id(self) -> str:
        statement, preamble, lemmas = self.context()
        return content_digest(
            {
                "statement": statement,
                "preamble": preamble,
                "helpers": lemmas,
                "policy": self.policy_id,
            }
        )

    def retrieval_revision(self) -> str:
        """Track only the retrieval pool currently admitted by its existing pins."""
        session = self.session()
        return str(getattr(getattr(session, "searcher", None), "index_snapshot_id", ""))

    def provenance(
        self,
        source_ids: tuple[str, ...] = (),
        *,
        accepted: bool = False,
        complete: bool = False,
    ) -> MemoryProvenance:
        session = self.session()
        if session is None:
            raise RuntimeError("memory session expired")
        if self.provenance_registry is not None and source_ids:
            authorized = self.provenance_registry.issue_provenance(
                source_ids, run_id=self.run_id, accepted=accepted
            )
            if authorized is not None:
                return authorized
        self._local_order += 1
        problem_id = content_digest(str(getattr(session.problem, "statement_type", "")))
        # Unknown family/ancestry stays session-local; a digest cannot fill it.
        # A configured campaign label and local counter are not authenticated
        # controller chronology. Only issue_provenance can make this portable.
        complete = False
        scope = "session"
        return MemoryProvenance(
            source_record_ids=source_ids,
            problem_ids=(problem_id,),
            family_ids=(self.config.family_id,) if self.config.family_id else (),
            scope=scope,
            scope_id=self.config.campaign_id if scope == "campaign" else self.scope_id,
            campaign_id="",
            run_id=self.run_id,
            producer_order=None,
            acceptance_order=None,
            complete=complete,
        )

    def record(
        self,
        kind: str,
        payload: Mapping[str, Any],
        *,
        event_id: str = "",
        operation_id: str = "",
        attempt_id: str = "",
        provenance: MemoryProvenance | None = None,
        budget: MemoryBudget | None = None,
        additional_evidence: tuple[Any, ...] = (),
        retry_of: str = "",
    ) -> MemoryEvent | None:
        try:
            if budget is not None:
                self.check_budget(budget)
            session = self.session()
            if session is None:
                return None
            operation = (
                operation_id
                or event_id
                or str(getattr(session, "_inflight_action_dispatch_id", ""))
                or uuid.uuid4().hex
            )
            deadline = (
                budget.deadline_monotonic
                if budget is not None
                else time.monotonic() + 0.025
            )
            artifact = self.catalog.put_artifact(
                canonical_json(dict(payload)).encode(),
                kind="memory_event",
                deadline_monotonic=deadline,
            )
            event = MemoryEvent(
                event_id=event_id or uuid.uuid4().hex,
                operation_id=operation,
                attempt_id=attempt_id or operation,
                kind=kind,
                payload=dict(payload),
                provenance=provenance
                or (
                    self.candidate_provenance(str(payload["candidate_id"]))
                    if payload.get("candidate_id")
                    else self.provenance()
                ),
                evidence=(artifact,) + additional_evidence,
                retry_of=retry_of,
            )
            intent = content_digest(
                {
                    "kind": kind,
                    "payload": dict(payload),
                    "operation_id": event.operation_id,
                    "attempt_id": event.attempt_id,
                    "retry_of": retry_of,
                    "evidence": [ref.to_record() for ref in event.evidence],
                    "provenance": {
                        key: value
                        for key, value in event.provenance.to_record().items()
                        if key not in {"producer_order", "acceptance_order"}
                    },
                }
            )
            previous = self._event_deliveries.get(event.event_id)
            if previous is not None and previous[1] == intent:
                event = previous[0]
            with _LOCAL_EVENTS_LOCK:
                issued = _LOCAL_EVENTS.setdefault(
                    str(Path(self.config.root).absolute()), OrderedDict()
                )
                issued[event.event_id] = event.payload_digest
                while len(issued) > 4096:
                    issued.popitem(last=False)
            self._event_deliveries[event.event_id] = (event, intent)
            while len(self._event_deliveries) > 4096:
                self._event_deliveries.pop(next(iter(self._event_deliveries)))
            result = self.catalog.append(event, deadline_monotonic=deadline)
            if result.status not in {"Stored", "Duplicate", "stored", "duplicate"}:
                self.health = str(result.status)
                return None
            return event
        except (OSError, ValueError, RuntimeError, TimeoutError, sqlite3.Error) as exc:
            self.health = "unavailable"
            _LOG.debug("Advisory memory persistence unavailable: %s", exc)
            return None

    def record_legacy_application(self, payload: Mapping[str, Any]) -> None:
        # This boundary knows operational probing, never ordinary acceptance.
        applicable = payload.get("applicable") is True
        residuals = tuple(payload.get("remaining_goals") or ())
        kind = str(payload.get("error_kind") or "")
        semantic = kind in {"type_mismatch", "invalid_decl_name", "no_applicable_probe"}
        outcome = (
            ("elaborated_partial" if residuals else "elaborated_closed")
            if applicable
            else ("probe_rejected" if semantic else "probe_inconclusive")
        )
        event = self.record(
            "application",
            {
                **dict(payload),
                "outcome": outcome,
                "legacy": True,
                "argument_capture_complete": False,
                "environment_id": self.context_id(),
                "goal_id": self.context_id(),
                "statement": self.context()[0],
                "candidate_id": self.known_candidate_ids.get(
                    str(payload.get("decl_name", "")), ""
                ),
            },
            provenance=self.application_provenance(
                self.known_candidate_ids.get(str(payload.get("decl_name", "")), "")
            ),
        )
        if event is not None:
            self.emit(
                goal_id=self.context_id(),
                applications=[{**dict(event.payload), "event_id": event.event_id}],
            )

    def record_use(
        self, payload: Mapping[str, Any], *, root_export: bool = False
    ) -> None:
        # Called only after existing observed-proof occurrence validation.
        helpers = dict(payload.get("helpers") or {})
        from ensemble_prover.proof_dossier import canonical_lean_identifier

        direct = {
            canonical_lean_identifier(str(name))
            for name in payload.get("direct_constants", ())
        }
        reachable = {
            canonical_lean_identifier(str(name))
            for name in payload.get("reachable_constants", ())
        }
        for name, profile in self.known_declarations.items():
            canonical = canonical_lean_identifier(name)
            helpers.setdefault(
                name,
                {
                    "source_hash": profile.declaration_id,
                    "usage": (
                        "direct"
                        if canonical in direct
                        else "transitive" if canonical in reachable else "unused"
                    ),
                },
            )
        consumer_id = content_digest(
            {key: value for key, value in payload.items() if key != "helpers"}
        )
        for name, binding in helpers.items():
            if binding.get("usage") not in {"direct", "transitive", "unused"}:
                continue
            usage_provenance = self.application_provenance(
                self.known_candidate_ids.get(name, ""), accepted=True
            )
            if name not in self.known_candidate_ids:
                usage_provenance = replace(
                    usage_provenance,
                    source_record_ids=tuple(
                        dict.fromkeys(
                            (
                                *usage_provenance.source_record_ids,
                                binding["source_hash"],
                            )
                        )
                    ),
                )
            event_id = content_digest(
                {
                    "run": self.run_id,
                    "consumer": consumer_id,
                    "source": binding["source_hash"],
                    "kind": binding["usage"],
                    "root_export": root_export,
                    "provenance": usage_provenance.to_record(),
                }
            )
            self.record(
                "use",
                {
                    **dict(payload),
                    "consumer_id": consumer_id,
                    "declaration_name": name,
                    "declaration_id": binding["source_hash"],
                    "usage": binding["usage"],
                    "root_export": root_export,
                    "candidate_id": self.known_candidate_ids.get(name, ""),
                },
                event_id=event_id,
                operation_id=consumer_id,
                attempt_id=consumer_id,
                provenance=usage_provenance,
            )

    def candidate_provenance(
        self, candidate_id: str, *, accepted: bool = False
    ) -> MemoryProvenance:
        profile = next(
            (
                self.known_declarations[name]
                for name, identity in self.known_candidate_ids.items()
                if identity == candidate_id
            ),
            None,
        )
        registry = self.provenance_registry
        if (
            profile is not None
            and profile.certified_source_binding
            and registry is not None
            and registry.source_matches(candidate_id, profile.source_digest)
        ):
            return self.provenance((candidate_id,), accepted=accepted)
        return replace(
            self.provenance(accepted=accepted),
            source_record_ids=(candidate_id,) if candidate_id else (),
        )

    def bind_context_source_owner(
        self, helper: Any, source_record_id: str, *, source_digest: str
    ) -> bool:
        """Bind the actual admitted record to a local owner without portability.

        Only the admission/profile seam may make this binding. Equal bytes in
        an unrelated record do not select an owner, and a denied owner remains
        bound so subsequent context admission fails closed.
        """
        from ensemble_prover.proof_dossier import VerifiedHelper
        from .profiles import digest

        session = self.session()
        if (
            session is None
            or not isinstance(helper, VerifiedHelper)
            or not any(
                record is helper for record in session.dossier.verified_helpers.values()
            )
            or not source_record_id
            or digest(helper.source) != source_digest
        ):
            return False
        key = id(helper)
        previous = self._local_context_sources.get(key)
        if previous is not None and (
            previous[0]() is not helper
            or previous[1:] != (source_digest, source_record_id)
        ):
            raise ValueError("immutable local admitted-context owner/version conflict")
        # This association grants no source permission. Keep denied owners
        # attached too, so revocation during admission cannot become an
        # anonymous helper on the next application.

        def expired(reference: Any) -> None:
            current = self._local_context_sources.get(key)
            if current is not None and current[0] is reference:
                self._local_context_sources.pop(key, None)

        self._local_context_sources[key] = (
            weakref.ref(helper, expired),
            source_digest,
            source_record_id,
        )
        # Persist only the obligation to revisit source permission. A replayed
        # tag cannot recreate this process-owned admission binding.
        tag = "mathematical_memory_owned_context"
        if tag not in helper.provenance_tags:
            helper.provenance_tags.append(tag)
        return True

    def _local_context_source_id(self, helper: Any) -> str | None:
        from .profiles import digest

        binding = self._local_context_sources.get(id(helper))
        if binding is None or binding[0]() is not helper:
            return None
        if digest(helper.source) != binding[1]:
            raise ValueError("local admitted context source version changed")
        return binding[2]

    def _application_source_ids(self, candidate_id: str) -> tuple[str, ...] | None:
        """Bound every admitted record to its owner; omitted support denies use."""
        from .profiles import digest

        session = self.session()
        _, _, lemmas = self.context()
        records = (
            tuple(getattr(session.dossier, "verified_helpers", {}).values())
            if session is not None
            else ()
        )
        bundles = tuple(getattr(session, "theory_imported_bundle_ids", ()))
        cap = self.config.cheap_candidate_cap
        if len(lemmas) > cap or len(records) > cap or len(bundles) > cap:
            return None
        registry = self.provenance_registry
        identities = [candidate_id] if candidate_id else []
        retired_imports = getattr(session, "mathematical_memory_state", {}).get(
            "retired_import_owners", ()
        )
        if (
            not isinstance(retired_imports, (list, tuple))
            or len(retired_imports) > cap
            or any(not isinstance(identity, str) for identity in retired_imports)
            or not set(retired_imports).issubset(self._memory_import_owners)
        ):
            return None
        identities.extend(sorted(self._memory_import_owners))
        for helper in records:
            try:
                local_owner = self._local_context_source_id(helper)
                controller_owner = (
                    registry.context_source_id(self.run_id, helper)
                    if registry is not None
                    else None
                )
                if local_owner and controller_owner and local_owner != controller_owner:
                    return None
                owner = controller_owner or local_owner
                if not owner and (
                    helper.phase.startswith("mathematical_memory")
                    or "mathematical_memory_owned_context" in helper.provenance_tags
                ):
                    return None
            except ValueError:
                return None
            # A bound but currently denied owner stays in the set. Admission
            # rejects it; it never turns into anonymous local discovery.
            identities.append(owner or "context_source:" + digest(helper.source))
            if registry is not None and local_owner and not controller_owner:
                # Local observation is not a trusted portable context binding.
                # Retain its owner for revocation and its unknown context marker
                # so restricted admission and complete history remain closed.
                identities.append("context_source:" + digest(helper.source))
        if lemmas and not records:
            identities.extend("context_source:" + digest(block) for block in lemmas)
        for bundle_id in bundles:
            if registry is not None and registry.has_source(bundle_id):
                identities.append(bundle_id)
                continue
            bound = tuple(
                self.known_candidate_ids[name]
                for name, profile in self.known_declarations.items()
                if profile.certified_source_binding
                and name in self.known_candidate_ids
                and bundle_id in self.profile_bundle_bindings.get(name, ())
            )
            for name, profile in self.known_declarations.items():
                if (
                    name in self.known_candidate_ids
                    and self.known_candidate_ids[name] in bound
                    and registry is not None
                    and registry.has_source(self.known_candidate_ids[name])
                    and not registry.source_matches(
                        self.known_candidate_ids[name], profile.source_digest
                    )
                ):
                    return None
            identities.extend(bound or (bundle_id,))
        result = tuple(dict.fromkeys(identities))
        if len(result) > cap or (
            registry is not None and len(result) > registry.closure_cap
        ):
            return None
        return result

    def application_provenance(
        self, candidate_id: str, *, accepted: bool = False
    ) -> MemoryProvenance:
        """Historical provenance includes the consuming event and all support."""
        base = self.candidate_provenance(candidate_id, accepted=accepted)
        identities = self._application_source_ids(candidate_id)
        if identities is None:
            # No partial source list may be mistaken for complete local history.
            return replace(
                self.provenance(accepted=accepted),
                source_record_ids=(candidate_id,) if candidate_id else (),
                complete=False,
                scope_id="",
            )
        registry = self.provenance_registry
        if base.complete and registry is not None:
            current = registry.issue_provenance(
                identities, run_id=self.run_id, accepted=accepted
            )
            if current is not None:
                return current
        return replace(
            self.provenance(accepted=accepted),
            source_record_ids=identities,
            complete=False,
        )

    def _sources_admitted(
        self, identities: tuple[str, ...], *, budget: MemoryBudget | None = None
    ) -> bool:
        registry = self.provenance_registry
        deadline = (
            budget.deadline_monotonic
            if budget is not None
            else time.monotonic() + 0.025
        )
        if budget is not None:
            self.check_budget(budget)
        if registry is not None and not registry.consumer_eligible(
            self.run_id, self.policy
        ):
            return False
        known = tuple(
            identity
            for identity in identities
            if registry is not None and registry.has_source(identity)
        )
        if registry is not None and known:
            admission = registry.admit_sources(
                known, run_id=self.run_id, policy=self.policy
            )
            if admission is None:
                return False
            checked = tuple(dict.fromkeys((*identities, *admission.source_record_ids)))
        else:
            checked = identities
        unknown = tuple(identity for identity in identities if identity not in known)
        if unknown or not identities:
            # Only an unrestricted current-session read may use unregistered
            # source metadata. This fallback never erases a registered denial.
            if not self.policy.permits(self.provenance()):
                return False
        cap = (
            registry.closure_cap
            if registry is not None
            else self.config.cheap_candidate_cap
        )
        if len(checked) > cap:
            return False
        return all(
            self.catalog.source_eligible(
                identity, self.policy, deadline_monotonic=deadline
            )
            for identity in checked
        )

    def application_eligible(
        self, candidate_id: str, *, budget: MemoryBudget | None = None
    ) -> bool:
        if not self.candidate_eligible(candidate_id, budget=budget):
            return False
        identities = self._application_source_ids(candidate_id)
        return identities is not None and self._sources_admitted(
            identities, budget=budget
        )

    def candidate_eligible(
        self,
        candidate: Any,
        *,
        source_digest: str = "",
        budget: MemoryBudget | None = None,
    ) -> bool:
        """Admit original source ancestry independently of fresh consumer history."""
        identity = str(getattr(candidate, "candidate_id", candidate) or "")
        if not identity or not self._sources_admitted((identity,), budget=budget):
            return False
        registry = self.provenance_registry
        return (
            not source_digest
            or registry is None
            or not registry.has_source(identity)
            or registry.source_matches(identity, source_digest)
        )

    async def capture_goal(self, budget: MemoryBudget) -> Any:
        from .profiles import capture_goal

        session = self.session()
        statement, preamble, lemmas = self.context()
        source = preamble + "\n" + "\n".join(lemmas) + "\n" + statement
        return await capture_goal(
            session.lean,
            statement=statement,
            source=source,
            environment_id=self.context_id(),
            preamble=preamble,
            lemmas=lemmas,
            budget=budget,
        )

    async def find_candidates(
        self, goal: Any, budget: MemoryBudget, pinned_generation: GenerationPin
    ) -> tuple[Any, ...]:
        from ensemble_prover.mathematical_retrieval.model import RetrievalQuery

        session = self.session()
        if session is None or session.searcher is None:
            return ()
        self.check_budget(budget)
        statement, _, _ = self.context()
        query = RetrievalQuery.create(
            target_statement=statement,
            max_candidates=self.config.cheap_candidate_cap,
            index_snapshot_id=str(getattr(session.searcher, "index_snapshot_id", "")),
        )
        retrieve = getattr(session.searcher, "retrieve_async", None)
        if retrieve is None:
            return ()
        result = await retrieve(
            query,
            deadline_monotonic=budget.deadline_monotonic,
            deadline_exhausted=lambda: budget.remaining_s() <= 0,
        )
        self.check_budget(budget)
        self.candidate_coverage = {
            "partial": bool(
                result.truncated
                or result.deadline_exhausted
                or any(
                    report.health
                    not in {"success_with_hits", "success_zero_hits", "disabled"}
                    for report in result.source_reports
                )
            ),
            "omitted": None if result.truncated else 0,
            "source_outcomes": [
                outcome.to_record() for outcome in result.source_reports
            ],
        }
        candidates = tuple(
            candidate
            for candidate in result.candidates
            if self.candidate_eligible(candidate, budget=budget)
        )
        # Existing retrieval performed source admission; memory only reorders
        # that already eligible pool and retains an exploration position.
        from .experience import ExperienceIndex

        index = ExperienceIndex(self.catalog)
        ranked = index.rank(
            candidates,
            policy=self.policy,
            pinned_generation=pinned_generation,
            deadline_monotonic=budget.deadline_monotonic,
        )
        return tuple(ranked)

    async def activate_candidate(self, candidate: Any, budget: MemoryBudget) -> bool:
        from ensemble_prover.lean_runner import lean_resource_scope

        with lean_resource_scope(
            memory_mb=budget.memory_mb,
            concurrency=budget.concurrency,
            max_heartbeats=budget.max_heartbeats,
            deadline_monotonic=budget.deadline_monotonic,
        ):
            return await self._activate_candidate(candidate, budget)

    async def _activate_candidate(self, candidate: Any, budget: MemoryBudget) -> bool:
        """Prepare through existing library/helper/import admission boundaries."""
        session = self.session()
        self.check_budget(budget)
        if not self.candidate_eligible(candidate, budget=budget):
            return False
        retired_imports = session.mathematical_memory_state.get(
            "retired_import_owners", ()
        )
        readmit_import = (
            isinstance(retired_imports, (list, tuple))
            and candidate.candidate_id in retired_imports
            and candidate.candidate_id not in self._memory_import_owners
        )
        if candidate.availability == "already_imported" and not readmit_import:
            return True
        for origin in candidate.origins:
            self.check_budget(budget)
            if origin.required_bundle_ids:
                if self.config.theory_mode == "off" or session.theory_library is None:
                    continue
                from ensemble_prover.mathematical_retrieval.async_runtime import (
                    run_sync_abandonment_safe,
                )

                prepared = await run_sync_abandonment_safe(
                    lambda: session.prepare_theory_bundles(origin.required_bundle_ids),
                    timeout_s=budget.remaining_s(),
                    deadline_exhausted=lambda: budget.remaining_s() <= 0,
                )
                self.check_budget(budget)
                if prepared is not None and session.apply_prepared_theory_bundles(
                    prepared
                ):
                    return self.candidate_eligible(candidate, budget=budget)
            elif (
                origin.helper_source
                and origin.availability == "requires_helper_recheck"
            ):
                from ensemble_prover.proof_state_executor import (
                    _accept_proof_state_helper,
                )

                status: dict[str, Any] = {}
                accepted = await _accept_proof_state_helper(
                    lean=session.lean,
                    conv=session.conv,
                    dossier=session.dossier,
                    helper_block=origin.helper_source,
                    phase="mathematical_memory_recheck",
                    turn_index=session.iteration,
                    timeout_s=budget.remaining_s(),
                    proof_cache=None,
                    proof_state=session.proof_state,
                    target_statement=self.context()[0],
                    require_relevance_gate=True,
                    verified_helper_accept_callback=getattr(
                        session, "theory_verified_helper_accept_callback", None
                    ),
                    deadline_monotonic=budget.deadline_monotonic,
                    deadline_exhausted=lambda: budget.remaining_s() <= 0,
                    status_out=status,
                )
                if accepted:
                    registry = self.provenance_registry
                    name = status.get(
                        "accepted_helper_name", candidate.declaration_name
                    )
                    helper = session.dossier.verified_helpers.get(name)
                    from .profiles import digest

                    if helper is None or not self.bind_context_source_owner(
                        helper,
                        candidate.candidate_id,
                        source_digest=digest(helper.source),
                    ):
                        return False
                    self.check_budget(budget)
                    if (
                        registry is not None
                        and helper is not None
                        and registry.source_matches(
                            candidate.candidate_id, digest(origin.helper_source)
                        )
                    ):
                        registry.bind_context_source(
                            self.run_id, helper, candidate.candidate_id
                        )
                    session.searcher.mark_verified_helper_rechecked(
                        origin.source_hash,
                        helper_name=status.get(
                            "accepted_helper_name", candidate.declaration_name
                        ),
                    )
                    session.searcher.set_verified_helper_context(
                        session.dossier, session.dossier.verified_helper_blocks()
                    )
                    return self.candidate_eligible(candidate, budget=budget)
                self.check_budget(budget)
            elif origin.module_name and (
                origin.availability == "importable"
                or readmit_import and origin.availability == "already_imported"
            ):
                from ensemble_prover.proof_dossier import text_hash
                from ensemble_prover.proof_state_executor import (
                    _await_serialized_lean_operation,
                )
                from ensemble_prover.mini_session.source_imports import (
                    apply_source_import, prepare_source_import,
                )

                pair = prepare_source_import(session, origin.module_name)
                preamble = pair.lean.render()
                result = await _await_serialized_lean_operation(
                    session.lean,
                    lambda: session.lean.check(
                        candidate.type_text,
                        f"by exact @{candidate.declaration_name}",
                        [],
                        preamble_override=preamble,
                        timeout_s=budget.remaining_s(),
                        check_kind="precheck",
                        max_heartbeats=budget.max_heartbeats,
                    ),
                    timeout_s=budget.remaining_s() * 0.95,
                    deadline_monotonic=budget.deadline_monotonic,
                )
                self.check_budget(budget)
                if result.ok and result.axiom_audit_ok is True:
                    if not self.candidate_eligible(candidate, budget=budget):
                        return False
                    previous = session.dossier.current_lean_environment_hash
                    apply_source_import(
                        session, pair, module=origin.module_name,
                        declaration=candidate.declaration_name,
                        statement=candidate.type_text,
                    )
                    # Import admission itself creates the source obligation;
                    # a later profile timeout cannot erase it. Commit only
                    # after confirming the checked context is still current.
                    self._memory_support_names[candidate.declaration_name] = (
                        candidate.candidate_id
                    )
                    # Imports expose siblings and transitive modules too.
                    self._memory_import_owners.add(candidate.candidate_id)
                    session.dossier.record_lean_environment(
                        text_hash(preamble),
                        extends_environment_hash=previous,
                        environment_source_text=preamble,
                    )
                    if origin.source_kind == "project":
                        session.searcher.mark_source_declaration_imported(
                            origin.source_id,
                            origin.module_name,
                            candidate.declaration_name,
                            candidate.type_text,
                        )
                        record = {
                            "source_id": origin.source_id,
                            "module_name": origin.module_name,
                            "declaration_name": candidate.declaration_name,
                            "declaration_type": candidate.type_text,
                        }
                        if record not in session.retrieval_imported_declarations:
                            session.retrieval_imported_declarations.append(record)
                    else:
                        session.searcher.mark_source_module_imported(
                            origin.source_id, origin.module_name
                        )
                        modules = session.retrieval_imported_source_modules.setdefault(
                            origin.source_id, []
                        )
                        if origin.module_name not in modules:
                            modules.append(origin.module_name)
                    return self.candidate_eligible(candidate, budget=budget)
        return False

    async def prepare_and_probe(
        self,
        goal: Any,
        candidate: Any,
        budget: MemoryBudget,
        recipe: Any = None,
        operation_id: str = "",
        attempt_id: str = "",
    ) -> Any:
        from .applications import OperationRecipe, prepare_and_probe
        from .profiles import profile_declaration

        session = self.session()
        if not self.candidate_eligible(candidate, budget=budget):
            raise ValueError("candidate source is no longer eligible")
        _, preamble, lemmas = self.context()
        origins = tuple(candidate.origins)
        source = next(
            (origin.helper_source for origin in origins if origin.helper_source), ""
        )
        if not source:
            for origin in origins:
                self.check_budget(budget)
                paths = []
                if origin.required_bundle_ids and session.theory_library is not None:
                    for bundle in session.theory_library.store.iter_bundles():
                        if bundle.bundle_id in origin.required_bundle_ids:
                            paths.append(
                                session.theory_library.store.source_path(bundle)
                            )
                elif origin.source_path and "#" not in origin.source_path:
                    path = Path(origin.source_path)
                    paths.append(path)
                    project = Path(session.lean.cfg.project_dir)
                    if not path.is_absolute():
                        paths.extend(
                            (project / path, project / ".lake/packages/mathlib" / path)
                        )
                for path in paths:
                    try:
                        import os
                        import stat

                        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
                        with os.fdopen(fd, "rb") as handle:
                            if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
                                continue
                            chunks, size = [], 0
                            while size <= self.config.artifact_byte_cap:
                                self.check_budget(budget)
                                chunk = handle.read(
                                    min(65536, self.config.artifact_byte_cap + 1 - size)
                                )
                                if not chunk:
                                    break
                                chunks.append(chunk)
                                size += len(chunk)
                            raw = b"".join(chunks)
                        if len(raw) <= self.config.artifact_byte_cap:
                            source = raw.decode("utf-8")
                            break
                    except (OSError, UnicodeError):
                        continue
                if source:
                    break
        from .profiles import digest

        if not self.candidate_eligible(
            candidate, source_digest=digest(source), budget=budget
        ):
            raise ValueError("candidate source version is no longer eligible")
        source_attested = source in lemmas
        attested_bundle_ids: list[str] = []
        library = session.theory_library
        if not source_attested and library is not None:
            # Store iteration admits only manifests whose exact source and
            # compiled artifact hashes currently match. The active context
            # must name that precise bundle and its declaration inventory.
            active = set(session.theory_imported_bundle_ids)
            for bundle in library.store.iter_bundles():
                self.check_budget(budget)
                if (
                    bundle.bundle_id in active
                    and bundle.source_hash == digest(source.strip())
                    and any(
                        declaration.fq_name == candidate.declaration_name
                        for declaration in bundle.declarations
                    )
                ):
                    source_attested = True
                    attested_bundle_ids.append(bundle.bundle_id)
                    break
        profile = await profile_declaration(
            session.lean,
            declaration_name=candidate.declaration_name,
            statement=candidate.type_text,
            source=source,
            environment_id=self.context_id(),
            source_store_id=origins[0].source_id if origins else "",
            preamble=preamble + "\n" + "\n".join(lemmas),
            source_available=True,
            source_binding_attested=source_attested,
            budget=budget,
        )
        if not self.candidate_eligible(
            candidate, source_digest=profile.source_digest, budget=budget
        ):
            raise ValueError("candidate source authority changed during profiling")
        if profile.complete:
            self.known_declarations[candidate.declaration_name] = profile
            self.known_candidate_ids[candidate.declaration_name] = (
                candidate.candidate_id
            )
            self.profile_bundle_bindings[candidate.declaration_name] = tuple(
                attested_bundle_ids
            )
            try:
                source_ref = self.catalog.put_artifact(
                    profile.source.encode(),
                    kind="declaration_source",
                    deadline_monotonic=budget.deadline_monotonic,
                )
                self.record(
                    "profile",
                    {**profile.to_record(), "candidate_id": candidate.candidate_id},
                    provenance=self.candidate_provenance(candidate.candidate_id),
                    budget=budget,
                    additional_evidence=(source_ref,),
                )
            except (OSError, ValueError, RuntimeError, TimeoutError):
                self.health = "unavailable"
        # This binding follows an explicit retrieved helper origin and its
        # exact admitted declaration record, never a search by shared digest.
        if profile.complete and profile.certified_source_binding:
            helper = session.dossier.verified_helpers.get(candidate.declaration_name)
            if (
                helper is not None
                and helper.source == source
                and any(
                    origin.source_kind == "verified_helper"
                    and origin.helper_source == helper.source
                    for origin in origins
                )
            ):
                if not self.bind_context_source_owner(
                    helper, candidate.candidate_id, source_digest=profile.source_digest
                ):
                    raise ValueError(
                        "admitted helper source binding is no longer eligible"
                    )
        registry = self.provenance_registry
        registered = registry is not None and registry.has_source(
            candidate.candidate_id
        )
        if (
            not profile.complete
            or (registered and not profile.certified_source_binding)
            or not self.application_eligible(candidate.candidate_id, budget=budget)
        ):
            raise ValueError(
                "application source/context attestation is incomplete or no longer eligible"
            )
        selected_recipe = recipe or OperationRecipe(
            kind="apply", declaration_name=candidate.declaration_name
        )
        from .experience import ExperienceIndex
        from .applications import ApplicationObservation

        key, _limits = self._attempt_identity(
            goal.goal_id,
            goal.environment_id,
            profile.declaration_id,
            selected_recipe,
            budget,
        )
        if ExperienceIndex(self.catalog).retry_suppressed(
            key,
            policy=self.policy,
            now_epoch=time.time(),
            deadline_monotonic=budget.deadline_monotonic,
        ):
            return ApplicationObservation(
                operation_id or uuid.uuid4().hex,
                attempt_id or uuid.uuid4().hex,
                goal.goal_id,
                profile.declaration_id,
                selected_recipe,
                goal.environment_id,
                "probe_inconclusive",
                reason="exact_retry_cooldown",
            )
        return await prepare_and_probe(
            session.lean,
            goal,
            profile,
            selected_recipe,
            preamble=preamble,
            lemmas=lemmas,
            budget=budget,
            operation_id=operation_id,
            attempt_id=attempt_id,
        )

    def _attempt_identity(
        self,
        goal_id: str,
        environment_id: str,
        declaration_id: str,
        recipe: Any,
        budget: MemoryBudget,
    ) -> tuple[str, dict[str, Any]]:
        from .experience import exact_attempt_key

        limits = {
            "heartbeats": budget.max_heartbeats,
            "memory_mb": budget.memory_mb,
            "probe_cap": budget.max_probes,
            "tokens": budget.remaining_tokens,
            "cost": budget.remaining_cost,
            "concurrency": budget.concurrency,
        }
        return (
            exact_attempt_key(
                goal_id=goal_id,
                environment_id=environment_id,
                context_id=self.context_id(),
                declaration_id=declaration_id,
                operation=recipe.kind,
                direction=recipe.direction,
                method_version="single_recipe_v1",
                limits=limits,
                instantiation=recipe.to_record(),
            ),
            limits,
        )

    def record_attempt_context(
        self,
        observation: Any,
        candidate_id: str,
        budget: MemoryBudget,
        *,
        retry_of: str = "",
    ) -> None:
        """Persist scoped failure and unresolved-obligation research proposals."""
        self.check_budget(budget)
        if observation.reason == "exact_retry_cooldown":
            return
        recipe = observation.recipe
        key, limits = self._attempt_identity(
            observation.goal_id,
            observation.environment_id,
            observation.declaration_id,
            recipe,
            budget,
        )
        provenance = self.application_provenance(candidate_id)
        if observation.outcome in {
            "probe_rejected",
            "probe_inconclusive",
            "unavailable",
        }:
            self.record(
                "route_failure",
                {
                    "attempt_key": key,
                    "goal_id": observation.goal_id,
                    "environment_id": observation.environment_id,
                    "candidate_id": candidate_id,
                    "recipe": recipe.to_record(),
                    "limits": limits,
                    "outcome": observation.outcome,
                    "reason": observation.reason,
                    "retry_after_epoch": time.time()
                    + (5 if observation.outcome == "probe_inconclusive" else 30),
                    "retry_conditions": "Fresh execution under changed support, context, method or remaining allocation; this report does not refute the goal",
                },
                operation_id=observation.operation_id,
                attempt_id=observation.attempt_id,
                provenance=provenance,
                budget=budget,
                retry_of=retry_of,
            )
        certificate = observation.reduction
        statements = (
            tuple(certificate.residual_statements)
            if certificate is not None
            else tuple(observation.remaining_goals)
        )
        session = self.session()
        obstruction_rows = []
        for index, statement in enumerate(
            statements[: self.config.prepared_candidate_cap]
        ):
            self.check_budget(budget)
            identity = content_digest(
                {
                    "goal": observation.goal_id,
                    "recipe": recipe.recipe_id,
                    "slot": index,
                    "statement": statement,
                }
            )
            payload = {
                "obstruction_id": identity,
                "goal_id": observation.goal_id,
                "candidate_id": candidate_id,
                "statement": statement,
                "environment_id": observation.environment_id,
                "outcome": observation.outcome,
                "recipe": recipe.to_record(),
                "formal": certificate is not None,
                "conditions": (
                    "Typed independent obligation"
                    if certificate is not None
                    else "Diagnostic residual; formalization is required before proof work"
                ),
                "retry_conditions": "New eligible support proposes a fresh application check; no work is granted by notification",
            }
            event = self.record(
                "obstruction",
                payload,
                operation_id=observation.operation_id,
                attempt_id=observation.attempt_id,
                provenance=provenance,
                budget=budget,
            )
            if event is not None:
                obstruction_rows.append({**payload, "event_id": event.event_id})
                self.record(
                    "subscription",
                    {
                        "obstruction_id": identity,
                        "route_id": "memory_goal:" + observation.goal_id,
                        "goal_id": observation.goal_id,
                        "environment_id": observation.environment_id,
                    },
                    event_id=content_digest(
                        {"subscription": identity, "scope": self.scope_id}
                    ),
                    provenance=provenance,
                    budget=budget,
                )
        if obstruction_rows:
            session.mathematical_memory_state["obstruction_rows"] = obstruction_rows
        # Wakeups are proposed investigations only, retained for the current
        # ordinary scheduler to check under its own remaining allocation.
        if self.known_declarations:
            profile = next(
                (
                    self.known_declarations[name]
                    for name, identity in self.known_candidate_ids.items()
                    if identity == candidate_id
                ),
                None,
            )
            if profile is not None:
                view = self.catalog.query(
                    self.policy,
                    kind="obstruction",
                    limit=32,
                    deadline_monotonic=budget.deadline_monotonic,
                )
                wanted = [
                    str(event.payload.get("obstruction_id", ""))
                    for event in view.events
                    if event.payload.get("candidate_id") != candidate_id
                    and set(profile.features).intersection(
                        str(event.payload.get("statement", "")).split()
                    )
                ]
                if wanted:
                    from .experience import ExperienceIndex

                    routes = ExperienceIndex(self.catalog).wake_routes(
                        wanted,
                        policy=self.policy,
                        limit=8,
                        deadline_monotonic=budget.deadline_monotonic,
                    )
                    for route in routes:
                        wake_id = content_digest(
                            {
                                "route": route,
                                "declaration": profile.declaration_id,
                                "environment": self.context_id(),
                            }
                        )
                        seen = session.mathematical_memory_state.setdefault(
                            "wake_proposal_ids", []
                        )
                        if wake_id in seen:
                            continue
                        event = self.record(
                            "retry_proposal",
                            {
                                "route_id": route,
                                "candidate_id": candidate_id,
                                "outcome": "proposed",
                                "goal_id": observation.goal_id,
                                "environment_id": self.context_id(),
                                "reason": "New eligible declaration shares structural features with an unresolved obligation",
                            },
                            event_id=wake_id,
                            provenance=provenance,
                            budget=budget,
                        )
                        if event is not None:
                            seen.append(wake_id)
                            del seen[:-1024]
                            if route == "memory_goal:" + observation.goal_id:
                                queue = session.mathematical_memory_state.setdefault(
                                    "wake_proposals", []
                                )
                                queue.append(
                                    {
                                        "event_id": event.event_id,
                                        "candidate_id": candidate_id,
                                        "environment_id": self.context_id(),
                                    }
                                )
                                del queue[: -self.config.prepared_candidate_cap]

    def finalization_eligible(self, candidate: Any) -> bool:
        """Recheck the live policy at the ordinary root acceptance seam."""
        from ensemble_prover.root_finalization import sanitize_lean_artifact_text

        session = self.session()
        pending = self._pending_solution
        try:
            if session is None:
                return False
            # Persisted graph origins carry dependency obligations, not live
            # admission. Restored reductions require a new current check.
            statement, preamble, lemmas = self.context()
            usage_getter = getattr(session.lean, "helper_usage_observation", None)
            usage = (
                usage_getter(
                    statement=candidate.target_statement or statement,
                    proof=candidate.proof,
                    preamble=preamble,
                    lemmas=candidate.replay_helpers,
                )
                if callable(usage_getter)
                else None
            )
            from ensemble_prover.proof_dossier import canonical_lean_identifier

            reachable = (
                {canonical_lean_identifier(name) for name in usage.reachable_constants}
                if usage is not None and usage.observed and usage.complete
                else None
            )
            support = {**self.known_candidate_ids, **self._memory_support_names}
            state = session.mathematical_memory_state
            retired = state.get("retired_support_names", ())
            retired_bundles = state.get("retired_bundle_obligations", ())
            retired_imports = state.get("retired_import_owners", ())
            if state.get("retired_support_incomplete") is True or any(
                not isinstance(items, (list, tuple))
                or len(items) > 4096
                or any(not isinstance(item, str) for item in items)
                for items in (retired, retired_bundles, retired_imports)
            ):
                return False
            # A theorem's name does not identify its defining module or all
            # imports that exposed it. Complete proof-use inventories therefore
            # cannot discharge these whole-environment source obligations.
            # Replayed identities retain obligations, never live admission.
            if not set(retired_imports).issubset(self._memory_import_owners) or any(
                not self.application_eligible(identity)
                for identity in self._memory_import_owners
            ):
                return False
            live_names = {canonical_lean_identifier(name) for name in support}
            for helper in session.dossier.verified_helpers.values():
                name = canonical_lean_identifier(helper.name)
                if reachable is not None and name not in reachable:
                    continue
                local_owner = self._local_context_source_id(helper)
                registry = self.provenance_registry
                controller_owner = (
                    registry.context_source_id(self.run_id, helper)
                    if registry is not None
                    else None
                )
                if local_owner and controller_owner and local_owner != controller_owner:
                    return False
                owner = controller_owner or local_owner
                memory_owned = (
                    helper.phase.startswith("mathematical_memory")
                    or "mathematical_memory_owned_context" in helper.provenance_tags
                )
                if memory_owned and not owner:
                    return False
                if owner:
                    if not self.application_eligible(owner):
                        return False
                    live_names.add(name)
            for name, identity in support.items():
                if (
                    reachable is not None
                    and canonical_lean_identifier(name) not in reachable
                ):
                    continue
                if not self.application_eligible(identity):
                    return False
            # Replayed theory imports retain source obligations even when the
            # old service's in-process activation map is gone. Module/constant
            # names select obligations only; they grant no source permission.
            bundle_ids = set(getattr(session, "theory_imported_bundle_ids", ())) | set(
                retired_bundles
            )
            for line in preamble.splitlines():
                tokens = line.strip().split()
                if not tokens or tokens[0] != "import":
                    continue
                for module in tokens[1:]:
                    match = re.fullmatch(
                        r"MiniTheory\.Domains\.[A-Za-z0-9_]+\.Bundles\.B_([A-Za-z0-9_]+)\.Theory",
                        module,
                    )
                    if match:
                        bundle_ids.add(match.group(1))
            for identity in bundle_ids:
                if reachable is not None and not any(
                    "B_" + identity in constant.split(".") for constant in reachable
                ):
                    continue
                if not self._sources_admitted((identity,)):
                    return False
            for raw_name in retired:
                name = canonical_lean_identifier(raw_name)
                if reachable is not None and name not in reachable:
                    continue
                if name not in live_names:
                    return False
            for node in getattr(
                getattr(session, "proof_state", None), "nodes", {}
            ).values():
                for group in getattr(node, "assembly_attempt_groups", ()):
                    prefix = "decl_application:mathematical_memory:"
                    if (
                        not str(group.source).startswith(prefix)
                        or group.status == "obsolete"
                    ):
                        continue
                    operation, declaration = str(group.source)[len(prefix) :].split(
                        ":", 1
                    )
                    if (
                        reachable is not None
                        and canonical_lean_identifier(declaration) not in reachable
                    ):
                        continue
                    binding = self._reduction_bindings.get(operation)
                    if (
                        binding is None
                        or binding[0] is not session.proof_state
                        or binding[2] != self.policy_id
                        or not self.application_eligible(binding[1])
                    ):
                        return False
            if candidate.source_action_id != "mathematical_memory":
                return True
            return bool(
                pending
                and pending.get("proof_hash")
                == content_digest(sanitize_lean_artifact_text(candidate.proof))
                and pending.get("environment_id") == self.context_id()
                and pending.get("policy_id") == self.policy_id
                and tuple(candidate.replay_helpers) == lemmas
                and self.application_eligible(str(pending.get("candidate_id", "")))
            )
        except (OSError, ValueError, RuntimeError, sqlite3.Error):
            return False

    def remember_solution(self, pending: Mapping[str, Any]) -> None:
        self._pending_solution = dict(pending)
        session = self.session()
        if session is not None:
            session.mathematical_memory_state["pending_solution"] = dict(pending)

    def remember_reduction(self, observation: Any, candidate_id: str) -> None:
        session = self.session()
        if session is not None:
            self._reduction_bindings[observation.operation_id] = (
                session.proof_state,
                candidate_id,
                self.policy_id,
            )

    def current_view(self) -> dict[str, Any]:
        """Use restored display state only while its actual context stays current."""
        session = self.session()
        view = self.last_view or (
            session.mathematical_memory_state.get("last_view", {}) if session else {}
        )
        if (
            not isinstance(view, dict)
            or view.get("environment_id") != self.context_id()
            or view.get("policy_id") != self.policy_id
        ):
            return {}
        return view

    def annotation_provenance(
        self, request: Mapping[str, Any], budget: MemoryBudget
    ) -> MemoryProvenance:
        """Bind candidate annotations to eligible retained evidence at dispatch."""
        candidate_id = str(request.get("candidate_id", ""))
        if not candidate_id:
            if request.get("kind") == "pin":
                raise ValueError("a pin requires a current candidate")
            return self.provenance()
        self.check_budget(budget)
        view = self.current_view()
        rows = list(view.get("candidates", ())) + list(view.get("applications", ()))
        for row in rows[: self.config.prepared_candidate_cap + self.config.probe_cap]:
            if not isinstance(row, dict) or row.get("candidate_id") != candidate_id:
                continue
            event = self.catalog.get_event(
                str(row.get("event_id", "")),
                self.policy,
                deadline_monotonic=budget.deadline_monotonic,
            )
            if (
                event is None
                or event.kind not in {"candidate", "application"}
                or any(
                    event.payload.get(key) != request.get(key)
                    for key in ("candidate_id", "goal_id", "environment_id")
                )
            ):
                continue
            if not self.candidate_eligible(candidate_id, budget=budget):
                break
            provenance = self.candidate_provenance(candidate_id)
            return replace(
                provenance,
                source_record_ids=tuple(
                    dict.fromkeys(
                        (
                            *provenance.source_record_ids,
                            *event.provenance.source_record_ids,
                            candidate_id,
                        )
                    )
                ),
            )
        raise ValueError(
            "annotation candidate evidence is no longer current or eligible"
        )

    async def _link_motivating_instance(
        self, request: Mapping[str, Any], result: Any, budget: MemoryBudget
    ) -> tuple[list[dict[str, Any]], tuple[Any, ...]]:
        """Check a direct motivating instance under the job's remaining budget."""
        from .applications import OperationRecipe
        from .generalization import (
            SpecializationLink,
            _bounded_worker,
            check_specialization,
        )
        from .profiles import DeclarationProfile, digest
        from ensemble_prover.mini_theory import TheoryContextPair

        session = self.session()
        candidate_id = str(request.get("candidate_id", ""))
        profile = next(
            (
                self.known_declarations[name]
                for name, identity in self.known_candidate_ids.items()
                if identity == candidate_id
            ),
            None,
        )
        candidate = result.candidate
        if (
            session is None
            or not isinstance(profile, DeclarationProfile)
            or not profile.complete
            or not profile.certified_source_binding
            or profile.environment_id != self.context_id()
            or candidate is None
            or result.status != "checked_theorem"
            or not getattr(result.publication, "published", False)
        ):
            return [], ()
        name = candidate.namespace + "." + result.proposal.theorem_name
        base = dict(
            generalized_name=name,
            instance_statement=profile.statement,
            instantiation="@" + name,
            kind="direct",
            checked=False,
            environment_id=self.context_id(),
        )
        evidence = ()
        try:
            self.check_budget(budget)
            if not self.candidate_eligible(
                candidate_id, source_digest=profile.source_digest, budget=budget
            ):
                return [
                    SpecializationLink(
                        **base, reason="motivating_source_ineligible"
                    ).to_record()
                ], ()
            _, preamble, lemmas = self.context()
            pair = TheoryContextPair.from_preambles(
                llm_preamble=preamble, lean_preamble=preamble
            )
            ids = tuple(
                dict.fromkeys(
                    (*session.theory_imported_bundle_ids, candidate.bundle_id)
                )
            )

            def prepare(*, cancellation_event: Any) -> Any:
                if cancellation_event.is_set():
                    raise TimeoutError("specialization context cancelled")
                selected, snapshot = session.theory_library.prepare_context(
                    pair, bundle_ids=ids
                )
                if cancellation_event.is_set():
                    raise TimeoutError("specialization context cancelled")
                return selected, snapshot

            selected, snapshot = await _bounded_worker(prepare, budget=budget)
            if not any(
                row.get("bundle_id") == candidate.bundle_id
                and row.get("source_hash") == candidate.source_hash
                for row in snapshot
            ):
                return [
                    SpecializationLink(
                        **base, reason="published_source_not_current"
                    ).to_record()
                ], ()
            arguments: tuple[str, ...] = ()
            view = self.current_view()
            for row in view.get("applications", ())[: self.config.probe_cap]:
                if not isinstance(row, dict) or row.get("candidate_id") != candidate_id:
                    continue
                event = self.catalog.get_event(
                    str(row.get("event_id", "")),
                    self.policy,
                    deadline_monotonic=budget.deadline_monotonic,
                )
                if (
                    event is None
                    or event.kind != "application"
                    or event.payload.get("declaration_id") != profile.declaration_id
                    or event.payload.get("environment_id") != self.context_id()
                    or event.payload.get("goal_id") != request.get("goal_id")
                ):
                    continue
                recipe = OperationRecipe.from_record(
                    dict(event.payload.get("recipe", {}))
                )
                if (
                    recipe.declaration_name == profile.declaration_name
                    and recipe.kind == "apply"
                ):
                    if len(recipe.arguments) > 64 or any(
                        not isinstance(arg, str) or len(arg) > 8192
                        for arg in recipe.arguments
                    ):
                        raise ValueError(
                            "specialization arguments exceed bounded explicit recipe"
                        )
                    arguments = recipe.arguments
                    break
            self.check_budget(budget)
            if not self.candidate_eligible(
                candidate_id, source_digest=profile.source_digest, budget=budget
            ):
                return [
                    SpecializationLink(
                        **base, reason="motivating_source_ineligible"
                    ).to_record()
                ], ()
            provenance = self.provenance((candidate.bundle_id,))
            budget.claim_probe()
            link = await check_specialization(
                session.lean,
                name,
                profile.statement,
                arguments,
                budget=budget,
                preamble=selected.lean.render(),
                lemmas=lemmas,
                environment_id=self.context_id(),
                provenance=provenance,
                policy=self.policy,
                forbidden_support_ids=(candidate_id,),
                ancestry_validator=lambda _checked, _term, ancestry: self._sources_admitted(
                    tuple(
                        dict.fromkeys(
                            ancestry.source_record_ids + ancestry.ancestry_source_ids
                        )
                    ),
                    budget=budget,
                ),
            )
            self.check_budget(budget)
            if not self.candidate_eligible(
                candidate_id, source_digest=profile.source_digest, budget=budget
            ):
                link = SpecializationLink(
                    **base, reason="motivating_source_permission_changed"
                )
            source_ref = self.catalog.put_artifact(
                profile.source.encode(),
                kind="specialization_instance_source",
                deadline_monotonic=budget.deadline_monotonic,
            )
            generalized_ref = self.catalog.put_artifact(
                candidate.source.encode(),
                kind="generalization_source",
                deadline_monotonic=budget.deadline_monotonic,
            )
            evidence = (source_ref, generalized_ref)
            payload = {
                **link.to_record(),
                "candidate_id": candidate_id,
                "instance_source_digest": digest(profile.source),
                "generalized_source_digest": candidate.source_hash,
                "instance_source_evidence": source_ref.to_record(),
                "generalized_source_evidence": generalized_ref.to_record(),
            }
            return [payload], evidence
        except (OSError, ValueError, RuntimeError, TimeoutError) as exc:
            return [
                SpecializationLink(**base, reason=type(exc).__name__).to_record()
            ], evidence

    async def _activate_generalization(
        self,
        result: Any,
        provenance: MemoryProvenance,
        budget: MemoryBudget,
        validator: Any,
    ) -> dict[str, Any]:
        """Install the explicit job's checked support through the theory seam."""
        from .generalization import _bounded_worker

        session = self.session()
        candidate = result.candidate
        base = {"context_installed": False, "activation_status": "not_published"}
        if (
            session is None
            or candidate is None
            or result.status != "checked_theorem"
            or not getattr(result.publication, "published", False)
        ):
            return base
        try:
            self.check_budget(budget)
            registry = self.provenance_registry
            source_ids = tuple(
                dict.fromkeys((*provenance.source_record_ids, candidate.bundle_id))
            )
            current = (
                registry.issue_provenance(source_ids, run_id=self.run_id)
                if registry is not None
                else None
            )
            registered = registry is not None and registry.has_source(
                candidate.bundle_id
            )
            if registered and (
                current is None
                or not registry.source_matches(
                    candidate.bundle_id, candidate.source_hash
                )
            ):
                return {**base, "activation_status": "source_permission_changed"}
            if current is None:
                current = replace(
                    provenance,
                    source_record_ids=source_ids,
                    complete=False,
                    scope="session",
                    scope_id=self.scope_id,
                )
            if not self._sources_admitted(source_ids, budget=budget) or not validator():
                return {**base, "activation_status": "source_ancestry_ineligible"}
            if not self.catalog.source_eligible(
                candidate.bundle_id,
                self.policy,
                deadline_monotonic=budget.deadline_monotonic,
            ):
                return {**base, "activation_status": "published_source_revoked"}

            def prepare(*, cancellation_event: Any) -> Any:
                if cancellation_event.is_set():
                    raise TimeoutError("theory context cancelled")
                prepared = session.prepare_theory_bundles((candidate.bundle_id,))
                if cancellation_event.is_set():
                    raise TimeoutError("theory context cancelled")
                return prepared

            prepared = await _bounded_worker(prepare, budget=budget)
            self.check_budget(budget)
            if prepared is None or not any(
                row.get("bundle_id") == candidate.bundle_id
                and row.get("source_hash") == candidate.source_hash
                for row in prepared[3]
            ):
                return {**base, "activation_status": "published_source_not_current"}
            if (
                not validator()
                or not self._sources_admitted(source_ids, budget=budget)
                or not self.catalog.source_eligible(
                    candidate.bundle_id,
                    self.policy,
                    deadline_monotonic=budget.deadline_monotonic,
                )
            ):
                return {**base, "activation_status": "source_permission_changed"}
            if current.complete:
                if (
                    registry is None
                    or registry.current_authority(current, candidate.bundle_id)
                    is not True
                    or not registry.source_matches(
                        candidate.bundle_id, candidate.source_hash
                    )
                ):
                    return {**base, "activation_status": "source_permission_changed"}
            installed = session.apply_prepared_theory_bundles(prepared)
            if installed:
                self._memory_support_names[
                    candidate.namespace + "." + result.proposal.theorem_name
                ] = candidate.bundle_id
            return {
                "context_installed": bool(installed),
                "activation_status": "installed" if installed else "unchanged",
                "activated_bundle_ids": list(session.theory_imported_bundle_ids),
                "activation_environment_id": self.context_id(),
            }
        except (OSError, ValueError, RuntimeError, TimeoutError) as exc:
            return {**base, "activation_status": type(exc).__name__}

    async def _checked_publication_current(
        self, result: Any, budget: MemoryBudget
    ) -> bool:
        """Bind a reported theorem to this library's current verified publication."""
        from .generalization import _bounded_worker

        session = self.session()
        library = getattr(session, "theory_library", None)
        candidate = getattr(result, "candidate", None)
        verification = getattr(result, "verification", None)
        publication = getattr(result, "publication", None)
        if (
            result.status != "checked_theorem"
            or candidate is None
            or verification is None
            or getattr(verification, "accepted", False) is not True
            or not getattr(publication, "published", False)
            or getattr(publication, "verification", None) is not verification
            or not callable(getattr(library, "reuse_published_candidate", None))
        ):
            return False

        def current(*, cancellation_event: Any) -> bool:
            published = library.reuse_published_candidate(
                candidate,
                helper_name=result.proposal.theorem_name,
                cancellation_event=cancellation_event,
            )
            return bool(
                published is not None
                and published.published
                and published.verification.accepted
                and published.verification.receipt.source_hash == candidate.source_hash
                and published.verification.receipt.compiled_artifact_hash
                == verification.receipt.compiled_artifact_hash
                and published.verification.receipt.verification_output_hash
                == verification.receipt.verification_output_hash
            )

        self.check_budget(budget)
        return await _bounded_worker(current, budget=budget)

    async def prove_requested_generalization(
        self,
        request: Mapping[str, Any],
        budget: MemoryBudget,
        *,
        source_provenance: MemoryProvenance | None = None,
    ) -> Any:
        """Execute a durably admitted formal proposal inside its research subset."""
        from .generalization import GeneralizationProposal, build_generalization

        session = self.session()
        if session is None or not self.config.generalization_enabled:
            raise ValueError("generalization requires develop mode")
        library = session.theory_library
        if library is None or library.mode != "build":
            raise ValueError("generalization requires actual theory build permission")
        if request.get("allocation_id") != self.config.research_allocation_id:
            raise ValueError(
                "generalization request names a different research allocation"
            )
        if (
            request.get("policy_id") != self.policy_id
            or request.get("environment_id") != self.context_id()
        ):
            raise ValueError("generalization request environment or policy changed")
        if request.get("goal_id") != self.current_view().get("goal_id"):
            raise ValueError("generalization request is bound to another obligation")
        if self.request_store is None:
            raise ValueError("generalization requires a durable run request ledger")
        records = self.request_store.list(limit=1024)
        dispatch = next(
            (
                record
                for record in records
                if record["payload"]["request_id"] == request.get("request_id")
            ),
            None,
        )
        if dispatch is None or dispatch["status"] not in {"admitted", "running"}:
            raise ValueError("generalization has not been durably admitted")
        builder = session.theory_candidate_builder
        if builder is None:
            raise ValueError("generalization candidate builder is unavailable")
        if getattr(session, "cost_controller", None) is not None and hasattr(
            builder, "with_cost_controller"
        ):
            builder = builder.with_cost_controller(session.cost_controller)
        self.check_budget(budget)
        allowance = min(float(request.get("max_seconds", 0)), budget.remaining_s())
        reservation = self.request_store.reserve_research(
            self.config.research_allocation_id,
            self.config.research_seconds,
            str(request["request_id"]),
            allowance,
            deadline_monotonic=budget.deadline_monotonic,
        )
        reserved = float(reservation["reserved_seconds"])
        budget.deadline_monotonic = min(
            budget.deadline_monotonic, time.monotonic() + reserved
        )
        started = time.monotonic()
        statement = str(request["statement"])
        proposal = GeneralizationProposal(
            statement=statement,
            theorem_name="memory_generalization_" + content_digest(statement)[:16],
            instance_ids=(
                (str(request["candidate_id"]),) if request.get("candidate_id") else ()
            ),
            intended_consumers=(self.context()[0],),
            rationale=str(request.get("text", "")),
            domain=str(getattr(session, "theory_domain", "mathematical_memory")),
        )
        operation_id, attempt_id = dispatch["operation_id"], dispatch["attempt_id"]
        candidate_id = str(request.get("candidate_id", ""))
        provenance = source_provenance or (
            self.application_provenance(candidate_id)
            if candidate_id
            else self.provenance((proposal.proposal_id,))
        )

        def eligible_sources() -> bool:
            self.check_budget(budget)
            if not self._sources_admitted(
                tuple(
                    dict.fromkeys(
                        provenance.source_record_ids + provenance.ancestry_source_ids
                    )
                ),
                budget=budget,
            ):
                return False
            if candidate_id and not self.application_eligible(
                candidate_id, budget=budget
            ):
                return False
            for identity in tuple(
                dict.fromkeys(
                    provenance.source_record_ids + provenance.ancestry_source_ids
                )
            ):
                if not self.catalog.source_eligible(
                    identity, self.policy, deadline_monotonic=budget.deadline_monotonic
                ):
                    return False
            authority = (
                self.provenance_registry.current_authority
                if self.provenance_registry is not None
                else None
            )
            if provenance.complete and authority is None:
                return False
            try:
                eligible = (
                    authority is None
                    or authority(provenance, proposal.proposal_id) is True
                )
                self.check_budget(budget)
                return eligible
            except Exception:
                return False

        if not eligible_sources():
            raise ValueError("generalization motivating source is no longer eligible")

        def validate_ancestry(
            _candidate: Any, _verification: Any, _provenance: Any
        ) -> bool:
            return eligible_sources()

        proposal_payload = {
            **proposal.to_record(),
            "name": proposal.theorem_name,
            "outcome": "proposed",
            "environment_id": self.context_id(),
        }
        proposal_event = self.record(
            "proposal",
            proposal_payload,
            operation_id=operation_id,
            attempt_id=attempt_id,
            provenance=provenance,
            budget=budget,
        )
        if proposal_event is not None:
            self.emit(
                proposals=[
                    {
                        **proposal_payload,
                        "event_id": proposal_event.event_id,
                        "evidence_digest": (
                            proposal_event.evidence[0].digest
                            if proposal_event.evidence
                            else ""
                        ),
                    }
                ]
            )
        # Start with the permitted base library. Imported campaign dependencies
        # need complete source ancestry before they may enter a new proof job.
        root_statement = str(getattr(session.problem, "statement_type", ""))
        try:
            result = await build_generalization(
                proposal,
                builder,
                library,
                runner=session.lean,
                budget=budget,
                imports=("Mathlib",),
                originating_root=root_statement or self.scope_id,
                forbidden_target_statements=(root_statement,) if root_statement else (),
                provenance=provenance,
                policy=None,
                ancestry_validator=validate_ancestry,
            )
            if (
                result.status == "checked_theorem"
                and not await self._checked_publication_current(result, budget)
            ):
                result = replace(
                    result,
                    status="inconclusive",
                    reason="publication_not_currently_verified",
                )
            (
                specialization_links,
                specialization_evidence,
            ) = await self._link_motivating_instance(request, result, budget)
            activation = await self._activate_generalization(
                result, provenance, budget, eligible_sources
            )
            payload = result.to_record()
            payload.update(activation)
            payload.update(
                instance_ids=list(proposal.instance_ids),
                source_instances=list(proposal.instance_ids),
                intended_consumers=list(proposal.intended_consumers),
                changed_assumptions=list(proposal.assumptions),
                specialization_links=specialization_links,
                expected_use="Proposed intended consumers; no transfer is established",
                observed_use="No accepted consumer use recorded for this new publication",
                statement=proposal.statement,
                name=proposal.theorem_name,
                outcome=result.status,
                environment_id=self.context_id(),
            )
            if result.verification is not None:
                payload["verification_receipt"] = result.verification.receipt.to_dict()
            source_evidence = specialization_evidence
            if result.candidate is not None:
                payload["source_digest"] = result.candidate.source_hash
                try:
                    artifact = self.catalog.put_artifact(
                        result.candidate.source.encode(),
                        kind="generalization_source",
                        deadline_monotonic=budget.deadline_monotonic,
                    )
                    payload["source_evidence"] = artifact.to_record()
                    source_evidence = tuple(dict.fromkeys((*source_evidence, artifact)))
                except (OSError, ValueError, RuntimeError, TimeoutError):
                    payload["source_evidence_unavailable"] = True
            event = self.record(
                "proposal",
                payload,
                operation_id=operation_id,
                attempt_id=attempt_id,
                provenance=provenance,
                additional_evidence=source_evidence,
                budget=budget,
            )
            if event is not None:
                try:
                    if (
                        self.catalog.get_event(
                            event.event_id,
                            self.policy,
                            deadline_monotonic=budget.deadline_monotonic,
                        )
                        is None
                    ):
                        event = None
                except (OSError, ValueError, RuntimeError, sqlite3.Error):
                    event = None
            if event is not None:
                payload["event_id"] = event.event_id
                payload["evidence_digest"] = (
                    event.evidence[0].digest if event.evidence else ""
                )
            self.emit(
                proposals=[payload] if event is not None else [],
                partial=result.status != "checked_theorem" or event is None,
            )
            return result
        finally:
            elapsed = time.monotonic() - started
            session.mathematical_memory_state["research_spent_s"] = (
                float(session.mathematical_memory_state.get("research_spent_s", 0))
                + elapsed
            )
            # A cancellation or ambiguous failure keeps its reservation charged;
            # only a completed worker/result may return an unused subset.
            if "result" in locals():
                try:
                    self.request_store.settle_research(
                        str(request["request_id"]),
                        elapsed,
                        deadline_monotonic=budget.deadline_monotonic,
                    )
                except (OSError, ValueError, TimeoutError):
                    # An unavailable advisory ledger conservatively retains the
                    # full reservation; it cannot revoke a published theorem.
                    session.mathematical_memory_state[
                        "research_settlement_deferred"
                    ] = True

    def propose_repeated_patterns(self, budget: MemoryBudget) -> list[dict[str, Any]]:
        """Expose bounded eligible typed motifs as unproved discovery proposals."""
        from .generalization import propose_generalization, repeated_patterns

        self.check_budget(budget)
        eligible = []
        for name, profile in tuple(self.known_declarations.items())[
            : self.config.cheap_candidate_cap
        ]:
            self.check_budget(budget)
            candidate_id = self.known_candidate_ids.get(name, "")
            if (
                candidate_id
                and profile.complete
                and self.candidate_eligible(candidate_id, budget=budget)
            ):
                eligible.append(profile)
        session = self.session()
        seen = session.mathematical_memory_state.setdefault("pattern_proposal_ids", [])
        rows = []
        for instances in repeated_patterns(eligible)[:8]:
            self.check_budget(budget)
            source_ids = tuple(
                self.known_candidate_ids[profile.declaration_name]
                for profile in instances
            )
            provenance = self.provenance(source_ids)
            if not self._sources_admitted(source_ids, budget=budget):
                continue
            # Reuse one explicit source type as an investigation starting point.
            # Typed grouping does not justify inventing or deleting assumptions.
            proposal = propose_generalization(
                instances,
                statement=instances[0].statement,
                theorem_name="memory_pattern_" + content_digest(source_ids)[:16],
                rationale="Repeated eligible typed shape; investigate a reusable general statement",
            )
            if proposal.proposal_id in seen:
                continue
            payload = {
                **proposal.to_record(),
                "name": proposal.theorem_name,
                "outcome": "proposed",
                "environment_id": self.context_id(),
                "conditions": "Discovery proposal; explicit allocated develop request required for proof research",
            }
            event = self.record(
                "proposal", payload, provenance=provenance, budget=budget
            )
            if event is None:
                continue
            seen.append(proposal.proposal_id)
            del seen[:-128]
            rows.append(
                {
                    **payload,
                    "event_id": event.event_id,
                    "evidence_digest": (
                        event.evidence[0].digest if event.evidence else ""
                    ),
                }
            )
        if rows:
            self.emit(proposals=rows, partial=True)
        return rows

    def query_experience(
        self,
        *,
        pinned_generation: GenerationPin | None = None,
        limit: int = 64,
        budget: MemoryBudget | None = None,
    ) -> Any:
        if budget is not None:
            self.check_budget(budget)
        return self.catalog.query(
            self.policy,
            pinned_generation=pinned_generation,
            limit=limit,
            deadline_monotonic=(
                budget.deadline_monotonic
                if budget is not None
                else time.monotonic() + 0.025
            ),
        )

    def observe_session_event(self, record: Mapping[str, Any]) -> None:
        if str(record.get("phase", "")).startswith("mathematical_memory"):
            return
        session = self.session()
        if session is None:
            return
        pending = self._pending_solution
        if pending and session.dossier.has_root_proof_finalization_receipt():
            proof = str(session.dossier.final_proof or "")
            if (
                content_digest(proof) == pending["proof_hash"]
                and pending.get("environment_id") == self.context_id()
                and pending.get("policy_id") == self.policy_id
                and self.application_eligible(str(pending.get("candidate_id", "")))
            ):
                payload = {
                    **pending["observation"],
                    "candidate_id": pending.get("candidate_id", ""),
                    "outcome": "checked_solution",
                    "accepted_root_proof": proof,
                    "acceptance_receipt": session.dossier.root_proof_finalization_receipt_hash(),
                    "root_certificate": dict(
                        session.dossier.root_proof_certificate or {}
                    ),
                    "accepted_replay_helpers": list(
                        session.dossier.final_replay_helpers
                    ),
                }
                event = self.record(
                    "application",
                    payload,
                    event_id=content_digest(
                        {
                            "accepted": pending["attempt_id"],
                            "proof": pending["proof_hash"],
                        }
                    ),
                    operation_id=pending["operation_id"],
                    attempt_id=pending["attempt_id"],
                    provenance=self.application_provenance(
                        str(pending.get("candidate_id", "")), accepted=True
                    ),
                )
                if event is not None:
                    self._pending_solution = None
                    session.mathematical_memory_state.pop("pending_solution", None)
                    payload["event_id"] = event.event_id
                    self.emit(goal_id=payload["goal_id"], applications=[payload])

    def emit(
        self,
        *,
        goal_id: str = "",
        applications: list[dict[str, Any]] | None = None,
        candidates: list[dict[str, Any]] | None = None,
        proposals: list[dict[str, Any]] | None = None,
        partial: bool = False,
        budget: MemoryBudget | None = None,
    ) -> dict[str, Any]:
        session = self.session()
        if session is None or (budget is not None and budget.remaining_s() <= 0):
            return {}
        try:
            pin = self.catalog.generation(
                deadline_monotonic=(
                    budget.deadline_monotonic if budget else time.monotonic() + 0.025
                )
            )
        except (OSError, RuntimeError, sqlite3.Error):
            self.health = "unavailable"
            return {}
        previous = self.last_view or session.mathematical_memory_state.get(
            "last_view", {}
        )
        if previous.get("environment_id") != self.context_id():
            previous = {}
        view = {
            "mode": self.config.mode,
            "status": self.health,
            "generation": pin.to_record(),
            "goal_id": goal_id or previous.get("goal_id", self.context_id()),
            "environment_id": self.context_id(),
            "policy_id": self.policy_id,
            "candidates": (
                candidates if candidates is not None else previous.get("candidates", [])
            )[: self.config.prepared_candidate_cap],
            "applications": (
                applications
                if applications is not None
                else previous.get("applications", [])
            )[: self.config.probe_cap],
            "obstructions": session.mathematical_memory_state.get(
                "obstruction_rows", []
            )[:16],
            "proposals": (
                proposals if proposals is not None else previous.get("proposals", [])
            )[:32],
            "notes": [],
            "omitted": 0,
            "partial": partial,
            "scope": session.scope,
            "allocation_id": "mathematical_memory",
            "research_allocation_id": self.config.research_allocation_id,
            "coverage": self.candidate_coverage,
            "request_owner": self.request_owner,
        }
        session.mathematical_memory_state["last_view"] = view
        self.last_view = view
        session._record_event(
            {"phase": "mathematical_memory", "mathematical_memory": view}
        )
        return view


@contextlib.contextmanager
def _owner_metadata_lease(output: Path, current_store: Any = None):
    """Use the dispatch election for startup and disablement metadata too."""
    if current_store is not None and current_store.owns_dispatch:
        yield True
        return
    from .requests import MemoryRequestStore

    temporary = MemoryRequestStore(output)
    try:
        try:
            owned = temporary._claim_dispatch()
        except (OSError, ValueError, RuntimeError):
            owned = False
        yield owned
    finally:
        temporary.close()


def persist_memory_owner(
    service: MathematicalMemoryService, *, elected_startup_owner: bool = False
) -> None:
    """Atomically replace the elected root's bounded current configuration."""
    session = service.session()
    if (
        session is None
        or session.parent is not None
        or not (service.request_owner or elected_startup_owner)
    ):
        return
    output = getattr(getattr(session, "recorder", None), "output_dir", None)
    if output is None:
        return
    from .export_observer import persist_export_binding

    with _owner_metadata_lease(Path(output), service.request_store) as owned:
        if not owned:
            return
        if not persist_export_binding(Path(output), service.catalog):
            _LOG.debug("Mathematical memory export ownership unavailable")
            return
        _write_memory_owner_metadata(
            Path(output), service.run_id, service.config, service.policy
        )


def _write_memory_owner_metadata(
    output: Path,
    run_id: str,
    config: MemoryConfig,
    policy: EligibilityPolicy,
    *,
    replace_only: bool = False,
) -> None:
    try:
        from .evidence import contained_directory, read_contained, write_contained

        payload = canonical_json(
            {
                "schema_version": 1,
                "run_id": run_id,
                "request_owner": True,
                "mathematical_memory_config": config.to_record(),
                "mathematical_memory_policy": policy.to_record(),
            }
        ).encode()
        if len(payload) > 65536:
            raise ValueError("memory owner metadata exceeds byte limit")
        deadline = time.monotonic() + 0.05
        with contained_directory(output) as directory:
            if replace_only:
                try:
                    read_contained(
                        directory, "mathematical_memory_owner.json", 65536, deadline
                    )
                except FileNotFoundError:
                    return
            write_contained(
                directory, "mathematical_memory_owner.json", payload, deadline
            )
    except Exception:
        _LOG.debug("Mathematical memory owner metadata unavailable", exc_info=True)


def persist_disabled_memory_owner(
    session: Any,
    config: MemoryConfig | None = None,
    policy: EligibilityPolicy | None = None,
    *,
    request_owner: bool = True,
) -> None:
    """Retire prior ownership on disablement without creating fresh off files."""
    output = getattr(getattr(session, "recorder", None), "output_dir", None)
    if output is None or session.parent is not None or not request_owner:
        return
    from .export_observer import read_regular_file

    try:
        read_regular_file(
            Path(output) / "mathematical_memory_owner.json",
            65536,
            time.monotonic() + 0.05,
        )
    except (OSError, ValueError, RuntimeError):
        return
    previous = getattr(session, "mathematical_memory", None)
    current_store = getattr(previous, "request_store", None)
    with _owner_metadata_lease(Path(output), current_store) as owned:
        if owned:
            _write_memory_owner_metadata(
                Path(output),
                str(output),
                config or MemoryConfig(),
                policy or EligibilityPolicy(),
                replace_only=True,
            )


def finalization_without_memory_eligible(session: Any, candidate: Any) -> bool:
    """Retain dependency obligations when current memory authority is absent."""
    if candidate.source_action_id == "mathematical_memory":
        return False
    from ensemble_prover.proof_dossier import canonical_lean_identifier

    names = {
        canonical_lean_identifier(helper.name)
        for helper in getattr(session.dossier, "verified_helpers", {}).values()
        if helper.phase.startswith("mathematical_memory")
        or "mathematical_memory_owned_context" in helper.provenance_tags
    }
    state = getattr(session, "mathematical_memory_state", {})
    if state.get("retired_support_incomplete") is True:
        return False
    retired_imports = state.get("retired_import_owners", ())
    if not isinstance(retired_imports, (list, tuple)) or retired_imports:
        return False
    retired = state.get("retired_support_names", ())
    if (
        not isinstance(retired, (list, tuple))
        or len(retired) > 4096
        or any(not isinstance(name, str) for name in retired)
    ):
        return False
    names.update(canonical_lean_identifier(name) for name in retired)
    bundles = state.get("retired_bundle_obligations", ())
    if (
        not isinstance(bundles, (list, tuple))
        or len(bundles) > 4096
        or any(not isinstance(identity, str) for identity in bundles)
    ):
        return False
    for node in getattr(getattr(session, "proof_state", None), "nodes", {}).values():
        for group in getattr(node, "assembly_attempt_groups", ()):
            prefix = "decl_application:mathematical_memory:"
            if str(group.source).startswith(prefix) and group.status != "obsolete":
                parts = str(group.source)[len(prefix) :].split(":", 1)
                if len(parts) != 2:
                    return False
                names.add(canonical_lean_identifier(parts[1]))
    if not names and not bundles:
        return True
    getter = getattr(session.lean, "helper_usage_observation", None)
    try:
        usage = (
            getter(
                statement=candidate.target_statement or session.problem.statement_type,
                proof=candidate.proof,
                preamble=session.acceptance_preamble(),
                lemmas=candidate.replay_helpers,
            )
            if callable(getter)
            else None
        )
        if usage is None or not usage.observed or not usage.complete:
            return False
        reachable = {
            canonical_lean_identifier(name) for name in usage.reachable_constants
        }
        return names.isdisjoint(reachable) and not any(
            "B_" + identity in constant.split(".")
            for identity in bundles
            for constant in reachable
        )
    except (OSError, ValueError, RuntimeError, sqlite3.Error):
        return False


def snapshot_memory_source_obligations(
    service: MathematicalMemoryService,
) -> dict[str, Any]:
    """Retain bounded dependency obligations, never replay authority."""
    session = service.session()
    if session is None:
        return {}
    state = dict(session.mathematical_memory_state)
    retired = state.get("retired_support_names", ())
    if (
        not isinstance(retired, (list, tuple))
        or len(retired) > 4096
        or any(not isinstance(name, str) for name in retired)
    ):
        state["retired_support_incomplete"] = True
        retired = ()
    names = tuple(
        dict.fromkeys(
            (
                *retired,
                *service.known_candidate_ids,
                *service._memory_support_names,
            )
        )
    )
    state["retired_support_names"] = list(names[:4096])
    if len(names) > 4096:
        state["retired_support_incomplete"] = True
    retired_bundles = state.get("retired_bundle_obligations", ())
    if (
        not isinstance(retired_bundles, (list, tuple))
        or len(retired_bundles) > 4096
        or any(not isinstance(identity, str) for identity in retired_bundles)
    ):
        state["retired_support_incomplete"] = True
        retired_bundles = ()
    bundles = set(retired_bundles) | set(
        getattr(session, "theory_imported_bundle_ids", ())
    )
    for line in service.context()[1].splitlines():
        tokens = line.strip().split()
        if not tokens or tokens[0] != "import":
            continue
        for module in tokens[1:]:
            match = re.fullmatch(
                r"MiniTheory\.Domains\.[A-Za-z0-9_]+\.Bundles\.B_([A-Za-z0-9_]+)\.Theory",
                module,
            )
            if match:
                bundles.add(match.group(1))
    state["retired_bundle_obligations"] = sorted(bundles)[:4096]
    if len(bundles) > 4096:
        state["retired_support_incomplete"] = True
    retired_imports = state.get("retired_import_owners", ())
    if (
        not isinstance(retired_imports, (list, tuple))
        or len(retired_imports) > 4096
        or any(not isinstance(identity, str) for identity in retired_imports)
    ):
        state["retired_support_incomplete"] = True
        retired_imports = ()
    imports = set(retired_imports) | service._memory_import_owners
    state["retired_import_owners"] = sorted(imports)[:4096]
    if len(imports) > 4096:
        state["retired_support_incomplete"] = True
    return state


def install_session_memory(
    session: Any,
    config: MemoryConfig | Mapping[str, Any] | None,
    *,
    policy: EligibilityPolicy | None = None,
    allocation: MemoryAllocation | None = None,
    request_owner: bool = True,
    provenance_registry: Any = None,
) -> None:
    def release_previous() -> None:
        previous = getattr(session, "mathematical_memory", None)
        if previous is not None and previous.session() is session:
            session.mathematical_memory_state.update(
                snapshot_memory_source_obligations(previous)
            )
            if previous.request_store is not None:
                previous.request_store.close()
            previous.catalog.close()
        session.mathematical_memory = None
        reference = _SESSIONS.get(id(session.dossier))
        if reference is not None and reference() is session:
            _SESSIONS.pop(id(session.dossier), None)

    if config is None:
        persist_disabled_memory_owner(
            session, policy=policy, request_owner=request_owner
        )
        release_previous()
        session.mathematical_memory = None
        reference = _SESSIONS.get(id(session.dossier))
        if reference is not None and reference() is session:
            _SESSIONS.pop(id(session.dossier), None)
        return
    config = (
        MemoryConfig.from_record(dict(config))
        if isinstance(config, Mapping)
        else config
    )
    if not config.enabled:
        persist_disabled_memory_owner(
            session, config, policy, request_owner=request_owner
        )
        release_previous()
        session.mathematical_memory = None
        reference = _SESSIONS.get(id(session.dossier))
        if reference is not None and reference() is session:
            _SESSIONS.pop(id(session.dossier), None)
        return
    actual_mode = str(getattr(getattr(session, "theory_library", None), "mode", "off"))
    if config.mode == "develop" and actual_mode != "build":
        raise ValueError(
            "develop memory requires the session's actual theory build capability"
        )
    release_previous()
    try:
        service = MathematicalMemoryService(
            session,
            config,
            policy,
            allocation=allocation,
            request_owner=request_owner,
            provenance_registry=provenance_registry,
        )
    except (OSError, RuntimeError, ValueError, sqlite3.Error) as exc:
        _LOG.warning("Mathematical memory unavailable: %s", exc)
        session._record_event(
            {
                "phase": "mathematical_memory",
                "mathematical_memory": {
                    "mode": config.mode,
                    "status": "unavailable",
                    "partial": True,
                    "scope": session.scope,
                    "request_owner": request_owner,
                },
            }
        )
        return
    session.mathematical_memory = service
    dossier_id = id(session.dossier)
    _SESSIONS[dossier_id] = weakref.ref(
        session,
        lambda reference: (
            _SESSIONS.pop(dossier_id, None)
            if _SESSIONS.get(dossier_id) is reference
            else None
        ),
    )
    from ensemble_prover.mini_session.actions.mathematical_memory import (
        MathematicalMemoryAction,
    )
    from ensemble_prover.mini_session.action import ActionBudget

    session.register(MathematicalMemoryAction())
    session.set_budget(
        "mathematical_memory",
        ActionBudget(
            max_invocations=config.max_invocations,
            max_total_seconds=config.action_seconds,
        ),
    )
    session._record_event(
        {
            "phase": "mathematical_memory_config",
            "mathematical_memory_request_owner": service.request_owner,
            "mathematical_memory_config": config.to_record(),
            "mathematical_memory_policy": service.policy.to_record(),
        }
    )
    persist_memory_owner(service)
    service.emit()
