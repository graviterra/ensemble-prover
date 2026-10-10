"""Controller-supplied live source/consumer provenance and permission authority.

Old cache rows lack complete mathematical family and derivation ancestry. They
remain discovery hints. Only an explicitly configured trusted controller can
register full source/consumer identities and live integrity/visibility checks;
JSON flags, user notes and memory config do not construct this authority.
"""

from __future__ import annotations
from dataclasses import dataclass
from threading import RLock
from typing import Any, Callable, Sequence
import weakref

from .model import (
    EligibilityPolicy,
    MemoryProvenance,
    content_digest,
    integer,
    strings,
    text,
)


@dataclass(frozen=True)
class SourceProvenance:
    source_record_id: str
    source_digest: str
    problem_ids: tuple[str, ...]
    family_ids: tuple[str, ...]
    dependency_source_ids: tuple[str, ...]
    integrity_authority: Callable[[str], bool]
    visibility_authority: Callable[[], bool]
    producer_campaign_id: str = ""
    producer_order: int | None = None

    def __post_init__(self) -> None:
        import re

        text(self.source_record_id, "source record identity")
        if not isinstance(self.source_digest, str) or not re.fullmatch(
            r"[0-9a-f]{64}", self.source_digest
        ):
            raise ValueError("source version requires a full digest")
        for name in ("problem_ids", "family_ids", "dependency_source_ids"):
            object.__setattr__(self, name, strings(getattr(self, name), name))
        if not self.problem_ids or not self.family_ids:
            raise ValueError(
                "complete source provenance requires original problem/family identities"
            )
        if not callable(self.integrity_authority) or not callable(
            self.visibility_authority
        ):
            raise ValueError(
                "source registration requires live integrity and visibility authorities"
            )
        text(self.producer_campaign_id, "source producer campaign", required=False)
        if self.producer_order is not None:
            integer(self.producer_order, "original source producer coordinate")
            text(self.producer_campaign_id, "source producer campaign")


@dataclass(frozen=True)
class SourceAdmission:
    """A live source read decision; it is never historical event provenance."""

    source_record_ids: tuple[str, ...]
    problem_ids: tuple[str, ...]
    family_ids: tuple[str, ...]
    run_id: str


@dataclass(frozen=True)
class ConsumerProvenance:
    run_id: str
    campaign_id: str
    problem_id: str
    family_id: str
    scope: str
    scope_id: str
    current_authority: Callable[[], bool]
    acceptance_order: int | None = None

    def __post_init__(self) -> None:
        for name in ("run_id", "problem_id", "family_id", "scope_id"):
            text(getattr(self, name), name)
        text(self.campaign_id, "campaign id", required=False)
        if self.scope not in {"session", "problem", "campaign", "shared"}:
            raise ValueError("unknown consumer scope")
        if not callable(self.current_authority):
            raise ValueError(
                "consumer registration requires a live provenance/permission authority"
            )
        if self.acceptance_order is not None and (
            type(self.acceptance_order) is not int or self.acceptance_order < 0
        ):
            raise ValueError(
                "consumer acceptance chronology must be a controller coordinate"
            )


class ControllerProvenanceRegistry:
    """Live immutable source versions and bounded controller authority snapshots.

    Authority callbacks must read precomputed in-memory state without blocking
    I/O or waiting. Refresh external state before supplying its current snapshot;
    synchronous callback execution cannot be preempted by the consuming owner.
    """

    def __init__(
        self,
        *,
        policy_version: int = 1,
        sequence_authority: Callable[[ConsumerProvenance], int | None] | None = None,
        chronology_authority: Callable[[MemoryProvenance], bool] | None = None,
        closure_cap: int = 0,
    ) -> None:
        if (
            type(policy_version) is not int
            or policy_version < 1
            or type(closure_cap) is not int
            or closure_cap < 0
        ):
            raise ValueError("invalid provenance registry limits")
        if sequence_authority is not None and not callable(sequence_authority):
            raise ValueError("producer chronology requires a live controller sequencer")
        self.policy_version = policy_version
        self.sequence_authority = sequence_authority
        if chronology_authority is not None and not callable(chronology_authority):
            raise ValueError(
                "chronology validation requires a live controller authority"
            )
        self.chronology_authority = chronology_authority
        # A positive limit is an explicit admission policy. Local retrieval
        # windows must not limit the ancestry of a completed mathematical fact.
        self.closure_cap = closure_cap
        self._sources: dict[str, SourceProvenance] = {}
        self._source_ids_by_digest: dict[str, set[str]] = {}
        self._consumers: dict[str, ConsumerProvenance] = {}
        self._lock = RLock()
        self._issued_coordinates: set[str] = set()
        self._context_sources: dict[tuple[str, int], tuple[Any, str, str]] = {}

    def register_source(self, source: SourceProvenance) -> None:
        if not isinstance(source, SourceProvenance):
            raise ValueError(
                "source registration requires controller-supplied live metadata"
            )
        with self._lock:
            existing = self._sources.get(source.source_record_id)
            if existing is not None and existing != source:
                raise ValueError(
                    "immutable source record conflict; use a new version identity"
                )
            self._sources[source.source_record_id] = source
            self._source_ids_by_digest.setdefault(source.source_digest, set()).add(
                source.source_record_id
            )

    def register_consumer(self, consumer: ConsumerProvenance) -> None:
        if not isinstance(consumer, ConsumerProvenance):
            raise ValueError(
                "consumer registration requires controller-supplied live metadata"
            )
        with self._lock:
            existing = self._consumers.get(consumer.run_id)
            if existing is not None and existing != consumer:
                raise ValueError("immutable consumer record conflict")
            self._consumers[consumer.run_id] = consumer

    def source_matches(self, source_record_id: str, source_digest: str) -> bool:
        """Bind a retrieved/profile identity to its registered exact source version."""
        with self._lock:
            source = self._sources.get(source_record_id)
        if source is None or source.source_digest != source_digest:
            return False
        try:
            return (
                source.visibility_authority() is True
                and source.integrity_authority(source_digest) is True
                and self._closure((source_record_id,)) is not None
            )
        except Exception:
            return False

    def source_ids_for_digest(self, source_digest: str) -> tuple[str, ...]:
        """Resolve exact context-source versions through registered live authority."""
        with self._lock:
            identities = tuple(
                sorted(self._source_ids_by_digest.get(source_digest, ()))
            )
        if self.closure_cap > 0 and len(identities) > self.closure_cap:
            return ()
        return tuple(
            identity
            for identity in identities
            if self.source_matches(identity, source_digest)
        )

    def has_source(self, source_record_id: str) -> bool:
        """Distinguish a registered-but-denied version from an unknown source."""
        with self._lock:
            return source_record_id in self._sources

    def bind_context_source(
        self, run_id: str, helper: Any, source_record_id: str
    ) -> bool:
        """Controller-bind one actual admitted helper object to its exact owner.

        The controller must supply the live record from the consumer dossier.
        Restored records need a new trusted binding; equal bytes alone cannot
        select a different owner or preserve this in-process permission.
        """
        from ensemble_prover.proof_dossier import VerifiedHelper
        from .profiles import digest

        if not isinstance(helper, VerifiedHelper):
            raise TypeError("context source binding requires an admitted helper record")
        text(run_id, "context run")
        text(source_record_id, "context source owner")
        source_digest = digest(helper.source)
        if not self.source_matches(source_record_id, source_digest):
            return False
        with self._lock:
            consumer = self._consumers.get(run_id)
        if consumer is None:
            return False
        try:
            if consumer.current_authority() is not True:
                return False
        except Exception:
            return False
        key = (run_id, id(helper))
        with self._lock:
            previous = self._context_sources.get(key)
            if previous is not None and (
                previous[0]() is not helper
                or previous[1:] != (source_digest, source_record_id)
            ):
                raise ValueError("immutable admitted-context owner/version conflict")

            def expired(reference: Any) -> None:
                with self._lock:
                    current = self._context_sources.get(key)
                    if current is not None and current[0] is reference:
                        self._context_sources.pop(key, None)

            reference = weakref.ref(helper, expired)
            self._context_sources[key] = (reference, source_digest, source_record_id)
        return True

    def context_source_id(self, run_id: str, helper: Any) -> str | None:
        """Resolve object ownership; admission separately checks live permissions."""
        from .profiles import digest

        with self._lock:
            binding = self._context_sources.get((run_id, id(helper)))
        if binding is None or binding[0]() is not helper:
            return None
        if digest(helper.source) != binding[1]:
            raise ValueError("admitted context source version changed")
        return binding[2]

    def admit_sources(
        self,
        source_record_ids: Sequence[str],
        *,
        run_id: str,
        policy: EligibilityPolicy,
    ) -> SourceAdmission | None:
        """Authorize original artifacts, without attributing a new consumer event.

        Holdout exclusions and cutoffs constrain the original source closure.
        The consuming run still needs current permission and visible scope, but
        its family/problem and a new execution coordinate do not date the source.
        """
        source_ids = strings(source_record_ids, "source admission identities")
        if (
            not source_ids
            or not isinstance(policy, EligibilityPolicy)
            or policy.policy_version != self.policy_version
        ):
            return None
        with self._lock:
            consumer = self._consumers.get(run_id)
        if (
            consumer is None
            or (consumer.scope, consumer.scope_id) not in policy.visible_scopes
        ):
            return None
        try:
            if consumer.current_authority() is not True:
                return None
        except Exception:
            return None
        closure = self._closure(source_ids)
        if closure is None:
            return None
        identities = tuple(source.source_record_id for source in closure)
        problems = tuple(
            dict.fromkeys(
                problem for source in closure for problem in source.problem_ids
            )
        )
        families = tuple(
            dict.fromkeys(family for source in closure for family in source.family_ids)
        )
        if policy.allowed_source_record_ids is not None and not set(
            identities
        ).issubset(policy.allowed_source_record_ids):
            return None
        if set(problems).intersection(policy.excluded_problem_ids) or set(
            families
        ).intersection(policy.excluded_family_ids):
            return None
        if policy.chronology_cutoff is not None and any(
            source.producer_campaign_id != policy.chronology_campaign_id
            or source.producer_order is None
            or source.producer_order > policy.chronology_cutoff
            for source in closure
        ):
            return None
        return SourceAdmission(identities, problems, families, run_id)

    def consumer_eligible(self, run_id: str, policy: EligibilityPolicy) -> bool:
        """Require live consumer permission without attributing an observed use."""
        with self._lock:
            consumer = self._consumers.get(run_id)
        if (
            consumer is None
            or policy.policy_version != self.policy_version
            or (consumer.scope, consumer.scope_id) not in policy.visible_scopes
        ):
            return False
        try:
            return consumer.current_authority() is True
        except Exception:
            return False

    def _closure(
        self, source_ids: Sequence[str]
    ) -> tuple[SourceProvenance, ...] | None:
        visited: set[str] = set()
        active: set[str] = set()
        result = []

        for root in source_ids:
            pending: list[tuple[str, SourceProvenance | None]] = [(root, None)]
            while pending:
                identity, completed = pending.pop()
                if completed is not None:
                    active.remove(identity)
                    try:
                        if (
                            completed.visibility_authority() is not True
                            or completed.integrity_authority(completed.source_digest) is not True
                        ):
                            return None
                    except Exception:
                        return None
                    visited.add(identity)
                    result.append(completed)
                    continue
                if identity in active:
                    return None
                if identity in visited:
                    continue
                if self.closure_cap > 0 and len(visited) + len(active) >= self.closure_cap:
                    return None
                # Registered versions are immutable and never removed. Read
                # only reachable records; unrelated campaign size is irrelevant.
                with self._lock:
                    source = self._sources.get(identity)
                if source is None:
                    return None
                active.add(identity)
                pending.append((identity, source))
                pending.extend((dependency, None) for dependency in reversed(source.dependency_source_ids))
        return tuple(result)

    def issue_provenance(
        self, source_record_ids: Sequence[str], *, run_id: str, accepted: bool = False
    ) -> MemoryProvenance | None:
        source_ids = strings(source_record_ids, "source record identities")
        with self._lock:
            consumer = self._consumers.get(run_id)
        if not source_ids or consumer is None:
            return None
        closure = self._closure(source_ids)
        if closure is None:
            return None
        try:
            if consumer.current_authority() is not True:
                return None
            order = (
                self.sequence_authority(consumer) if self.sequence_authority else None
            )
            if order is not None and (type(order) is not int or order < 0):
                return None
        except Exception:
            return None
        closure_ids = tuple(source.source_record_id for source in closure)
        provenance = MemoryProvenance(
            source_record_ids=source_ids,
            problem_ids=(consumer.problem_id,),
            family_ids=(consumer.family_id,),
            scope=consumer.scope,
            scope_id=consumer.scope_id,
            campaign_id=consumer.campaign_id,
            run_id=consumer.run_id,
            producer_order=order,
            acceptance_order=consumer.acceptance_order if accepted else None,
            complete=True,
            policy_version=self.policy_version,
            ancestry_source_ids=tuple(
                identity for identity in closure_ids if identity not in source_ids
            ),
            ancestry_problem_ids=tuple(
                dict.fromkeys(
                    problem for source in closure for problem in source.problem_ids
                )
            ),
            ancestry_family_ids=tuple(
                dict.fromkeys(
                    family for source in closure for family in source.family_ids
                )
            ),
        )
        if order is not None:
            with self._lock:
                self._issued_coordinates.add(content_digest(provenance.to_record()))
        return provenance

    def current_authority(self, provenance: MemoryProvenance, event_id: str) -> bool:
        del event_id  # Event conflicts and retractions remain the catalog/journal's job.
        if not provenance.complete:
            # Session-local incomplete observations do not gain portability.
            if (
                provenance.scope != "session"
                or provenance.policy_version != self.policy_version
            ):
                return False
            with self._lock:
                referenced = tuple(
                    identity
                    for identity in (
                        *provenance.source_record_ids,
                        *provenance.ancestry_source_ids,
                    )
                    if identity in self._sources
                )
                consumer = self._consumers.get(provenance.run_id)
            if referenced and self._closure(referenced) is None:
                return False
            if consumer is not None:
                try:
                    if consumer.current_authority() is not True:
                        return False
                except Exception:
                    return False
            return True
        if provenance.policy_version != self.policy_version:
            return False
        if provenance.producer_order is not None:
            with self._lock:
                issued = (
                    content_digest(provenance.to_record()) in self._issued_coordinates
                )
            if not issued:
                try:
                    if (
                        self.chronology_authority is None
                        or self.chronology_authority(provenance) is not True
                    ):
                        return False
                except Exception:
                    return False
        with self._lock:
            consumer = self._consumers.get(provenance.run_id)
        if consumer is None or (
            consumer.scope,
            consumer.scope_id,
            consumer.campaign_id,
        ) != (provenance.scope, provenance.scope_id, provenance.campaign_id):
            return False
        try:
            if consumer.current_authority() is not True:
                return False
        except Exception:
            return False
        closure = self._closure(provenance.source_record_ids)
        if closure is None:
            return False
        expected_sources = {source.source_record_id for source in closure} - set(
            provenance.source_record_ids
        )
        expected_problems = {
            problem for source in closure for problem in source.problem_ids
        }
        expected_families = {
            family for source in closure for family in source.family_ids
        }
        return (
            provenance.problem_ids == (consumer.problem_id,)
            and provenance.family_ids == (consumer.family_id,)
            and set(provenance.ancestry_source_ids) == expected_sources
            and set(provenance.ancestry_problem_ids) == expected_problems
            and set(provenance.ancestry_family_ids) == expected_families
            and (
                provenance.acceptance_order is None
                or provenance.acceptance_order == consumer.acceptance_order
            )
        )
