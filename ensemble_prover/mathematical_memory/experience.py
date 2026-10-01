"""Policy-filtered use, failure and exposure history; utility never proves truth."""

from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Callable, Mapping, Sequence

from .catalog import MemoryCatalog
from .model import (
    EligibilityPolicy,
    GenerationPin,
    MemoryEvent,
    MemoryProvenance,
    StoreResult,
    content_digest,
    text,
)


def exact_attempt_key(
    *,
    goal_id: str,
    environment_id: str,
    context_id: str,
    declaration_id: str,
    operation: str,
    direction: str,
    method_version: str,
    limits: Mapping[str, Any],
    instantiation: Mapping[str, Any] | None = None,
) -> str:
    fields = {
        "goal_id": goal_id,
        "environment_id": environment_id,
        "context_id": context_id,
        "declaration_id": declaration_id,
        "operation": operation,
        "direction": direction,
        "method_version": method_version,
    }
    for name, value in fields.items():
        text(value, name)
    return content_digest(
        {**fields, "limits": limits, "instantiation": instantiation or {}}
    )


@dataclass(frozen=True)
class ExperienceSummary:
    declaration_id: str
    checked_applications: int = 0
    rejected_probes: int = 0
    inconclusive_probes: int = 0
    exposures: int = 0
    distinct_consumers: int = 0
    distinct_families: int = 0
    root_exports: int = 0
    complete: bool = True

    @property
    def utility(self) -> float:
        # Only a small bounded advisory preference, including failures/costs.
        return min(
            3.0,
            self.checked_applications * 0.1
            + self.distinct_consumers * 0.2
            + self.root_exports * 0.2,
        ) - min(1.0, self.rejected_probes * 0.05 + self.inconclusive_probes * 0.02)


class ExperienceIndex:
    def __init__(self, catalog: MemoryCatalog) -> None:
        self.catalog = catalog

    def summaries(
        self,
        *,
        policy: EligibilityPolicy,
        pinned_generation: GenerationPin | None = None,
        deadline_monotonic: float | None = None,
    ) -> dict[str, ExperienceSummary]:
        view = self.catalog.query(
            policy,
            pinned_generation,
            limit=self.catalog.query_scan_cap,
            deadline_monotonic=deadline_monotonic,
        )
        metrics: dict[str, dict[str, Any]] = {}
        applications: dict[tuple[str, str], str] = {}
        seen_exposures: set[tuple[str, str]] = set()
        uses = {event.event_id: event for event in view.events if event.kind == "use"}
        for event in view.events:
            payload = event.payload
            # The retrieval alias is separate from the immutable declaration
            # version retained in the event for evidence/source validation.
            declaration = str(
                payload.get("candidate_id") or payload.get("declaration_id") or ""
            )
            if event.kind in {"candidate", "exposure"}:
                declarations = payload.get("candidates", ()) or (declaration,)
                for item in declarations:
                    identity = (
                        str(
                            item.get("candidate_id") or item.get("declaration_id") or ""
                        )
                        if isinstance(item, Mapping)
                        else str(item)
                    )
                    if not identity:
                        continue
                    bucket = metrics.setdefault(identity, self._empty())
                    key = (event.operation_id, identity)
                    if key not in seen_exposures:
                        bucket["exposures"] += 1
                        seen_exposures.add(key)
                continue
            if not declaration:
                continue
            bucket = metrics.setdefault(declaration, self._empty())
            if event.kind == "application":
                outcome = str(payload.get("outcome") or "")
                key = (event.attempt_id, declaration)
                priority = {
                    "checked_solution": 6,
                    "checked_reduction": 5,
                    "elaborated_closed": 4,
                    "elaborated_partial": 3,
                    "probe_rejected": 2,
                    "probe_inconclusive": 1,
                    "unavailable": 0,
                }
                prior = applications.get(key)
                if prior is None or priority.get(outcome, -1) > priority.get(prior, -1):
                    applications[key] = outcome
            elif event.kind == "use":
                consumer = payload.get("consumer_id")
                usage = payload.get("usage")
                if (
                    not isinstance(consumer, str)
                    or not consumer
                    or usage not in {"direct", "transitive"}
                ):
                    continue
                verified_export = self._verified_export_join(event, uses)
                if payload.get("root_export") is True and not verified_export:
                    continue
                # Proof version identity, not event/attempt transport identity.
                bucket["consumers"].add(consumer)
                bucket["families"].update(event.provenance.family_ids)
                if verified_export:
                    bucket["exports"].add(consumer)
        for (_, declaration), outcome in applications.items():
            bucket = metrics[declaration]
            if outcome in {"checked_solution", "checked_reduction"}:
                bucket["checked_applications"] += 1
            elif outcome == "probe_rejected":
                bucket["rejected_probes"] += 1
            elif outcome in {"probe_inconclusive", "unavailable"}:
                bucket["inconclusive_probes"] += 1
        return {
            identity: ExperienceSummary(
                identity,
                bucket["checked_applications"],
                bucket["rejected_probes"],
                bucket["inconclusive_probes"],
                bucket["exposures"],
                len(bucket["consumers"]),
                len(bucket["families"]),
                len(bucket["exports"]),
                view.complete,
            )
            for identity, bucket in metrics.items()
        }

    @staticmethod
    def _verified_export_join(
        event: MemoryEvent, uses: Mapping[str, MemoryEvent]
    ) -> bool:
        payload = event.payload
        prior = uses.get(str(payload.get("export_use_event_id") or ""))
        if (
            payload.get("root_export") is not True
            or prior is None
            or prior.payload.get("root_export") is True
        ):
            return False
        source_digest = payload.get("verified_source_digest")
        if (
            not isinstance(source_digest, str)
            or payload.get("consumer_kind") != "root"
            or payload.get("accepted_root_proof_hash")
            != prior.payload.get("proof_hash")
            or event.provenance.run_id != prior.provenance.run_id
            or event.provenance.source_record_ids != prior.provenance.source_record_ids
            or not any(
                ref.digest == source_digest and ref.kind == "lean"
                for ref in event.evidence
            )
        ):
            return False
        return all(
            payload.get(key) == prior.payload.get(key)
            for key in (
                "consumer_id",
                "proof_hash",
                "declaration_id",
                "candidate_id",
                "usage",
                "environment_hash",
            )
        )

    @staticmethod
    def _empty() -> dict[str, Any]:
        return {
            "checked_applications": 0,
            "rejected_probes": 0,
            "inconclusive_probes": 0,
            "exposures": 0,
            "consumers": set(),
            "families": set(),
            "exports": set(),
        }

    def rank(
        self,
        candidates: Sequence[Any],
        *,
        policy: EligibilityPolicy,
        pinned_generation: GenerationPin | None = None,
        deadline_monotonic: float | None = None,
    ) -> list[Any]:
        ranked = list(candidates)
        summaries = self.summaries(
            policy=policy,
            pinned_generation=pinned_generation,
            deadline_monotonic=deadline_monotonic,
        )

        def identity(candidate: Any) -> str:
            if isinstance(candidate, Mapping):
                return str(
                    candidate.get("candidate_id")
                    or candidate.get("declaration_id")
                    or ""
                )
            return str(
                getattr(candidate, "candidate_id", "")
                or getattr(candidate, "declaration_id", "")
            )

        # Preserve the leading source choice and every unseen/speculative slot.
        slots = [
            i
            for i, candidate in enumerate(ranked)
            if i > 0
            and identity(candidate) in summaries
            and summaries[identity(candidate)].complete
        ]
        existing = [ranked[i] for i in slots]
        existing.sort(key=lambda item: -summaries[identity(item)].utility)
        for i, candidate in zip(slots, existing):
            ranked[i] = candidate
        return ranked

    def record_use(
        self,
        *,
        consumer_id: str,
        declaration_id: str,
        usage: str,
        provenance: MemoryProvenance,
        accepted_consumer: Any,
        validator: Callable[[Any], bool],
        root_export: bool = False,
        evidence: tuple = (),
    ) -> StoreResult:
        if not callable(validator) or validator(accepted_consumer) is not True:
            raise ValueError(
                "use recording requires a current accepted-consumer validation"
            )
        if usage not in {"direct", "transitive"}:
            raise ValueError("unobserved/context inclusion is not proof use")
        key = content_digest(
            {
                "consumer": consumer_id,
                "declaration": declaration_id,
                "usage": usage,
                "root_export": root_export,
                "provenance": provenance.to_record(),
            }
        )
        event = MemoryEvent(
            key,
            consumer_id,
            consumer_id,
            "use",
            {
                "consumer_id": consumer_id,
                "declaration_id": declaration_id,
                "usage": usage,
                "root_export": root_export,
            },
            provenance,
            evidence,
        )
        return self.catalog.append(event)

    def failure(
        self,
        attempt_key: str,
        *,
        policy: EligibilityPolicy,
        pinned_generation: GenerationPin | None = None,
        deadline_monotonic: float | None = None,
    ) -> MemoryEvent | None:
        view = self.catalog.query(
            policy,
            pinned_generation,
            kind="route_failure",
            limit=self.catalog.query_scan_cap,
            deadline_monotonic=deadline_monotonic,
        )
        candidates = [
            event
            for event in view.events
            if event.payload.get("attempt_key") == attempt_key
        ]
        return candidates[0] if candidates else None

    def retry_suppressed(
        self,
        attempt_key: str,
        *,
        policy: EligibilityPolicy,
        now_epoch: float,
        method_changed: bool = False,
        support_changed: bool = False,
        deadline_monotonic: float | None = None,
    ) -> bool:
        if method_changed or support_changed:
            return False
        event = self.failure(
            attempt_key, policy=policy, deadline_monotonic=deadline_monotonic
        )
        if event is None:
            return False
        # Operational backoff only; never theorem falsity or global exclusion.
        until = event.payload.get("retry_after_epoch")
        return type(until) in (int, float) and now_epoch < until

    def subscribe(
        self, *, obstruction_id: str, route_id: str, provenance: MemoryProvenance
    ) -> StoreResult:
        identity = content_digest(
            {
                "obstruction": obstruction_id,
                "route": route_id,
                "scope": provenance.scope_id,
            }
        )
        return self.catalog.append(
            MemoryEvent(
                identity,
                route_id,
                identity,
                "subscription",
                {"obstruction_id": obstruction_id, "route_id": route_id},
                provenance,
            )
        )

    def wake_routes(
        self,
        obstruction_ids: Sequence[str],
        *,
        policy: EligibilityPolicy,
        pinned_generation: GenerationPin | None = None,
        limit: int = 32,
    ) -> tuple[str, ...]:
        if type(limit) is not int or limit < 1:
            raise ValueError("wake limit must be positive")
        wanted = set(obstruction_ids)
        view = self.catalog.query(
            policy,
            pinned_generation,
            kind="subscription",
            limit=self.catalog.query_scan_cap,
        )
        routes = dict.fromkeys(
            str(event.payload["route_id"])
            for event in view.events
            if event.payload.get("obstruction_id") in wanted
            and event.payload.get("route_id")
        )
        # Notifications are fresh-check proposals, never proof or free work.
        return tuple(routes)[:limit]
