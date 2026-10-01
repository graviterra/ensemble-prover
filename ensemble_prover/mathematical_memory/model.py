"""Immutable advisory memory records; none is a proof-acceptance receipt."""

from __future__ import annotations

import hashlib
import json
import math
import re
from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import Any, Mapping

SCHEMA_VERSION = 1
_DIGEST = re.compile(r"[0-9a-f]{64}\Z")


def canonical_json(value: Any) -> str:
    return json.dumps(
        thaw(value),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )


def content_digest(value: Any) -> str:
    data = value if isinstance(value, bytes) else canonical_json(value).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def text(value: Any, name: str, *, required: bool = True) -> str:
    if not isinstance(value, str) or (required and not value.strip()):
        raise ValueError(f"{name} requires {'nonempty ' if required else ''}text")
    return value


def strings(value: Any, name: str) -> tuple[str, ...]:
    if not isinstance(value, (tuple, list)):
        raise ValueError(f"{name} requires a string sequence")
    return tuple(dict.fromkeys(text(item, name) for item in value))


def integer(value: Any, name: str, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} requires an integer >= {minimum}")
    return value


def freeze(value: Any, depth: int = 0) -> Any:
    if depth > 32:
        raise ValueError("memory payload exceeds nesting limit")
    if isinstance(value, Mapping):
        return MappingProxyType(
            {text(k, "payload key"): freeze(v, depth + 1) for k, v in value.items()}
        )
    if isinstance(value, (list, tuple)):
        return tuple(freeze(v, depth + 1) for v in value)
    if value is None or type(value) in (str, int, bool):
        return value
    if type(value) is float and math.isfinite(value):
        return value
    raise ValueError("memory payload must contain finite JSON values")


def thaw(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {k: thaw(v) for k, v in value.items()}
    if isinstance(value, tuple):
        return [thaw(v) for v in value]
    if hasattr(value, "to_record"):
        return value.to_record()
    return value


class ApplicationOutcome(str, Enum):
    NOT_CHECKED = "not_checked"
    UNAVAILABLE = "unavailable"
    PROBE_REJECTED = "probe_rejected"
    PROBE_INCONCLUSIVE = "probe_inconclusive"
    ELABORATED_PARTIAL = "elaborated_partial"
    ELABORATED_CLOSED = "elaborated_closed"
    CHECKED_REDUCTION = "checked_reduction"
    CHECKED_SOLUTION = "checked_solution"


@dataclass(frozen=True)
class GenerationPin:
    lineage: str
    epoch: str
    sequence: int

    def __post_init__(self) -> None:
        text(self.lineage, "lineage")
        text(self.epoch, "epoch")
        integer(self.sequence, "sequence")

    def to_record(self) -> dict[str, Any]:
        return {"lineage": self.lineage, "epoch": self.epoch, "sequence": self.sequence}

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> GenerationPin:
        return cls(record["lineage"], record["epoch"], record["sequence"])


@dataclass(frozen=True)
class EvidenceReference:
    digest: str
    size: int
    kind: str = "json"

    def __post_init__(self) -> None:
        if not isinstance(self.digest, str) or not _DIGEST.fullmatch(self.digest):
            raise ValueError("evidence digest must be a full lowercase SHA256")
        integer(self.size, "evidence size")
        text(self.kind, "evidence kind")

    def to_record(self) -> dict[str, Any]:
        return {"digest": self.digest, "size": self.size, "kind": self.kind}

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> EvidenceReference:
        return cls(record["digest"], record["size"], record.get("kind", "json"))


@dataclass(frozen=True)
class MemoryProvenance:
    source_record_ids: tuple[str, ...] = ()
    problem_ids: tuple[str, ...] = ()
    family_ids: tuple[str, ...] = ()
    scope: str = "session"
    scope_id: str = ""
    campaign_id: str = ""
    run_id: str = ""
    producer_order: int | None = None
    acceptance_order: int | None = None
    complete: bool = False
    policy_version: int = 1
    ancestry_source_ids: tuple[str, ...] = ()
    ancestry_problem_ids: tuple[str, ...] = ()
    ancestry_family_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        for name in (
            "source_record_ids",
            "problem_ids",
            "family_ids",
            "ancestry_source_ids",
            "ancestry_problem_ids",
            "ancestry_family_ids",
        ):
            object.__setattr__(self, name, strings(getattr(self, name), name))
        if self.scope not in {"session", "problem", "campaign", "shared"}:
            raise ValueError("unknown memory visibility scope")
        for name in ("scope_id", "campaign_id", "run_id"):
            text(getattr(self, name), name, required=False)
        integer(self.policy_version, "policy_version", 1)
        if type(self.complete) is not bool:
            raise ValueError("complete requires a boolean")
        for name in ("producer_order", "acceptance_order"):
            if getattr(self, name) is not None:
                integer(getattr(self, name), name)
        # A late proof-use observation can be produced after the accepted
        # consumer proof. Both coordinates remain immutable and independently
        # constrained by a chronological cutoff; their order is event-specific.
        if self.complete and (
            not self.scope_id
            or not self.source_record_ids
            or not self.problem_ids
            or not self.family_ids
        ):
            raise ValueError(
                "complete provenance requires scope, source, problem and family identities"
            )

    def to_record(self) -> dict[str, Any]:
        return {name: thaw(getattr(self, name)) for name in self.__dataclass_fields__}

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> MemoryProvenance:
        unknown = set(record) - set(cls.__dataclass_fields__)
        if unknown:
            raise ValueError(f"unknown provenance fields: {sorted(unknown)}")
        return cls(**record)


Provenance = MemoryProvenance


@dataclass(frozen=True)
class EligibilityPolicy:
    allowed_source_record_ids: tuple[str, ...] | None = None
    excluded_problem_ids: tuple[str, ...] = ()
    excluded_family_ids: tuple[str, ...] = ()
    visible_scopes: tuple[tuple[str, str], ...] = ()
    chronology_campaign_id: str = ""
    chronology_cutoff: int | None = None
    policy_version: int = 1
    allow_incomplete_session: bool = False

    def __post_init__(self) -> None:
        for name in (
            "allowed_source_record_ids",
            "excluded_problem_ids",
            "excluded_family_ids",
        ):
            val = getattr(self, name)
            if val is not None:
                object.__setattr__(self, name, strings(val, name))
        scopes = []
        for scope in self.visible_scopes:
            if not isinstance(scope, (tuple, list)) or len(scope) != 2:
                raise ValueError("visible scopes require scope/id pairs")
            if scope[0] not in {"session", "problem", "campaign", "shared"}:
                raise ValueError("unknown visible scope")
            scopes.append((scope[0], text(scope[1], "scope id")))
        object.__setattr__(self, "visible_scopes", tuple(dict.fromkeys(scopes)))
        text(self.chronology_campaign_id, "chronology campaign", required=False)
        integer(self.policy_version, "policy version", 1)
        if self.chronology_cutoff is not None:
            integer(self.chronology_cutoff, "chronology cutoff")
            text(self.chronology_campaign_id, "chronology campaign")
        if type(self.allow_incomplete_session) is not bool:
            raise ValueError("incomplete-session option requires a boolean")

    def permits(self, provenance: MemoryProvenance) -> bool:
        if (provenance.scope, provenance.scope_id) not in self.visible_scopes:
            return False
        if provenance.policy_version != self.policy_version:
            return False
        if not provenance.complete:
            if not (
                self.allow_incomplete_session
                and provenance.scope == "session"
                and not self.excluded_problem_ids
                and not self.excluded_family_ids
                and self.allowed_source_record_ids is None
                and self.chronology_cutoff is None
            ):
                return False
        sources = set(provenance.source_record_ids + provenance.ancestry_source_ids)
        if self.allowed_source_record_ids is not None and not sources.issubset(
            self.allowed_source_record_ids
        ):
            return False
        if set(provenance.problem_ids + provenance.ancestry_problem_ids).intersection(
            self.excluded_problem_ids
        ):
            return False
        if set(provenance.family_ids + provenance.ancestry_family_ids).intersection(
            self.excluded_family_ids
        ):
            return False
        if self.chronology_cutoff is not None:
            if (
                provenance.campaign_id != self.chronology_campaign_id
                or not provenance.run_id
                or provenance.producer_order is None
            ):
                return False
            if (
                max(provenance.producer_order, provenance.acceptance_order or 0)
                > self.chronology_cutoff
            ):
                return False
        return True

    def to_record(self) -> dict[str, Any]:
        return {name: thaw(getattr(self, name)) for name in self.__dataclass_fields__}

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> EligibilityPolicy:
        return cls(**record)

    @property
    def policy_id(self) -> str:
        return content_digest(self.to_record())


@dataclass(frozen=True)
class MemoryEvent:
    event_id: str
    operation_id: str
    attempt_id: str
    kind: str
    payload: Mapping[str, Any]
    provenance: MemoryProvenance
    evidence: tuple[EvidenceReference, ...] = ()
    retry_of: str = ""
    schema_version: int = SCHEMA_VERSION

    def __post_init__(self) -> None:
        for name in ("event_id", "operation_id", "attempt_id", "kind"):
            text(getattr(self, name), name)
        text(self.retry_of, "retry_of", required=False)
        if (
            self.schema_version != SCHEMA_VERSION
            or type(self.schema_version) is not int
        ):
            raise ValueError("unsupported memory event schema")
        if not isinstance(self.provenance, MemoryProvenance):
            raise ValueError("memory event requires typed provenance")
        if not isinstance(self.payload, Mapping):
            raise ValueError("memory event payload must be a mapping")
        object.__setattr__(self, "payload", freeze(self.payload))
        if len(canonical_json(self.payload).encode("utf-8")) > 1024 * 1024:
            raise ValueError("memory event payload exceeds byte limit")
        object.__setattr__(self, "evidence", tuple(self.evidence))
        if any(not isinstance(ref, EvidenceReference) for ref in self.evidence):
            raise ValueError("memory event requires typed evidence references")
        if len(self.evidence) > 64:
            raise ValueError("too many evidence references")

    def to_record(self) -> dict[str, Any]:
        return {name: thaw(getattr(self, name)) for name in self.__dataclass_fields__}

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> MemoryEvent:
        values = dict(record)
        values["provenance"] = MemoryProvenance.from_record(values["provenance"])
        values["evidence"] = tuple(
            EvidenceReference.from_record(item) for item in values.get("evidence", ())
        )
        return cls(**values)

    @property
    def payload_digest(self) -> str:
        return content_digest(self.to_record())


@dataclass(frozen=True)
class StoreResult:
    status: str
    event_id: str
    diagnostic: str = ""
    dropped: bool = False

    @property
    def stored(self) -> bool:
        return self.status in {"stored", "duplicate"}


@dataclass(frozen=True)
class CatalogView:
    events: tuple[MemoryEvent, ...]
    pin: GenerationPin
    complete: bool
    omitted: int | None = 0
    diagnostics: tuple[str, ...] = ()
    invalidated: int = 0
