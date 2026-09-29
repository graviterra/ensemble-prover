"""Stable contracts for mathematical retrieval requests and evidence."""

from __future__ import annotations

import hashlib
import json
import math
from dataclasses import asdict, dataclass, field
from types import MappingProxyType
from typing import Any, Mapping, Sequence


RETRIEVAL_CONTRACT_SCHEMA_VERSION = 1
_SOURCE_HEALTH = frozenset(
    {
        "success_with_hits",
        "success_zero_hits",
        "disabled",
        "unavailable",
        "degraded",
        "stale",
        "corrupt",
        "timeout",
        "error",
    }
)
_AVAILABILITY = frozenset(
    {
        "already_imported",
        "importable",
        "requires_bundle_activation",
        "requires_helper_recheck",
        "unavailable",
        "unknown",
    }
)
_APPLICABILITY = frozenset(
    {
        "not_checked",
        "exact_type",
        "applies",
        "rewrites",
        "simplifies",
        "creates_residual_goals",
        "not_applicable",
        "probe_timeout",
        "probe_error",
    }
)


def _text(value: Any) -> str:
    return str(value or "").strip()


def _text_tuple(values: Sequence[Any] | None) -> tuple[str, ...]:
    return tuple(
        dict.fromkeys(
            text for value in list(values or ()) if (text := _text(value))
        )
    )


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def stable_retrieval_hash(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class RetrievalSourcePolicy:
    """Per-query source and trust policy.

    Inactive/importable results may be returned as discovery evidence, but
    consumers must not advertise them as directly usable declarations.
    """

    include_mathlib: bool = True
    include_project: bool = True
    include_published_theory: bool = True
    include_verified_helpers: bool = True
    include_inactive: bool = True
    theorem_kinds_only: bool = True
    allowed_source_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "allowed_source_ids",
            _text_tuple(self.allowed_source_ids),
        )

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RetrievalSourcePolicy":
        return cls(
            include_mathlib=bool(record.get("include_mathlib", True)),
            include_project=bool(record.get("include_project", True)),
            include_published_theory=bool(
                record.get("include_published_theory", True)
            ),
            include_verified_helpers=bool(
                record.get("include_verified_helpers", True)
            ),
            include_inactive=bool(record.get("include_inactive", True)),
            theorem_kinds_only=bool(record.get("theorem_kinds_only", True)),
            allowed_source_ids=_text_tuple(record.get("allowed_source_ids", ())),
        )


@dataclass(frozen=True)
class RetrievalQuery:
    schema_version: int
    request_id: str
    theorem_name: str
    target_statement: str
    normalized_goal_hash: str
    ordered_local_context: tuple[str, ...] = ()
    local_context_hash: str = ""
    result_head: str = ""
    constants: tuple[str, ...] = ()
    namespaces: tuple[str, ...] = ()
    binder_heads: tuple[str, ...] = ()
    typeclass_needs: tuple[str, ...] = ()
    shape_tags: tuple[str, ...] = ()
    natural_language: str = ""
    route_context: str = ""
    intended_uses: tuple[str, ...] = ()
    source_policy: RetrievalSourcePolicy = field(
        default_factory=RetrievalSourcePolicy
    )
    max_candidates: int = 10
    index_snapshot_id: str = ""

    def __post_init__(self) -> None:
        if int(self.schema_version) != RETRIEVAL_CONTRACT_SCHEMA_VERSION:
            raise ValueError(
                f"unsupported retrieval query schema: {self.schema_version}"
            )
        if not _text(self.target_statement) and not _text(self.natural_language):
            raise ValueError("retrieval query requires target_statement or natural_language")
        if int(self.max_candidates) <= 0:
            raise ValueError("retrieval query max_candidates must be positive")
        for attr in (
            "ordered_local_context",
            "constants",
            "namespaces",
            "binder_heads",
            "typeclass_needs",
            "shape_tags",
            "intended_uses",
        ):
            object.__setattr__(self, attr, _text_tuple(getattr(self, attr)))
        if not self.local_context_hash:
            object.__setattr__(
                self,
                "local_context_hash",
                stable_retrieval_hash(list(self.ordered_local_context)),
            )
        if not self.normalized_goal_hash:
            object.__setattr__(
                self,
                "normalized_goal_hash",
                stable_retrieval_hash(
                    {
                        "target": _text(self.target_statement),
                        "context": list(self.ordered_local_context),
                    }
                ),
            )
        expected_id = stable_retrieval_hash(self.identity_payload())
        if self.request_id and self.request_id != expected_id:
            raise ValueError("retrieval request_id does not match query payload")
        if not self.request_id:
            object.__setattr__(self, "request_id", expected_id)

    def identity_payload(self) -> dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "theorem_name": _text(self.theorem_name),
            "target_statement": _text(self.target_statement),
            "normalized_goal_hash": _text(self.normalized_goal_hash),
            "ordered_local_context": list(self.ordered_local_context),
            "local_context_hash": _text(self.local_context_hash),
            "result_head": _text(self.result_head),
            "constants": list(self.constants),
            "namespaces": list(self.namespaces),
            "binder_heads": list(self.binder_heads),
            "typeclass_needs": list(self.typeclass_needs),
            "shape_tags": list(self.shape_tags),
            "natural_language": _text(self.natural_language),
            "route_context": _text(self.route_context),
            "intended_uses": list(self.intended_uses),
            "source_policy": self.source_policy.to_record(),
            "max_candidates": int(self.max_candidates),
            "index_snapshot_id": _text(self.index_snapshot_id),
        }

    def to_record(self) -> dict[str, Any]:
        return {"request_id": self.request_id, **self.identity_payload()}

    @classmethod
    def create(
        cls,
        *,
        theorem_name: str = "",
        target_statement: str = "",
        ordered_local_context: Sequence[str] = (),
        result_head: str = "",
        constants: Sequence[str] = (),
        namespaces: Sequence[str] = (),
        binder_heads: Sequence[str] = (),
        typeclass_needs: Sequence[str] = (),
        shape_tags: Sequence[str] = (),
        natural_language: str = "",
        route_context: str = "",
        intended_uses: Sequence[str] = (),
        source_policy: RetrievalSourcePolicy | None = None,
        max_candidates: int = 10,
        index_snapshot_id: str = "",
    ) -> "RetrievalQuery":
        return cls(
            schema_version=RETRIEVAL_CONTRACT_SCHEMA_VERSION,
            request_id="",
            theorem_name=theorem_name,
            target_statement=target_statement,
            normalized_goal_hash="",
            ordered_local_context=tuple(ordered_local_context),
            local_context_hash="",
            result_head=result_head,
            constants=tuple(constants),
            namespaces=tuple(namespaces),
            binder_heads=tuple(binder_heads),
            typeclass_needs=tuple(typeclass_needs),
            shape_tags=tuple(shape_tags),
            natural_language=natural_language,
            route_context=route_context,
            intended_uses=tuple(intended_uses),
            source_policy=source_policy or RetrievalSourcePolicy(),
            max_candidates=max_candidates,
            index_snapshot_id=index_snapshot_id,
        )

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RetrievalQuery":
        return cls(
            schema_version=int(record.get("schema_version", 0) or 0),
            request_id=_text(record.get("request_id")),
            theorem_name=_text(record.get("theorem_name")),
            target_statement=_text(record.get("target_statement")),
            normalized_goal_hash=_text(record.get("normalized_goal_hash")),
            ordered_local_context=_text_tuple(record.get("ordered_local_context", ())),
            local_context_hash=_text(record.get("local_context_hash")),
            result_head=_text(record.get("result_head")),
            constants=_text_tuple(record.get("constants", ())),
            namespaces=_text_tuple(record.get("namespaces", ())),
            binder_heads=_text_tuple(record.get("binder_heads", ())),
            typeclass_needs=_text_tuple(record.get("typeclass_needs", ())),
            shape_tags=_text_tuple(record.get("shape_tags", ())),
            natural_language=_text(record.get("natural_language")),
            route_context=_text(record.get("route_context")),
            intended_uses=_text_tuple(record.get("intended_uses", ())),
            source_policy=RetrievalSourcePolicy.from_record(
                dict(record.get("source_policy") or {})
            ),
            max_candidates=int(record.get("max_candidates", 10) or 10),
            index_snapshot_id=_text(record.get("index_snapshot_id")),
        )


@dataclass(frozen=True)
class CandidateOrigin:
    source_kind: str
    source_id: str
    module_name: str = ""
    import_text: str = ""
    source_path: str = ""
    source_hash: str = ""
    environment_hash: str = ""
    trust_kind: str = "unverified_index_hint"
    availability: str = "unknown"
    required_bundle_ids: tuple[str, ...] = ()
    helper_source: str = ""

    def __post_init__(self) -> None:
        if not _text(self.source_kind) or not _text(self.source_id):
            raise ValueError("candidate origin requires source_kind and source_id")
        if self.availability not in _AVAILABILITY:
            raise ValueError(f"unsupported candidate availability: {self.availability}")
        object.__setattr__(
            self,
            "required_bundle_ids",
            _text_tuple(self.required_bundle_ids),
        )

    def to_record(self, *, include_helper_source: bool = True) -> dict[str, Any]:
        record = asdict(self)
        if not include_helper_source:
            record["helper_source"] = ""
        return record

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "CandidateOrigin":
        return cls(
            source_kind=_text(record.get("source_kind")),
            source_id=_text(record.get("source_id")),
            module_name=_text(record.get("module_name")),
            import_text=_text(record.get("import_text")),
            source_path=_text(record.get("source_path")),
            source_hash=_text(record.get("source_hash")),
            environment_hash=_text(record.get("environment_hash")),
            trust_kind=_text(record.get("trust_kind")) or "unverified_index_hint",
            availability=_text(record.get("availability")) or "unknown",
            required_bundle_ids=_text_tuple(record.get("required_bundle_ids", ())),
            helper_source=_text(record.get("helper_source")),
        )


@dataclass(frozen=True)
class ApplicabilityReceipt:
    query_goal_hash: str
    candidate_id: str
    probe_kind: str
    lean_environment_hash: str
    context_hash: str
    accepted: bool
    residual_goals: tuple[str, ...] = ()
    diagnostic_kind: str = ""
    elapsed_s: float = 0.0

    def __post_init__(self) -> None:
        if not math.isfinite(float(self.elapsed_s)) or float(self.elapsed_s) < 0.0:
            raise ValueError("applicability elapsed_s must be finite and nonnegative")
        object.__setattr__(self, "residual_goals", _text_tuple(self.residual_goals))

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "ApplicabilityReceipt":
        return cls(
            query_goal_hash=_text(record.get("query_goal_hash")),
            candidate_id=_text(record.get("candidate_id")),
            probe_kind=_text(record.get("probe_kind")),
            lean_environment_hash=_text(record.get("lean_environment_hash")),
            context_hash=_text(record.get("context_hash")),
            accepted=bool(record.get("accepted", False)),
            residual_goals=_text_tuple(record.get("residual_goals", ())),
            diagnostic_kind=_text(record.get("diagnostic_kind")),
            elapsed_s=float(record.get("elapsed_s", 0.0) or 0.0),
        )


@dataclass(frozen=True)
class RetrievalCandidate:
    candidate_id: str
    declaration_name: str
    type_text: str
    declaration_kind: str
    origins: tuple[CandidateOrigin, ...]
    channel_ranks: Mapping[str, int] = field(default_factory=dict)
    channel_scores: Mapping[str, float] = field(default_factory=dict)
    fusion_score: float = 0.0
    rerank_score: float | None = None
    reasons: tuple[str, ...] = ()
    availability: str = "unknown"
    applicability: str = "not_checked"
    applicability_receipts: tuple[ApplicabilityReceipt, ...] = ()

    def __post_init__(self) -> None:
        declaration_name = _text(self.declaration_name)
        type_text = _text(self.type_text)
        declaration_kind = _text(self.declaration_kind)
        if not declaration_name or not type_text:
            raise ValueError("retrieval candidate requires declaration name and type")
        if not declaration_kind:
            raise ValueError("retrieval candidate requires declaration kind")
        origins = tuple(self.origins)
        if not origins:
            raise ValueError("retrieval candidate requires at least one origin")
        if not all(isinstance(origin, CandidateOrigin) for origin in origins):
            raise TypeError("retrieval candidate origins must be CandidateOrigin records")
        applicability_receipts = tuple(self.applicability_receipts)
        if not all(
            isinstance(receipt, ApplicabilityReceipt)
            for receipt in applicability_receipts
        ):
            raise TypeError(
                "retrieval candidate applicability receipts must be "
                "ApplicabilityReceipt records"
            )
        if self.availability not in _AVAILABILITY:
            raise ValueError(f"unsupported candidate availability: {self.availability}")
        if self.applicability not in _APPLICABILITY:
            raise ValueError(f"unsupported candidate applicability: {self.applicability}")
        ranks = {str(key): int(value) for key, value in self.channel_ranks.items()}
        scores = {
            str(key): float(value)
            for key, value in self.channel_scores.items()
            if math.isfinite(float(value))
        }
        object.__setattr__(self, "channel_ranks", MappingProxyType(ranks))
        object.__setattr__(self, "channel_scores", MappingProxyType(scores))
        object.__setattr__(self, "candidate_id", _text(self.candidate_id))
        object.__setattr__(self, "declaration_name", declaration_name)
        object.__setattr__(self, "type_text", type_text)
        object.__setattr__(self, "declaration_kind", declaration_kind)
        object.__setattr__(self, "origins", origins)
        object.__setattr__(self, "reasons", _text_tuple(self.reasons))
        object.__setattr__(
            self,
            "applicability_receipts",
            applicability_receipts,
        )
        expected_id = stable_retrieval_hash(self.identity_payload())
        if self.candidate_id and self.candidate_id != expected_id:
            raise ValueError("candidate_id does not match declaration identity")
        if not self.candidate_id:
            object.__setattr__(self, "candidate_id", expected_id)

    def identity_payload(self) -> dict[str, Any]:
        origin_keys = sorted(
            {
                (
                    origin.environment_hash,
                    origin.module_name,
                )
                for origin in self.origins
            }
        )
        return {
            "declaration_name": self.declaration_name,
            "type_hash": stable_retrieval_hash(self.type_text),
            "declaration_kind": self.declaration_kind,
            "origin_keys": [list(item) for item in origin_keys],
        }

    def to_record(self, *, include_helper_source: bool = False) -> dict[str, Any]:
        return {
            "candidate_id": self.candidate_id,
            "declaration_name": self.declaration_name,
            "type_text": self.type_text,
            "declaration_kind": self.declaration_kind,
            "origins": [
                origin.to_record(include_helper_source=include_helper_source)
                for origin in self.origins
            ],
            "channel_ranks": dict(self.channel_ranks),
            "channel_scores": dict(self.channel_scores),
            "fusion_score": float(self.fusion_score),
            "rerank_score": self.rerank_score,
            "reasons": list(self.reasons),
            "availability": self.availability,
            "applicability": self.applicability,
            "applicability_receipts": [
                receipt.to_record() for receipt in self.applicability_receipts
            ],
        }

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RetrievalCandidate":
        return cls(
            candidate_id=_text(record.get("candidate_id")),
            declaration_name=_text(record.get("declaration_name")),
            type_text=_text(record.get("type_text")),
            declaration_kind=_text(record.get("declaration_kind")),
            origins=tuple(
                CandidateOrigin.from_record(dict(item or {}))
                for item in record.get("origins", ()) or ()
            ),
            channel_ranks={
                str(key): int(value)
                for key, value in dict(record.get("channel_ranks") or {}).items()
            },
            channel_scores={
                str(key): float(value)
                for key, value in dict(record.get("channel_scores") or {}).items()
            },
            fusion_score=float(record.get("fusion_score", 0.0) or 0.0),
            rerank_score=(
                None
                if record.get("rerank_score") is None
                else float(record.get("rerank_score"))
            ),
            reasons=_text_tuple(record.get("reasons", ())),
            availability=_text(record.get("availability")) or "unknown",
            applicability=_text(record.get("applicability")) or "not_checked",
            applicability_receipts=tuple(
                ApplicabilityReceipt.from_record(dict(item or {}))
                for item in record.get("applicability_receipts", ()) or ()
            ),
        )


@dataclass(frozen=True)
class RetrievalSourceReport:
    source_id: str
    source_kind: str
    health: str
    hit_count: int = 0
    elapsed_s: float = 0.0
    error: str = ""
    index_snapshot_id: str = ""
    truncated: bool = False

    def __post_init__(self) -> None:
        if self.health not in _SOURCE_HEALTH:
            raise ValueError(f"unsupported retrieval source health: {self.health}")
        if int(self.hit_count) < 0:
            raise ValueError("retrieval hit_count must be nonnegative")
        if not math.isfinite(float(self.elapsed_s)) or float(self.elapsed_s) < 0.0:
            raise ValueError("retrieval elapsed_s must be finite and nonnegative")

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RetrievalSourceReport":
        return cls(
            source_id=_text(record.get("source_id")),
            source_kind=_text(record.get("source_kind")),
            health=_text(record.get("health")),
            hit_count=int(record.get("hit_count", 0) or 0),
            elapsed_s=float(record.get("elapsed_s", 0.0) or 0.0),
            error=_text(record.get("error")),
            index_snapshot_id=_text(record.get("index_snapshot_id")),
            truncated=bool(record.get("truncated", False)),
        )


@dataclass(frozen=True)
class RetrievalResult:
    request_id: str
    index_snapshot_id: str
    candidates: tuple[RetrievalCandidate, ...]
    source_reports: tuple[RetrievalSourceReport, ...]
    elapsed_s: float
    truncated: bool = False
    deadline_exhausted: bool = False

    def __post_init__(self) -> None:
        if not math.isfinite(float(self.elapsed_s)) or float(self.elapsed_s) < 0.0:
            raise ValueError("retrieval result elapsed_s must be finite and nonnegative")

    @property
    def clean_zero_hit(self) -> bool:
        return bool(self.source_reports) and not self.candidates and all(
            report.health == "success_zero_hits" for report in self.source_reports
        )

    def to_record(self, *, include_helper_source: bool = False) -> dict[str, Any]:
        return {
            "request_id": self.request_id,
            "index_snapshot_id": self.index_snapshot_id,
            "candidates": [
                candidate.to_record(include_helper_source=include_helper_source)
                for candidate in self.candidates
            ],
            "source_reports": [report.to_record() for report in self.source_reports],
            "elapsed_s": float(self.elapsed_s),
            "truncated": bool(self.truncated),
            "deadline_exhausted": bool(self.deadline_exhausted),
            "clean_zero_hit": bool(self.clean_zero_hit),
        }

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RetrievalResult":
        return cls(
            request_id=_text(record.get("request_id")),
            index_snapshot_id=_text(record.get("index_snapshot_id")),
            candidates=tuple(
                RetrievalCandidate.from_record(dict(item or {}))
                for item in record.get("candidates", ()) or ()
            ),
            source_reports=tuple(
                RetrievalSourceReport.from_record(dict(item or {}))
                for item in record.get("source_reports", ()) or ()
            ),
            elapsed_s=float(record.get("elapsed_s", 0.0) or 0.0),
            truncated=bool(record.get("truncated", False)),
            deadline_exhausted=bool(record.get("deadline_exhausted", False)),
        )
