"""Durable identities for end-to-end Mini proof lineage.

The graph remains the proof authority.  This module supplies immutable lineage
coordinates plus a descriptive proof-idea lifecycle aggregate shared by the
planner, graph, scheduler, child, repair, and finalization layers.  The latter
conserves intent and observations without granting planner prose proof status.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass, replace
from typing import Any, Iterable, Mapping, Sequence


LINEAGE_SCHEMA_VERSION = 1
PROOF_IDEA_SCHEMA_VERSION = 1

PROOF_IDEA_STATUSES = frozenset(
    {
        "proposed",
        "active",
        "blocked",
        "abandoned",
        "retired",
        "solved",
        "invalidated",
    }
)
PROOF_IDEA_STATUS_AUTHORITIES = frozenset(
    {"advisory", "controller", "accepted_fact", "lean"}
)
PROOF_IDEA_OBSERVATION_KINDS = frozenset(
    {
        "alternative",
        "theorem_discovery",
        "lean_residual",
        "repair",
        "child_attempt",
        "formal_state",
        "abandonment",
        "evidence_delta",
        "note",
    }
)
PROOF_IDEA_CONTEXT_RESOLUTION_STATUSES = frozenset(
    {"resolved", "ambiguous", "unbound", "stale"}
)
PROOF_IDEA_CONTEXT_POLICIES = frozenset(
    {"exact_selected", "root_ranked", "planning_all_active", "protocol_only"}
)
PROOF_IDEA_CONTEXT_AUDIENCES = frozenset(
    {"conversation", "formal_policy", "planner", "child", "repair", "theory"}
)
PROOF_IDEA_CONTEXT_COMPLETENESS = frozenset(
    {"exact", "preview", "withheld"}
)

_STATUS_AUTHORITY_RANK = {
    "advisory": 0,
    "controller": 1,
    "accepted_fact": 2,
    "lean": 3,
}
_STATUS_RANK = {
    "proposed": 0,
    "active": 1,
    "blocked": 2,
    "abandoned": 3,
    "retired": 4,
    "solved": 5,
    "invalidated": 6,
}
_STATUS_BY_AUTHORITY = {
    "advisory": {"proposed", "active", "blocked", "abandoned"},
    "controller": {"proposed", "active", "blocked", "abandoned", "retired"},
    # Accepted-fact authority also owns compensation when the final live
    # attestation is removed.  ``active`` does not assert proof truth; it
    # retracts the fact-derived retirement while preserving the event history.
    "accepted_fact": {"active", "retired", "solved"},
    "lean": {"solved", "invalidated"},
}


def _clean(value: Any) -> str:
    return str(value or "").strip()


def _identity_text(value: Any, *, field_name: str) -> str:
    """Validate an externally supplied lineage coordinate.

    Identity coordinates cross persistence and telemetry trust boundaries.
    Stringifying arbitrary objects here would turn malformed dictionaries or
    lists into apparently valid durable identities that downstream reducers
    cannot distinguish from producer-authored strings.
    """

    if value is None:
        return ""
    if not isinstance(value, str):
        raise TypeError(
            f"proof lineage {field_name} must be a string, got "
            f"{type(value).__name__}"
        )
    return value.strip()


def _proof_idea_text(
    value: Any,
    *,
    field_name: str,
    required: bool = False,
) -> str:
    if value is None:
        text = ""
    elif not isinstance(value, str):
        raise TypeError(
            f"proof idea {field_name} must be a string, got "
            f"{type(value).__name__}"
        )
    else:
        text = value.strip()
    if required and not text:
        raise ValueError(f"proof idea {field_name} must not be empty")
    return text


def _proof_idea_string_tuple(
    value: Any,
    *,
    field_name: str,
) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, (list, tuple)):
        raise TypeError(
            f"proof idea {field_name} must be a list or tuple of strings, got "
            f"{type(value).__name__}"
        )
    cleaned = []
    for item in value:
        text = _proof_idea_text(
            item,
            field_name=f"{field_name} item",
            required=True,
        )
        cleaned.append(text)
    return tuple(sorted(set(cleaned)))


def _proof_idea_turn_index(value: Any, *, field_name: str) -> int:
    if type(value) is not int or value < 0:
        raise TypeError(f"proof idea {field_name} must be a non-negative integer")
    return value


def _strict_record(
    raw: Mapping[str, Any] | None,
    *,
    record_name: str,
    allowed_keys: Iterable[str],
    required_keys: Iterable[str] = (),
) -> dict[str, Any]:
    if not isinstance(raw, Mapping):
        raise TypeError(f"{record_name} must be a mapping")
    data = dict(raw)
    non_string_keys = [key for key in data if not isinstance(key, str)]
    if non_string_keys:
        raise TypeError(f"{record_name} field names must be strings")
    allowed = set(allowed_keys)
    unknown = sorted(set(data) - allowed)
    if unknown:
        raise ValueError(f"unknown {record_name} fields: {', '.join(unknown)}")
    missing = sorted(set(required_keys) - set(data))
    if missing:
        raise ValueError(f"missing {record_name} fields: {', '.join(missing)}")
    return data


def _typed_record_tuple(
    value: Any,
    *,
    field_name: str,
    record_type: Any,
) -> tuple[Any, ...]:
    if not isinstance(value, (list, tuple)):
        raise TypeError(f"proof idea {field_name} must be a list or tuple")
    return tuple(
        item if isinstance(item, record_type) else record_type.from_record(item)
        for item in value
    )


def _merge_optional_text(left: str, right: str, *, field_name: str) -> str:
    if left and right and left != right:
        raise ValueError(f"conflicting proof idea {field_name}")
    return left or right


def stable_identity(namespace: str, *parts: Any) -> str:
    """Return a stable, opaque identity with an auditable namespace."""

    payload = json.dumps(
        [_clean(namespace), *[_clean(part) for part in parts]],
        ensure_ascii=False,
        separators=(",", ":"),
    )
    digest = hashlib.sha256(payload.encode("utf-8", errors="replace")).hexdigest()
    return f"{_clean(namespace) or 'identity'}:{digest[:24]}"


def structural_statement_identity(
    statement: str,
    *,
    contract_identity: str = "",
    statement_key: str = "",
) -> str:
    """Prefer Lean structural identity and fall back to a canonical surface key."""

    structural = _clean(contract_identity)
    if structural.startswith("lean-expr-"):
        return structural
    surface = _clean(statement_key) or " ".join(_clean(statement).split())
    return stable_identity("surface-statement", surface) if surface else ""


def proof_candidate_identity(*, target_id: str, proof_hash: str) -> str:
    """Canonical identity for one proof text against one formal target."""

    clean_target = _clean(target_id)
    clean_hash = _clean(proof_hash)
    return (
        stable_identity("proof-candidate", clean_target, clean_hash)
        if clean_target and clean_hash
        else ""
    )


def lean_residual_identity(
    *,
    proof_candidate_id: str,
    error_type: str,
    failure_signature: str,
    proof_attempt_id: str = "",
    target_id: str = "",
) -> str:
    """Canonical diagnostic identity attached to its originating candidate."""

    clean_candidate = _clean(proof_candidate_id)
    residual_origin = clean_candidate or (
        stable_identity("proof-attempt", target_id, proof_attempt_id)
        if _clean(target_id) and _clean(proof_attempt_id)
        else ""
    )
    clean_error = _clean(error_type)
    clean_signature = _clean(failure_signature)
    return (
        stable_identity(
            "lean-residual",
            residual_origin,
            clean_error,
            clean_signature,
        )
        if residual_origin and (clean_error or clean_signature)
        else ""
    )


def strategy_lineage_identity(
    *,
    theorem_name: str,
    root_statement_identity: str,
    strategy: str,
    pass_index: Any = "",
    parent_lineage_id: str = "",
) -> str:
    return stable_identity(
        "strategy",
        theorem_name,
        root_statement_identity,
        strategy,
        pass_index,
        parent_lineage_id,
    )


def proof_idea_identity(
    *,
    theorem_name: str,
    root_statement_identity: str,
    strategy: str,
    route_shape_identity: str = "",
) -> str:
    """Identity for a mathematical route, independent of pass and branch.

    Per-pass execution belongs in ``strategy_lineage_id``.  This identity is
    based on the root contract, normalized mathematical strategy, and canonical
    claim/dependency topology. Retries and branch copies converge while generic
    strategy prose cannot conflate genuinely different mathematical routes.
    """

    theorem = _proof_idea_text(
        theorem_name,
        field_name="theorem_name",
        required=True,
    )
    root = _proof_idea_text(
        root_statement_identity,
        field_name="root_statement_identity",
        required=True,
    )
    normalized_strategy = " ".join(
        _proof_idea_text(strategy, field_name="strategy", required=True).split()
    )
    route_shape = _proof_idea_text(
        route_shape_identity,
        field_name="route_shape_identity",
    )
    return stable_identity(
        "proof-idea",
        theorem,
        root,
        normalized_strategy,
        route_shape,
    )


@dataclass(frozen=True)
class ProofIdeaClaimIntent:
    """Planner-authored intent for one claim, without proof authority."""

    claim_id: str
    statement_identity: str
    statement: str = ""
    role: str = ""
    role_alternatives: tuple[str, ...] = ()
    rationale: str = ""
    rationale_alternatives: tuple[str, ...] = ()
    sanity_check: str = ""
    sanity_check_alternatives: tuple[str, ...] = ()
    counting_classification: str = ""
    counting_classification_alternatives: tuple[str, ...] = ()
    # One semantic claim can be materialized by several independently bound
    # plan obligations. ``obligation_id`` remains the deterministic legacy
    # primary; ``obligation_ids`` conserves every occurrence identity.
    obligation_id: str = ""
    obligation_ids: tuple[str, ...] = ()
    invariant_refs: tuple[str, ...] = ()
    consumer_ids: tuple[str, ...] = ()
    dependency_claim_ids: tuple[str, ...] = ()
    dependency_labels: tuple[str, ...] = ()
    alternative_statement_identities: tuple[str, ...] = ()
    alternative_statements: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        for field_name in (
            "claim_id",
            "statement_identity",
            "statement",
            "role",
            "rationale",
            "sanity_check",
            "counting_classification",
            "obligation_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _proof_idea_text(
                    getattr(self, field_name),
                    field_name=f"claim_intent.{field_name}",
                    required=field_name in {"claim_id", "statement_identity"},
                ),
            )
        for field_name in (
            "obligation_ids",
            "invariant_refs",
            "role_alternatives",
            "rationale_alternatives",
            "sanity_check_alternatives",
            "counting_classification_alternatives",
            "consumer_ids",
            "dependency_claim_ids",
            "dependency_labels",
            "alternative_statement_identities",
            "alternative_statements",
        ):
            object.__setattr__(
                self,
                field_name,
                _proof_idea_string_tuple(
                    getattr(self, field_name),
                    field_name=f"claim_intent.{field_name}",
                ),
            )
        obligation_ids = tuple(
            sorted(
                {
                    value
                    for value in (self.obligation_id, *self.obligation_ids)
                    if value
                }
            )
        )
        object.__setattr__(self, "obligation_ids", obligation_ids)
        object.__setattr__(
            self,
            "obligation_id",
            obligation_ids[0] if obligation_ids else "",
        )

    def to_record(self) -> dict[str, Any]:
        return {
            "claim_id": self.claim_id,
            "statement_identity": self.statement_identity,
            "statement": self.statement,
            "role": self.role,
            "role_alternatives": list(self.role_alternatives),
            "rationale": self.rationale,
            "rationale_alternatives": list(self.rationale_alternatives),
            "sanity_check": self.sanity_check,
            "sanity_check_alternatives": list(
                self.sanity_check_alternatives
            ),
            "counting_classification": self.counting_classification,
            "counting_classification_alternatives": list(
                self.counting_classification_alternatives
            ),
            "obligation_id": self.obligation_id,
            "obligation_ids": list(self.obligation_ids),
            "invariant_refs": list(self.invariant_refs),
            "consumer_ids": list(self.consumer_ids),
            "dependency_claim_ids": list(self.dependency_claim_ids),
            "dependency_labels": list(self.dependency_labels),
            "alternative_statement_identities": list(
                self.alternative_statement_identities
            ),
            "alternative_statements": list(self.alternative_statements),
        }

    @classmethod
    def from_record(cls, raw: Mapping[str, Any] | None) -> "ProofIdeaClaimIntent":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea claim intent",
            allowed_keys=keys,
            required_keys={"claim_id", "statement_identity"},
        )
        tuple_fields = {
            "obligation_ids",
            "invariant_refs",
            "role_alternatives",
            "rationale_alternatives",
            "sanity_check_alternatives",
            "counting_classification_alternatives",
            "consumer_ids",
            "dependency_claim_ids",
            "dependency_labels",
            "alternative_statement_identities",
            "alternative_statements",
        }
        return cls(
            **{
                key: data.get(key, ()) if key in tuple_fields else data.get(key, "")
                for key in keys
            }
        )

    def merged(self, other: "ProofIdeaClaimIntent") -> "ProofIdeaClaimIntent":
        if self.claim_id != other.claim_id:
            raise ValueError("cannot merge different proof idea claim intents")
        if self.statement_identity != other.statement_identity:
            raise ValueError("conflicting proof idea claim statement_identity")

        def merged_values(*values: str) -> tuple[str, ...]:
            return tuple(sorted({value for value in values if value}))

        statements = merged_values(
            self.statement,
            *self.alternative_statements,
            other.statement,
            *other.alternative_statements,
        )
        roles = merged_values(
            self.role,
            *self.role_alternatives,
            other.role,
            *other.role_alternatives,
        )
        rationales = merged_values(
            self.rationale,
            *self.rationale_alternatives,
            other.rationale,
            *other.rationale_alternatives,
        )
        sanity_checks = merged_values(
            self.sanity_check,
            *self.sanity_check_alternatives,
            other.sanity_check,
            *other.sanity_check_alternatives,
        )
        counting_classifications = merged_values(
            self.counting_classification,
            *self.counting_classification_alternatives,
            other.counting_classification,
            *other.counting_classification_alternatives,
        )
        # Primary fields are lifecycle state, not unordered set members.  The
        # previous lexicographic selection made an idempotent upsert of the
        # same intent rotate an older alternative into the active rationale or
        # statement.  Prefer the incoming fragment's explicit primary (it is
        # the newer lifecycle projection), then retain every other value as a
        # deterministically ordered alternative.
        primary_statement = other.statement or self.statement
        primary_role = other.role or self.role
        primary_rationale = other.rationale or self.rationale
        primary_sanity_check = other.sanity_check or self.sanity_check
        primary_counting_classification = (
            other.counting_classification or self.counting_classification
        )
        return ProofIdeaClaimIntent(
            claim_id=self.claim_id,
            statement_identity=self.statement_identity,
            statement=primary_statement,
            role=primary_role,
            role_alternatives=tuple(
                item for item in roles if item != primary_role
            ),
            rationale=primary_rationale,
            rationale_alternatives=tuple(
                item for item in rationales if item != primary_rationale
            ),
            sanity_check=primary_sanity_check,
            sanity_check_alternatives=tuple(
                item for item in sanity_checks if item != primary_sanity_check
            ),
            counting_classification=primary_counting_classification,
            counting_classification_alternatives=tuple(
                item
                for item in counting_classifications
                if item != primary_counting_classification
            ),
            obligation_id="",
            obligation_ids=self.obligation_ids + other.obligation_ids,
            invariant_refs=self.invariant_refs + other.invariant_refs,
            consumer_ids=self.consumer_ids + other.consumer_ids,
            dependency_claim_ids=(
                self.dependency_claim_ids + other.dependency_claim_ids
            ),
            dependency_labels=(
                self.dependency_labels + other.dependency_labels
            ),
            alternative_statement_identities=(
                self.alternative_statement_identities
                + other.alternative_statement_identities
            ),
            alternative_statements=tuple(
                item for item in statements if item != primary_statement
            ),
        )


@dataclass(frozen=True)
class ProofIdeaObservation:
    """One durable, route-linked discovery or exact failure observation."""

    observation_id: str
    kind: str
    summary: str
    claim_id: str = ""
    route_id: str = ""
    attempt_id: str = ""
    proof_candidate_id: str = ""
    lean_residual_id: str = ""
    exact_lean_output: str = ""
    lean_output_preview: str = ""
    attempted_lean_code: str = ""
    theorem_names: tuple[str, ...] = ()
    evidence_hash: str = ""
    result_sha256: str = ""
    result_length: int = 0
    output_truncated: bool = False
    source_pass_index: int = 0
    source_trigger: str = ""
    source_model_id: str = ""
    source_helpers_seen: int = 0
    source_reasoning_tokens: int = 0
    source_visible_output: str = ""
    branch_id: str = ""
    turn_index: int = 0

    def __post_init__(self) -> None:
        for field_name in (
            "observation_id",
            "kind",
            "summary",
            "claim_id",
            "route_id",
            "attempt_id",
            "proof_candidate_id",
            "lean_residual_id",
            "exact_lean_output",
            "lean_output_preview",
            "attempted_lean_code",
            "evidence_hash",
            "result_sha256",
            "source_trigger",
            "source_model_id",
            "source_visible_output",
            "branch_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _proof_idea_text(
                    getattr(self, field_name),
                    field_name=f"observation.{field_name}",
                    required=field_name in {"observation_id", "kind", "summary"},
                ),
            )
        if self.kind not in PROOF_IDEA_OBSERVATION_KINDS:
            raise ValueError(f"unsupported proof idea observation kind={self.kind!r}")
        object.__setattr__(
            self,
            "theorem_names",
            _proof_idea_string_tuple(
                self.theorem_names,
                field_name="observation.theorem_names",
            ),
        )
        object.__setattr__(
            self,
            "result_length",
            _proof_idea_turn_index(
                self.result_length,
                field_name="observation.result_length",
            ),
        )
        for field_name in (
            "source_pass_index",
            "source_helpers_seen",
            "source_reasoning_tokens",
        ):
            object.__setattr__(
                self,
                field_name,
                _proof_idea_turn_index(
                    getattr(self, field_name),
                    field_name=f"observation.{field_name}",
                ),
            )
        if type(self.output_truncated) is not bool:
            raise TypeError("proof idea observation.output_truncated must be a boolean")
        if self.output_truncated and self.exact_lean_output:
            raise ValueError("proof idea truncated output cannot be exact")
        if self.result_sha256 and not (
            len(self.result_sha256) == 64
            and all(ch in "0123456789abcdefABCDEF" for ch in self.result_sha256)
        ):
            raise ValueError("proof idea observation.result_sha256 must be hex sha256")
        object.__setattr__(
            self,
            "turn_index",
            _proof_idea_turn_index(
                self.turn_index,
                field_name="observation.turn_index",
            ),
        )

    def to_record(self) -> dict[str, Any]:
        record = asdict(self)
        record["theorem_names"] = list(self.theorem_names)
        return record

    @classmethod
    def create(
        cls,
        *,
        proof_idea_id: str,
        occurrence_key: str = "",
        **content: Any,
    ) -> "ProofIdeaObservation":
        """Mint a replay-safe ID from the complete normalized observation."""

        idea_id = _proof_idea_text(
            proof_idea_id,
            field_name="observation.proof_idea_id",
            required=True,
        )
        occurrence = _proof_idea_text(
            occurrence_key,
            field_name="observation.occurrence_key",
        )
        draft = cls(observation_id="pending", **content)
        payload = draft.to_record()
        payload.pop("observation_id", None)
        observation_id = stable_identity(
            "proof-idea-observation",
            idea_id,
            occurrence,
            json.dumps(
                payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ),
        )
        return replace(draft, observation_id=observation_id)

    @classmethod
    def from_record(cls, raw: Mapping[str, Any] | None) -> "ProofIdeaObservation":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea observation",
            allowed_keys=keys,
            required_keys={"observation_id", "kind", "summary"},
        )
        return cls(
            **{
                key: data.get(
                    key,
                    ()
                    if key == "theorem_names"
                    else 0
                    if key
                    in {
                        "turn_index",
                        "result_length",
                        "source_pass_index",
                        "source_helpers_seen",
                        "source_reasoning_tokens",
                    }
                    else False
                    if key == "output_truncated"
                    else "",
                )
                for key in keys
            }
        )


@dataclass(frozen=True)
class ProofIdeaStatusTransition:
    """Auditable lifecycle transition with explicit proof authority."""

    transition_id: str
    status: str
    authority: str
    reason: str
    turn_index: int
    claim_id: str = ""
    route_id: str = ""
    branch_id: str = ""
    evidence_id: str = ""

    def __post_init__(self) -> None:
        for field_name in (
            "transition_id",
            "status",
            "authority",
            "reason",
            "claim_id",
            "route_id",
            "branch_id",
            "evidence_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _proof_idea_text(
                    getattr(self, field_name),
                    field_name=f"status_transition.{field_name}",
                    required=field_name
                    in {"transition_id", "status", "authority", "reason"},
                ),
            )
        if self.status not in PROOF_IDEA_STATUSES:
            raise ValueError(f"unsupported proof idea status={self.status!r}")
        if self.authority not in PROOF_IDEA_STATUS_AUTHORITIES:
            raise ValueError(
                f"unsupported proof idea status authority={self.authority!r}"
            )
        if self.status not in _STATUS_BY_AUTHORITY[self.authority]:
            raise ValueError(
                "proof idea status is incompatible with its authority: "
                f"{self.status!r} from {self.authority!r}"
            )
        object.__setattr__(
            self,
            "turn_index",
            _proof_idea_turn_index(
                self.turn_index,
                field_name="status_transition.turn_index",
            ),
        )

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @property
    def effective_authority_rank(self) -> int:
        """Rank closure authority without making compensation authoritative.

        An accepted-fact ``active`` event retracts an earlier fact-derived
        retirement; it does not certify that the controller's route remains
        active.  Give that compensation controller rank so a newer route
        transition can immediately block, abandon, or retire the strategy.
        """

        if self.authority == "accepted_fact" and self.status == "active":
            return _STATUS_AUTHORITY_RANK["controller"]
        return _STATUS_AUTHORITY_RANK[self.authority]

    @classmethod
    def create(
        cls,
        *,
        proof_idea_id: str,
        occurrence_key: str = "",
        **content: Any,
    ) -> "ProofIdeaStatusTransition":
        """Mint a transition ID from every normalized status field."""

        idea_id = _proof_idea_text(
            proof_idea_id,
            field_name="status_transition.proof_idea_id",
            required=True,
        )
        occurrence = _proof_idea_text(
            occurrence_key,
            field_name="status_transition.occurrence_key",
        )
        draft = cls(transition_id="pending", **content)
        payload = draft.to_record()
        payload.pop("transition_id", None)
        transition_id = stable_identity(
            "proof-idea-status",
            idea_id,
            occurrence,
            json.dumps(
                payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ),
        )
        return replace(draft, transition_id=transition_id)

    @classmethod
    def from_record(
        cls,
        raw: Mapping[str, Any] | None,
    ) -> "ProofIdeaStatusTransition":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea status transition",
            allowed_keys=keys,
            required_keys={
                "transition_id",
                "status",
                "authority",
                "reason",
                "turn_index",
            },
        )
        return cls(**{key: data.get(key, "") for key in keys})


@dataclass(frozen=True)
class ProofIdeaClaimResolution:
    """Certified resolution of one claim intent or an equivalent graph alias."""

    resolution_id: str
    claim_id: str
    status: str
    authority: str
    reason: str
    evidence_id: str
    turn_index: int
    node_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        for field_name in (
            "resolution_id",
            "claim_id",
            "status",
            "authority",
            "reason",
            "evidence_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _proof_idea_text(
                    getattr(self, field_name),
                    field_name=f"claim_resolution.{field_name}",
                    required=True,
                ),
            )
        if self.status not in {"retired", "solved", "invalidated", "retracted"}:
            raise ValueError(
                f"unsupported proof idea claim resolution status={self.status!r}"
            )
        if self.authority not in {"accepted_fact", "lean"}:
            raise ValueError(
                "proof idea claim resolution requires accepted_fact or lean authority"
            )
        if self.authority == "accepted_fact" and self.status not in {
            "retired",
            "solved",
            "retracted",
        }:
            raise ValueError("accepted facts cannot invalidate a proof idea claim")
        object.__setattr__(
            self,
            "turn_index",
            _proof_idea_turn_index(
                self.turn_index,
                field_name="claim_resolution.turn_index",
            ),
        )
        object.__setattr__(
            self,
            "node_ids",
            _proof_idea_string_tuple(
                self.node_ids,
                field_name="claim_resolution.node_ids",
            ),
        )

    def to_record(self) -> dict[str, Any]:
        record = asdict(self)
        record["node_ids"] = list(self.node_ids)
        return record

    @classmethod
    def from_record(
        cls,
        raw: Mapping[str, Any] | None,
    ) -> "ProofIdeaClaimResolution":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea claim resolution",
            allowed_keys=keys,
            required_keys={
                "resolution_id",
                "claim_id",
                "status",
                "authority",
                "reason",
                "evidence_id",
                "turn_index",
            },
        )
        return cls(
            **{
                key: data.get(key, ()) if key == "node_ids" else data.get(key, "")
                for key in keys
            }
        )

    @classmethod
    def create(
        cls,
        *,
        proof_idea_id: str,
        occurrence_key: str = "",
        **content: Any,
    ) -> "ProofIdeaClaimResolution":
        idea_id = _proof_idea_text(
            proof_idea_id,
            field_name="claim_resolution.proof_idea_id",
            required=True,
        )
        occurrence = _proof_idea_text(
            occurrence_key,
            field_name="claim_resolution.occurrence_key",
        )
        draft = cls(resolution_id="pending", **content)
        payload = draft.to_record()
        payload.pop("resolution_id", None)
        resolution_id = stable_identity(
            "proof-idea-claim-resolution",
            idea_id,
            occurrence,
            json.dumps(
                payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ),
        )
        return replace(draft, resolution_id=resolution_id)


@dataclass(frozen=True)
class ProofIdeaBranchProvenance:
    """Where one proof-idea lifecycle fragment originated."""

    branch_id: str
    source: str
    parent_branch_id: str = ""

    def __post_init__(self) -> None:
        for field_name in self.__dataclass_fields__:
            object.__setattr__(
                self,
                field_name,
                _proof_idea_text(
                    getattr(self, field_name),
                    field_name=f"branch_provenance.{field_name}",
                    required=field_name in {"branch_id", "source"},
                ),
            )

    def to_record(self) -> dict[str, str]:
        return asdict(self)

    @classmethod
    def from_record(
        cls,
        raw: Mapping[str, Any] | None,
    ) -> "ProofIdeaBranchProvenance":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea branch provenance",
            allowed_keys=keys,
            required_keys={"branch_id", "source"},
        )
        return cls(**{key: data.get(key, "") for key in keys})


def _merge_keyed_records(
    left: Sequence[Any],
    right: Sequence[Any],
    *,
    key_name: str,
    record_name: str,
    merge_items: bool = False,
) -> tuple[Any, ...]:
    merged = {getattr(item, key_name): item for item in left}
    for item in right:
        key = getattr(item, key_name)
        existing = merged.get(key)
        if existing is None:
            merged[key] = item
        elif merge_items:
            merged[key] = existing.merged(item)
        elif existing != item:
            raise ValueError(f"conflicting {record_name} for {key_name}={key!r}")
    return tuple(merged[key] for key in sorted(merged))


@dataclass(frozen=True)
class ProofIdeaRecord:
    """Durable aggregate owning one mathematical strategy's lifecycle.

    The aggregate is descriptive, not proof-authoritative.  Status is reduced
    from immutable transitions, making branch merges commutative, idempotent,
    and auditable instead of overwriting a single mutable verdict.
    """

    theorem_name: str
    root_statement_identity: str
    strategy: str
    status_history: tuple[ProofIdeaStatusTransition, ...]
    branch_provenance: tuple[ProofIdeaBranchProvenance, ...]
    proof_idea_id: str = ""
    parent_proof_idea_id: str = ""
    route_shape_identity: str = ""
    notes: tuple[str, ...] = ()
    consumer_ids: tuple[str, ...] = ()
    claim_intents: tuple[ProofIdeaClaimIntent, ...] = ()
    claim_resolutions: tuple[ProofIdeaClaimResolution, ...] = ()
    observations: tuple[ProofIdeaObservation, ...] = ()

    def __post_init__(self) -> None:
        theorem = _proof_idea_text(
            self.theorem_name,
            field_name="theorem_name",
            required=True,
        )
        root = _proof_idea_text(
            self.root_statement_identity,
            field_name="root_statement_identity",
            required=True,
        )
        strategy = " ".join(
            _proof_idea_text(
                self.strategy,
                field_name="strategy",
                required=True,
            ).split()
        )
        route_shape_identity = _proof_idea_text(
            self.route_shape_identity,
            field_name="route_shape_identity",
        )
        expected_id = proof_idea_identity(
            theorem_name=theorem,
            root_statement_identity=root,
            strategy=strategy,
            route_shape_identity=route_shape_identity,
        )
        supplied_id = _proof_idea_text(
            self.proof_idea_id,
            field_name="proof_idea_id",
        )
        if supplied_id and supplied_id != expected_id:
            raise ValueError("proof idea identity does not match its mathematical route")
        object.__setattr__(self, "theorem_name", theorem)
        object.__setattr__(self, "root_statement_identity", root)
        object.__setattr__(self, "strategy", strategy)
        object.__setattr__(self, "route_shape_identity", route_shape_identity)
        object.__setattr__(self, "proof_idea_id", expected_id)
        object.__setattr__(
            self,
            "parent_proof_idea_id",
            _proof_idea_text(
                self.parent_proof_idea_id,
                field_name="parent_proof_idea_id",
            ),
        )
        if self.parent_proof_idea_id == expected_id:
            raise ValueError("proof idea must not be its own parent")
        object.__setattr__(
            self,
            "notes",
            _proof_idea_string_tuple(self.notes, field_name="notes"),
        )
        object.__setattr__(
            self,
            "consumer_ids",
            _proof_idea_string_tuple(
                self.consumer_ids,
                field_name="consumer_ids",
            ),
        )
        typed_claims = _typed_record_tuple(
            self.claim_intents,
            field_name="claim_intents",
            record_type=ProofIdeaClaimIntent,
        )
        typed_observations = _typed_record_tuple(
            self.observations,
            field_name="observations",
            record_type=ProofIdeaObservation,
        )
        typed_claim_resolutions = _typed_record_tuple(
            self.claim_resolutions,
            field_name="claim_resolutions",
            record_type=ProofIdeaClaimResolution,
        )
        typed_statuses = _typed_record_tuple(
            self.status_history,
            field_name="status_history",
            record_type=ProofIdeaStatusTransition,
        )
        typed_branches = _typed_record_tuple(
            self.branch_provenance,
            field_name="branch_provenance",
            record_type=ProofIdeaBranchProvenance,
        )
        if not typed_statuses:
            raise ValueError("proof idea status_history must not be empty")
        if not typed_branches:
            raise ValueError("proof idea branch_provenance must not be empty")
        known_branch_ids = {item.branch_id for item in typed_branches}
        referenced_branch_ids = {
            item.branch_id
            for item in (*typed_observations, *typed_statuses)
            if item.branch_id
        }
        unknown_branch_ids = sorted(referenced_branch_ids - known_branch_ids)
        if unknown_branch_ids:
            raise ValueError(
                "proof idea observations/statuses reference unknown branches: "
                + ", ".join(unknown_branch_ids)
            )
        object.__setattr__(
            self,
            "claim_intents",
            _merge_keyed_records(
                (), typed_claims,
                key_name="claim_id",
                record_name="proof idea claim intent",
                merge_items=True,
            ),
        )
        object.__setattr__(
            self,
            "claim_resolutions",
            _merge_keyed_records(
                (),
                typed_claim_resolutions,
                key_name="resolution_id",
                record_name="proof idea claim resolution",
            ),
        )
        object.__setattr__(
            self,
            "observations",
            _merge_keyed_records(
                (), typed_observations,
                key_name="observation_id",
                record_name="proof idea observation",
            ),
        )
        object.__setattr__(
            self,
            "status_history",
            _merge_keyed_records(
                (), typed_statuses,
                key_name="transition_id",
                record_name="proof idea status transition",
            ),
        )
        object.__setattr__(
            self,
            "branch_provenance",
            _merge_keyed_records(
                (), typed_branches,
                key_name="branch_id",
                record_name="proof idea branch provenance",
            ),
        )

    @property
    def current_status_transition(self) -> ProofIdeaStatusTransition:
        lean_transitions = [
            item for item in self.status_history if item.authority == "lean"
        ]
        if lean_transitions:
            return max(
                lean_transitions,
                key=lambda item: (
                    item.turn_index,
                    _STATUS_RANK[item.status],
                    item.transition_id,
                ),
            )
        accepted_fact_transitions = [
            item
            for item in self.status_history
            if item.authority == "accepted_fact"
        ]
        latest_accepted_fact = (
            max(
                accepted_fact_transitions,
                key=lambda item: (
                    item.turn_index,
                    _STATUS_RANK[item.status],
                    item.transition_id,
                ),
            )
            if accepted_fact_transitions
            else None
        )
        if (
            latest_accepted_fact is not None
            and latest_accepted_fact.status != "active"
        ):
            return latest_accepted_fact
        candidates = [
            item
            for item in self.status_history
            if item.authority in {"advisory", "controller"}
        ]
        if latest_accepted_fact is not None:
            candidates.append(latest_accepted_fact)
        return max(
            candidates,
            key=lambda item: (
                item.effective_authority_rank,
                item.turn_index,
                _STATUS_RANK[item.status],
                item.transition_id,
            ),
        )

    @property
    def current_status(self) -> str:
        return self.current_status_transition.status

    @property
    def current_status_authority(self) -> str:
        return self.current_status_transition.authority

    def current_claim_resolution(
        self,
        claim_id: str,
    ) -> ProofIdeaClaimResolution | None:
        clean_claim_id = _proof_idea_text(
            claim_id,
            field_name="claim_resolution.claim_id",
        )
        matches = [
            item for item in self.claim_resolutions if item.claim_id == clean_claim_id
        ]
        if not matches:
            return None
        authority_rank = {"accepted_fact": 1, "lean": 2}
        status_rank = {
            "retired": 1,
            "solved": 2,
            "invalidated": 3,
            "retracted": 4,
        }
        return max(
            matches,
            key=lambda item: (
                authority_rank[item.authority],
                item.turn_index,
                status_rank[item.status],
                item.resolution_id,
            ),
        )

    def to_record(self) -> dict[str, Any]:
        return {
            "schema_version": PROOF_IDEA_SCHEMA_VERSION,
            "proof_idea_id": self.proof_idea_id,
            "parent_proof_idea_id": self.parent_proof_idea_id,
            "theorem_name": self.theorem_name,
            "root_statement_identity": self.root_statement_identity,
            "strategy": self.strategy,
            "route_shape_identity": self.route_shape_identity,
            "notes": list(self.notes),
            "consumer_ids": list(self.consumer_ids),
            "claim_intents": [item.to_record() for item in self.claim_intents],
            "claim_resolutions": [
                item.to_record() for item in self.claim_resolutions
            ],
            "observations": [item.to_record() for item in self.observations],
            "status_history": [item.to_record() for item in self.status_history],
            "branch_provenance": [
                item.to_record() for item in self.branch_provenance
            ],
        }

    @classmethod
    def from_record(cls, raw: Mapping[str, Any] | None) -> "ProofIdeaRecord":
        if not isinstance(raw, Mapping):
            raise TypeError("proof idea record must be a mapping")
        version = raw.get("schema_version")
        if type(version) is not int:
            raise ValueError("proof idea schema_version must be an integer")
        if version == 0:
            return cls._from_v0_record(raw)
        if version != PROOF_IDEA_SCHEMA_VERSION:
            raise ValueError(f"unsupported proof idea schema_version={version}")
        keys = {
            "schema_version",
            "proof_idea_id",
            "parent_proof_idea_id",
            "theorem_name",
            "root_statement_identity",
            "strategy",
            "route_shape_identity",
            "notes",
            "consumer_ids",
            "claim_intents",
            "claim_resolutions",
            "observations",
            "status_history",
            "branch_provenance",
        }
        data = _strict_record(
            raw,
            record_name="proof idea record",
            allowed_keys=keys,
            required_keys={
                "schema_version",
                "proof_idea_id",
                "theorem_name",
                "root_statement_identity",
                "strategy",
                "status_history",
                "branch_provenance",
            },
        )
        return cls(
            theorem_name=data["theorem_name"],
            root_statement_identity=data["root_statement_identity"],
            strategy=data["strategy"],
            route_shape_identity=data.get("route_shape_identity", ""),
            status_history=data["status_history"],
            branch_provenance=data["branch_provenance"],
            proof_idea_id=data["proof_idea_id"],
            parent_proof_idea_id=data.get("parent_proof_idea_id", ""),
            notes=data.get("notes", ()),
            consumer_ids=data.get("consumer_ids", ()),
            claim_intents=data.get("claim_intents", ()),
            claim_resolutions=data.get("claim_resolutions", ()),
            observations=data.get("observations", ()),
        )

    @classmethod
    def _from_v0_record(cls, raw: Mapping[str, Any]) -> "ProofIdeaRecord":
        """Migrate the only supported flat legacy shape without guessing data."""

        keys = {
            "schema_version",
            "proof_idea_id",
            "parent_proof_idea_id",
            "theorem_name",
            "root_statement_identity",
            "strategy",
            "route_shape_identity",
            "notes",
            "consumer_ids",
            "claim_intents",
            "claim_resolutions",
            "observations",
            "status",
            "status_authority",
            "status_reason",
            "status_transition_id",
            "status_turn_index",
            "branch_id",
            "parent_branch_id",
            "branch_source",
        }
        data = _strict_record(
            raw,
            record_name="legacy proof idea record",
            allowed_keys=keys,
            required_keys={
                "schema_version",
                "proof_idea_id",
                "theorem_name",
                "root_statement_identity",
                "strategy",
                "status",
                "status_authority",
                "status_reason",
                "status_transition_id",
                "status_turn_index",
                "branch_id",
                "branch_source",
            },
        )
        return cls(
            theorem_name=data["theorem_name"],
            root_statement_identity=data["root_statement_identity"],
            strategy=data["strategy"],
            route_shape_identity=data.get("route_shape_identity", ""),
            status_history=(
                ProofIdeaStatusTransition(
                    transition_id=data["status_transition_id"],
                    status=data["status"],
                    authority=data["status_authority"],
                    reason=data["status_reason"],
                    turn_index=data["status_turn_index"],
                    branch_id=data["branch_id"],
                ),
            ),
            branch_provenance=(
                ProofIdeaBranchProvenance(
                    branch_id=data["branch_id"],
                    source=data["branch_source"],
                    parent_branch_id=data.get("parent_branch_id", ""),
                ),
            ),
            proof_idea_id=data["proof_idea_id"],
            parent_proof_idea_id=data.get("parent_proof_idea_id", ""),
            notes=data.get("notes", ()),
            consumer_ids=data.get("consumer_ids", ()),
            claim_intents=data.get("claim_intents", ()),
            claim_resolutions=data.get("claim_resolutions", ()),
            observations=data.get("observations", ()),
        )

    def merged(self, other: "ProofIdeaRecord") -> "ProofIdeaRecord":
        if self.proof_idea_id != other.proof_idea_id:
            raise ValueError("cannot merge different proof ideas")
        for field_name in (
            "theorem_name",
            "root_statement_identity",
            "strategy",
            "route_shape_identity",
        ):
            if getattr(self, field_name) != getattr(other, field_name):
                raise ValueError(f"conflicting proof idea {field_name}")
        return ProofIdeaRecord(
            theorem_name=self.theorem_name,
            root_statement_identity=self.root_statement_identity,
            strategy=self.strategy,
            route_shape_identity=self.route_shape_identity,
            status_history=_merge_keyed_records(
                self.status_history,
                other.status_history,
                key_name="transition_id",
                record_name="proof idea status transition",
            ),
            branch_provenance=_merge_keyed_records(
                self.branch_provenance,
                other.branch_provenance,
                key_name="branch_id",
                record_name="proof idea branch provenance",
            ),
            proof_idea_id=self.proof_idea_id,
            parent_proof_idea_id=_merge_optional_text(
                self.parent_proof_idea_id,
                other.parent_proof_idea_id,
                field_name="parent_proof_idea_id",
            ),
            notes=self.notes + other.notes,
            consumer_ids=self.consumer_ids + other.consumer_ids,
            claim_intents=_merge_keyed_records(
                self.claim_intents,
                other.claim_intents,
                key_name="claim_id",
                record_name="proof idea claim intent",
                merge_items=True,
            ),
            claim_resolutions=_merge_keyed_records(
                self.claim_resolutions,
                other.claim_resolutions,
                key_name="resolution_id",
                record_name="proof idea claim resolution",
            ),
            observations=_merge_keyed_records(
                self.observations,
                other.observations,
                key_name="observation_id",
                record_name="proof idea observation",
            ),
        )


@dataclass(frozen=True)
class ProofLineageEnvelope:
    """Immutable cross-subsystem coordinates for one proof-path event."""

    strategy_lineage_id: str = ""
    proof_idea_id: str = ""
    parent_lineage_id: str = ""
    route_id: str = ""
    claim_id: str = ""
    statement_identity: str = ""
    proof_candidate_id: str = ""
    lean_residual_id: str = ""
    repair_ticket_id: str = ""
    accepted_fact_id: str = ""
    assembly_id: str = ""

    def __post_init__(self) -> None:
        # Direct construction is a producer boundary too. Without this hook,
        # callers could bypass from_record()/updated() and serialize mappings,
        # booleans, or numbers as nominal schema-v1 identities.
        for field_name in self.__dataclass_fields__:
            object.__setattr__(
                self,
                field_name,
                _identity_text(
                    getattr(self, field_name),
                    field_name=field_name,
                ),
            )

    def updated(self, **changes: Any) -> "ProofLineageEnvelope":
        allowed = {
            field_name: _identity_text(value, field_name=field_name)
            for field_name, value in changes.items()
            if field_name in self.__dataclass_fields__
        }
        return replace(self, **allowed)

    def to_record(self) -> dict[str, str | int]:
        return {
            "schema_version": LINEAGE_SCHEMA_VERSION,
            **asdict(self),
        }

    @classmethod
    def from_record(cls, raw: Mapping[str, Any] | None) -> "ProofLineageEnvelope":
        data = dict(raw or {})
        version = data.pop("schema_version", LINEAGE_SCHEMA_VERSION)
        if type(version) is not int or version != LINEAGE_SCHEMA_VERSION:
            raise ValueError(f"unsupported proof lineage schema_version={version}")
        return cls(
            **{
                field_name: _identity_text(
                    data.get(field_name),
                    field_name=field_name,
                )
                for field_name in cls.__dataclass_fields__
            }
        )

    @classmethod
    def from_metadata(
        cls,
        metadata: Mapping[str, Any] | None,
    ) -> "ProofLineageEnvelope":
        data = dict(metadata or {})
        embedded = data.get("proof_lineage")
        if isinstance(embedded, Mapping):
            envelope = cls.from_record(embedded)
        else:
            envelope = cls()
        changes = {}
        for field_name in cls.__dataclass_fields__:
            if field_name not in data or data[field_name] in (None, ""):
                continue
            changes[field_name] = _identity_text(
                data[field_name],
                field_name=field_name,
            )
        return envelope.updated(**changes)

    def merged_metadata(
        self,
        metadata: Mapping[str, Any] | None = None,
    ) -> dict[str, Any]:
        out = dict(metadata or {})
        for field_name in self.__dataclass_fields__:
            out.pop(field_name, None)
        record = self.to_record()
        out["proof_lineage"] = record
        for field_name in self.__dataclass_fields__:
            value = _clean(getattr(self, field_name))
            # Return an authoritative overlay, not a sparse convenience
            # mapping. Several graph/telemetry producers merge this result
            # with ``existing.update(...)``; omitting an empty coordinate
            # there would leave a malformed or stale legacy value alive.
            out[field_name] = value
        return out


@dataclass(frozen=True)
class ProofIdeaExecutionScope:
    """Reusable formal-work identity, separate from its strategy consumer.

    ``target_statement`` is an executable unit and is therefore preserved
    byte-for-byte.  The remaining coordinates identify the Lean environment
    in which that target and its helper context are meaningful.
    """

    target_statement: str = ""
    # Exact elaborated contract/formulation identity.  Version and telescope
    # coordinates are intentionally conserved here because exact-selected
    # execution must not silently cross formulation boundaries.
    statement_identity: str = ""
    # Semantic proposition identity used only for equivalence/fact sharing.
    # It must never replace ``statement_identity`` at an exact boundary.
    proposition_identity: str = ""
    environment_hash: str = ""
    helper_context_hash: str = ""
    graph_revision: str = ""

    def __post_init__(self) -> None:
        if not isinstance(self.target_statement, str):
            raise TypeError("proof idea execution target_statement must be a string")
        for field_name in (
            "statement_identity",
            "proposition_identity",
            "environment_hash",
            "helper_context_hash",
            "graph_revision",
        ):
            object.__setattr__(
                self,
                field_name,
                _identity_text(
                    getattr(self, field_name),
                    field_name=f"execution_scope.{field_name}",
                ),
            )

    def to_record(self) -> dict[str, str]:
        return asdict(self)

    @classmethod
    def from_record(
        cls,
        raw: Mapping[str, Any] | None,
    ) -> "ProofIdeaExecutionScope":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea execution scope",
            allowed_keys=keys,
        )
        return cls(**{key: data.get(key, "") for key in keys})


@dataclass(frozen=True)
class ProofIdeaConsumerBinding:
    """One route/claim/branch cognition owner for shared formal work."""

    proof_idea_id: str = ""
    route_id: str = ""
    claim_id: str = ""
    statement_identity: str = ""
    branch_id: str = ""
    occurrence_key: str = ""
    proof_candidate_id: str = ""
    lean_residual_id: str = ""
    repair_ticket_id: str = ""
    graph_node_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        for field_name in (
            "proof_idea_id",
            "route_id",
            "claim_id",
            "statement_identity",
            "branch_id",
            "occurrence_key",
            "proof_candidate_id",
            "lean_residual_id",
            "repair_ticket_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _identity_text(
                    getattr(self, field_name),
                    field_name=f"consumer_binding.{field_name}",
                ),
            )
        object.__setattr__(
            self,
            "graph_node_ids",
            _proof_idea_string_tuple(
                self.graph_node_ids,
                field_name="consumer_binding.graph_node_ids",
            ),
        )
        if not any(
            (
                self.proof_idea_id,
                self.route_id,
                self.claim_id,
                self.statement_identity,
                self.graph_node_ids,
            )
        ):
            raise ValueError(
                "proof idea consumer binding requires an explicit cognition coordinate"
            )

    def to_record(self) -> dict[str, Any]:
        record = asdict(self)
        record["graph_node_ids"] = list(self.graph_node_ids)
        return record

    @classmethod
    def from_record(
        cls,
        raw: Mapping[str, Any] | None,
    ) -> "ProofIdeaConsumerBinding":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea consumer binding",
            allowed_keys=keys,
        )
        return cls(
            **{
                key: data.get(key, ()) if key == "graph_node_ids" else data.get(key, "")
                for key in keys
            }
        )

    @classmethod
    def from_lineage(
        cls,
        envelope: ProofLineageEnvelope,
        *,
        branch_id: str = "",
        occurrence_key: str = "",
        graph_node_ids: Sequence[str] = (),
    ) -> "ProofIdeaConsumerBinding":
        if not isinstance(envelope, ProofLineageEnvelope):
            raise TypeError("consumer binding lineage must be ProofLineageEnvelope")
        return cls(
            proof_idea_id=envelope.proof_idea_id,
            route_id=envelope.route_id,
            claim_id=envelope.claim_id,
            statement_identity=envelope.statement_identity,
            branch_id=branch_id,
            occurrence_key=occurrence_key,
            proof_candidate_id=envelope.proof_candidate_id,
            lean_residual_id=envelope.lean_residual_id,
            repair_ticket_id=envelope.repair_ticket_id,
            graph_node_ids=tuple(graph_node_ids),
        )


@dataclass(frozen=True)
class ProofIdeaContextEvidence:
    """One projection unit with explicit completeness and integrity receipt."""

    kind: str
    content: str
    sha256: str
    char_length: int
    completeness: str
    omitted_reason: str = ""

    def __post_init__(self) -> None:
        kind = _proof_idea_text(
            self.kind,
            field_name="context_evidence.kind",
            required=True,
        )
        if not isinstance(self.content, str):
            raise TypeError("proof idea context evidence content must be a string")
        digest = _proof_idea_text(
            self.sha256,
            field_name="context_evidence.sha256",
            required=True,
        ).lower()
        if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
            raise ValueError("proof idea context evidence sha256 must be hex sha256")
        if type(self.char_length) is not int or self.char_length < 0:
            raise TypeError(
                "proof idea context evidence char_length must be a non-negative integer"
            )
        completeness = _proof_idea_text(
            self.completeness,
            field_name="context_evidence.completeness",
            required=True,
        )
        if completeness not in PROOF_IDEA_CONTEXT_COMPLETENESS:
            raise ValueError(
                f"unsupported proof idea context completeness={completeness!r}"
            )
        omitted_reason = _proof_idea_text(
            self.omitted_reason,
            field_name="context_evidence.omitted_reason",
        )
        if completeness == "exact":
            if self.char_length != len(self.content):
                raise ValueError(
                    "proof idea exact context evidence char_length does not match content"
                )
            actual = hashlib.sha256(self.content.encode("utf-8")).hexdigest()
            if digest != actual:
                raise ValueError(
                    "proof idea exact context evidence sha256 does not match content"
                )
            if omitted_reason:
                raise ValueError("exact proof idea context evidence cannot be omitted")
        elif completeness == "preview":
            if self.char_length < len(self.content):
                raise ValueError(
                    "proof idea preview char_length cannot be shorter than its content"
                )
        else:
            if self.content:
                raise ValueError("withheld proof idea context evidence must have no content")
            if not omitted_reason:
                raise ValueError(
                    "withheld proof idea context evidence requires omitted_reason"
                )
        object.__setattr__(self, "kind", kind)
        object.__setattr__(self, "sha256", digest)
        object.__setattr__(self, "completeness", completeness)
        object.__setattr__(self, "omitted_reason", omitted_reason)

    @classmethod
    def exact(cls, kind: str, content: str) -> "ProofIdeaContextEvidence":
        if not isinstance(content, str):
            raise TypeError("proof idea exact context evidence must be a string")
        return cls(
            kind=kind,
            content=content,
            sha256=hashlib.sha256(content.encode("utf-8")).hexdigest(),
            char_length=len(content),
            completeness="exact",
        )

    @classmethod
    def preview(
        cls,
        kind: str,
        content: str,
        *,
        original_sha256: str,
        original_char_length: int,
    ) -> "ProofIdeaContextEvidence":
        return cls(
            kind=kind,
            content=content,
            sha256=original_sha256,
            char_length=original_char_length,
            completeness="preview",
        )

    @classmethod
    def withheld(
        cls,
        kind: str,
        original_content: str,
        *,
        reason: str,
    ) -> "ProofIdeaContextEvidence":
        if not isinstance(original_content, str):
            raise TypeError("withheld proof idea context source must be a string")
        return cls.withheld_receipt(
            kind,
            sha256=hashlib.sha256(original_content.encode("utf-8")).hexdigest(),
            char_length=len(original_content),
            reason=reason,
        )

    @classmethod
    def withheld_receipt(
        cls,
        kind: str,
        *,
        sha256: str,
        char_length: int,
        reason: str,
    ) -> "ProofIdeaContextEvidence":
        """Withhold content while preserving its original artifact receipt."""

        return cls(
            kind=kind,
            content="",
            sha256=sha256,
            char_length=char_length,
            completeness="withheld",
            omitted_reason=reason,
        )

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(
        cls,
        raw: Mapping[str, Any] | None,
    ) -> "ProofIdeaContextEvidence":
        keys = set(cls.__dataclass_fields__)
        data = _strict_record(
            raw,
            record_name="proof idea context evidence",
            allowed_keys=keys,
            required_keys={"kind", "content", "sha256", "char_length", "completeness"},
        )
        return cls(
            kind=data["kind"],
            content=data["content"],
            sha256=data["sha256"],
            char_length=data["char_length"],
            completeness=data["completeness"],
            omitted_reason=data.get("omitted_reason", ""),
        )


@dataclass(frozen=True)
class ProofIdeaContextResolution:
    """Pure result of binding selected formal work to descriptive cognition."""

    status: str
    policy: str
    reason: str
    execution_scope: ProofIdeaExecutionScope
    current_graph_revision: str
    primary_binding: ProofIdeaConsumerBinding | None = None
    candidate_bindings: tuple[ProofIdeaConsumerBinding, ...] = ()
    candidate_proof_idea_ids: tuple[str, ...] = ()
    proof_idea: ProofIdeaRecord | None = None
    claim_intent: ProofIdeaClaimIntent | None = None
    claim_resolution: ProofIdeaClaimResolution | None = None
    observations: tuple[ProofIdeaObservation, ...] = ()
    context_digest: str = ""
    revision_scope_json: str = ""

    def __post_init__(self) -> None:
        status = _proof_idea_text(
            self.status,
            field_name="context_resolution.status",
            required=True,
        )
        if status not in PROOF_IDEA_CONTEXT_RESOLUTION_STATUSES:
            raise ValueError(f"unsupported proof idea context status={status!r}")
        policy = _proof_idea_text(
            self.policy,
            field_name="context_resolution.policy",
            required=True,
        )
        if policy not in PROOF_IDEA_CONTEXT_POLICIES:
            raise ValueError(f"unsupported proof idea context policy={policy!r}")
        if not isinstance(self.execution_scope, ProofIdeaExecutionScope):
            raise TypeError("context resolution execution_scope has invalid type")
        if self.primary_binding is not None and not isinstance(
            self.primary_binding, ProofIdeaConsumerBinding
        ):
            raise TypeError("context resolution primary_binding has invalid type")
        candidate_bindings = tuple(self.candidate_bindings)
        if any(
            not isinstance(item, ProofIdeaConsumerBinding)
            for item in candidate_bindings
        ):
            raise TypeError("context resolution candidate_bindings have invalid type")
        candidate_ids = _proof_idea_string_tuple(
            self.candidate_proof_idea_ids,
            field_name="context_resolution.candidate_proof_idea_ids",
        )
        observations = tuple(self.observations)
        if any(not isinstance(item, ProofIdeaObservation) for item in observations):
            raise TypeError("context resolution observations have invalid type")
        if status == "resolved" and (
            self.primary_binding is None or self.proof_idea is None
        ):
            raise ValueError(
                "resolved proof idea context requires binding and proof idea"
            )
        if status != "resolved" and self.proof_idea is not None:
            raise ValueError(
                "unresolved proof idea context cannot expose one proof idea as selected"
            )
        object.__setattr__(self, "status", status)
        object.__setattr__(self, "policy", policy)
        object.__setattr__(
            self,
            "reason",
            _proof_idea_text(self.reason, field_name="context_resolution.reason"),
        )
        object.__setattr__(
            self,
            "current_graph_revision",
            _identity_text(
                self.current_graph_revision,
                field_name="context_resolution.current_graph_revision",
            ),
        )
        object.__setattr__(self, "candidate_bindings", candidate_bindings)
        object.__setattr__(self, "candidate_proof_idea_ids", candidate_ids)
        object.__setattr__(self, "observations", observations)
        revision_scope_json = _proof_idea_text(
            self.revision_scope_json,
            field_name="context_resolution.revision_scope_json",
        )
        if revision_scope_json:
            try:
                revision_scope = json.loads(revision_scope_json)
            except (TypeError, ValueError) as exc:
                raise ValueError(
                    "context resolution revision scope must be valid JSON"
                ) from exc
            if not isinstance(revision_scope, dict):
                raise ValueError(
                    "context resolution revision scope must be a JSON object"
                )
        object.__setattr__(self, "revision_scope_json", revision_scope_json)
        object.__setattr__(
            self,
            "context_digest",
            _identity_text(
                self.context_digest,
                field_name="context_resolution.context_digest",
            ),
        )


@dataclass(frozen=True)
class ProofIdeaContextProjection:
    """Audience-specific advisory packet composed of indivisible evidence units."""

    audience: str
    resolution_status: str
    context_digest: str
    target: ProofIdeaContextEvidence
    evidence: tuple[ProofIdeaContextEvidence, ...] = ()
    proof_authority: bool = False

    def __post_init__(self) -> None:
        audience = _proof_idea_text(
            self.audience,
            field_name="context_projection.audience",
            required=True,
        )
        if audience not in PROOF_IDEA_CONTEXT_AUDIENCES:
            raise ValueError(f"unsupported proof idea context audience={audience!r}")
        resolution_status = _proof_idea_text(
            self.resolution_status,
            field_name="context_projection.resolution_status",
            required=True,
        )
        if resolution_status not in PROOF_IDEA_CONTEXT_RESOLUTION_STATUSES:
            raise ValueError(
                "proof idea context projection has invalid resolution_status"
            )
        context_digest = _identity_text(
            self.context_digest,
            field_name="context_projection.context_digest",
        )
        if not isinstance(self.target, ProofIdeaContextEvidence):
            raise TypeError("proof idea context projection target has invalid type")
        evidence = tuple(self.evidence)
        if any(not isinstance(item, ProofIdeaContextEvidence) for item in evidence):
            raise TypeError("proof idea context projection evidence has invalid type")
        if type(self.proof_authority) is not bool or self.proof_authority:
            raise ValueError("proof idea context projection must remain advisory")
        object.__setattr__(self, "audience", audience)
        object.__setattr__(self, "resolution_status", resolution_status)
        object.__setattr__(self, "context_digest", context_digest)
        object.__setattr__(self, "evidence", evidence)

    def render(self) -> str:
        """Render without altering, truncating, or prefix-slicing any unit."""

        lines = [
            "Conserved proof-idea context (advisory; Lean/graph remain authoritative):",
            f"- audience: {self.audience}",
            f"- resolution: {self.resolution_status}",
            f"- context digest: {self.context_digest or '(none)'}",
        ]
        for item in (self.target, *self.evidence):
            header = (
                f"[{item.kind}; completeness={item.completeness}; "
                f"sha256={item.sha256}; chars={item.char_length}]"
            )
            lines.append(header)
            if item.completeness == "withheld":
                lines.append(f"(withheld: {item.omitted_reason})")
            else:
                lines.append(item.content)
        return "\n".join(lines)


@dataclass(frozen=True)
class ProofIdeaGlobalContextProjection:
    """Lossless advisory inventory for consumers without selected work."""

    audience: str
    context_digest: str
    evidence: tuple[ProofIdeaContextEvidence, ...] = ()
    proof_authority: bool = False

    def __post_init__(self) -> None:
        audience = _proof_idea_text(
            self.audience,
            field_name="global_context_projection.audience",
            required=True,
        )
        if audience not in PROOF_IDEA_CONTEXT_AUDIENCES:
            raise ValueError(
                f"unsupported proof idea global context audience={audience!r}"
            )
        evidence = tuple(self.evidence)
        if any(not isinstance(item, ProofIdeaContextEvidence) for item in evidence):
            raise TypeError(
                "proof idea global context projection evidence has invalid type"
            )
        if type(self.proof_authority) is not bool or self.proof_authority:
            raise ValueError("proof idea global context projection must remain advisory")
        object.__setattr__(self, "audience", audience)
        object.__setattr__(
            self,
            "context_digest",
            _identity_text(
                self.context_digest,
                field_name="global_context_projection.context_digest",
            ),
        )
        object.__setattr__(self, "evidence", evidence)

    def render(self) -> str:
        lines = [
            "Global conserved proof-idea inventory "
            "(advisory; Lean/graph remain authoritative):",
            f"- audience: {self.audience}",
            f"- context digest: {self.context_digest or '(none)'}",
        ]
        for item in self.evidence:
            lines.append(
                f"[{item.kind}; completeness={item.completeness}; "
                f"sha256={item.sha256}; chars={item.char_length}]"
            )
            if item.completeness == "withheld":
                lines.append(f"(withheld: {item.omitted_reason})")
            else:
                lines.append(item.content)
        return "\n".join(lines)


def lineage_event_identity(
    *,
    event_type: str,
    envelope: ProofLineageEnvelope,
    phase: str = "",
    verdict: str = "",
    evidence_hash: str = "",
    occurrence_key: str = "",
) -> str:
    return stable_identity(
        "lineage-event",
        event_type,
        json.dumps(envelope.to_record(), sort_keys=True, ensure_ascii=False),
        phase,
        verdict,
        evidence_hash,
        # Distinct attempts / retirement expansions must not collapse when they
        # share the same envelope coordinates. Callers pass attempt ids or a
        # resolved-set fingerprint here; exact replays keep the empty key.
        occurrence_key,
    )
