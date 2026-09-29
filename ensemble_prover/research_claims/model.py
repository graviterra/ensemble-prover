"""Exact, non-authoritative contracts for written mathematical research."""

from __future__ import annotations

import json
import math
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping


MAX_JSON_NESTING = 64
# Persisted reports and assignment packets wrap validated input in additional
# containers. Keep headroom without allowing recursive or unbounded records.
INTERNAL_JSON_NESTING = 256
MATHEMATICAL_STATUSES = ("proposed", "supported", "refuted", "unresolved")
EVIDENCE_KINDS = (
    "written_proof",
    "counterexample",
    "exact_computation",
    "primary_source",
    "kernel_report",
    "gap",
)
REVIEW_VERDICTS = ("supported", "refuted", "unresolved", "dismissed")
CONTRIBUTION_DECISIONS = (
    "closes",
    "improves_bound",
    "eliminates_route",
    "irrelevant",
    "unresolved",
)
OPERATIONAL_OUTCOMES = (
    "completed",
    "timeout",
    "provider_failure",
    "tool_unavailable",
    "cancelled",
)


def text(value: Any, name: str, *, optional: bool = False) -> str:
    """Validate without rewriting potentially significant mathematical text."""
    if not isinstance(value, str) or (not optional and not value.strip()):
        raise ValueError(
            f"{name} must be {'a string' if optional else 'nonempty text'}"
        )
    return value


def identifier(value: Any, name: str = "identifier") -> str:
    if not isinstance(value, str) or not re.fullmatch(
        r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}", value
    ):
        raise ValueError(
            f"{name} must be a simple identifier of at most 128 characters"
        )
    return value


def positive_int(value: Any, name: str) -> int:
    if type(value) is not int or value < 1:
        raise ValueError(f"{name} must be a positive integer")
    return value


def strings(value: Any, name: str, *, ids: bool = False) -> tuple[str, ...]:
    if not isinstance(value, (tuple, list)):
        raise ValueError(f"{name} must be an array")
    result = tuple((identifier if ids else text)(item, name) for item in value)
    if len(set(result)) != len(result):
        raise ValueError(f"{name} must not contain duplicates")
    return result


def object_fields(
    value: Any, allowed: set[str], required: set[str], name: str
) -> dict[str, Any]:
    if not isinstance(value, Mapping) or any(not isinstance(key, str) for key in value):
        raise ValueError(f"{name} must be an object")
    unknown, missing = set(value) - allowed, required - set(value)
    if unknown or missing:
        raise ValueError(
            f"{name}: unknown fields {sorted(unknown)}, missing fields {sorted(missing)}"
        )
    return dict(value)


def validate_json_structure(value: Any, *, max_depth: int = MAX_JSON_NESTING) -> None:
    """Validate finite JSON iteratively, with a bounded number of containers.

    Tuples are accepted as arrays because dataclass specifications use them.
    Repeated references are valid; a cycle eventually exceeds the depth bound.
    Text and array lengths remain unrestricted.
    """
    positive_int(max_depth, "JSON maximum nesting")
    pending = [(value, 0)]
    while pending:
        item, depth = pending.pop()
        if isinstance(item, (dict, list, tuple)):
            depth += 1
            if depth > max_depth:
                raise ValueError(f"JSON nesting exceeds {max_depth} levels")
            if isinstance(item, dict):
                if any(not isinstance(key, str) for key in item):
                    raise ValueError("JSON objects require string keys")
                children: Iterable[Any] = item.values()
                pending.extend((key, depth) for key in item)
            else:
                children = item
            pending.extend((child, depth) for child in children)
        elif isinstance(item, str):
            # JSON escapes can decode to lone UTF-16 surrogates, which cannot
            # be stored as UTF-8 in artifacts or SQLite (including diagnostics).
            # Reject without echoing the malformed scalar into the error.
            if re.search(r"[\ud800-\udfff]", item):
                raise ValueError("JSON text contains an unpaired Unicode surrogate")
        elif isinstance(item, float):
            if not math.isfinite(item):
                raise ValueError("JSON numbers must be finite")
        elif item is not None and not isinstance(item, (bool, int)):
            raise ValueError("unsupported JSON value type")


def json_text(value: Any) -> str:
    validate_json_structure(value, max_depth=INTERNAL_JSON_NESTING)
    return json.dumps(
        value,
        ensure_ascii=False,
        allow_nan=False,
        sort_keys=True,
        separators=(",", ":"),
    )


def assignment_output_path(value: Any) -> str:
    """Validate and canonicalize the output path recorded in an assignment."""
    text(value, "owned_output")
    if "\x00" in value:
        raise ValueError("owned_output must be a valid path")
    try:
        output = Path(value).expanduser().resolve()
        is_directory = output.is_dir()
    except (OSError, RuntimeError) as exc:
        raise ValueError(f"owned_output must be a valid path: {exc}") from exc
    if is_directory:
        raise ValueError("owned_output must name a file")
    return str(output)


def assignment_context_record(assignment: Mapping[str, Any]) -> dict[str, Any]:
    """Retain lifecycle/context metadata without recursively embedding packets."""
    return {
        key: value
        for key, value in assignment.items()
        if key
        not in {
            "history_context",
            "target",
            "subject",
            "dependency_context",
            "artifacts",
            "context_revisions",
            "context_state_tokens",
            "context_assessment_tokens",
            "required_by",
            "quantitative_checks",
        }
    }


def load_json(value: str, *, max_depth: int = MAX_JSON_NESTING) -> Any:
    """Read strict JSON; internal envelopes can opt into bounded headroom."""
    positive_int(max_depth, "JSON maximum nesting")

    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in items:
            if key in result:
                raise ValueError(f"duplicate JSON field: {key!r}")
            result[key] = item
        return result

    def invalid(value: str) -> None:
        raise ValueError(f"nonfinite JSON number: {value}")

    def finite_float(value: str) -> float:
        result = float(value)
        if not math.isfinite(result):
            raise ValueError(f"nonfinite JSON number: {value}")
        return result

    try:
        result = json.loads(
            value,
            object_pairs_hook=pairs,
            parse_constant=invalid,
            parse_float=finite_float,
        )
    except RecursionError as exc:
        raise ValueError(f"JSON nesting exceeds {max_depth} levels") from exc
    validate_json_structure(result, max_depth=max_depth)
    return result


@dataclass(frozen=True)
class MathematicalContract:
    statement: str
    domain: str
    hypotheses: tuple[str, ...] = ()
    quantifiers: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        text(self.statement, "statement")
        text(self.domain, "domain")
        object.__setattr__(self, "hypotheses", strings(self.hypotheses, "hypotheses"))
        object.__setattr__(
            self, "quantifiers", strings(self.quantifiers, "quantifiers")
        )

    @classmethod
    def from_dict(cls, value: Any) -> MathematicalContract:
        return cls(
            **object_fields(
                value,
                {"statement", "domain", "hypotheses", "quantifiers"},
                {"statement", "domain"},
                "contract",
            )
        )


@dataclass(frozen=True)
class QuantitativeCosts:
    density: str = ""
    domain_size: str = ""
    characteristic_dependence: str = ""
    exceptional_terms: str = ""

    def __post_init__(self) -> None:
        for key, value in asdict(self).items():
            text(value, key, optional=True)

    @classmethod
    def from_dict(cls, value: Any) -> QuantitativeCosts:
        return cls(
            **object_fields(
                value, set(cls.__dataclass_fields__), set(), "quantitative costs"
            )
        )


@dataclass(frozen=True)
class Obligation:
    obligation_id: str
    supplier_id: str
    contract: MathematicalContract
    quantitative_requirements: QuantitativeCosts = field(
        default_factory=QuantitativeCosts
    )

    def __post_init__(self) -> None:
        identifier(self.obligation_id, "obligation_id")
        identifier(self.supplier_id, "supplier_id")
        if not isinstance(self.contract, MathematicalContract):
            raise ValueError("obligation contract must be a MathematicalContract")
        if not isinstance(self.quantitative_requirements, QuantitativeCosts):
            raise ValueError("quantitative_requirements must be QuantitativeCosts")

    @classmethod
    def from_dict(cls, value: Any) -> Obligation:
        data = object_fields(
            value,
            set(cls.__dataclass_fields__),
            {"obligation_id", "supplier_id", "contract"},
            "obligation",
        )
        data["contract"] = MathematicalContract.from_dict(data["contract"])
        data["quantitative_requirements"] = QuantitativeCosts.from_dict(
            data.get("quantitative_requirements", {})
        )
        return cls(**data)


@dataclass(frozen=True)
class ClaimSpec:
    claim_id: str
    contract: MathematicalContract
    author: str
    dependencies: tuple[Obligation, ...] = ()
    quantitative_costs: QuantitativeCosts = field(default_factory=QuantitativeCosts)
    remaining_gap: str = ""
    supersedes: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        identifier(self.claim_id, "claim_id")
        identifier(self.author, "author")
        if not isinstance(self.contract, MathematicalContract):
            raise ValueError("contract must be a MathematicalContract")
        if not isinstance(self.quantitative_costs, QuantitativeCosts):
            raise ValueError("quantitative_costs must be QuantitativeCosts")
        if not isinstance(self.dependencies, (tuple, list)) or any(
            not isinstance(item, Obligation) for item in self.dependencies
        ):
            raise ValueError("dependencies must be an array of obligations")
        dependencies = tuple(self.dependencies)
        if len({item.obligation_id for item in dependencies}) != len(dependencies):
            raise ValueError("duplicate obligation_id")
        if any(item.supplier_id == self.claim_id for item in dependencies):
            raise ValueError("claim cannot depend on itself")
        object.__setattr__(self, "dependencies", dependencies)
        object.__setattr__(
            self, "supersedes", strings(self.supersedes, "supersedes", ids=True)
        )
        if self.claim_id in self.supersedes:
            raise ValueError("claim cannot supersede itself")
        text(self.remaining_gap, "remaining_gap", optional=True)

    @classmethod
    def from_dict(cls, value: Any) -> ClaimSpec:
        data = object_fields(
            value,
            set(cls.__dataclass_fields__),
            {"claim_id", "contract", "author"},
            "claim",
        )
        data["contract"] = MathematicalContract.from_dict(data["contract"])
        dependencies = data.get("dependencies", [])
        if not isinstance(dependencies, (tuple, list)):
            raise ValueError("dependencies must be an array")
        data["dependencies"] = tuple(
            Obligation.from_dict(item) for item in dependencies
        )
        data["quantitative_costs"] = QuantitativeCosts.from_dict(
            data.get("quantitative_costs", {})
        )
        return cls(**data)

    def to_dict(self) -> dict[str, Any]:
        return json.loads(json_text(asdict(self)))


def compatibility_issues(supplier: ClaimSpec, obligation: Obligation) -> list[str]:
    """Conservative syntactic checks; no assertion of mathematical equivalence.

    A helper may require fewer assumptions. Different prose, domains, or
    quantifier order need an explicit bridge claim rather than fuzzy matching.
    Quantitative inequalities are judged separately by a recorded reviewer.
    """
    offered, required = supplier.contract, obligation.contract
    issues = []
    for key in ("statement", "domain", "quantifiers"):
        if getattr(offered, key) != getattr(required, key):
            issues.append(f"{key}_mismatch")
    if not set(offered.hypotheses).issubset(required.hypotheses):
        issues.append("extra_hypotheses")
    for key, requirement in asdict(obligation.quantitative_requirements).items():
        if (
            requirement.strip()
            and not getattr(supplier.quantitative_costs, key).strip()
        ):
            issues.append(f"unknown_cost:{key}")
    return issues
