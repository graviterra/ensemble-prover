"""Pure, versioned projection of research-graph routes into executable work.

This module is intentionally a leaf-side compiler over JSON-compatible graph
records.  It never calls ``ProofGraph.work_frontier`` or
``ProofSearchState.work_frontier`` because those APIs may mutate live search
state.  Shadow projection can therefore be run for any mathematical domain
without changing the graph, dossier, scheduler, or proof state.

The projector is conservative by construction:

* an uncertified proposition may become a goal, never a usable fact;
* a ``proved`` status without pinned certificate evidence is not trusted;
* missing local context, preflight, assembly, or dependency records becomes
  explicit authoring/repair work instead of being silently discarded; and
* every legacy-open route is classified and contributes projection debt until
  it has executable work or a terminal disposition.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from dataclasses import asdict, dataclass, field
from typing import Any, Dict, Mapping, Sequence, Tuple

from .proof_graph import ProofGraph
from .proof_state import (
    ProofSearchState,
    canonicalize_lean_statement_for_identity,
    lean_statement_bound_names,
)


GRAPH_EXECUTION_SCHEMA_VERSION = 1
_CERTIFICATE_KINDS = frozenset({"verified_helper", "lean_proof"})
_ACCEPTANCE_KINDS = frozenset({"target_preflight", "certificate"})
_SLOT_RESOLUTION_KINDS = frozenset(
    {
        "missing_dependency",
        "ambiguous_dependency",
        "invalid_dependency",
        "certificate",
        "terminal_dependency",
        "unresolved_goal",
    }
)
GRAPH_PROJECTION_METRICS = (
    "mini_graph_projection_routes_total",
    "mini_graph_projection_routes_active",
    "mini_graph_projection_debt_before",
    "mini_graph_projection_debt",
    "mini_graph_projection_executable_obligations",
    "mini_graph_projection_work_items",
    "mini_graph_projection_dangling_dependencies",
)

SYNTAX_STATUSES = frozenset(
    {"lean_executable", "needs_elaboration", "needs_formalization", "invalid"}
)
TRUTH_STATUSES = frozenset({"certified", "candidate", "contradicted", "rejected"})
EXECUTION_INTENTS = frozenset(
    {
        "prove_required",
        "adjudicate_candidate",
        "formalize_statement",
        "assemble_parent",
        "measure_helper_impact",
    }
)
ACTIVATION_STATUSES = frozenset(
    {"research_draft", "candidate", "active", "parked", "archived"}
)

_TERMINAL_ROUTE_STATUSES = frozenset(
    {"proved", "failed", "rejected", "contradicted", "retired", "obsolete"}
)
_TERMINAL_DEPENDENCY_STATUSES = frozenset(
    {"failed", "rejected", "contradicted", "retired", "obsolete"}
)
_IDENTIFIER_RE = re.compile(r"(?<![\w'])[^\W\d]\w*'*(?![\w'])")
_PROSE_PREFIX_RE = re.compile(
    r"^(?:repair|find|show how|explain|derive|formalize|construct|investigate|"
    r"prove or refute|replace)\b",
    re.IGNORECASE,
)


def _canonical_value(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {
            str(key): _canonical_value(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if isinstance(value, (list, tuple)):
        return [_canonical_value(item) for item in value]
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    return str(value)


def _canonical_json(value: Any) -> str:
    return json.dumps(
        _canonical_value(value),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _semantic_graph_record(record: Mapping[str, Any]) -> Dict[str, Any]:
    """Canonicalize unordered graph collections for stable semantic hashes."""

    canonical = copy.deepcopy(dict(record))
    for key in ("nodes", "edges", "attempts", "branch_frames"):
        raw = canonical.get(key)
        if isinstance(raw, Sequence) and not isinstance(raw, (str, bytes)):
            canonical[key] = sorted(
                (_canonical_value(item) for item in raw),
                key=_canonical_json,
            )
    return canonical


def _text(value: Any) -> str:
    return str(value or "").strip()


def _statement_context_hash(
    statement: str,
    local_context: Sequence[str] = (),
) -> str:
    canonical_statement = (
        canonicalize_lean_statement_for_identity(statement) or _text(statement)
    )
    return _digest(
        {
            "statement": canonical_statement,
            "local_context": [_text(item) for item in local_context if _text(item)],
        }
    )


def _normalized_payload_context(payload: Mapping[str, Any]) -> Tuple[str, ...]:
    raw_context = payload.get("local_hypotheses")
    if not (
        isinstance(raw_context, Sequence)
        and not isinstance(raw_context, (str, bytes))
    ):
        return ()
    context = []
    for item in raw_context:
        if isinstance(item, Mapping):
            name = _text(item.get("name"))
            typ = _text(item.get("type"))
            rendered = f"{name} : {typ}" if name and typ else ""
        else:
            rendered = _text(item)
        if rendered:
            context.append(rendered)
    return tuple(context)


def _int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return int(default)


def _float(value: Any, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return float(default)


def _require_schema(record: Mapping[str, Any]) -> None:
    raw_version = record.get("schema_version")
    if isinstance(raw_version, bool) or not isinstance(raw_version, int):
        raise ValueError("graph-execution schema_version must be an integer")
    version = raw_version
    if version != GRAPH_EXECUTION_SCHEMA_VERSION:
        raise ValueError(
            f"unsupported graph-execution schema_version={version}; "
            f"expected {GRAPH_EXECUTION_SCHEMA_VERSION}"
        )


def _positive_int_field(record: Mapping[str, Any], key: str) -> int:
    value = record.get(key)
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError(f"{key} must be an integer >= 1")
    return value


@dataclass(frozen=True)
class PinnedCertificateRef:
    schema_version: int
    graph_node_id: str
    statement_hash: str
    certificate_kind: str
    certificate_id: str
    proof_hash: str
    source_hash: str
    lean_acceptance_hash: str
    declaration_signature_hash: str
    project_environment_hash: str

    def to_record(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "PinnedCertificateRef":
        _require_schema(record)
        certificate = cls(
            schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
            graph_node_id=_text(record.get("graph_node_id")),
            statement_hash=_text(record.get("statement_hash")),
            certificate_kind=_text(record.get("certificate_kind")),
            certificate_id=_text(record.get("certificate_id")),
            proof_hash=_text(record.get("proof_hash")),
            source_hash=_text(record.get("source_hash")),
            lean_acceptance_hash=_text(record.get("lean_acceptance_hash")),
            declaration_signature_hash=_text(
                record.get("declaration_signature_hash")
            ),
            project_environment_hash=_text(record.get("project_environment_hash")),
        )
        required = (
            certificate.graph_node_id,
            certificate.statement_hash,
            certificate.certificate_kind,
            certificate.certificate_id,
            certificate.proof_hash,
            certificate.source_hash,
            certificate.lean_acceptance_hash,
            certificate.declaration_signature_hash,
            certificate.project_environment_hash,
        )
        if not all(required):
            raise ValueError("pinned certificate is missing required provenance")
        if certificate.certificate_kind not in _CERTIFICATE_KINDS:
            raise ValueError("unsupported pinned certificate kind")
        if certificate.statement_hash != certificate.declaration_signature_hash:
            raise ValueError("certificate declaration identity mismatch")
        return certificate


def pinned_certificate_ref(
    *,
    graph_node_id: str,
    statement: str,
    certificate_kind: str,
    certificate_id: str,
    proof_hash: str,
    source_hash: str,
    lean_acceptance_hash: str,
    project_environment_hash: str,
    local_context: Sequence[str] = (),
    declaration_signature_hash: str = "",
) -> PinnedCertificateRef:
    """Build the record persisted by a trusted Lean-certificate boundary."""

    statement_text = _text(statement)
    context = tuple(_text(item) for item in local_context if _text(item))
    computed_declaration_signature_hash = _statement_context_hash(
        statement_text,
        context,
    )
    if declaration_signature_hash and (
        _text(declaration_signature_hash) != computed_declaration_signature_hash
    ):
        raise ValueError("declaration signature does not match statement/context")
    certificate = PinnedCertificateRef(
        schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
        graph_node_id=_text(graph_node_id),
        statement_hash=computed_declaration_signature_hash,
        certificate_kind=_text(certificate_kind),
        certificate_id=_text(certificate_id),
        proof_hash=_text(proof_hash),
        source_hash=_text(source_hash),
        lean_acceptance_hash=_text(lean_acceptance_hash),
        declaration_signature_hash=computed_declaration_signature_hash,
        project_environment_hash=_text(project_environment_hash),
    )
    return PinnedCertificateRef.from_record(certificate.to_record())


def lean_acceptance_ref(
    *,
    artifact_kind: str,
    statement: str,
    local_context: Sequence[str] = (),
    project_environment_hash: str,
    lean_acceptance_hash: str,
    proof_hash: str = "",
    source_hash: str = "",
) -> Dict[str, str | int]:
    """Build a typed registry entry supplied by the trusted Lean boundary."""

    kind = _text(artifact_kind)
    if kind not in _ACCEPTANCE_KINDS:
        raise ValueError("unsupported Lean acceptance artifact kind")
    record: Dict[str, str | int] = {
        "schema_version": GRAPH_EXECUTION_SCHEMA_VERSION,
        "artifact_kind": kind,
        "statement_context_hash": _statement_context_hash(
            statement,
            local_context,
        ),
        "project_environment_hash": _text(project_environment_hash),
        "lean_acceptance_hash": _text(lean_acceptance_hash),
        "proof_hash": _text(proof_hash),
        "source_hash": _text(source_hash),
    }
    if not all(
        (
            record["statement_context_hash"],
            record["project_environment_hash"],
            record["lean_acceptance_hash"],
        )
    ) or (
        kind == "certificate"
        and not (record["proof_hash"] and record["source_hash"])
    ):
        raise ValueError("Lean acceptance registry entry is incomplete")
    return record


def _trusted_acceptance_registry(
    records: Sequence[Mapping[str, Any]],
) -> frozenset[Tuple[str, str, str, str, str, str]]:
    if isinstance(records, (str, bytes)):
        raise ValueError("trusted Lean acceptances must be typed records")
    out = set()
    for raw in records:
        if not isinstance(raw, Mapping):
            raise ValueError("trusted Lean acceptances must be typed records")
        _require_schema(raw)
        kind = _text(raw.get("artifact_kind"))
        entry = (
            kind,
            _text(raw.get("lean_acceptance_hash")),
            _text(raw.get("statement_context_hash")),
            _text(raw.get("project_environment_hash")),
            _text(raw.get("proof_hash")),
            _text(raw.get("source_hash")),
        )
        if kind not in _ACCEPTANCE_KINDS or not all(entry[:4]):
            raise ValueError("invalid trusted Lean acceptance record")
        if kind == "certificate" and not all(entry[4:]):
            raise ValueError("certificate acceptance lacks proof/source binding")
        out.add(entry)
    return frozenset(out)


@dataclass(frozen=True)
class RouteDependencySlot:
    schema_version: int
    slot_id: str
    ordinal: int
    role: str
    graph_node_id: str
    expected_statement_hash: str
    resolution_kind: str
    pinned_certificate: PinnedCertificateRef | None = None

    def to_record(self) -> Dict[str, Any]:
        record = asdict(self)
        record["pinned_certificate"] = (
            self.pinned_certificate.to_record() if self.pinned_certificate else None
        )
        return record

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RouteDependencySlot":
        _require_schema(record)
        raw_certificate = record.get("pinned_certificate")
        if raw_certificate is not None and not isinstance(raw_certificate, Mapping):
            raise ValueError("slot pinned_certificate must be a record or null")
        certificate = (
            PinnedCertificateRef.from_record(raw_certificate)
            if isinstance(raw_certificate, Mapping)
            else None
        )
        slot = cls(
            schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
            slot_id=_text(record.get("slot_id")),
            ordinal=_positive_int_field(record, "ordinal"),
            role=_text(record.get("role")),
            graph_node_id=_text(record.get("graph_node_id")),
            expected_statement_hash=_text(record.get("expected_statement_hash")),
            resolution_kind=_text(record.get("resolution_kind")),
            pinned_certificate=certificate,
        )
        if not all(
            (
                slot.slot_id,
                slot.ordinal > 0,
                slot.role,
                slot.graph_node_id,
                slot.resolution_kind,
            )
        ):
            raise ValueError("route dependency slot is incomplete")
        if slot.resolution_kind not in _SLOT_RESOLUTION_KINDS:
            raise ValueError("unsupported route dependency resolution kind")
        if slot.resolution_kind in {
            "missing_dependency",
            "ambiguous_dependency",
            "invalid_dependency",
        }:
            if slot.expected_statement_hash or certificate is not None:
                raise ValueError("missing dependency slot has unexpected evidence")
        elif not slot.expected_statement_hash:
            raise ValueError("non-missing dependency slot lacks statement identity")
        if slot.resolution_kind == "certificate":
            if certificate is None:
                raise ValueError("certificate slot lacks pinned certificate")
            if certificate.graph_node_id != slot.graph_node_id:
                raise ValueError("slot certificate graph node does not match slot")
            if certificate.statement_hash != slot.expected_statement_hash:
                raise ValueError("slot certificate statement does not match slot")
        elif certificate is not None:
            raise ValueError("non-certificate slot carries pinned certificate")
        return slot


def _route_contract_seed(
    *,
    route_id: str,
    root_target_hash: str,
    route_revision: int,
    slots: Sequence[RouteDependencySlot],
    assembly: Mapping[str, Any],
) -> Dict[str, Any]:
    return {
        "schema_version": GRAPH_EXECUTION_SCHEMA_VERSION,
        "route_id": route_id,
        "root_target_hash": root_target_hash,
        "route_revision": route_revision,
        "slots": [slot.to_record() for slot in slots],
        "assembly": _canonical_value(dict(assembly)),
    }


@dataclass(frozen=True)
class RouteExecutionContractV2:
    schema_version: int
    contract_id: str
    route_id: str
    root_target_statement: str
    root_target_hash: str
    route_revision: int
    predecessor_contract_id: str
    slots: Tuple[RouteDependencySlot, ...]
    assembly: Dict[str, Any] = field(default_factory=dict)

    def to_record(self) -> Dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "contract_id": self.contract_id,
            "route_id": self.route_id,
            "root_target_statement": self.root_target_statement,
            "root_target_hash": self.root_target_hash,
            "route_revision": self.route_revision,
            "predecessor_contract_id": self.predecessor_contract_id,
            "slots": [slot.to_record() for slot in self.slots],
            "assembly": copy.deepcopy(self.assembly),
        }

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RouteExecutionContractV2":
        _require_schema(record)
        raw_slots = record.get("slots")
        if not (
            isinstance(raw_slots, Sequence)
            and not isinstance(raw_slots, (str, bytes))
            and raw_slots
            and all(isinstance(item, Mapping) for item in raw_slots)
        ):
            raise ValueError("route execution contract slots must be nonempty records")
        slots = tuple(
            RouteDependencySlot.from_record(item)
            for item in list(raw_slots)
        )
        assembly = record.get("assembly")
        if not isinstance(assembly, Mapping):
            raise ValueError("route execution contract assembly must be a record")
        contract = cls(
            schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
            contract_id=_text(record.get("contract_id")),
            route_id=_text(record.get("route_id")),
            root_target_statement=_text(record.get("root_target_statement")),
            root_target_hash=_text(record.get("root_target_hash")),
            route_revision=_positive_int_field(record, "route_revision"),
            predecessor_contract_id=_text(record.get("predecessor_contract_id")),
            slots=slots,
            assembly=copy.deepcopy(dict(assembly)) if isinstance(assembly, Mapping) else {},
        )
        if not all(
            (
                contract.contract_id,
                contract.route_id,
                contract.root_target_statement,
                contract.root_target_hash,
                contract.slots,
            )
        ):
            raise ValueError("route execution contract is incomplete")
        if [slot.ordinal for slot in contract.slots] != list(
            range(1, len(contract.slots) + 1)
        ) or len({slot.slot_id for slot in contract.slots}) != len(contract.slots):
            raise ValueError("route execution contract slot ordering is invalid")
        expected_target_hash = _digest(
            canonicalize_lean_statement_for_identity(contract.root_target_statement)
            or contract.root_target_statement
        )
        if contract.root_target_hash != expected_target_hash:
            raise ValueError("route execution contract target hash mismatch")
        expected_contract_id = (
            "route-contract:"
            + _digest(
                _route_contract_seed(
                    route_id=contract.route_id,
                    root_target_hash=contract.root_target_hash,
                    route_revision=contract.route_revision,
                    slots=contract.slots,
                    assembly=contract.assembly,
                )
            )[:24]
        )
        if contract.contract_id != expected_contract_id:
            raise ValueError("route execution contract identity mismatch")
        return contract


@dataclass(frozen=True)
class RouteSlotBinding:
    schema_version: int
    binding_id: str
    route_id: str
    contract_id: str
    route_revision: int
    slot_id: str
    graph_node_id: str
    status: str
    status_version: int
    resolution_kind: str
    goal_identity_hash: str = ""
    work_id: str = ""
    certificate_id: str = ""
    reason: str = ""

    def to_record(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "RouteSlotBinding":
        _require_schema(record)
        binding = cls(
            schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
            binding_id=_text(record.get("binding_id")),
            route_id=_text(record.get("route_id")),
            contract_id=_text(record.get("contract_id")),
            route_revision=_positive_int_field(record, "route_revision"),
            slot_id=_text(record.get("slot_id")),
            graph_node_id=_text(record.get("graph_node_id")),
            status=_text(record.get("status")),
            status_version=_positive_int_field(record, "status_version"),
            resolution_kind=_text(record.get("resolution_kind")),
            goal_identity_hash=_text(record.get("goal_identity_hash")),
            work_id=_text(record.get("work_id")),
            certificate_id=_text(record.get("certificate_id")),
            reason=_text(record.get("reason")),
        )
        if not all(
            (
                binding.binding_id,
                binding.route_id,
                binding.contract_id,
                binding.slot_id,
                binding.graph_node_id,
                binding.status,
                binding.resolution_kind,
            )
        ):
            raise ValueError("route slot binding is incomplete")
        expected_binding_id = "route-binding:" + _digest(
            [
                binding.contract_id,
                binding.route_id,
                binding.route_revision,
                binding.slot_id,
                binding.graph_node_id,
            ]
        )[:24]
        if binding.binding_id != expected_binding_id:
            raise ValueError("route slot binding identity mismatch")
        tagged_payloads = sum(
            bool(value)
            for value in (
                binding.goal_identity_hash,
                binding.work_id,
                binding.certificate_id,
            )
        )
        if tagged_payloads != 1:
            raise ValueError("route slot binding must have exactly one resolution")
        expected_tag = {
            "certificate": "certificate_id",
            "goal": "goal_identity_hash",
            "authoring_work": "work_id",
            "terminal": "work_id",
        }.get(binding.resolution_kind)
        actual_tag = (
            "certificate_id"
            if binding.certificate_id
            else "goal_identity_hash"
            if binding.goal_identity_hash
            else "work_id"
        )
        if expected_tag is None or expected_tag != actual_tag:
            raise ValueError("route slot binding resolution tag mismatch")
        expected_status = {
            "certificate": "resolved",
            "goal": "executable",
            "authoring_work": "blocked",
            "terminal": "terminal",
        }[binding.resolution_kind]
        if binding.status != expected_status:
            raise ValueError("route slot binding status/resolution mismatch")
        return binding


@dataclass(frozen=True)
class GraphExecutionObligation:
    schema_version: int
    obligation_id: str
    target_statement: str
    local_context: Tuple[str, ...]
    normalized_goal_payload: Dict[str, Any]
    goal_identity_hash: str
    context_origin: str
    context_origin_hash: str
    origin_graph_node_id: str
    route_id: str
    route_contract_id: str
    route_revision: int
    dependency_slot_id: str
    route_slot_binding_id: str
    syntax_status: str
    truth_status: str
    execution_intent: str
    expected_parent_effect: str
    semantic_evidence_hash: str
    root_statement: str
    root_statement_hash: str
    project_environment_hash: str
    priority: float

    def __post_init__(self) -> None:
        if self.syntax_status not in SYNTAX_STATUSES:
            raise ValueError(f"invalid syntax_status={self.syntax_status!r}")
        if self.truth_status not in TRUTH_STATUSES:
            raise ValueError(f"invalid truth_status={self.truth_status!r}")
        if self.truth_status == "certified":
            raise ValueError(
                "certified dependencies resolve route slots and are not proof goals"
            )
        if self.execution_intent not in EXECUTION_INTENTS:
            raise ValueError(f"invalid execution_intent={self.execution_intent!r}")

    def to_record(self) -> Dict[str, Any]:
        return asdict(self)

    def to_prompt_obligation(self) -> Any:
        """Adapt the internal execution contract to the existing prompt type."""

        if self.syntax_status != "lean_executable":
            raise ValueError("only Lean-executable obligations may enter prompts")
        from .types import ExecutableObligation

        local_context = list(self.local_context)
        contextualized_statement = self.target_statement
        for item in reversed(local_context):
            if ":=" in item:
                contextualized_statement = f"let {item}; {contextualized_statement}"
            elif (
                (item.startswith("[") and item.endswith("]"))
                or (item.startswith("{") and item.endswith("}"))
                or (item.startswith("(") and item.endswith(")"))
            ):
                contextualized_statement = f"∀ {item}, {contextualized_statement}"
            else:
                contextualized_statement = f"∀ ({item}), {contextualized_statement}"
        return ExecutableObligation(
            obligation_id=self.obligation_id,
            statement=contextualized_statement,
            original_statement=self.target_statement,
            source="graph_execution_projection",
            sources=[self.origin_graph_node_id, self.route_id],
            roles=[self.execution_intent],
            binding_state="binding",
            admission_mode="typed_graph_projection",
            validated=True,
            solved=False,
            dependency_ids=[self.dependency_slot_id],
            score=self.priority,
        )

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "GraphExecutionObligation":
        _require_schema(record)
        payload = record.get("normalized_goal_payload")
        obligation = cls(
            schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
            obligation_id=_text(record.get("obligation_id")),
            target_statement=_text(record.get("target_statement")),
            local_context=tuple(
                _text(item)
                for item in list(record.get("local_context") or ())
                if _text(item)
            ),
            normalized_goal_payload=(
                copy.deepcopy(dict(payload)) if isinstance(payload, Mapping) else {}
            ),
            goal_identity_hash=_text(record.get("goal_identity_hash")),
            context_origin=_text(record.get("context_origin")),
            context_origin_hash=_text(record.get("context_origin_hash")),
            origin_graph_node_id=_text(record.get("origin_graph_node_id")),
            route_id=_text(record.get("route_id")),
            route_contract_id=_text(record.get("route_contract_id")),
            route_revision=_positive_int_field(record, "route_revision"),
            dependency_slot_id=_text(record.get("dependency_slot_id")),
            route_slot_binding_id=_text(record.get("route_slot_binding_id")),
            syntax_status=_text(record.get("syntax_status")),
            truth_status=_text(record.get("truth_status")),
            execution_intent=_text(record.get("execution_intent")),
            expected_parent_effect=_text(record.get("expected_parent_effect")),
            semantic_evidence_hash=_text(record.get("semantic_evidence_hash")),
            root_statement=_text(record.get("root_statement")),
            root_statement_hash=_text(record.get("root_statement_hash")),
            project_environment_hash=_text(record.get("project_environment_hash")),
            priority=_float(record.get("priority")),
        )
        if not all(
            (
                obligation.obligation_id,
                obligation.target_statement,
                obligation.normalized_goal_payload,
                obligation.goal_identity_hash,
                obligation.context_origin,
                obligation.context_origin_hash,
                obligation.origin_graph_node_id,
                obligation.route_id,
                obligation.route_contract_id,
                obligation.dependency_slot_id,
                obligation.route_slot_binding_id,
                obligation.expected_parent_effect,
                obligation.semantic_evidence_hash,
                obligation.root_statement,
                obligation.root_statement_hash,
                obligation.project_environment_hash,
            )
        ):
            raise ValueError("graph execution obligation is incomplete")
        expected_binding_id = "route-binding:" + _digest(
            [
                obligation.route_contract_id,
                obligation.route_id,
                obligation.route_revision,
                obligation.dependency_slot_id,
                obligation.origin_graph_node_id,
            ]
        )[:24]
        expected_goal_identity = _digest(
            {
                "normalized_goal": obligation.normalized_goal_payload,
                "context_origin_hash": obligation.context_origin_hash,
                "project_environment_hash": obligation.project_environment_hash,
            }
        )
        expected_obligation_id = "graph-obligation:" + _digest(
            [
                expected_binding_id,
                expected_goal_identity,
                obligation.syntax_status,
                obligation.truth_status,
                obligation.execution_intent,
                obligation.expected_parent_effect,
                obligation.route_contract_id,
                obligation.origin_graph_node_id,
                obligation.context_origin,
                obligation.semantic_evidence_hash,
                obligation.root_statement_hash,
            ]
        )[:24]
        if (
            obligation.route_slot_binding_id != expected_binding_id
            or obligation.goal_identity_hash != expected_goal_identity
            or obligation.obligation_id != expected_obligation_id
        ):
            raise ValueError("graph execution obligation identity mismatch")
        if obligation.context_origin_hash != _digest(list(obligation.local_context)):
            raise ValueError("graph execution obligation context identity mismatch")
        payload_target = _text(
            obligation.normalized_goal_payload.get("target_expr")
        )
        if (
            canonicalize_lean_statement_for_identity(payload_target)
            != canonicalize_lean_statement_for_identity(
                obligation.target_statement
            )
        ):
            raise ValueError("graph execution obligation target payload mismatch")
        expected_root_hash = _digest(
            canonicalize_lean_statement_for_identity(obligation.root_statement)
            or obligation.root_statement
        )
        if obligation.root_statement_hash != expected_root_hash:
            raise ValueError("graph execution obligation root identity mismatch")
        expected_goal_payload = ProofSearchState(
            theorem_name="graph_execution_contract_validation",
            root_statement=obligation.root_statement,
        )._goal_signature(
            obligation.target_statement,
            obligation.local_context,
            source_failure="graph_execution_projection",
        ).to_execution_record()
        if _canonical_json(obligation.normalized_goal_payload) != _canonical_json(
            expected_goal_payload
        ):
            raise ValueError("graph execution obligation normalized payload mismatch")
        return obligation


@dataclass(frozen=True)
class ProjectionWorkItem:
    schema_version: int
    work_id: str
    route_id: str
    graph_node_id: str
    slot_id: str
    work_type: str
    reason: str
    target_statement: str = ""

    def to_record(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class ActivationDecision:
    schema_version: int
    decision_id: str
    route_id: str
    expected_route_revision: int
    prior_status: str
    next_status: str
    owner: str
    evidence_hash: str
    reason: str
    wake_condition: str = ""

    def __post_init__(self) -> None:
        if self.prior_status not in ACTIVATION_STATUSES:
            raise ValueError(f"invalid prior activation status={self.prior_status!r}")
        if self.next_status not in ACTIVATION_STATUSES:
            raise ValueError(f"invalid next activation status={self.next_status!r}")
        if self.next_status == "parked" and not self.wake_condition:
            raise ValueError("parking a route requires a wake condition")
        allowed_transitions = {
            "research_draft": {"candidate", "parked", "archived"},
            "candidate": {"active", "parked", "archived"},
            "active": {"parked", "archived"},
            "parked": {"candidate", "active", "archived"},
            "archived": set(),
        }
        if self.next_status not in allowed_transitions[self.prior_status]:
            raise ValueError(
                "illegal activation transition: "
                f"{self.prior_status}->{self.next_status}"
            )
        if not all(
            (
                self.route_id,
                self.owner,
                self.evidence_hash,
                self.reason,
            )
        ):
            raise ValueError("activation decision is incomplete")

    def to_record(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def create(
        cls,
        *,
        route_id: str,
        expected_route_revision: int,
        prior_status: str,
        next_status: str,
        owner: str,
        evidence_hash: str,
        reason: str,
        wake_condition: str = "",
    ) -> "ActivationDecision":
        seed = {
            "schema_version": GRAPH_EXECUTION_SCHEMA_VERSION,
            "route_id": _text(route_id),
            "expected_route_revision": max(1, _int(expected_route_revision, 1)),
            "prior_status": _text(prior_status),
            "next_status": _text(next_status),
            "owner": _text(owner),
            "evidence_hash": _text(evidence_hash),
            "reason": _text(reason),
            "wake_condition": _text(wake_condition),
        }
        return cls(
            decision_id=f"activation-decision:{_digest(seed)[:24]}",
            **seed,
        )

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "ActivationDecision":
        _require_schema(record)
        decision = cls(
            schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
            decision_id=_text(record.get("decision_id")),
            route_id=_text(record.get("route_id")),
            expected_route_revision=_positive_int_field(
                record,
                "expected_route_revision",
            ),
            prior_status=_text(record.get("prior_status")),
            next_status=_text(record.get("next_status")),
            owner=_text(record.get("owner")),
            evidence_hash=_text(record.get("evidence_hash")),
            reason=_text(record.get("reason")),
            wake_condition=_text(record.get("wake_condition")),
        )
        expected = cls.create(
            route_id=decision.route_id,
            expected_route_revision=decision.expected_route_revision,
            prior_status=decision.prior_status,
            next_status=decision.next_status,
            owner=decision.owner,
            evidence_hash=decision.evidence_hash,
            reason=decision.reason,
            wake_condition=decision.wake_condition,
        )
        if not all(
            (
                decision.route_id,
                decision.owner,
                decision.evidence_hash,
                decision.reason,
            )
        ) or decision.decision_id != expected.decision_id:
            raise ValueError("activation decision is incomplete or has stale identity")
        return decision


@dataclass(frozen=True)
class RouteProjectionResult:
    schema_version: int
    route_id: str
    activation_status: str
    lifecycle_status: str
    classification: str
    projection_debt: bool
    contract: RouteExecutionContractV2 | None
    bindings: Tuple[RouteSlotBinding, ...]
    obligations: Tuple[GraphExecutionObligation, ...]
    work_items: Tuple[ProjectionWorkItem, ...]
    required_node_ids: Tuple[str, ...]
    dangling_node_ids: Tuple[str, ...]

    def __post_init__(self) -> None:
        if self.activation_status not in ACTIVATION_STATUSES:
            raise ValueError(f"invalid activation_status={self.activation_status!r}")

    def to_record(self) -> Dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "route_id": self.route_id,
            "activation_status": self.activation_status,
            "lifecycle_status": self.lifecycle_status,
            "classification": self.classification,
            "projection_debt": self.projection_debt,
            "contract": self.contract.to_record() if self.contract else None,
            "bindings": [item.to_record() for item in self.bindings],
            "obligations": [item.to_record() for item in self.obligations],
            "work_items": [item.to_record() for item in self.work_items],
            "required_node_ids": list(self.required_node_ids),
            "dangling_node_ids": list(self.dangling_node_ids),
        }


@dataclass(frozen=True)
class GraphProjectionReport:
    schema_version: int
    theorem_name: str
    input_graph_digest: str
    project_environment_hash: str
    acceptance_registry_hash: str
    route_results: Tuple[RouteProjectionResult, ...]
    counts: Dict[str, int]
    unique_required_node_ids: Tuple[str, ...]
    dangling_required_node_ids: Tuple[str, ...]
    input_unchanged: bool

    def to_record(self) -> Dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "theorem_name": self.theorem_name,
            "input_graph_digest": self.input_graph_digest,
            "project_environment_hash": self.project_environment_hash,
            "acceptance_registry_hash": self.acceptance_registry_hash,
            "route_results": [item.to_record() for item in self.route_results],
            "counts": dict(sorted(self.counts.items())),
            "unique_required_node_ids": list(self.unique_required_node_ids),
            "dangling_required_node_ids": list(self.dangling_required_node_ids),
            "input_unchanged": self.input_unchanged,
        }

    @property
    def report_digest(self) -> str:
        return _digest(self.to_record())


def _route_activation(node: Mapping[str, Any]) -> str:
    metadata = node.get("metadata")
    metadata = dict(metadata) if isinstance(metadata, Mapping) else {}
    explicit = _text(metadata.get("activation_status"))
    if explicit in ACTIVATION_STATUSES:
        return explicit
    status = _text(node.get("status") or "open")
    if status in _TERMINAL_ROUTE_STATUSES:
        return "archived"
    # Compatibility migration policy: current generic-open routes were live
    # scheduler candidates, so shadow mode makes their execution debt visible.
    if status == "open":
        return "active"
    return "candidate"


def _route_has_projection_disposition(node: Mapping[str, Any]) -> bool:
    metadata = node.get("metadata")
    if not isinstance(metadata, Mapping):
        return False
    return bool(_text(metadata.get("graph_execution_projection_disposition")))


def _route_has_execution_projection_debt(
    *,
    activation_status: str,
    lifecycle_status: str,
    executable_obligation_count: int,
) -> bool:
    """Report active graph intent that has not reached executable proof work."""

    return bool(
        activation_status == "active"
        and executable_obligation_count <= 0
        and lifecycle_status not in {"executable", "ready_to_assemble"}
        and lifecycle_status not in _TERMINAL_ROUTE_STATUSES
    )


def _certificate_for_node(
    node: Mapping[str, Any],
    *,
    project_environment_hash: str,
    trusted_lean_acceptances: frozenset[Tuple[str, str, str, str, str, str]],
) -> PinnedCertificateRef | None:
    metadata = node.get("metadata")
    metadata = dict(metadata) if isinstance(metadata, Mapping) else {}
    if _text(node.get("status")) != "proved":
        return None
    raw_certificate = metadata.get("pinned_certificate")
    if not isinstance(raw_certificate, Mapping):
        return None
    try:
        certificate = PinnedCertificateRef.from_record(raw_certificate)
    except (TypeError, ValueError):
        return None
    statement = _text(node.get("statement"))
    local_context = _explicit_local_context(metadata)
    statement_hash = _statement_context_hash(
        statement,
        local_context,
    )
    if not all(
        (
            project_environment_hash,
            certificate.graph_node_id == _text(node.get("node_id")),
            certificate.statement_hash == statement_hash,
            certificate.declaration_signature_hash == statement_hash,
            certificate.proof_hash == _text(node.get("proof_hash")),
            certificate.source_hash == _text(node.get("source_hash")),
            certificate.project_environment_hash == project_environment_hash,
            (
                "certificate",
                certificate.lean_acceptance_hash,
                certificate.statement_hash,
                certificate.project_environment_hash,
                certificate.proof_hash,
                certificate.source_hash,
            )
            in trusted_lean_acceptances,
        )
    ):
        return None
    return certificate


def _explicit_local_context(metadata: Mapping[str, Any]) -> Tuple[str, ...]:
    raw = metadata.get("local_context")
    if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
        return ()
    out = []
    for item in raw:
        if isinstance(item, Mapping):
            name = _text(item.get("name"))
            typ = _text(item.get("type"))
            text = f"{name} : {typ}" if name and typ else ""
        else:
            text = _text(item)
        if text:
            out.append(text)
    return tuple(out)


def _local_context_bound_names(local_context: Sequence[str]) -> set[str]:
    names: set[str] = set()
    for item in local_context:
        head, separator, _tail = str(item or "").partition(":")
        if not separator:
            continue
        names.update(_IDENTIFIER_RE.findall(head))
    return names


def _lean_identifier_occurs(text: str, identifier: str) -> bool:
    if not identifier:
        return False
    return bool(
        re.search(
            rf"(?<![\w']){re.escape(identifier)}(?![\w'])",
            str(text or ""),
        )
    )


def _missing_root_context_names(
    root_statement: str,
    target_statement: str,
    local_context: Sequence[str] = (),
) -> Tuple[str, ...]:
    root_bound = set(lean_statement_bound_names(root_statement))
    if not root_bound:
        return ()
    target_bound = set(lean_statement_bound_names(target_statement))
    context_heads = [str(item or "").partition(":")[0] for item in local_context]
    context_bound = {
        name
        for name in root_bound
        if any(_lean_identifier_occurs(head, name) for head in context_heads)
    }
    used_text = "\n".join((target_statement, *tuple(local_context)))
    target_names = {
        name for name in root_bound if _lean_identifier_occurs(used_text, name)
    }
    return tuple(
        sorted((root_bound - target_bound - context_bound).intersection(target_names))
    )


def graph_target_preflight_evidence(
    target_statement: str,
    local_context: Sequence[str] = (),
    *,
    project_environment_hash: str,
    lean_acceptance_hash: str,
) -> Dict[str, str]:
    """Build the hashes a completed target-preflight operation must persist."""

    statement = _text(target_statement)
    context = tuple(_text(item) for item in local_context if _text(item))
    return {
        "target_preflight_status": "accepted_target",
        "target_preflight_statement_hash": _digest(
            canonicalize_lean_statement_for_identity(statement) or statement
        ),
        "target_preflight_context_hash": _digest(list(context)),
        "target_preflight_project_environment_hash": _text(
            project_environment_hash
        ),
        "target_preflight_lean_acceptance_hash": _text(lean_acceptance_hash),
    }


def _target_preflight_evidence_valid(
    metadata: Mapping[str, Any],
    *,
    target_statement: str,
    local_context: Sequence[str],
    project_environment_hash: str,
    trusted_lean_acceptances: frozenset[Tuple[str, str, str, str, str, str]],
) -> bool:
    if _text(metadata.get("target_preflight_status")) != "accepted_target":
        return False
    expected = graph_target_preflight_evidence(
        target_statement,
        local_context,
        project_environment_hash=project_environment_hash,
        lean_acceptance_hash=_text(
            metadata.get("target_preflight_lean_acceptance_hash")
        ),
    )
    return bool(
        expected["target_preflight_lean_acceptance_hash"]
        and expected["target_preflight_project_environment_hash"]
        and (
            "target_preflight",
            expected["target_preflight_lean_acceptance_hash"],
            _statement_context_hash(target_statement, local_context),
            expected["target_preflight_project_environment_hash"],
            "",
            "",
        )
        in trusted_lean_acceptances
    ) and all(
        _text(metadata.get(key)) == value
        for key, value in expected.items()
    )


def _syntax_status(
    node: Mapping[str, Any],
    *,
    target_statement: str,
    context_missing: bool,
    preflight_evidence_valid: bool,
) -> Tuple[str, str]:
    metadata = node.get("metadata")
    metadata = dict(metadata) if isinstance(metadata, Mapping) else {}
    if not target_statement:
        return "invalid", "missing_target_statement"
    if (
        bool(metadata.get("graph_native_statement_type_rejected"))
        or context_missing
    ):
        return "needs_elaboration", (
            "missing_local_context" if context_missing else "prior_target_type_rejection"
        )
    if (
        bool(metadata.get("nonexecutable_target_statement"))
        or _PROSE_PREFIX_RE.match(target_statement)
    ):
        return "needs_formalization", "nonexecutable_or_prose_target"
    explicit = _text(metadata.get("syntax_status"))
    if explicit in SYNTAX_STATUSES and explicit != "lean_executable":
        return explicit, "explicit_syntax_status"
    if preflight_evidence_valid:
        return "lean_executable", "accepted_target_evidence"
    return "needs_elaboration", "lean_target_preflight_required"


def _truth_status(node: Mapping[str, Any], certificate: PinnedCertificateRef | None) -> str:
    metadata = node.get("metadata")
    metadata = dict(metadata) if isinstance(metadata, Mapping) else {}
    if certificate is not None:
        return "certified"
    if bool(metadata.get("certified_contradiction")) or _text(node.get("status")) == "contradicted":
        return "contradicted"
    if _text(node.get("status")) == "rejected" and bool(metadata.get("invalid_target")):
        return "rejected"
    return "candidate"


def _work_item(
    *,
    route_id: str,
    graph_node_id: str,
    slot_id: str,
    work_type: str,
    reason: str,
    target_statement: str = "",
) -> ProjectionWorkItem:
    identity = {
        "schema_version": GRAPH_EXECUTION_SCHEMA_VERSION,
        "route_id": route_id,
        "graph_node_id": graph_node_id,
        "slot_id": slot_id,
        "work_type": work_type,
        "reason": reason,
        "target_statement": target_statement,
    }
    return ProjectionWorkItem(
        schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
        work_id=f"projection-work:{_digest(identity)[:24]}",
        route_id=route_id,
        graph_node_id=graph_node_id,
        slot_id=slot_id,
        work_type=work_type,
        reason=reason,
        target_statement=target_statement,
    )


def _legacy_contract_validation_reason(
    *,
    route_id: str,
    route_metadata: Mapping[str, Any],
    contract: Mapping[str, Any],
    nodes: Mapping[str, Mapping[str, Any]],
    edges: Sequence[Mapping[str, Any]],
    root_node_id: str,
    root_statement: str,
    statement_key: Any,
) -> str:
    route_scope = _text(route_metadata.get("route_scope"))
    contract_scope = _text(contract.get("scope"))
    if not route_scope:
        return "route scope is missing"
    if not contract_scope:
        return "contract scope is missing"
    if route_scope != contract_scope:
        return "route and contract scopes disagree"
    if route_scope not in {"root_assembly", "partial_route"}:
        return f"unsupported route contract scope: {route_scope}"
    target_node_id = _text(contract.get("target_node_id"))
    if not target_node_id:
        return "contract target_node_id is missing"
    if route_scope == "root_assembly":
        expected_target_node_id = root_node_id
        expected_target_statement = root_statement
    else:
        expected_target_node_id = target_node_id
        target_node = nodes.get(target_node_id)
        if target_node is None:
            return "partial-route target node is missing or ambiguous"
        expected_target_statement = _text(target_node.get("statement"))
    if target_node_id != expected_target_node_id:
        return "contract target_node_id does not match route scope target"
    target_statement = _text(contract.get("target_statement"))
    if not expected_target_statement:
        return "graph route target statement is missing"
    if (
        canonicalize_lean_statement_for_identity(target_statement)
        != canonicalize_lean_statement_for_identity(expected_target_statement)
    ):
        return "contract target statement does not match target node"
    target_statement_key = _text(contract.get("target_statement_key"))
    if not target_statement_key:
        return "contract target_statement_key is missing"
    if target_statement_key != statement_key(expected_target_statement):
        return "contract target_statement_key does not match target node"
    raw_required = list(contract.get("required_node_ids") or ())
    if not all(isinstance(item, str) and item.strip() for item in raw_required):
        return "required_node_ids must contain only nonempty strings"
    required_ids = list(dict.fromkeys(item.strip() for item in raw_required))
    if len(required_ids) != len(raw_required):
        return "required_node_ids contains duplicates"
    if list(contract.get("required_helper_names") or ()):
        return "legacy helper-name dependencies require contract migration"
    if "required_obligation_count" in contract:
        try:
            declared_count = int(contract.get("required_obligation_count"))
        except (TypeError, ValueError):
            return "required_obligation_count is invalid"
        if declared_count != len(required_ids):
            return "required_obligation_count does not match dependencies"
    dependency_ids = {
        _text(edge.get("target"))
        for edge in edges
        if _text(edge.get("source")) == route_id
        and _text(edge.get("kind"))
        in {"route_requires", "route_blocked_by", "route_replan"}
    }
    if set(required_ids) - dependency_ids:
        return "contract dependencies are missing graph edges"
    internal_ids = {
        _text(route_metadata.get("route_assembly_contract_replan_id")),
        _text(
            route_metadata.get("route_assembly_contract_replan_obligation_id")
        ),
    }
    internal_ids.discard("")
    if dependency_ids - set(required_ids) - internal_ids:
        return "graph dependency edges are absent from contract"
    return ""


def project_graph_execution_shadow(
    graph_record: Mapping[str, Any],
    *,
    project_environment_hash: str = "",
    trusted_lean_acceptances: Sequence[Mapping[str, Any]] = (),
) -> GraphProjectionReport:
    """Classify every strategy route without mutating the supplied record."""

    if not isinstance(graph_record, Mapping):
        raise TypeError("graph_record must be a mapping")
    snapshot = copy.deepcopy(dict(graph_record))
    trusted_acceptance_registry = _trusted_acceptance_registry(
        trusted_lean_acceptances
    )
    acceptance_registry_hash = _digest(sorted(trusted_acceptance_registry))
    if "schema_version" in snapshot:
        version = _int(snapshot.get("schema_version"), 0)
        if version != GRAPH_EXECUTION_SCHEMA_VERSION:
            raise ValueError(
                f"unsupported proof-graph schema_version={version}; "
                f"expected {GRAPH_EXECUTION_SCHEMA_VERSION}"
            )
    input_digest = _digest(_semantic_graph_record(snapshot))
    theorem_name = _text(snapshot.get("theorem_name") or "mini")
    root_statement = _text(snapshot.get("root_statement"))
    root_node_id = _text(snapshot.get("root_node_id") or "root")
    root_statement_hash = _digest(
        canonicalize_lean_statement_for_identity(root_statement) or root_statement
    )
    raw_nodes = [
        dict(item)
        for item in list(snapshot.get("nodes") or ())
        if isinstance(item, Mapping)
    ]
    node_groups: Dict[str, list[Dict[str, Any]]] = {}
    for item in raw_nodes:
        node_id = _text(item.get("node_id"))
        if node_id:
            node_groups.setdefault(node_id, []).append(item)
    ambiguous_node_ids = {
        node_id for node_id, group in node_groups.items() if len(group) != 1
    }
    nodes = {
        node_id: group[0]
        for node_id, group in node_groups.items()
        if len(group) == 1
    }
    raw_edges = [
        dict(item)
        for item in list(snapshot.get("edges") or ())
        if isinstance(item, Mapping)
    ]
    routes = []
    route_sources = sorted(
        (
            item
            for item in raw_nodes
            if _text(item.get("kind")) == "strategy_route"
        ),
        key=_canonical_json,
    )
    for source_index, item in enumerate(route_sources):
        route = dict(item)
        original_id = _text(route.get("node_id"))
        identity_error = ""
        if not original_id:
            identity_error = "missing route node_id"
        elif original_id in ambiguous_node_ids:
            identity_error = f"duplicate route node_id: {original_id}"
        if identity_error:
            route_id = (
                f"malformed-route:{source_index}:"
                f"{_digest(_canonical_value(route))[:12]}"
            )
        else:
            route_id = original_id
        route["_projection_route_id"] = route_id
        route["_projection_identity_error"] = identity_error
        routes.append(route)
    routes.sort(key=lambda item: _text(item.get("_projection_route_id")))
    normalizer = ProofSearchState(
        theorem_name=theorem_name,
        root_statement=root_statement or "True",
    )
    results = []
    seen_goal_payloads: Dict[str, str] = {}

    for route in routes:
        route_id = _text(route.get("_projection_route_id"))
        identity_error = _text(route.get("_projection_identity_error"))
        route_status = _text(route.get("status") or "open")
        activation = _route_activation(route)
        metadata = route.get("metadata")
        metadata = dict(metadata) if isinstance(metadata, Mapping) else {}
        explicit_activation = _text(metadata.get("activation_status"))
        raw_contract = metadata.get("route_assembly_contract")
        route_scope = _text(metadata.get("route_scope"))
        if (
            not explicit_activation
            and route_scope == "partial_route"
            and not isinstance(raw_contract, Mapping)
        ):
            activation = "candidate"
        work_items = []
        bindings = []
        obligations = []
        required_ids: Tuple[str, ...] = ()
        dangling_ids: Tuple[str, ...] = ()
        contract = None

        if explicit_activation and explicit_activation not in ACTIVATION_STATUSES:
            classification = "repair_activation_lifecycle"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="repair_activation_lifecycle",
                    reason=f"invalid explicit activation status: {explicit_activation}",
                )
            )
        elif identity_error:
            classification = "repair_route_identity"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=_text(route.get("node_id")),
                    slot_id="",
                    work_type="repair_route_identity",
                    reason=identity_error,
                    target_statement=_text(route.get("statement")),
                )
            )
        elif (
            route_status in _TERMINAL_ROUTE_STATUSES
            and explicit_activation
            and explicit_activation != "archived"
        ):
            classification = "repair_activation_lifecycle"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="repair_activation_lifecycle",
                    reason=(
                        f"terminal route status {route_status} requires "
                        "archived activation"
                    ),
                )
            )
        elif route_status in {"proved", "contradicted"}:
            classification = f"repair_route_{route_status}_provenance"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type=f"repair_route_{route_status}_provenance",
                    reason=(
                        f"route {route_status} status lacks a pinned Lean "
                        "evidence contract"
                    ),
                    target_statement=root_statement,
                )
            )
        elif route_status in _TERMINAL_ROUTE_STATUSES:
            classification = f"terminal_{route_status}"
            lifecycle = route_status
        elif activation == "parked":
            raw_decision = metadata.get("activation_decision")
            try:
                parking_decision = (
                    ActivationDecision.from_record(raw_decision)
                    if isinstance(raw_decision, Mapping)
                    else None
                )
            except (TypeError, ValueError):
                parking_decision = None
            revision = max(1, _int(metadata.get("route_revision"), 1))
            if not (
                parking_decision is not None
                and parking_decision.route_id == route_id
                and parking_decision.expected_route_revision == revision
                and parking_decision.next_status == "parked"
            ):
                classification = "repair_activation_lifecycle"
                lifecycle = "blocked"
                work_items.append(
                    _work_item(
                        route_id=route_id,
                        graph_node_id=route_id,
                        slot_id="",
                        work_type="repair_activation_lifecycle",
                        reason=(
                            "parked route lacks a matching, digest-pinned "
                            "activation decision and wake condition"
                        ),
                    )
                )
            else:
                classification = "parked_route"
                lifecycle = "parked"
        elif activation == "archived":
            classification = "repair_activation_lifecycle"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="repair_activation_lifecycle",
                    reason="nonterminal route cannot have archived activation",
                )
            )
        elif activation == "research_draft":
            classification = "activation_evidence_required"
            lifecycle = "research_draft"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="activation_evidence_required",
                    reason="research draft needs an activation decision before execution",
                    target_statement=_text(route.get("statement")),
                )
            )
        elif (
            route_scope == "partial_route"
            and not isinstance(raw_contract, Mapping)
            and not explicit_activation
        ):
            legacy_dependency_ids = [
                _text(edge.get("target"))
                for edge in raw_edges
                if _text(edge.get("source")) == route_id
                and _text(edge.get("kind"))
                in {"route_requires", "route_blocked_by", "route_replan"}
                and _text(edge.get("target"))
            ]
            dependency_statuses = [
                _text(nodes.get(node_id, {}).get("status"))
                for node_id in legacy_dependency_ids
            ]
            dangling_ids = tuple(
                sorted(
                    {
                        node_id
                        for node_id in legacy_dependency_ids
                        if node_id not in nodes
                    }
                )
            )
            required_ids = tuple(sorted(set(legacy_dependency_ids)))
            if dangling_ids:
                classification = "repair_dangling_dependencies"
                lifecycle = "blocked"
                for node_id in dangling_ids:
                    work_items.append(
                        _work_item(
                            route_id=route_id,
                            graph_node_id=node_id,
                            slot_id="",
                            work_type="repair_dangling_dependency",
                            reason="legacy partial route dependency node is absent",
                        )
                    )
            elif any(
                status in _TERMINAL_DEPENDENCY_STATUSES
                for status in dependency_statuses
            ):
                classification = "partial_route_exhausted"
                lifecycle = "historical_terminal"
            elif any(
                status in {"open", "blocked"}
                for status in dependency_statuses
            ):
                classification = "activation_evidence_required"
                lifecycle = "research_draft"
                work_items.append(
                    _work_item(
                        route_id=route_id,
                        graph_node_id=route_id,
                        slot_id="",
                        work_type="activation_evidence_required",
                        reason=(
                            "legacy open or blocked partial route needs an activation "
                            "decision before contract authoring"
                        ),
                        target_statement=_text(route.get("statement")),
                    )
                )
            elif dependency_statuses and all(
                status == "proved" for status in dependency_statuses
            ):
                classification = "partial_route_completed"
                lifecycle = "historical_complete"
            else:
                classification = "partial_route_history"
                lifecycle = "historical"
        elif not isinstance(raw_contract, Mapping):
            classification = "author_route_contract"
            lifecycle = "projection_pending"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="author_route_contract",
                    reason="active route has no assembly/dependency contract",
                    target_statement=_text(route.get("statement")),
                )
            )
        elif not root_statement:
            classification = "repair_missing_root_target"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="repair_missing_root_target",
                    reason="graph root statement is missing",
                )
            )
        elif not (
            isinstance(raw_contract.get("required_node_ids"), Sequence)
            and not isinstance(
                raw_contract.get("required_node_ids"), (str, bytes)
            )
        ):
            classification = "repair_malformed_contract"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="repair_malformed_contract",
                    reason="required_node_ids must be a sequence of node IDs",
                    target_statement=_text(route.get("statement")),
                )
            )
        elif not any(
            _text(item)
            for item in list(raw_contract.get("required_node_ids") or ())
        ):
            classification = "repair_empty_contract"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="repair_empty_contract",
                    reason="route contract contains no dependency slots",
                    target_statement=_text(raw_contract.get("target_statement")),
                )
            )
        elif not _text(raw_contract.get("target_statement")):
            classification = "repair_missing_route_target"
            lifecycle = "blocked"
            work_items.append(
                _work_item(
                    route_id=route_id,
                    graph_node_id=route_id,
                    slot_id="",
                    work_type="repair_missing_route_target",
                    reason="route contract has no explicit target statement",
                    target_statement=_text(route.get("statement")),
                )
            )
        else:
            contract_validation_reason = _legacy_contract_validation_reason(
                route_id=route_id,
                route_metadata=metadata,
                contract=raw_contract,
                nodes=nodes,
                edges=raw_edges,
                root_node_id=root_node_id,
                root_statement=root_statement,
                statement_key=ProofGraph._route_target_statement_key,
            )
            if contract_validation_reason:
                invalid_required_ids = tuple(
                    item.strip()
                    for item in list(raw_contract.get("required_node_ids") or ())
                    if isinstance(item, str) and item.strip()
                )
                invalid_dangling_ids = tuple(
                    sorted(
                        {
                            item
                            for item in invalid_required_ids
                            if item not in nodes
                        }
                    )
                )
                classification = "repair_route_contract_invariants"
                lifecycle = "blocked"
                work_items.append(
                    _work_item(
                        route_id=route_id,
                        graph_node_id=route_id,
                        slot_id="",
                        work_type="repair_route_contract_invariants",
                        reason=contract_validation_reason,
                        target_statement=_text(raw_contract.get("target_statement")),
                    )
                )
                projection_debt = _route_has_execution_projection_debt(
                    activation_status=activation,
                    lifecycle_status=lifecycle,
                    executable_obligation_count=0,
                )
                results.append(
                    RouteProjectionResult(
                        schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
                        route_id=route_id,
                        activation_status=activation,
                        lifecycle_status=lifecycle,
                        classification=classification,
                        projection_debt=projection_debt,
                        contract=None,
                        bindings=(),
                        obligations=(),
                        work_items=tuple(work_items),
                        required_node_ids=invalid_required_ids,
                        dangling_node_ids=invalid_dangling_ids,
                    )
                )
                continue
            required_ids = tuple(
                _text(item)
                for item in list(raw_contract.get("required_node_ids") or ())
                if _text(item)
            )
            revision = max(1, _int(metadata.get("route_revision"), 1))
            target_statement = _text(raw_contract.get("target_statement"))
            target_hash = _digest(
                canonicalize_lean_statement_for_identity(target_statement)
                or target_statement
            )
            slot_records = []
            for ordinal, node_id in enumerate(required_ids, 1):
                dependency = nodes.get(node_id)
                certificate = (
                    _certificate_for_node(
                        dependency,
                        project_environment_hash=project_environment_hash,
                        trusted_lean_acceptances=trusted_acceptance_registry,
                    )
                    if dependency is not None
                    else None
                )
                statement = _text(dependency.get("statement")) if dependency else ""
                dependency_metadata = (
                    dependency.get("metadata")
                    if dependency and isinstance(dependency.get("metadata"), Mapping)
                    else {}
                )
                statement_hash = (
                    _statement_context_hash(
                        statement,
                        _explicit_local_context(dependency_metadata),
                    )
                    if statement
                    else ""
                )
                slot_id = f"slot:{ordinal}:{_digest(node_id)[:12]}"
                if node_id in ambiguous_node_ids:
                    resolution_kind = "ambiguous_dependency"
                elif dependency is None:
                    resolution_kind = "missing_dependency"
                elif not statement:
                    resolution_kind = "invalid_dependency"
                elif certificate is not None:
                    resolution_kind = "certificate"
                elif _text(dependency.get("status")) in _TERMINAL_DEPENDENCY_STATUSES:
                    resolution_kind = "terminal_dependency"
                else:
                    resolution_kind = "unresolved_goal"
                slot_records.append(
                    RouteDependencySlot(
                        schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
                        slot_id=slot_id,
                        ordinal=ordinal,
                        role="required_dependency",
                        graph_node_id=node_id,
                        expected_statement_hash=statement_hash,
                        resolution_kind=resolution_kind,
                        pinned_certificate=certificate,
                    )
                )
            contract_seed = _route_contract_seed(
                route_id=route_id,
                root_target_hash=target_hash,
                route_revision=revision,
                slots=slot_records,
                assembly=raw_contract,
            )
            contract_id = f"route-contract:{_digest(contract_seed)[:24]}"
            contract = RouteExecutionContractV2(
                schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
                contract_id=contract_id,
                route_id=route_id,
                root_target_statement=target_statement,
                root_target_hash=target_hash,
                route_revision=revision,
                predecessor_contract_id=_text(metadata.get("predecessor_contract_id")),
                slots=tuple(slot_records),
                assembly=copy.deepcopy(dict(raw_contract)),
            )
            dangling_ids = tuple(
                sorted({slot.graph_node_id for slot in slot_records if slot.resolution_kind == "missing_dependency"})
            )

            for slot in slot_records:
                binding_id = "route-binding:" + _digest(
                    [
                        contract_id,
                        route_id,
                        revision,
                        slot.slot_id,
                        slot.graph_node_id,
                    ]
                )[:24]
                dependency = nodes.get(slot.graph_node_id)
                if slot.graph_node_id in ambiguous_node_ids:
                    work = _work_item(
                        route_id=route_id,
                        graph_node_id=slot.graph_node_id,
                        slot_id=slot.slot_id,
                        work_type="repair_ambiguous_dependency",
                        reason="required dependency node_id is duplicated",
                    )
                    work_items.append(work)
                    bindings.append(
                        RouteSlotBinding(
                            GRAPH_EXECUTION_SCHEMA_VERSION,
                            binding_id,
                            route_id,
                            contract_id,
                            revision,
                            slot.slot_id,
                            slot.graph_node_id,
                            "blocked",
                            1,
                            "authoring_work",
                            work_id=work.work_id,
                            reason=work.reason,
                        )
                    )
                    continue
                if dependency is None:
                    work = _work_item(
                        route_id=route_id,
                        graph_node_id=slot.graph_node_id,
                        slot_id=slot.slot_id,
                        work_type="repair_dangling_dependency",
                        reason="required dependency node is absent",
                    )
                    work_items.append(work)
                    bindings.append(
                        RouteSlotBinding(
                            GRAPH_EXECUTION_SCHEMA_VERSION,
                            binding_id,
                            route_id,
                            contract_id,
                            revision,
                            slot.slot_id,
                            slot.graph_node_id,
                            "blocked",
                            1,
                            "authoring_work",
                            work_id=work.work_id,
                            reason=work.reason,
                        )
                    )
                    continue
                certificate = slot.pinned_certificate
                if certificate is not None:
                    bindings.append(
                        RouteSlotBinding(
                            GRAPH_EXECUTION_SCHEMA_VERSION,
                            binding_id,
                            route_id,
                            contract_id,
                            revision,
                            slot.slot_id,
                            slot.graph_node_id,
                            "resolved",
                            1,
                            "certificate",
                            certificate_id=certificate.certificate_id,
                        )
                    )
                    continue
                dependency_status = _text(dependency.get("status"))
                if dependency_status == "proved":
                    work = _work_item(
                        route_id=route_id,
                        graph_node_id=slot.graph_node_id,
                        slot_id=slot.slot_id,
                        work_type="repair_certificate_provenance",
                        reason=(
                            "proved dependency lacks complete, environment-matched "
                            "Lean certificate provenance"
                        ),
                        target_statement=_text(dependency.get("statement")),
                    )
                    work_items.append(work)
                    bindings.append(
                        RouteSlotBinding(
                            GRAPH_EXECUTION_SCHEMA_VERSION,
                            binding_id,
                            route_id,
                            contract_id,
                            revision,
                            slot.slot_id,
                            slot.graph_node_id,
                            "blocked",
                            1,
                            "authoring_work",
                            work_id=work.work_id,
                            reason=work.reason,
                        )
                    )
                    continue
                if dependency_status in _TERMINAL_DEPENDENCY_STATUSES:
                    work = _work_item(
                        route_id=route_id,
                        graph_node_id=slot.graph_node_id,
                        slot_id=slot.slot_id,
                        work_type="revise_terminal_dependency",
                        reason=f"required dependency is terminal: {dependency_status}",
                        target_statement=_text(dependency.get("statement")),
                    )
                    work_items.append(work)
                    bindings.append(
                        RouteSlotBinding(
                            GRAPH_EXECUTION_SCHEMA_VERSION,
                            binding_id,
                            route_id,
                            contract_id,
                            revision,
                            slot.slot_id,
                            slot.graph_node_id,
                            "terminal",
                            1,
                            "terminal",
                            work_id=work.work_id,
                            reason=work.reason,
                        )
                    )
                    continue

                dependency_metadata = dependency.get("metadata")
                dependency_metadata = (
                    dict(dependency_metadata)
                    if isinstance(dependency_metadata, Mapping)
                    else {}
                )
                statement = _text(dependency.get("statement"))
                local_context = _explicit_local_context(dependency_metadata)
                missing_context_names = _missing_root_context_names(
                    root_statement,
                    statement,
                    local_context,
                )
                preflight_evidence_valid = _target_preflight_evidence_valid(
                    dependency_metadata,
                    target_statement=statement,
                    local_context=local_context,
                    project_environment_hash=project_environment_hash,
                    trusted_lean_acceptances=trusted_acceptance_registry,
                )
                syntax_status, syntax_reason = _syntax_status(
                    dependency,
                    target_statement=statement,
                    context_missing=bool(missing_context_names),
                    preflight_evidence_valid=preflight_evidence_valid,
                )
                truth_status = _truth_status(dependency, None)
                if syntax_status == "lean_executable":
                    goal = normalizer._goal_signature(
                        statement,
                        local_context,
                        source_failure="graph_execution_projection",
                    )
                    goal_payload = goal.to_execution_record()
                    context_origin = "explicit" if local_context else "closed_target"
                    context_origin_hash = _digest(list(local_context))
                    identity_payload = {
                        "normalized_goal": goal_payload,
                        "context_origin_hash": context_origin_hash,
                        "project_environment_hash": project_environment_hash,
                    }
                    goal_identity_hash = _digest(identity_payload)
                    canonical_payload = _canonical_json(identity_payload)
                    collision = (
                        goal_identity_hash in seen_goal_payloads
                        and seen_goal_payloads[goal_identity_hash] != canonical_payload
                    )
                    if collision:
                        work = _work_item(
                            route_id=route_id,
                            graph_node_id=slot.graph_node_id,
                            slot_id=slot.slot_id,
                            work_type="repair_goal_identity_collision",
                            reason="goal hash matched a different canonical payload",
                            target_statement=statement,
                        )
                        work_items.append(work)
                        bindings.append(
                            RouteSlotBinding(
                                GRAPH_EXECUTION_SCHEMA_VERSION,
                                binding_id,
                                route_id,
                                contract_id,
                                revision,
                                slot.slot_id,
                                slot.graph_node_id,
                                "blocked",
                                1,
                                "authoring_work",
                                work_id=work.work_id,
                                reason=work.reason,
                            )
                        )
                        continue
                    seen_goal_payloads[goal_identity_hash] = canonical_payload
                    execution_intent = (
                        "prove_required"
                        if activation == "active"
                        else "adjudicate_candidate"
                    )
                    expected_parent_effect = "resolve_route_dependency_slot"
                    semantic_evidence_hash = _digest(
                        [slot.to_record(), dependency_status, dependency_metadata]
                    )
                    obligation_id = "graph-obligation:" + _digest(
                        [
                            binding_id,
                            goal_identity_hash,
                            syntax_status,
                            truth_status,
                            execution_intent,
                            expected_parent_effect,
                            contract_id,
                            slot.graph_node_id,
                            context_origin,
                            semantic_evidence_hash,
                            root_statement_hash,
                        ]
                    )[:24]
                    obligation = GraphExecutionObligation(
                        schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
                        obligation_id=obligation_id,
                        target_statement=statement,
                        local_context=tuple(local_context),
                        normalized_goal_payload=goal_payload,
                        goal_identity_hash=goal_identity_hash,
                        context_origin=context_origin,
                        context_origin_hash=context_origin_hash,
                        origin_graph_node_id=slot.graph_node_id,
                        route_id=route_id,
                        route_contract_id=contract_id,
                        route_revision=revision,
                        dependency_slot_id=slot.slot_id,
                        route_slot_binding_id=binding_id,
                        syntax_status=syntax_status,
                        truth_status=truth_status,
                        execution_intent=execution_intent,
                        expected_parent_effect=expected_parent_effect,
                        semantic_evidence_hash=semantic_evidence_hash,
                        root_statement=root_statement,
                        root_statement_hash=root_statement_hash,
                        project_environment_hash=project_environment_hash,
                        priority=_float(metadata.get("score"), 0.0),
                    )
                    obligations.append(obligation)
                    bindings.append(
                        RouteSlotBinding(
                            GRAPH_EXECUTION_SCHEMA_VERSION,
                            binding_id,
                            route_id,
                            contract_id,
                            revision,
                            slot.slot_id,
                            slot.graph_node_id,
                            "executable",
                            1,
                            "goal",
                            goal_identity_hash=goal_identity_hash,
                        )
                    )
                    continue

                if bool(missing_context_names):
                    work_type = "author_local_context"
                    reason = "missing inherited root binders: " + ", ".join(
                        missing_context_names
                    )
                elif syntax_status == "needs_formalization":
                    work_type = "formalize_statement"
                    reason = syntax_reason
                elif syntax_status == "invalid":
                    work_type = "repair_invalid_target"
                    reason = syntax_reason
                else:
                    work_type = "preflight_target"
                    reason = syntax_reason
                work = _work_item(
                    route_id=route_id,
                    graph_node_id=slot.graph_node_id,
                    slot_id=slot.slot_id,
                    work_type=work_type,
                    reason=reason,
                    target_statement=statement,
                )
                work_items.append(work)
                bindings.append(
                    RouteSlotBinding(
                        GRAPH_EXECUTION_SCHEMA_VERSION,
                        binding_id,
                        route_id,
                        contract_id,
                        revision,
                        slot.slot_id,
                        slot.graph_node_id,
                        "blocked",
                        1,
                        "authoring_work",
                        work_id=work.work_id,
                        reason=work.reason,
                    )
                )

            if dangling_ids:
                classification = "repair_dangling_dependencies"
                lifecycle = "blocked"
            elif any(item.resolution_kind == "terminal" for item in bindings):
                classification = "revise_terminal_dependencies"
                lifecycle = "blocked"
            elif obligations:
                classification = "executable_obligations"
                lifecycle = "executable"
            elif work_items:
                work_types = {item.work_type for item in work_items}
                if "author_local_context" in work_types:
                    classification = "author_local_context"
                elif "formalize_statement" in work_types:
                    classification = "formalize_statements"
                elif "preflight_target" in work_types:
                    classification = "preflight_targets"
                else:
                    classification = sorted(work_types)[0]
                lifecycle = "projection_pending"
            elif bindings and all(item.status == "resolved" for item in bindings):
                if _text(raw_contract.get("assembly_template") or raw_contract.get("proof_stub")):
                    classification = "ready_to_assemble"
                    lifecycle = "ready_to_assemble"
                else:
                    classification = "author_assembly_bridge"
                    lifecycle = "projection_pending"
                    work_items.append(
                        _work_item(
                            route_id=route_id,
                            graph_node_id=route_id,
                            slot_id="",
                            work_type="author_assembly_bridge",
                            reason="all dependencies are certified but no executable assembly template exists",
                            target_statement=target_statement,
                        )
                    )
            else:
                classification = "repair_empty_contract"
                lifecycle = "blocked"
                work_items.append(
                    _work_item(
                        route_id=route_id,
                        graph_node_id=route_id,
                        slot_id="",
                        work_type="repair_empty_contract",
                        reason="route contract contains no dependency slots",
                        target_statement=target_statement,
                    )
                )
        projection_debt = _route_has_execution_projection_debt(
            activation_status=activation,
            lifecycle_status=lifecycle,
            executable_obligation_count=len(obligations),
        )
        results.append(
            RouteProjectionResult(
                schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
                route_id=route_id,
                activation_status=activation,
                lifecycle_status=lifecycle,
                classification=classification,
                projection_debt=projection_debt,
                contract=contract,
                bindings=tuple(bindings),
                obligations=tuple(obligations),
                work_items=tuple(work_items),
                required_node_ids=required_ids,
                dangling_node_ids=dangling_ids,
            )
        )

    unique_required_ids = tuple(
        sorted({node_id for result in results for node_id in result.required_node_ids})
    )
    dangling_required_ids = tuple(
        sorted({node_id for result in results for node_id in result.dangling_node_ids})
    )
    counts: Dict[str, int] = {
        "routes_total": len(results),
        "routes_active": sum(item.activation_status == "active" for item in results),
        "routes_with_contract": sum(
            isinstance(
                (
                    route.get("metadata")
                    if isinstance(route.get("metadata"), Mapping)
                    else {}
                ).get("route_assembly_contract"),
                Mapping,
            )
            for route in routes
        ),
        "routes_projection_debt": sum(item.projection_debt for item in results),
        "routes_projection_debt_before": sum(
            _text(route.get("status") or "open") == "open"
            and not _route_has_projection_disposition(route)
            for route in routes
        ),
        "bindings_total": sum(len(item.bindings) for item in results),
        "obligations_executable": sum(len(item.obligations) for item in results),
        "work_items_total": sum(len(item.work_items) for item in results),
        "unique_required_node_ids": len(unique_required_ids),
        "dangling_required_node_ids": len(dangling_required_ids),
    }
    for result in results:
        key = f"classification_{result.classification}"
        counts[key] = counts.get(key, 0) + 1
    unchanged = dict(graph_record) == snapshot
    if not unchanged:
        raise RuntimeError("shadow graph projection mutated its input")
    return GraphProjectionReport(
        schema_version=GRAPH_EXECUTION_SCHEMA_VERSION,
        theorem_name=theorem_name,
        input_graph_digest=input_digest,
        project_environment_hash=project_environment_hash,
        acceptance_registry_hash=acceptance_registry_hash,
        route_results=tuple(results),
        counts=counts,
        unique_required_node_ids=unique_required_ids,
        dangling_required_node_ids=dangling_required_ids,
        input_unchanged=True,
    )


__all__ = [
    "ACTIVATION_STATUSES",
    "ActivationDecision",
    "EXECUTION_INTENTS",
    "GRAPH_EXECUTION_SCHEMA_VERSION",
    "GRAPH_PROJECTION_METRICS",
    "graph_target_preflight_evidence",
    "pinned_certificate_ref",
    "lean_acceptance_ref",
    "GraphExecutionObligation",
    "GraphProjectionReport",
    "PinnedCertificateRef",
    "ProjectionWorkItem",
    "RouteDependencySlot",
    "RouteExecutionContractV2",
    "RouteProjectionResult",
    "RouteSlotBinding",
    "SYNTAX_STATUSES",
    "TRUTH_STATUSES",
    "project_graph_execution_shadow",
]
