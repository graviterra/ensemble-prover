"""Source-bound Lean profiles and reconstruction of closed obligations."""

from __future__ import annotations

import asyncio
import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Mapping, Sequence

from ensemble_prover.deep_json import loads_deep_json


def digest(value: str | bytes) -> str:
    return hashlib.sha256(
        value.encode() if isinstance(value, str) else value
    ).hexdigest()


def record_digest(record: Mapping[str, Any]) -> str:
    return digest(
        json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    )


def remaining(budget: Any) -> float:
    budget.check_cancelled()
    seconds = float(budget.remaining_s())
    if seconds <= 0:
        raise asyncio.TimeoutError("mathematical memory allocation exhausted")
    return seconds


async def lean_call(runner: Any, budget: Any, operation: Any) -> Any:
    """Use the existing strict checker lease for every semantic boundary."""
    from ensemble_prover.proof_state_executor import _await_serialized_lean_operation

    heartbeat_cap = getattr(budget, "max_heartbeats", None)
    if heartbeat_cap is not None and (
        type(heartbeat_cap) is not int or heartbeat_cap <= 0
    ):
        raise TimeoutError("mathematical memory heartbeat allocation exhausted")
    from ensemble_prover.lean_runner import lean_resource_scope

    with lean_resource_scope(
        memory_mb=getattr(budget, "memory_mb", 8192),
        concurrency=getattr(budget, "concurrency", 1),
        max_heartbeats=getattr(budget, "max_heartbeats", None),
        deadline_monotonic=getattr(budget, "deadline_monotonic", None),
    ):
        result = await _await_serialized_lean_operation(
            runner,
            operation,
            timeout_s=remaining(budget) * 0.95,
            deadline_monotonic=getattr(budget, "deadline_monotonic", None),
            operation_label="mathematical_memory_semantics",
        )
    remaining(budget)
    return result


@dataclass(frozen=True)
class DeclarationProfile:
    declaration_name: str
    statement: str
    source: str
    environment_id: str
    source_store_id: str
    source_digest: str
    exact_expr_json: str = ""
    binder_kinds: tuple[str, ...] = ()
    binder_sorts: tuple[str, ...] = ()
    binder_types: tuple[str, ...] = ()
    binder_dependencies: tuple[tuple[int, ...], ...] = ()
    conclusion_dependencies: tuple[int, ...] = ()
    universe_parameters: tuple[str, ...] = ()
    resolved_constants: tuple[str, ...] = ()
    structural_identity: str = ""
    certified_source_binding: bool = False
    complete: bool = False
    diagnostic: str = ""
    schema_version: int = 1

    def __post_init__(self) -> None:
        if self.schema_version != 1:
            raise ValueError("unsupported declaration profile schema")
        if self.source_digest != digest(self.source):
            raise ValueError("declaration source digest mismatch")
        if self.complete:
            if not all(
                (
                    self.declaration_name,
                    self.statement,
                    self.source,
                    self.environment_id,
                    self.source_store_id,
                    self.exact_expr_json,
                )
            ):
                raise ValueError(
                    "complete profile requires exact source and environment"
                )
            if len(self.binder_kinds) != len(self.binder_dependencies):
                raise ValueError("incomplete binder metadata")
            loads_deep_json(self.exact_expr_json)

    @property
    def declaration_id(self) -> str:
        return record_digest(
            {
                "source": self.source_digest,
                "name": self.declaration_name,
                "type": digest(self.exact_expr_json),
                "store": self.source_store_id,
                "environment": self.environment_id,
                "version": self.schema_version,
            }
        )

    @property
    def features(self) -> tuple[str, ...]:
        # Heuristics retain qualified Lean constants; they confer no fit proof.
        return self.resolved_constants

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "DeclarationProfile":
        fields = dict(record)
        for key in (
            "binder_kinds",
            "binder_sorts",
            "binder_types",
            "conclusion_dependencies",
            "universe_parameters",
            "resolved_constants",
        ):
            fields[key] = tuple(fields.get(key, ()))
        fields["binder_dependencies"] = tuple(
            tuple(v) for v in fields.get("binder_dependencies", ())
        )
        return cls(**fields)


@dataclass(frozen=True)
class GoalContextSnapshot:
    statement: str
    source: str
    environment_id: str
    source_digest: str
    statement_digest: str
    context_digest: str = ""
    ordered_helper_digests: tuple[str, ...] = ()
    source_variant: str = ""
    exact_expr_json: str = ""
    binder_kinds: tuple[str, ...] = ()
    binder_dependencies: tuple[tuple[int, ...], ...] = ()
    conclusion_dependencies: tuple[int, ...] = ()
    universe_parameters: tuple[str, ...] = ()
    resolved_constants: tuple[str, ...] = ()
    capture_kind: str = "source_reconstructed_closed"
    complete: bool = False
    diagnostic: str = ""
    schema_version: int = 1

    def __post_init__(self) -> None:
        if (
            self.schema_version != 1
            or self.capture_kind != "source_reconstructed_closed"
        ):
            raise ValueError("unsupported goal capture")
        if self.source_digest != digest(self.source) or self.statement_digest != digest(
            self.statement
        ):
            raise ValueError("goal source binding mismatch")
        if self.complete and not all(
            (self.statement, self.source, self.environment_id, self.exact_expr_json)
        ):
            raise ValueError("complete goal requires source and environment")

    @property
    def goal_id(self) -> str:
        return record_digest(self.to_record())

    def to_record(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_record(cls, record: Mapping[str, Any]) -> "GoalContextSnapshot":
        fields = dict(record)
        for key in (
            "binder_kinds",
            "conclusion_dependencies",
            "universe_parameters",
            "resolved_constants",
            "ordered_helper_digests",
        ):
            fields[key] = tuple(fields.get(key, ()))
        fields["binder_dependencies"] = tuple(
            tuple(v) for v in fields.get("binder_dependencies", ())
        )
        return cls(**fields)


def _analysis_fields(analysis: Any) -> dict[str, Any]:
    return {
        "exact_expr_json": str(getattr(analysis, "exact_expr_json", "")),
        "binder_kinds": tuple(getattr(analysis, "binder_kinds", ())),
        "binder_dependencies": tuple(getattr(analysis, "binder_dependencies", ())),
        "conclusion_dependencies": tuple(
            getattr(analysis, "conclusion_dependencies", ())
        ),
        "universe_parameters": tuple(getattr(analysis, "universe_parameters", ())),
        "resolved_constants": tuple(getattr(analysis, "resolved_constants", ())),
        "complete": bool(getattr(analysis, "profile_complete", False)),
    }


async def capture_goal(
    runner: Any,
    *,
    statement: str,
    source: str,
    environment_id: str,
    budget: Any,
    source_variant: str = "",
    preamble: str | None = None,
    lemmas: Sequence[str] = (),
) -> GoalContextSnapshot:
    resolved_preamble = runner._resolve_preamble(preamble)
    context = resolved_preamble + "\n" + "\n".join(lemmas)
    base = dict(
        statement=statement,
        source=source,
        environment_id=environment_id,
        source_digest=digest(source),
        statement_digest=digest(statement),
        source_variant=source_variant,
        context_digest=digest(resolved_preamble),
        ordered_helper_digests=tuple(digest(block) for block in lemmas),
    )
    try:
        analyses, output, code = await lean_call(
            runner,
            budget,
            lambda: runner.analyze_statement_contracts(
                (statement,),
                preamble_override=context,
                timeout_s=remaining(budget),
                _operation_deadline=getattr(budget, "deadline_monotonic", None),
                _preamble_resolved=True,
                max_heartbeats=getattr(budget, "max_heartbeats", None),
            ),
        )
        remaining(budget)
        if code != 0 or not analyses:
            return GoalContextSnapshot(**base, diagnostic="goal_capture_unavailable")
        fields = _analysis_fields(analyses[0])
        fields["complete"] = fields["complete"] and bool(source and environment_id)
        return GoalContextSnapshot(**base, **fields)
    except (TimeoutError, OSError, ValueError) as exc:
        return GoalContextSnapshot(**base, diagnostic=type(exc).__name__)


async def profile_declaration(
    runner: Any,
    *,
    declaration_name: str,
    statement: str,
    source: str,
    environment_id: str,
    source_store_id: str,
    budget: Any,
    preamble: str | None = None,
    source_available: bool = False,
    source_binding_attested: bool = False,
) -> DeclarationProfile:
    base = dict(
        declaration_name=declaration_name,
        statement=statement,
        source=source,
        environment_id=environment_id,
        source_store_id=source_store_id,
        source_digest=digest(source),
    )
    try:
        # This binds the supplied statement to the kernel declaration, rather
        # than merely proving that a pretty-printed type elaborates somewhere.
        context = runner._resolve_preamble(preamble)
        if source_available and not source_binding_attested:
            base.update(
                source=context,
                source_digest=digest(context),
                source_store_id="environment:" + environment_id,
            )
        standalone_source = (
            context
            if source_available
            else (
                source
                if source.lstrip().startswith("import ")
                else context + "\n" + source
            )
        )
        _parsed, _output, code = await lean_call(
            runner,
            budget,
            lambda: runner.check_source_declaration_type_equivalence(
                standalone_source,
                declaration_name,
                statement,
                timeout_s=remaining(budget),
                preamble_override=preamble,
                max_heartbeats=getattr(budget, "max_heartbeats", None),
            ),
        )
        if code != 0:
            return DeclarationProfile(
                **base, diagnostic="declaration_type_binding_failed"
            )
        if not source_available:
            context = standalone_source
        analyses, _output, code = await lean_call(
            runner,
            budget,
            lambda: runner.analyze_statement_contracts(
                (statement,),
                preamble_override=context,
                timeout_s=remaining(budget),
                _operation_deadline=getattr(budget, "deadline_monotonic", None),
                _preamble_resolved=True,
                max_heartbeats=getattr(budget, "max_heartbeats", None),
            ),
        )
        remaining(budget)
        if code != 0 or not analyses:
            return DeclarationProfile(
                **base, diagnostic="profile_extraction_unavailable"
            )
        analysis = analyses[0]
        fields = _analysis_fields(analysis)
        fields["complete"] = fields["complete"] and bool(
            source and environment_id and source_store_id
        )
        return DeclarationProfile(
            **base,
            **fields,
            binder_sorts=analysis.binder_sorts,
            binder_types=analysis.binder_types,
            structural_identity=analysis.structural_identity,
            certified_source_binding=source_binding_attested is True,
        )
    except (TimeoutError, OSError, ValueError) as exc:
        return DeclarationProfile(**base, diagnostic=type(exc).__name__)
