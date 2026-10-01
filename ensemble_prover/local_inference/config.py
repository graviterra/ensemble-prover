"""Strict local endpoint profiles and immutable role resolution.

A profile is transport configuration. Loading it does not open a socket, read
an API key, or invent a cloud model default. Role selection is an explicit
argument; a model name never becomes a local binding by itself.

Required document shape::

    schema: 1
    coordinator:
      installation_id: lab_a
      scope_id: host_main
    endpoints:
      workstation:
        base_url: http://127.0.0.1:8000/v1
        dialect: vllm
        auth: {kind: none}
        capacity_group: workstation_gpu
        max_inflight: 1
        billing: {kind: owned_compute}
    deployments:
      math:
        endpoint: workstation
        model: exact-served-model-id
        context_tokens: 32768
        max_output_tokens: 8192
        output_semantics: total_generated
        tools: native_required
        native_n: unsupported
        execution: operator_asserted_local
        reasoning:
          mode: provider-default
          output_limit_includes_reasoning: unknown
        sampling:
          temperature: {policy: unrestricted}
          top_p: {policy: unrestricted}
    capacity_groups:
      workstation_gpu:
        max_inflight: 1
        max_queued: 8
        queue_timeout_s: 120
        request_timeout_s: 600
    run_budget:
      max_local_dispatches: 256
      max_local_requested_output_tokens: 2097152
      max_local_observed_request_wall_s: 14400
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from types import MappingProxyType
from typing import Any, Mapping, Sequence
from urllib.parse import urlsplit

from .errors import ContextCapacityInsufficient, LocalInferenceError
from .protocol_config import ProtocolPolicy, parse_protocol_policy, protocol_body, validate_protocol_policy
from .strictload import canonical_json, content_hash, fingerprint, parse_json_text, parse_yaml_text

_MAX_TOKENS = 10_000_000
_MAX_COUNT = 10_000_000
_MAX_INFLIGHT = 10_000
_MAX_TIMEOUT_S = 10_000_000
_MAX_WALL_S = 1_000_000_000
_IDENTIFIER = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]{0,63}$")
_ENV_NAME = re.compile(r"^[A-Z][A-Z0-9_]{2,63}$")
_MODEL = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:/-]{0,255}$")
_PLAIN = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:/-]{0,255}$")
_DECIMAL = re.compile(r"(?:0|[1-9][0-9]{0,6})(?:\.[0-9]{1,6})?")
_HEX64 = re.compile(r"^[0-9a-f]{64}$")
_DIALECTS = frozenset({"generic", "vllm", "ollama", "llamacpp"})
_TOOLS = frozenset({"native_required", "text_only", "disabled"})
_OUTPUT = frozenset({"total_generated", "visible_completion", "unknown"})
_EXECUTION = frozenset({"operator_asserted_local", "hosted_upstream"})
_REASONING = frozenset({"provider-default", "auto", "on", "off"})
_EFFORT = frozenset({"none", "low", "medium", "high", "max"})
_SAMPLING = frozenset({"unrestricted", "forbidden", "fixed"})
_POLICIES = frozenset({"mixed", "local-only"})
_CLOUD_MARKERS = (
    "OPENAI",
    "ANTHROPIC",
    "OPENROUTER",
    "DEEPSEEK",
    "CURSOR",
    "HUGGINGFACE",
    "HF_TOKEN",
)
_IDENTITY_FIELDS = (
    "revision",
    "server_build",
    "quantization",
    "tokenizer_id",
    "template_id",
    "parser_id",
)
_TOP_FIELDS = frozenset({
    "schema", "coordinator", "endpoints", "deployments", "capacity_groups", "run_budget",
})
_ENDPOINT_FIELDS = frozenset({
    "base_url", "dialect", "auth", "capacity_group", "max_inflight", "billing",
})
_DEPLOYMENT_FIELDS = frozenset({
    "endpoint", "model", "context_tokens", "max_output_tokens", "output_semantics",
    "tools", "native_n", "execution", "reasoning", "sampling", "protocol", *_IDENTITY_FIELDS,
})
_GROUP_FIELDS = frozenset({
    "max_inflight", "max_queued", "queue_timeout_s", "request_timeout_s",
})
_BUDGET_FIELDS = frozenset({
    "max_local_dispatches",
    "max_local_requested_output_tokens",
    "max_local_observed_request_wall_s",
})


@dataclass(frozen=True)
class AuthRef:
    kind: str
    name: str | None = None


@dataclass(frozen=True)
class BillingPolicy:
    kind: str
    tariff_id: str | None = None
    tariff_version: int | None = None


@dataclass(frozen=True)
class SamplingAxis:
    policy: str
    value: str | None = None


@dataclass(frozen=True)
class SamplingPolicy:
    temperature: SamplingAxis
    top_p: SamplingAxis


@dataclass(frozen=True)
class ReasoningPolicy:
    mode: str
    effort: str | None
    output_limit_includes_reasoning: str


@dataclass(frozen=True)
class IdentityField:
    source: str
    value: str | None = None


@dataclass(frozen=True)
class CapacityGroupPolicy:
    name: str
    max_inflight: int
    max_queued: int
    queue_timeout_s: int
    request_timeout_s: int


@dataclass(frozen=True)
class RunBudgetLimits:
    max_local_dispatches: int
    max_local_requested_output_tokens: int
    max_local_observed_request_wall_s: int


@dataclass(frozen=True)
class CoordinatorIdentity:
    installation_id: str
    scope_id: str


@dataclass(frozen=True)
class EndpointProfile:
    name: str
    base_url: str
    dialect: str
    auth: AuthRef
    capacity_group: str
    max_inflight: int
    billing: BillingPolicy

    @property
    def origin_fingerprint(self) -> str:
        return _prefixed_hash("origin", self.base_url)

    @property
    def auth_reference_fingerprint(self) -> str:
        if self.auth.kind == "none" or self.auth.name is None:
            return ""
        return _prefixed_hash("auth-ref", self.auth.name)

    @property
    def endpoint_fingerprint(self) -> str:
        return fingerprint("local_endpoint", _endpoint_fingerprint_payload(self))


@dataclass(frozen=True)
class DeploymentProfile:
    name: str
    endpoint: str
    model: str
    context_tokens: int
    max_output_tokens: int
    output_semantics: str
    tools: str
    native_n: str
    execution: str
    reasoning: ReasoningPolicy
    sampling: SamplingPolicy
    identity: Mapping[str, IdentityField]
    protocol: ProtocolPolicy


@dataclass(frozen=True)
class ProfileDocument:
    profile_hash: str
    coordinator: CoordinatorIdentity | None
    endpoints: Mapping[str, EndpointProfile]
    deployments: Mapping[str, DeploymentProfile]
    capacity_groups: Mapping[str, CapacityGroupPolicy]
    run_budget: RunBudgetLimits | None

    def canonical_body(self) -> dict[str, Any]:
        return _canonical_body(self)


@dataclass(frozen=True)
class RoleSelection:
    role: str
    deployment_id: str
    requested_model: str | None = None
    requested_reasoning_mode: str | None = None
    requested_reasoning_effort: str | None = None


@dataclass(frozen=True)
class ResolvedRole:
    role: str
    deployment_id: str
    endpoint_id: str
    model: str
    dialect: str
    context_tokens: int
    max_output_tokens: int
    output_semantics: str
    tools: str
    native_n: str
    execution: str
    execution_source: str
    reasoning_mode: str
    reasoning_effort: str | None
    output_limit_includes_reasoning: str
    sampling: SamplingPolicy
    billing_kind: str
    deployment_fingerprint: str
    endpoint_fingerprint: str
    capacity_group: str
    capacity_group_fingerprint: str


@dataclass(frozen=True)
class ResolvedLocalRun:
    profile_hash: str
    selection_hash: str
    inference_policy: str
    document: ProfileDocument
    roles: Mapping[str, ResolvedRole]


@dataclass(frozen=True)
class FrozenLocalRequest:
    """Admitted request identity. Later profile loads do not change this object."""

    profile_hash: str
    selection_hash: str
    deployment_fingerprint: str
    endpoint_fingerprint: str
    capacity_group_fingerprint: str
    role: str
    deployment_id: str
    endpoint_id: str
    model: str
    dialect: str
    context_tokens: int
    max_output_tokens: int
    requested_output_tokens: int
    reserved_prompt_tokens: int
    output_semantics: str
    reasoning_mode: str
    reasoning_effort: str | None
    output_limit_includes_reasoning: str
    tools: str
    native_n: str
    billing_kind: str
    execution: str
    execution_source: str
    fit_guarantee: bool
    count_source: str
    protocol: ProtocolPolicy


def load_profile_text(text: str, *, format: str) -> ProfileDocument:
    """Validate a YAML or JSON profile. This never connects to the endpoint."""

    if format == "yaml":
        data = parse_yaml_text(text)
    elif format == "json":
        data = parse_json_text(text)
    else:
        raise LocalInferenceError("invalid_field", "format")
    if type(data) is not dict:
        raise LocalInferenceError("mapping_required")
    return load_profile_data(data)


def load_profile_path(path: str | Path) -> ProfileDocument:
    """Read a ``.yaml``, ``.yml``, or ``.json`` file. The path is not part of the hash."""

    source = Path(path)
    suffix = source.suffix.lower()
    if suffix in {".yaml", ".yml"}:
        format = "yaml"
    elif suffix == ".json":
        format = "json"
    else:
        raise LocalInferenceError("invalid_field", "format")
    if source.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    try:
        text = source.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        raise LocalInferenceError("invalid_field", "format") from None
    return load_profile_text(text, format=format)


def load_profile_data(data: Mapping[str, Any]) -> ProfileDocument:
    if type(data) is not dict:
        raise LocalInferenceError("mapping_required")
    _reject_unknown(data, _TOP_FIELDS)
    schema = data.get("schema")
    if type(schema) is not int or schema != 1:
        if type(schema) is int:
            raise LocalInferenceError("unsupported_schema")
        raise LocalInferenceError("invalid_field", "schema")
    endpoints = _parse_endpoints(_require_mapping(data, "endpoints"))
    deployments = _parse_deployments(_require_mapping(data, "deployments"))
    groups = _parse_groups(_require_mapping(data, "capacity_groups"))
    coordinator = _parse_coordinator(data.get("coordinator")) if "coordinator" in data else None
    budget = _parse_budget(data["run_budget"]) if "run_budget" in data else None
    _link_profile(endpoints, deployments, groups, coordinator, budget)
    document = ProfileDocument(
        profile_hash="",
        coordinator=coordinator,
        endpoints=_proxy(endpoints),
        deployments=_proxy(deployments),
        capacity_groups=_proxy(groups),
        run_budget=budget,
    )
    body = _canonical_body(document)
    return ProfileDocument(
        profile_hash=content_hash(body),
        coordinator=document.coordinator,
        endpoints=document.endpoints,
        deployments=document.deployments,
        capacity_groups=document.capacity_groups,
        run_budget=document.run_budget,
    )


def resolve_run(
    document: ProfileDocument,
    selections: Sequence[RoleSelection],
    *,
    inference_policy: str = "mixed",
) -> ResolvedLocalRun:
    """Bind explicit roles to deployments. Unused hosted deployments stay unused."""

    if type(inference_policy) is not str or inference_policy not in _POLICIES:
        raise LocalInferenceError("invalid_field", "inference_policy")
    if not selections:
        raise LocalInferenceError("role_required")
    roles: dict[str, ResolvedRole] = {}
    for selection in selections:
        if type(selection) is not RoleSelection:
            raise LocalInferenceError("invalid_field", "roles")
        role = _identifier(selection.role, "roles")
        if role in roles:
            raise LocalInferenceError("duplicate_role")
        deployment = document.deployments.get(selection.deployment_id)
        if deployment is None:
            raise LocalInferenceError("unknown_deployment")
        endpoint = document.endpoints[deployment.endpoint]
        _reject_model_override(selection, deployment)
        _reject_reasoning_override(selection, deployment)
        if inference_policy == "local-only" and deployment.execution != "operator_asserted_local":
            raise LocalInferenceError("hosted_upstream_forbidden")
        group = document.capacity_groups[endpoint.capacity_group]
        assert document.coordinator is not None
        roles[role] = ResolvedRole(
            role=role,
            deployment_id=deployment.name,
            endpoint_id=endpoint.name,
            model=deployment.model,
            dialect=endpoint.dialect,
            context_tokens=deployment.context_tokens,
            max_output_tokens=deployment.max_output_tokens,
            output_semantics=deployment.output_semantics,
            tools=deployment.tools,
            native_n=deployment.native_n,
            execution=deployment.execution,
            execution_source="configured",
            reasoning_mode=deployment.reasoning.mode,
            reasoning_effort=deployment.reasoning.effort,
            output_limit_includes_reasoning=deployment.reasoning.output_limit_includes_reasoning,
            sampling=deployment.sampling,
            billing_kind=endpoint.billing.kind,
            deployment_fingerprint=_deployment_fingerprint(document, deployment),
            endpoint_fingerprint=endpoint.endpoint_fingerprint,
            capacity_group=group.name,
            capacity_group_fingerprint=_group_fingerprint(document, group),
        )
    resolved = ResolvedLocalRun(
        profile_hash=document.profile_hash,
        selection_hash="",
        inference_policy=inference_policy,
        document=document,
        roles=_proxy(roles),
    )
    return ResolvedLocalRun(
        profile_hash=resolved.profile_hash,
        selection_hash=_selection_hash(resolved),
        inference_policy=resolved.inference_policy,
        document=resolved.document,
        roles=resolved.roles,
    )


def freeze_request(
    resolved: ResolvedLocalRun,
    role: str,
    *,
    requested_output_tokens: int,
    reserved_prompt_tokens: int,
) -> FrozenLocalRequest:
    """Copy the admitted limits. The result does not retain a live profile lookup."""

    selected = resolved.roles.get(role)
    if selected is None:
        raise LocalInferenceError("unknown_role")
    output = _bounded_int(requested_output_tokens, minimum=1, maximum=selected.max_output_tokens, field="requested_output_tokens")
    if output > selected.max_output_tokens:
        raise LocalInferenceError("output_allowance_exceeded")
    prompt = _bounded_int(reserved_prompt_tokens, minimum=1, maximum=_MAX_TOKENS, field="reserved_prompt_tokens")
    require_declared_context_fit(
        context_tokens=selected.context_tokens,
        requested_output_tokens=output,
        reserved_prompt_tokens=prompt,
    )
    return FrozenLocalRequest(
        profile_hash=resolved.profile_hash,
        selection_hash=resolved.selection_hash,
        deployment_fingerprint=selected.deployment_fingerprint,
        endpoint_fingerprint=selected.endpoint_fingerprint,
        capacity_group_fingerprint=selected.capacity_group_fingerprint,
        role=selected.role,
        deployment_id=selected.deployment_id,
        endpoint_id=selected.endpoint_id,
        model=selected.model,
        dialect=selected.dialect,
        context_tokens=selected.context_tokens,
        max_output_tokens=selected.max_output_tokens,
        requested_output_tokens=output,
        reserved_prompt_tokens=prompt,
        output_semantics=selected.output_semantics,
        reasoning_mode=selected.reasoning_mode,
        reasoning_effort=selected.reasoning_effort,
        output_limit_includes_reasoning=selected.output_limit_includes_reasoning,
        tools=selected.tools,
        native_n=selected.native_n,
        billing_kind=selected.billing_kind,
        execution=selected.execution,
        execution_source=selected.execution_source,
        fit_guarantee=False,
        count_source="caller_supplied",
        protocol=resolved.document.deployments[selected.deployment_id].protocol,
    )


def require_declared_context_fit(
    *,
    context_tokens: int,
    requested_output_tokens: int,
    reserved_prompt_tokens: int,
) -> dict[str, Any]:
    """Accept caller-supplied counts or refuse. This is not a tokenizer guarantee."""

    context = _bounded_int(context_tokens, minimum=2, maximum=_MAX_TOKENS, field="context_tokens")
    output = _bounded_int(requested_output_tokens, minimum=1, maximum=_MAX_TOKENS, field="requested_output_tokens")
    if type(reserved_prompt_tokens) is not int or isinstance(reserved_prompt_tokens, bool):
        raise LocalInferenceError("invalid_prompt_reservation")
    if reserved_prompt_tokens < 1 or reserved_prompt_tokens > _MAX_TOKENS:
        raise LocalInferenceError("invalid_prompt_reservation")
    needed = reserved_prompt_tokens + output
    if needed > context:
        raise ContextCapacityInsufficient(needed=needed, available=context)
    return {
        "result": "accepted_declared_counts",
        "fit_guarantee": False,
        "count_source": "caller_supplied",
        "context_tokens": context,
        "requested_output_tokens": output,
        "reserved_prompt_tokens": reserved_prompt_tokens,
        "remaining_after_reservation": context - needed,
    }


def marginal_api_usd_declaration(billing: BillingPolicy) -> dict[str, Any]:
    """Describe dollar treatment for the existing cost ledger. This module does not price it."""

    if billing.kind == "owned_compute":
        return {
            "billing_kind": "owned_compute",
            "marginal_api_usd": 0,
            "source": "operator_declared_owned_compute",
            "priced_by_this_module": False,
        }
    return {
        "billing_kind": "metered",
        "tariff_id": billing.tariff_id,
        "tariff_version": billing.tariff_version,
        "marginal_api_usd": None,
        "source": "tariff_reference_only",
        "priced_by_this_module": False,
    }


def public_manifest(resolved: ResolvedLocalRun) -> dict[str, Any]:
    """Safe run projection: ids, limits, and fingerprints, without URLs or auth names."""

    document = resolved.document
    forbidden = _private_strings(document)
    manifest = {
        "schema_version": 1,
        "kind": "public_manifest",
        "profile_hash": resolved.profile_hash,
        "selection_hash": resolved.selection_hash,
        "inference_policy": resolved.inference_policy,
        "coordinator": _public_coordinator(document),
        "roles": {
            name: _public_role(role, document)
            for name, role in resolved.roles.items()
        },
        "run_budget": _public_budget(document.run_budget),
    }
    return _redacted_copy(manifest, forbidden)


def private_worker_snapshot(resolved: ResolvedLocalRun) -> dict[str, Any]:
    """Worker copy with normalized URLs and auth reference names, never secret values."""

    snapshot = {
        "schema_version": 1,
        "kind": "private_worker_snapshot",
        "profile_hash": resolved.profile_hash,
        "selection_hash": resolved.selection_hash,
        "inference_policy": resolved.inference_policy,
        "document": resolved.document.canonical_body(),
        "selections": [
            {"role": role.role, "deployment_id": role.deployment_id}
            for role in resolved.roles.values()
        ],
    }
    reloaded = load_private_worker_snapshot(snapshot)
    if reloaded.profile_hash != resolved.profile_hash or reloaded.selection_hash != resolved.selection_hash:
        raise LocalInferenceError("snapshot_mismatch")
    return json.loads(canonical_json(snapshot))


def load_private_worker_snapshot(payload: Mapping[str, Any]) -> ResolvedLocalRun:
    """Rebuild a worker snapshot and refuse a body that no longer matches its hashes."""

    if type(payload) is not dict:
        raise LocalInferenceError("snapshot_kind_mismatch")
    allowed = {
        "schema_version", "kind", "profile_hash", "selection_hash",
        "inference_policy", "document", "selections",
    }
    _reject_unknown(payload, allowed)
    version = payload.get("schema_version")
    if type(version) is not int or version != 1 or payload.get("kind") != "private_worker_snapshot":
        raise LocalInferenceError("snapshot_kind_mismatch")
    document = load_profile_data(_require_mapping(payload, "document"))
    if payload.get("profile_hash") != document.profile_hash:
        raise LocalInferenceError("snapshot_mismatch")
    selections = []
    raw_selections = payload.get("selections")
    if type(raw_selections) is not list or not raw_selections:
        raise LocalInferenceError("invalid_field", "roles")
    for item in raw_selections:
        if type(item) is not dict:
            raise LocalInferenceError("invalid_field", "roles")
        _reject_unknown(item, {"role", "deployment_id"})
        selections.append(RoleSelection(
            role=_identifier(item.get("role"), "roles"),
            deployment_id=_identifier(item.get("deployment_id"), "deployments"),
        ))
    policy = payload.get("inference_policy")
    if type(policy) is not str or policy not in _POLICIES:
        raise LocalInferenceError("invalid_field", "inference_policy")
    resolved = resolve_run(document, selections, inference_policy=policy)
    if resolved.selection_hash != payload.get("selection_hash"):
        raise LocalInferenceError("snapshot_mismatch")
    return resolved


def credential_configured(auth: AuthRef, environ: Mapping[str, str]) -> bool:
    """Report whether auth is satisfied without copying a secret into the result."""

    if auth.kind == "none":
        return True
    if auth.name is None:
        return False
    try:
        value = environ[auth.name]
    except KeyError:
        return False
    if type(value) is not str:
        return False
    return value.strip() != ""


def require_auth_available(auth: AuthRef, environ: Mapping[str, str]) -> None:
    if not credential_configured(auth, environ):
        raise LocalInferenceError("credential_unavailable")


def checkpoint_binding(resolved: ResolvedLocalRun) -> dict[str, Any]:
    """Public checkpoint section. Absence of this object is the legacy format."""

    binding = _binding_body(resolved)
    binding["schema_version"] = 1
    binding["selection_hash"] = resolved.selection_hash
    return json.loads(canonical_json(binding))


def reconcile_checkpoint(
    saved: Mapping[str, Any] | None,
    resolved: ResolvedLocalRun | None,
    *,
    reconfigure: bool,
) -> dict[str, Any]:
    """Resume or explicitly reconfigure. Never invents a local binding or resets a budget."""

    if type(reconfigure) is not bool:
        raise LocalInferenceError("invalid_checkpoint_binding")
    legacy = _saved_binding(saved)
    if legacy is None and resolved is None:
        return {
            "action": "legacy",
            "reset_budget": False,
            "profile_hash": None,
            "selection_hash": None,
        }
    if legacy is None and resolved is not None:
        if not reconfigure:
            raise LocalInferenceError("legacy_checkpoint_refuses_local_binding")
        return {
            "action": "reconfigure",
            "reset_budget": False,
            "profile_hash": resolved.profile_hash,
            "selection_hash": resolved.selection_hash,
        }
    if resolved is None:
        raise LocalInferenceError("resolved_profile_required")
    assert legacy is not None
    if legacy["selection_hash"] == resolved.selection_hash and legacy["profile_hash"] == resolved.profile_hash:
        return {
            "action": "resume",
            "reset_budget": False,
            "profile_hash": resolved.profile_hash,
            "selection_hash": resolved.selection_hash,
        }
    if not reconfigure:
        raise LocalInferenceError("profile_conflict")
    return {
        "action": "reconfigure",
        "reset_budget": False,
        "profile_hash": resolved.profile_hash,
        "selection_hash": resolved.selection_hash,
    }


def _saved_binding(saved: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if saved is None:
        return None
    if type(saved) is not dict:
        raise LocalInferenceError("invalid_checkpoint_binding")
    if "local_inference" not in saved:
        return None
    value = saved["local_inference"]
    if type(value) is not dict:
        raise LocalInferenceError("invalid_checkpoint_binding")
    allowed = {"schema_version", "profile_hash", "selection_hash", "inference_policy", "roles"}
    _reject_unknown(value, allowed)
    version = value.get("schema_version")
    if type(version) is not int or version != 1:
        raise LocalInferenceError("invalid_checkpoint_binding")
    profile_hash = value.get("profile_hash")
    selection_hash = value.get("selection_hash")
    policy = value.get("inference_policy")
    roles = value.get("roles")
    if (
        type(profile_hash) is not str or _HEX64.fullmatch(profile_hash) is None
        or type(selection_hash) is not str or _HEX64.fullmatch(selection_hash) is None
        or type(policy) is not str or policy not in _POLICIES or type(roles) is not dict or not roles
    ):
        raise LocalInferenceError("invalid_checkpoint_binding")
    for role, item in roles.items():
        if _IDENTIFIER.fullmatch(role) is None or type(item) is not dict:
            raise LocalInferenceError("invalid_checkpoint_binding")
        _reject_unknown(item, {
            "deployment_id", "deployment_fingerprint", "endpoint_fingerprint",
            "capacity_group_fingerprint",
        })
        for field in (
            "deployment_id", "deployment_fingerprint", "endpoint_fingerprint",
            "capacity_group_fingerprint",
        ):
            token = item.get(field)
            if type(token) is not str or not token:
                raise LocalInferenceError("invalid_checkpoint_binding")
            if field == "deployment_id":
                if _IDENTIFIER.fullmatch(token) is None:
                    raise LocalInferenceError("invalid_checkpoint_binding")
            elif _HEX64.fullmatch(token) is None:
                raise LocalInferenceError("invalid_checkpoint_binding")
    expected = content_hash({
        "profile_hash": profile_hash,
        "inference_policy": policy,
        "roles": roles,
    })
    if expected != selection_hash:
        raise LocalInferenceError("invalid_checkpoint_binding")
    return value


def _binding_body(resolved: ResolvedLocalRun) -> dict[str, Any]:
    return {
        "profile_hash": resolved.profile_hash,
        "inference_policy": resolved.inference_policy,
        "roles": {
            name: {
                "deployment_id": role.deployment_id,
                "deployment_fingerprint": role.deployment_fingerprint,
                "endpoint_fingerprint": role.endpoint_fingerprint,
                "capacity_group_fingerprint": role.capacity_group_fingerprint,
            }
            for name, role in resolved.roles.items()
        },
    }


def _selection_hash(resolved: ResolvedLocalRun) -> str:
    return content_hash(_binding_body(resolved))


def _canonical_body(document: ProfileDocument) -> dict[str, Any]:
    body: dict[str, Any] = {
        "schema": 1,
        "endpoints": {name: _endpoint_body(item) for name, item in document.endpoints.items()},
        "deployments": {name: _deployment_body(item) for name, item in document.deployments.items()},
        "capacity_groups": {name: _group_body(item) for name, item in document.capacity_groups.items()},
    }
    if document.coordinator is not None:
        body["coordinator"] = {
            "installation_id": document.coordinator.installation_id,
            "scope_id": document.coordinator.scope_id,
        }
    if document.run_budget is not None:
        body["run_budget"] = {
            "max_local_dispatches": document.run_budget.max_local_dispatches,
            "max_local_requested_output_tokens": document.run_budget.max_local_requested_output_tokens,
            "max_local_observed_request_wall_s": document.run_budget.max_local_observed_request_wall_s,
        }
    return body


def _endpoint_body(endpoint: EndpointProfile) -> dict[str, Any]:
    auth: dict[str, Any] = {"kind": endpoint.auth.kind}
    if endpoint.auth.name is not None:
        auth["name"] = endpoint.auth.name
    body: dict[str, Any] = {
        "base_url": endpoint.base_url,
        "dialect": endpoint.dialect,
        "auth": auth,
        "capacity_group": endpoint.capacity_group,
        "max_inflight": endpoint.max_inflight,
        "billing": _billing_body(endpoint.billing),
    }
    return body


def _billing_body(billing: BillingPolicy) -> dict[str, Any]:
    if billing.kind == "owned_compute":
        return {"kind": "owned_compute"}
    return {
        "kind": "metered",
        "tariff_id": billing.tariff_id,
        "tariff_version": billing.tariff_version,
    }


def _deployment_body(deployment: DeploymentProfile) -> dict[str, Any]:
    reasoning: dict[str, Any] = {
        "mode": deployment.reasoning.mode,
        "output_limit_includes_reasoning": deployment.reasoning.output_limit_includes_reasoning,
    }
    if deployment.reasoning.effort is not None:
        reasoning["effort"] = deployment.reasoning.effort
    body: dict[str, Any] = {
        "endpoint": deployment.endpoint,
        "model": deployment.model,
        "context_tokens": deployment.context_tokens,
        "max_output_tokens": deployment.max_output_tokens,
        "output_semantics": deployment.output_semantics,
        "tools": deployment.tools,
        "native_n": deployment.native_n,
        "execution": deployment.execution,
        "reasoning": reasoning,
        "protocol": protocol_body(deployment.protocol),
        "sampling": {
            "temperature": _axis_body(deployment.sampling.temperature),
            "top_p": _axis_body(deployment.sampling.top_p),
        },
    }
    for field in _IDENTITY_FIELDS:
        item = deployment.identity[field]
        if item.source == "configured" and item.value is not None:
            body[field] = item.value
    return body


def _axis_body(axis: SamplingAxis) -> dict[str, Any]:
    body: dict[str, Any] = {"policy": axis.policy}
    if axis.value is not None:
        body["value"] = axis.value
    return body


def _group_body(group: CapacityGroupPolicy) -> dict[str, Any]:
    return {
        "max_inflight": group.max_inflight,
        "max_queued": group.max_queued,
        "queue_timeout_s": group.queue_timeout_s,
        "request_timeout_s": group.request_timeout_s,
    }


def _parse_endpoints(data: Mapping[str, Any]) -> dict[str, EndpointProfile]:
    endpoints: dict[str, EndpointProfile] = {}
    origins: dict[str, str] = {}
    for raw_name, raw in data.items():
        name = raw_name if type(raw_name) is str and _IDENTIFIER.fullmatch(raw_name) else None
        if name is None:
            raise LocalInferenceError("invalid_field", "endpoints")
        item = _require_mapping_value(raw, "endpoints")
        _reject_unknown(item, _ENDPOINT_FIELDS)
        url = _normalize_base_url(item.get("base_url"))
        if url in origins:
            raise LocalInferenceError("duplicate_origin")
        origins[url] = name
        endpoints[name] = EndpointProfile(
            name=name,
            base_url=url,
            dialect=_choice(item.get("dialect"), _DIALECTS, "dialect"),
            auth=_parse_auth(item.get("auth")),
            capacity_group=_identifier(item.get("capacity_group"), "capacity_group"),
            max_inflight=_bounded_int(item.get("max_inflight"), minimum=1, maximum=_MAX_INFLIGHT, field="max_inflight"),
            billing=_parse_billing(item.get("billing")),
        )
    return endpoints


def _parse_deployments(data: Mapping[str, Any]) -> dict[str, DeploymentProfile]:
    deployments: dict[str, DeploymentProfile] = {}
    for raw_name, raw in data.items():
        name = raw_name if type(raw_name) is str and _IDENTIFIER.fullmatch(raw_name) else None
        if name is None:
            raise LocalInferenceError("invalid_field", "deployments")
        item = _require_mapping_value(raw, "deployments")
        _reject_unknown(item, _DEPLOYMENT_FIELDS)
        for field in (
            "endpoint", "model", "context_tokens", "max_output_tokens", "output_semantics",
            "tools", "native_n", "execution", "reasoning", "sampling",
        ):
            if field not in item:
                raise LocalInferenceError("invalid_field", field)
        context = _bounded_int(item.get("context_tokens"), minimum=2, maximum=_MAX_TOKENS, field="context_tokens")
        output = _bounded_int(item.get("max_output_tokens"), minimum=1, maximum=_MAX_TOKENS, field="max_output_tokens")
        if output >= context:
            raise LocalInferenceError("invalid_field", "max_output_tokens")
        native_n = item.get("native_n")
        if native_n != "unsupported":
            raise LocalInferenceError("native_batch_unsupported")
        deployments[name] = DeploymentProfile(
            name=name,
            endpoint=_identifier(item.get("endpoint"), "endpoint"),
            model=_model(item.get("model")),
            context_tokens=context,
            max_output_tokens=output,
            output_semantics=_choice(item.get("output_semantics"), _OUTPUT, "output_semantics"),
            tools=_choice(item.get("tools"), _TOOLS, "tools"),
            native_n="unsupported",
            execution=_choice(item.get("execution"), _EXECUTION, "execution"),
            reasoning=_parse_reasoning(item.get("reasoning")),
            sampling=_parse_sampling(item.get("sampling")),
            identity=_proxy(_parse_identity(item)),
            protocol=parse_protocol_policy(item.get("protocol", {"schema": 1})),
        )
    return deployments


def _parse_groups(data: Mapping[str, Any]) -> dict[str, CapacityGroupPolicy]:
    groups: dict[str, CapacityGroupPolicy] = {}
    for raw_name, raw in data.items():
        name = raw_name if type(raw_name) is str and _IDENTIFIER.fullmatch(raw_name) else None
        if name is None:
            raise LocalInferenceError("invalid_field", "capacity_groups")
        item = _require_mapping_value(raw, "capacity_groups")
        _reject_unknown(item, _GROUP_FIELDS)
        for field in _GROUP_FIELDS:
            if field not in item:
                raise LocalInferenceError("invalid_field", field)
        groups[name] = CapacityGroupPolicy(
            name=name,
            max_inflight=_bounded_int(item.get("max_inflight"), minimum=1, maximum=_MAX_INFLIGHT, field="max_inflight"),
            max_queued=_bounded_int(item.get("max_queued"), minimum=0, maximum=_MAX_INFLIGHT, field="max_queued"),
            queue_timeout_s=_bounded_int(item.get("queue_timeout_s"), minimum=1, maximum=_MAX_TIMEOUT_S, field="queue_timeout_s"),
            request_timeout_s=_bounded_int(item.get("request_timeout_s"), minimum=1, maximum=_MAX_TIMEOUT_S, field="request_timeout_s"),
        )
    return groups


def _parse_coordinator(value: Any) -> CoordinatorIdentity:
    item = _require_mapping_value(value, "coordinator")
    _reject_unknown(item, {"installation_id", "scope_id"})
    return CoordinatorIdentity(
        installation_id=_identifier(item.get("installation_id"), "installation_id"),
        scope_id=_identifier(item.get("scope_id"), "scope_id"),
    )


def _parse_budget(value: Any) -> RunBudgetLimits:
    item = _require_mapping_value(value, "run_budget")
    _reject_unknown(item, _BUDGET_FIELDS)
    for field in _BUDGET_FIELDS:
        if field not in item:
            raise LocalInferenceError("invalid_field", field)
    return RunBudgetLimits(
        max_local_dispatches=_bounded_int(
            item.get("max_local_dispatches"), minimum=1, maximum=_MAX_COUNT, field="max_local_dispatches",
        ),
        max_local_requested_output_tokens=_bounded_int(
            item.get("max_local_requested_output_tokens"),
            minimum=1,
            maximum=_MAX_COUNT,
            field="max_local_requested_output_tokens",
        ),
        max_local_observed_request_wall_s=_bounded_int(
            item.get("max_local_observed_request_wall_s"),
            minimum=1,
            maximum=_MAX_WALL_S,
            field="max_local_observed_request_wall_s",
        ),
    )


def _link_profile(
    endpoints: Mapping[str, EndpointProfile],
    deployments: Mapping[str, DeploymentProfile],
    groups: Mapping[str, CapacityGroupPolicy],
    coordinator: CoordinatorIdentity | None,
    budget: RunBudgetLimits | None,
) -> None:
    if deployments and budget is None:
        raise LocalInferenceError("run_budget_required")
    if (endpoints or groups) and coordinator is None:
        raise LocalInferenceError("coordinator_required")
    used_groups: set[str] = set()
    used_endpoints: set[str] = set()
    for deployment in deployments.values():
        endpoint = endpoints.get(deployment.endpoint)
        if endpoint is None:
            raise LocalInferenceError("unknown_endpoint")
        validate_protocol_policy(
            deployment.protocol, dialect=endpoint.dialect,
            reasoning_mode=deployment.reasoning.mode, reasoning_effort=deployment.reasoning.effort,
        )
        used_endpoints.add(endpoint.name)
        group = groups.get(endpoint.capacity_group)
        if group is None:
            raise LocalInferenceError("unknown_capacity_group")
        if endpoint.max_inflight > group.max_inflight:
            raise LocalInferenceError("endpoint_cap_exceeds_group")
        used_groups.add(group.name)
    if set(endpoints) != used_endpoints and (endpoints or deployments):
        raise LocalInferenceError("invalid_field", "endpoints")
    if set(groups) != used_groups and (groups or endpoints):
        raise LocalInferenceError("invalid_field", "capacity_groups")


def _parse_auth(value: Any) -> AuthRef:
    item = _require_mapping_value(value, "auth")
    kind = item.get("kind")
    if kind == "none":
        _reject_unknown(item, {"kind"})
        return AuthRef(kind="none")
    if kind == "env":
        _reject_unknown(item, {"kind", "name"})
        name = item.get("name")
        if type(name) is not str or _ENV_NAME.fullmatch(name) is None:
            raise LocalInferenceError("invalid_field", "auth")
        if any(marker in name for marker in _CLOUD_MARKERS):
            raise LocalInferenceError("cloud_credential_reuse")
        return AuthRef(kind="env", name=name)
    raise LocalInferenceError("invalid_field", "auth")


def _parse_billing(value: Any) -> BillingPolicy:
    item = _require_mapping_value(value, "billing")
    kind = item.get("kind")
    if kind == "owned_compute":
        _reject_unknown(item, {"kind"})
        return BillingPolicy(kind="owned_compute")
    if kind == "metered":
        _reject_unknown(item, {"kind", "tariff_id", "tariff_version"})
        tariff = item.get("tariff_id")
        if type(tariff) is not str or _IDENTIFIER.fullmatch(tariff) is None:
            raise LocalInferenceError("invalid_field", "billing")
        version = _bounded_int(item.get("tariff_version"), minimum=1, maximum=_MAX_COUNT, field="billing")
        return BillingPolicy(kind="metered", tariff_id=tariff, tariff_version=version)
    raise LocalInferenceError("invalid_field", "billing")


def _parse_reasoning(value: Any) -> ReasoningPolicy:
    item = _require_mapping_value(value, "reasoning")
    _reject_unknown(item, {"mode", "effort", "output_limit_includes_reasoning"})
    mode = _choice(item.get("mode"), _REASONING, "reasoning")
    effort = item.get("effort")
    if effort is None and "effort" in item:
        raise LocalInferenceError("invalid_field", "effort")
    if effort is not None:
        effort = _choice(effort, _EFFORT, "effort")
        if mode in {"provider-default", "off"}:
            raise LocalInferenceError("invalid_field", "effort")
    return ReasoningPolicy(
        mode=mode,
        effort=effort,
        output_limit_includes_reasoning=_tri_state(
            item.get("output_limit_includes_reasoning"), "output_limit_includes_reasoning",
        ),
    )


def _parse_sampling(value: Any) -> SamplingPolicy:
    item = _require_mapping_value(value, "sampling")
    _reject_unknown(item, {"temperature", "top_p"})
    return SamplingPolicy(
        temperature=_parse_axis(item.get("temperature"), "temperature", "2"),
        top_p=_parse_axis(item.get("top_p"), "top_p", "1"),
    )


def _parse_axis(value: Any, field: str, upper: str) -> SamplingAxis:
    item = _require_mapping_value(value, field)
    _reject_unknown(item, {"policy", "value"})
    policy = _choice(item.get("policy"), _SAMPLING, field)
    if policy == "fixed":
        if "value" not in item:
            raise LocalInferenceError("invalid_field", field)
        return SamplingAxis(policy=policy, value=_canonical_decimal(item.get("value"), upper=upper, field=field))
    if "value" in item:
        raise LocalInferenceError("invalid_field", field)
    return SamplingAxis(policy=policy)


def _parse_identity(item: Mapping[str, Any]) -> dict[str, IdentityField]:
    identity: dict[str, IdentityField] = {}
    for field in _IDENTITY_FIELDS:
        if field not in item:
            identity[field] = IdentityField(source="unknown")
            continue
        value = item.get(field)
        if type(value) is not str or _PLAIN.fullmatch(value) is None:
            raise LocalInferenceError("invalid_field", field)
        identity[field] = IdentityField(source="configured", value=value)
    return identity


def _deployment_fingerprint(document: ProfileDocument, deployment: DeploymentProfile) -> str:
    endpoint = document.endpoints[deployment.endpoint]
    return fingerprint("local_deployment", {
        "deployment": deployment.name,
        "profile_schema": 1,
        "endpoint": _endpoint_fingerprint_payload(endpoint),
        "model": deployment.model,
        "identity": {
            field: (
                {"source": "unknown"}
                if deployment.identity[field].source == "unknown"
                else {"source": "configured", "value": deployment.identity[field].value}
            )
            for field in _IDENTITY_FIELDS
        },
        "limits": {
            "context_tokens": deployment.context_tokens,
            "max_output_tokens": deployment.max_output_tokens,
            "output_semantics": deployment.output_semantics,
        },
        "protocol": protocol_body(deployment.protocol),
        "controls": {
            "reasoning_mode": deployment.reasoning.mode,
            "reasoning_effort": deployment.reasoning.effort,
            "output_limit_includes_reasoning": deployment.reasoning.output_limit_includes_reasoning,
            "tools": deployment.tools,
            "native_n": deployment.native_n,
            "sampling": {
                "temperature": _axis_body(deployment.sampling.temperature),
                "top_p": _axis_body(deployment.sampling.top_p),
            },
        },
        "execution": deployment.execution,
        "execution_source": "configured",
    })


def _endpoint_fingerprint_payload(endpoint: EndpointProfile) -> dict[str, Any]:
    return {
        "name": endpoint.name,
        "origin_fingerprint": endpoint.origin_fingerprint,
        "dialect": endpoint.dialect,
        "auth_kind": endpoint.auth.kind,
        "auth_reference_fingerprint": endpoint.auth_reference_fingerprint,
        "max_inflight": endpoint.max_inflight,
        "capacity_group": endpoint.capacity_group,
        "billing_kind": endpoint.billing.kind,
        "tariff_id": endpoint.billing.tariff_id,
        "tariff_version": endpoint.billing.tariff_version,
    }


def _group_fingerprint(document: ProfileDocument, group: CapacityGroupPolicy) -> str:
    assert document.coordinator is not None
    return fingerprint("capacity_group", {
        "installation_id": document.coordinator.installation_id,
        "scope_id": document.coordinator.scope_id,
        "group": group.name,
        "max_inflight": group.max_inflight,
        "max_queued": group.max_queued,
        "queue_timeout_s": group.queue_timeout_s,
        "request_timeout_s": group.request_timeout_s,
    })


def _public_role(role: ResolvedRole, document: ProfileDocument) -> dict[str, Any]:
    deployment = document.deployments[role.deployment_id]
    endpoint = document.endpoints[role.endpoint_id]
    return {
        "deployment_id": role.deployment_id,
        "endpoint_id": role.endpoint_id,
        "dialect": role.dialect,
        "model": role.model,
        "revision": _public_identity(deployment.identity["revision"]),
        "server_build": _public_identity(deployment.identity["server_build"]),
        "template_id": _public_identity(deployment.identity["template_id"]),
        "parser_id": _public_identity(deployment.identity["parser_id"]),
        "deployment_fingerprint": role.deployment_fingerprint,
        "endpoint_fingerprint": role.endpoint_fingerprint,
        "capacity_group": role.capacity_group,
        "capacity_group_fingerprint": role.capacity_group_fingerprint,
        "context_tokens": role.context_tokens,
        "max_output_tokens": role.max_output_tokens,
        "output_semantics": role.output_semantics,
        "reasoning_mode": role.reasoning_mode,
        "reasoning_effort": role.reasoning_effort,
        "output_limit_includes_reasoning": role.output_limit_includes_reasoning,
        "tools": role.tools,
        "native_n": role.native_n,
        "execution": role.execution,
        "execution_source": "configured",
        "billing": marginal_api_usd_declaration(endpoint.billing),
    }


def _public_identity(field: IdentityField) -> dict[str, Any]:
    if field.source == "unknown":
        return {"source": "unknown"}
    return {"source": "configured", "value": field.value}


def _public_coordinator(document: ProfileDocument) -> dict[str, Any] | None:
    if document.coordinator is None:
        return None
    return {
        "installation_id": document.coordinator.installation_id,
        "scope_id": document.coordinator.scope_id,
    }


def _public_budget(budget: RunBudgetLimits | None) -> dict[str, int] | None:
    if budget is None:
        return None
    return {
        "max_local_dispatches": budget.max_local_dispatches,
        "max_local_requested_output_tokens": budget.max_local_requested_output_tokens,
        "max_local_observed_request_wall_s": budget.max_local_observed_request_wall_s,
    }


def _private_strings(document: ProfileDocument) -> tuple[str, ...]:
    values: list[str] = []
    for endpoint in document.endpoints.values():
        values.append(endpoint.base_url)
        if endpoint.auth.name is not None:
            values.append(endpoint.auth.name)
    return tuple(values)


def _redacted_copy(value: dict[str, Any], forbidden: Sequence[str]) -> dict[str, Any]:
    encoded = canonical_json(value)
    for item in forbidden:
        if len(item) >= 4 and item in encoded:
            raise LocalInferenceError("redaction_failed")
    cloned = json.loads(encoded)
    if type(cloned) is not dict:
        raise LocalInferenceError("redaction_failed")
    return cloned


def _normalize_base_url(value: Any) -> str:
    if type(value) is not str or not value or value != value.strip() or any(ord(ch) < 33 or ord(ch) == 127 for ch in value):
        raise LocalInferenceError("invalid_base_url")
    if any(mark in value for mark in ("?", "#", "\\", "@")):
        if "@" in value:
            raise LocalInferenceError("embedded_credentials")
        raise LocalInferenceError("invalid_base_url")
    parse_failed = False
    try:
        parts = urlsplit(value)
        if parts.username is not None or parts.password is not None:
            raise LocalInferenceError("embedded_credentials")
        scheme = parts.scheme.lower()
        host = parts.hostname
        if scheme not in {"http", "https"} or not host:
            raise LocalInferenceError("invalid_base_url")
        host = host.lower()
        if "%" in host:
            raise LocalInferenceError("invalid_base_url")
        port = parts.port
    except LocalInferenceError:
        raise
    except (UnicodeError, ValueError):
        parse_failed = True
    # Raise outside the handler so even the exception context cannot retain
    # a private host, port, or credential-bearing parser message.
    if parse_failed:
        raise LocalInferenceError("invalid_base_url")
    if port is not None and (port <= 0 or port > 65535):
        raise LocalInferenceError("invalid_base_url")
    path = parts.path
    if path.startswith("//"):
        raise LocalInferenceError("invalid_base_url")
    default = 80 if scheme == "http" else 443
    authority = f"[{host}]" if ":" in host else host
    if port is not None and port != default:
        authority = f"{authority}:{port}"
    return f"{scheme}://{authority}{path}"


def _reject_model_override(selection: RoleSelection, deployment: DeploymentProfile) -> None:
    if selection.requested_model is None:
        return
    if type(selection.requested_model) is not str or selection.requested_model != deployment.model:
        raise LocalInferenceError("model_conflict")


def _reject_reasoning_override(selection: RoleSelection, deployment: DeploymentProfile) -> None:
    if selection.requested_reasoning_mode is not None and selection.requested_reasoning_mode != deployment.reasoning.mode:
        raise LocalInferenceError("reasoning_conflict")
    if selection.requested_reasoning_effort is not None and selection.requested_reasoning_effort != deployment.reasoning.effort:
        raise LocalInferenceError("reasoning_conflict")


def _prefixed_hash(kind: str, text: str) -> str:
    material = f"local-inference/{kind}/v1\0{text}".encode("utf-8")
    return hashlib.sha256(material).hexdigest()


def _canonical_decimal(value: Any, *, upper: str, field: str) -> str:
    if type(value) is bool:
        raise LocalInferenceError("invalid_field", field)
    if type(value) is int:
        raw = str(value)
    elif type(value) is float:
        raw = str(value)
    elif type(value) is str:
        raw = value
    else:
        raise LocalInferenceError("invalid_field", field)
    if re.fullmatch(_DECIMAL, raw) is None:
        raise LocalInferenceError("invalid_field", field)
    whole, dot, fraction = raw.partition(".")
    if fraction:
        fraction = fraction.rstrip("0")
        raw = whole if not fraction else whole + "." + fraction
    if dot and not fraction and type(value) is str and raw != value.partition(".")[0]:
        raw = whole
    upper_number = _decimal_tuple(upper)
    current = _decimal_tuple(raw)
    if current < (0, 0) or current > upper_number:
        raise LocalInferenceError("invalid_field", field)
    return raw


def _decimal_tuple(value: str) -> tuple[int, int]:
    whole, _, fraction = value.partition(".")
    return (int(whole), int((fraction + "000000")[:6]))


def _tri_state(value: Any, field: str) -> str:
    if value is True or value == "true":
        return "true"
    if value is False or value == "false":
        return "false"
    if value == "unknown":
        return "unknown"
    raise LocalInferenceError("invalid_field", field)


def _choice(value: Any, allowed: frozenset[str], field: str) -> str:
    if type(value) is str and value in allowed:
        return value
    raise LocalInferenceError("invalid_field", field)


def _identifier(value: Any, field: str) -> str:
    if type(value) is not str or _IDENTIFIER.fullmatch(value) is None:
        raise LocalInferenceError("invalid_field", field)
    return value


def _model(value: Any) -> str:
    if type(value) is not str or _MODEL.fullmatch(value) is None:
        raise LocalInferenceError("invalid_field", "model")
    return value


def _bounded_int(value: Any, *, minimum: int, maximum: int, field: str) -> int:
    if type(value) is not int or isinstance(value, bool) or value < minimum or value > maximum:
        raise LocalInferenceError("invalid_field", field)
    return value


def _require_mapping(data: Mapping[str, Any], field: str) -> dict[str, Any]:
    value = data.get(field)
    return _require_mapping_value(value, field)


def _require_mapping_value(value: Any, field: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise LocalInferenceError("invalid_field", field)
    return value


def _reject_unknown(data: Mapping[str, Any], allowed: set[str] | frozenset[str]) -> None:
    for key in data:
        if key not in allowed:
            raise LocalInferenceError("unknown_field")


def _proxy(items: dict[str, Any]) -> Mapping[str, Any]:
    return MappingProxyType(dict(items))
