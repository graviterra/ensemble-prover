"""Auxiliary local and Cursor role wiring.

Subscription roles use ``mini_prover._make_mini_role_client``. Local roles use
``local_inference.roles.local_role_config`` and its JSON binding. The binding
keys are ``snapshot``, ``role``, ``coordinator_root``, ``budget_root``, and
``budget_id``. ``role`` is the resolved profile key. The HTTP endpoint stays
inside ``snapshot``. The client label is
``local://owned-compute/<deployment_fingerprint>`` or
``local://metered/<deployment_fingerprint>``.

``LocalRuntime.prepare_resources(binding, allow_create)`` creates this
workflow's finite grant only under explicit startup authority. The shared
runtime owns coordinator initialization and persists its incarnation in the
returned binding. Resume uses ``allow_create=False`` and refuses missing
coordinator, snapshot, or ledger state.
Local-only does not mean offline. Embedding and reranker devices default to
CPU when the main parser already has those destinations.
"""

from __future__ import annotations

import json
from pathlib import Path
import secrets
from typing import Any, Mapping, Sequence

from .local_inference.config import (
    RoleSelection,
    load_private_worker_snapshot,
    load_profile_path,
    private_worker_snapshot,
    public_manifest,
    resolve_run,
)
from .local_inference.errors import LocalInferenceError
from .local_inference.roles import (
    BINDING_KEYS,
    LocalPreparation,
    coordinator_root_from_environ,
    local_inference_binding,
    local_role_config,
    load_run_bundle,
    persist_local_inference,
)
from .local_inference.strictload import canonical_json, content_hash

_SUBSCRIPTION_BASES = {
    "codex://chatgpt",
    "claude-code://subscription",
    "cursor://subscription",
}
AUXILIARY_DEVICE_DEFAULTS = {"embedding_device": "cpu", "cross_encoder_device": "cpu"}


def coordinator_root(explicit: Path | str | None = None) -> str:
    if explicit is None or not str(explicit).strip():
        return str(coordinator_root_from_environ())
    return str(Path(explicit).expanduser().resolve())


def original_binding_role(cfg: Any) -> str | None:
    """Resolved profile key. A renamed ``cfg.name`` is not an allocation identity."""
    binding = getattr(cfg, "local_inference_binding", None)
    if binding is None:
        return None
    if not isinstance(binding, dict) or not binding.get("role"):
        raise ValueError("local binding is missing its original role key")
    return str(binding["role"])


def freeze_binding(binding: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if binding is None:
        return None
    try:
        copied = json.loads(json.dumps(binding))
    except (TypeError, ValueError):
        raise ValueError("local binding must be a JSON object") from None
    if set(copied) not in (
        set(BINDING_KEYS),
        set(BINDING_KEYS) | {"coordinator_id", "resource_marker"},
    ) or copied.get("role") != binding.get("role"):
        raise ValueError(
            "local binding must keep its original role, budget, and coordinator"
        )
    return copied


def _preparation(
    resolved: Any,
    *,
    inference_policy: str,
    coordinator: str,
    budget_id: str | None,
) -> LocalPreparation:
    snapshot = private_worker_snapshot(resolved)
    manifest = public_manifest(resolved)
    preparation = LocalPreparation(
        snapshot=json.loads(canonical_json(snapshot)),
        manifest=json.loads(canonical_json(manifest)),
        snapshot_hash=content_hash(snapshot),
        manifest_hash=content_hash(manifest),
        profile_hash=resolved.profile_hash,
        selection_hash=resolved.selection_hash,
        inference_policy=inference_policy,
        budget_id="",
        coordinator_root=coordinator,
        budget_root="",
        roles=tuple(resolved.roles),
    )
    return preparation.with_budget(budget_id or secrets.token_hex(16), coordinator)


def prepare_auxiliary(
    specs: Sequence[tuple[str, str, str | None]],
    *,
    inference_policy: str,
    coordinator: Path | str | None = None,
    budget_id: str | None = None,
    config_path: Path | str | None = None,
) -> LocalPreparation:
    """Resolve explicit auxiliary roles. This writes nothing and opens nothing."""
    if config_path is None:
        raise LocalInferenceError("snapshot_missing")
    document = load_profile_path(config_path)
    resolved = resolve_run(
        document,
        [
            RoleSelection(role, deployment, requested_model=model)
            for role, deployment, model in specs
        ],
        inference_policy=inference_policy,
    )
    return _preparation(
        resolved,
        inference_policy=resolved.inference_policy,
        coordinator=coordinator_root(coordinator),
        budget_id=budget_id,
    )


def rebind_saved_roles(
    directory: Path | str,
    specs: Sequence[tuple[str, str | None, str | None]],
    *,
    budget_id: str | None = None,
    inference_policy: str | None = None,
) -> LocalPreparation:
    """Point new role names at the saved deployment and coordinator.

    The new workflow receives a new budget id. The parent ledger is not reset
    and is not given a fresh allowance.
    """
    bundle = load_run_bundle(directory)
    if inference_policy not in {None, "mixed", "local-only"}:
        raise LocalInferenceError("invalid_field", "inference_policy")
    # Adoption can tighten a mixed source. An implicit mixed CLI default must
    # not weaken the source's existing local-only constraint.
    policy = (
        "local-only"
        if "local-only" in {bundle.inference_policy, inference_policy}
        else bundle.inference_policy
    )
    previous = load_private_worker_snapshot(bundle.snapshot)
    if "prover" in previous.roles:
        default_deployment = previous.roles["prover"].deployment_id
    elif len(previous.roles) == 1:
        default_deployment = next(iter(previous.roles.values())).deployment_id
    else:
        raise LocalInferenceError("unknown_role")
    resolved = resolve_run(
        previous.document,
        [
            RoleSelection(role, deployment or default_deployment, requested_model=model)
            for role, deployment, model in specs
        ],
        inference_policy=policy,
    )
    return _preparation(
        resolved,
        inference_policy=policy,
        coordinator=bundle.coordinator_root,
        budget_id=budget_id,
    )


def saved_local_adoption(
    config: Mapping[str, Any], directory: Path | str, model: str
) -> dict[str, Any]:
    """Return public adoption facts. A missing snapshot does not select a cloud provider."""
    try:
        bundle = load_run_bundle(directory)
    except LocalInferenceError as exc:
        raise ValueError(
            "local research requires the original private snapshot; a cloud provider was not selected"
        ) from exc
    public_hash = config.get("local_inference_profile_hash")
    nested = config.get("local_inference")
    if public_hash is None and isinstance(nested, dict):
        encoded = json.dumps(nested)
        if "http://" in encoded or "https://" in encoded:
            raise ValueError(
                "saved local binding contains a private URL and was refused"
            )
        public_hash = nested.get("profile_hash")
    if not isinstance(public_hash, str) or public_hash != bundle.profile_hash:
        raise ValueError(
            "local research requires the saved public binding; a cloud provider was not selected"
        )
    resolved = load_private_worker_snapshot(bundle.snapshot)
    selected = resolved.roles.get("prover")
    if selected is None or selected.model != model:
        matched = [role for role in resolved.roles.values() if role.model == model]
        selected = matched[0] if len(resolved.roles) == 1 and matched else None
    if selected is None or selected.model != model:
        raise ValueError(
            "saved local model does not match the deployment and was not substituted"
        )
    snapshot = Path(directory) / "local_inference" / "private_snapshot.json"
    return {
        "snapshot": snapshot,
        "deployment_id": selected.deployment_id,
        "policy": bundle.inference_policy,
        "profile_hash": bundle.profile_hash,
    }


def _resolved_binding(binding: Mapping[str, Any]) -> Any:
    if set(binding) not in (
        set(BINDING_KEYS),
        set(BINDING_KEYS) | {"coordinator_id", "resource_marker"},
    ):
        raise LocalInferenceError("invalid_field", "binding")
    resolved = load_private_worker_snapshot(binding["snapshot"])
    if binding["role"] not in resolved.roles:
        raise LocalInferenceError("unknown_role")
    return resolved


def public_binding_view(binding: Mapping[str, Any]) -> dict[str, Any]:
    copied = freeze_binding(binding)
    assert copied is not None
    resolved = _resolved_binding(copied)
    role = resolved.roles[copied["role"]]
    view = {
        "role": copied["role"],
        "budget_id": copied["budget_id"],
        "profile_hash": resolved.profile_hash,
        "model": role.model,
        "deployment_id": role.deployment_id,
        "deployment_fingerprint": role.deployment_fingerprint,
        "billing_kind": role.billing_kind,
        "offline": False,
        "auxiliary_devices": dict(AUXILIARY_DEVICE_DEFAULTS),
    }
    if role.endpoint_id and any(
        endpoint.base_url and endpoint.base_url in json.dumps(view)
        for endpoint in resolved.document.endpoints.values()
    ):
        raise LocalInferenceError("redaction_failed")
    return view


def transport_record(cfg: Any) -> dict[str, Any]:
    binding = getattr(cfg, "local_inference_binding", None)
    if not isinstance(binding, dict):
        return {"base_url": str(getattr(cfg, "base_url", ""))}
    view = public_binding_view(binding)
    return {
        "transport": "local",
        "model": view["model"],
        "deployment_fingerprint": view["deployment_fingerprint"],
        "offline": False,
        "auxiliary_devices": view["auxiliary_devices"],
    }


class LocalRuntime:
    """Budget and coordinator admission for one auxiliary workflow."""

    @staticmethod
    def prepare_resources(
        binding: Mapping[str, Any], allow_create: bool
    ) -> dict[str, Any]:
        from .local_inference.runtime import prepare_resources

        copied = freeze_binding(binding)
        assert copied is not None
        return prepare_resources(copied, allow_create=allow_create)

    @staticmethod
    def open_budget(binding: Mapping[str, Any]) -> Any:
        from .local_inference.budget import LocalComputeLedger

        copied = freeze_binding(binding)
        assert copied is not None
        return LocalComputeLedger.open(copied["budget_root"])

    @staticmethod
    def open_coordinator(binding: Mapping[str, Any]) -> Any:
        from .local_inference.capacity import CapacityCoordinator

        copied = freeze_binding(binding)
        assert copied is not None
        resolved = _resolved_binding(copied)
        return CapacityCoordinator.open(
            copied["coordinator_root"],
            installation_id=resolved.document.coordinator.installation_id,
            scope_id=resolved.document.coordinator.scope_id,
        )


def auxiliary_role_config(
    preparation: LocalPreparation,
    role: str,
    *,
    timeout_s: float | None,
    model: str | None = None,
) -> Any:
    from types import SimpleNamespace

    cfg = local_role_config(
        preparation,
        role_name=role,
        model=model,
        timeout_s=timeout_s,
        request_timeout_s=None,
        request_timeout_disabled=None,
        cli_args=SimpleNamespace(llm_deadline_policy="hard"),
    )
    cfg.operation_timeout_s = cfg.timeout_s
    return cfg


def workflow_client(cfg: Any) -> Any:
    from .mini_prover import _make_mini_role_client
    from .models import OpenAICompatClient

    base = str(getattr(cfg, "base_url", "") or "")
    if base.startswith("local://"):
        cfg.local_inference_binding = LocalRuntime.prepare_resources(
            cfg.local_inference_binding,
            allow_create=False,
        )
        try:
            return _make_mini_role_client(cfg)
        except SystemExit as exc:
            raise RuntimeError(str(exc) or "local_client_unavailable") from None
    if base in _SUBSCRIPTION_BASES:
        return _make_mini_role_client(cfg)
    return OpenAICompatClient(cfg)


def wire_response_format(client: Any, requested: str | None) -> str | None:
    """Choose the wire format. Prompt JSON and the host parser stay authoritative.

    Subscription adapters retain their host-side JSON validation contract.
    The local protocol has no ``json_object`` or JSON-schema generation switch.
    ``None`` and ``json`` are
    the only requested values; anything else, or ``response_format_required``,
    is refused instead of being dropped on the wire.
    """
    cfg = getattr(client, "cfg", None)
    required = getattr(cfg, "response_format_required", None)
    if required not in (None, False, ""):
        raise ValueError(
            "explicit response_format is unsupported and was not downgraded"
        )
    if requested not in (None, "json"):
        raise ValueError(
            "explicit response_format is unsupported and was not downgraded"
        )
    base = str(getattr(cfg, "base_url", "") or "")
    local = base.startswith("local://") or isinstance(
        getattr(cfg, "local_inference_binding", None), dict
    )
    if local:
        return None
    return "json" if requested == "json" else None


def start_workflow(
    directory: Path | str, preparation: LocalPreparation
) -> list[dict[str, Any]]:
    from types import SimpleNamespace
    from .local_inference.network_policy import (
        admit_network_policy,
        current_network_policy,
    )

    admit_network_policy(
        SimpleNamespace(network_policy=current_network_policy().mode),
        preparation,
        directory,
        directory=directory,
    )
    persist_local_inference(directory, preparation, include_binding=True)
    from .local_inference.network_policy import persist_network_policy

    persist_network_policy(directory)
    return [
        public_binding_view(
            LocalRuntime.prepare_resources(
                local_inference_binding(preparation, role),
                allow_create=True,
            )
        )
        for role in preparation.roles
    ]


def resume_workflow(directory: Path | str) -> LocalPreparation:
    preparation = load_run_bundle(directory)
    from .local_inference.network_policy import restore_network_policy

    restore_network_policy(directory, preparation)
    for role in preparation.roles:
        LocalRuntime.prepare_resources(
            local_inference_binding(preparation, role),
            allow_create=False,
        )
    return preparation


def attach_local_resources(client: Any, *, allow_create: bool) -> Any:
    binding = getattr(getattr(client, "cfg", None), "local_inference_binding", None)
    if not isinstance(binding, dict):
        return client
    prepared = LocalRuntime.prepare_resources(binding, allow_create=allow_create)
    client.cfg.local_inference_binding = prepared
    client._local_budget_identity = public_binding_view(prepared)
    client._local_ledger = LocalRuntime.open_budget(binding)
    client._local_coordinator = LocalRuntime.open_coordinator(binding)
    return client


def resume_role_client(directory: Path | str, role: str, *, timeout_s: float) -> Any:
    preparation = resume_workflow(directory)
    cfg = auxiliary_role_config(preparation, role, timeout_s=timeout_s)
    client = workflow_client(cfg)
    return attach_local_resources(client, allow_create=False)


def deployment_of(preparation: LocalPreparation, role: str) -> str:
    selected = load_private_worker_snapshot(preparation.snapshot).roles.get(role)
    if selected is None:
        raise LocalInferenceError("unknown_role")
    return selected.deployment_id


def forward_cpu_auxiliary_args(extra: Sequence[str]) -> list[str]:
    """Add CPU device defaults when the main parser already has those flags."""
    try:
        from .mini_prover import _build_argparser

        parser = _build_argparser()
    except Exception:
        return list(extra)
    by_dest = {
        action.dest: action.option_strings
        for action in parser._actions
        if action.option_strings and action.dest in AUXILIARY_DEVICE_DEFAULTS
    }
    out = list(extra)
    for dest, value in AUXILIARY_DEVICE_DEFAULTS.items():
        options = by_dest.get(dest) or ()
        if not options or any(arg.split("=", 1)[0] in options for arg in extra):
            continue
        out.extend([options[0], value])
    return out


def _handoff_namespace(extra: Sequence[str]) -> Any:
    from .mini_prover import _build_argparser

    parser = _build_argparser()
    parser.allow_abbrev = False
    try:
        return parser.parse_args(
            [
                "--lean-file",
                "Problem.lean",
                "--theorem-name",
                "nl_problem",
                "--project-path",
                ".",
                *extra,
            ]
        )
    except SystemExit as exc:
        raise ValueError(
            "local-only prover handoff was rejected. local-only does not mean offline "
            "and does not by itself stop downloads."
        ) from exc


def reject_nonlocal_handoff(extra: Sequence[str]) -> None:
    namespace = _handoff_namespace(extra)
    if (
        namespace.prover != "local"
        or not namespace.prover_deployment
        or not (namespace.local_inference_config or namespace.local_inference_snapshot)
    ):
        raise ValueError(
            "local-only cannot start the prover on a cloud provider. "
            "Pass --prover local with its deployment and profile. "
            "local-only does not mean offline and does not by itself stop downloads."
        )
    if namespace.refiner not in (None, "local"):
        raise ValueError(
            "local-only cannot start the refiner on a cloud provider. "
            "local-only does not mean offline and does not by itself stop downloads."
        )
    if namespace.planner_escalation not in (None, "", "off", "local"):
        raise ValueError(
            "local-only cannot use cloud planner escalation. "
            "local-only does not mean offline and does not by itself stop downloads."
        )
    flags = {item.split("=", 1)[0] for item in extra}
    if "--inference-policy" in flags and namespace.inference_policy != "local-only":
        raise ValueError(
            "local-only handoff cannot select mixed inference. "
            "local-only does not mean offline and does not by itself stop downloads."
        )


def handoff_is_local(extra: Sequence[str]) -> bool:
    try:
        namespace = _handoff_namespace(extra)
    except ValueError:
        return False
    return "local" in {
        namespace.prover,
        namespace.refiner,
        namespace.planner_escalation,
    }


def handoff_arguments(extra: Sequence[str], *, policy: str) -> list[str]:
    tail = list(extra)
    flags = {item.split("=", 1)[0] for item in tail}
    if policy == "local-only" and "--inference-policy" not in flags:
        tail = ["--inference-policy", "local-only", *tail]
    return forward_cpu_auxiliary_args(tail)


def prepare_handoff_snapshot(
    extra: Sequence[str],
    directory: Path,
    *,
    parent: LocalPreparation | None = None,
) -> tuple[list[str], LocalPreparation | None]:
    """Freeze proof role selection before translation under its parent allowance."""
    from .local_inference.roles import _drop_flags, resolve_local_inference

    namespace = _handoff_namespace(extra)
    preparation = resolve_local_inference(
        namespace,
        coordinator_root=Path(parent.coordinator_root) if parent else None,
    )
    if preparation is None:
        return list(extra), None
    if parent is not None:
        if preparation.profile_hash != parent.profile_hash:
            raise LocalInferenceError("profile_conflict")
        if preparation.budget_id and preparation.budget_id != parent.budget_id:
            raise LocalInferenceError("profile_conflict")
        preparation = preparation.with_budget(parent.budget_id, parent.coordinator_root)
    elif not preparation.budget_id:
        preparation = preparation.with_budget(
            secrets.token_hex(16), preparation.coordinator_root
        )
    private = (
        directory.resolve()
        / "proof_handoff"
        / "local_inference"
        / "private_snapshot.json"
    )
    flags = _drop_flags(extra)
    flags.extend(
        [
            "--local-inference-snapshot",
            str(private),
            "--local-inference-snapshot-hash",
            preparation.snapshot_hash,
            "--local-inference-budget-id",
            preparation.budget_id,
        ]
    )
    return flags, preparation
