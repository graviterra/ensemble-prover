"""Bind Mini roles to one immutable local profile.

Static resolution reads a profile and returns plain JSON. It does not open a
socket, create a coordinator, or create a compute ledger. An actual run writes
a mode-0600 snapshot and a redacted manifest; resume reloads that snapshot and
its original budget id.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from decimal import Decimal, InvalidOperation
import json
import math
import os
from pathlib import Path
import re
import secrets
import tempfile
from typing import Any, Mapping, Sequence

from .config import (
    RoleSelection,
    load_private_worker_snapshot,
    load_profile_path,
    private_worker_snapshot,
    public_manifest,
    resolve_run,
)
from .errors import LocalInferenceError
from .strictload import (
    atomic_write_json,
    canonical_json,
    content_hash,
    read_json_object,
)

_MAX_BYTES = 1024 * 1024
_HASH = re.compile(r"^[0-9a-f]{64}$")
_BUDGET = re.compile(r"^[0-9a-f]{32}$")
STATE_ROOT_ENV = "ENSEMBLE_LOCAL_INFERENCE_STATE_ROOT"
BINDING_KEYS = ("snapshot", "role", "coordinator_root", "budget_root", "budget_id")
LOCAL_SCHEMA_KEYS = (
    "inference_policy",
    "prover_deployment",
    "refiner_deployment",
    "planner_escalation_deployment",
    "local_inference_profile_hash",
    "local_inference_selection_hash",
    "local_inference_manifest_hash",
)
LOCAL_PRIVATE_KEYS = (
    "local_inference_config",
    "local_inference_snapshot",
    "local_inference_snapshot_hash",
    "local_inference_budget_id",
)
DEVICE_KEYS = ("embedding_device", "cross_encoder_device")
_DROP_FLAGS = {
    "--local-inference-config",
    "--local-inference-snapshot",
    "--local-inference-snapshot-hash",
    "--local-inference-budget-id",
}
_PROVER_TEMPERATURES = (
    "mini_temperature_planner",
    "mini_temperature_initial_proof",
    "mini_temperature_formalization_helper",
    "mini_temperature_lean_repair",
    "mini_temperature_route_assembly",
    "mini_temperature_stagnation_escape",
)
_REFINER_TEMPERATURES = (
    "mini_temperature_refine",
    "mini_temperature_formalization_helper",
    "mini_temperature_lean_repair",
    "mini_temperature_route_assembly",
    "mini_temperature_stagnation_escape",
)


@dataclass(frozen=True)
class LocalPreparation:
    """JSON-ready run identity. It does not retain a live profile object."""

    snapshot: dict[str, Any]
    manifest: dict[str, Any]
    snapshot_hash: str
    manifest_hash: str
    profile_hash: str
    selection_hash: str
    inference_policy: str
    budget_id: str
    coordinator_root: str
    budget_root: str
    roles: tuple[str, ...]

    def with_budget(self, budget_id: str, coordinator_root: str) -> "LocalPreparation":
        _budget_id(budget_id)
        root = str(Path(coordinator_root))
        return replace(
            self,
            budget_id=budget_id,
            coordinator_root=root,
            budget_root=str(Path(root) / "budgets" / budget_id),
        )


def coordinator_root_from_environ(environ: Mapping[str, str] | None = None) -> Path:
    """Return the one operator coordinator directory. This does not create it."""

    env = os.environ if environ is None else environ
    configured = str(env.get(STATE_ROOT_ENV, "") or "").strip()
    if configured:
        base = Path(configured).expanduser()
    else:
        xdg = str(env.get("XDG_STATE_HOME", "") or "").strip()
        base = Path(xdg).expanduser() if xdg else Path.home() / ".local" / "state"
        base = base / "ensemble-prover" / "local-inference"
    return (base / "coordinator").resolve()


def planner_escalation_choice(args: Any) -> str:
    """Local-only suppresses automatic cloud escalation before any key is read."""

    choice = str(getattr(args, "planner_escalation", "off") or "off").strip().lower()
    if _policy(args) == "local-only" and choice == "auto":
        return "off"
    return choice


def auxiliary_devices(args: Any) -> tuple[str | None, str | None]:
    """CPU for an unset local embedding or reranker device; keep an explicit one."""

    local = _namespace_selects_local(args)

    def one(name: str) -> str | None:
        value = getattr(args, name, None)
        if value is None or str(value).strip() == "":
            return "cpu" if local else None
        return str(value)

    return one("embedding_device"), one("cross_encoder_device")


def resolve_local_inference(
    args: Any,
    *,
    coordinator_root: Path | None = None,
) -> LocalPreparation | None:
    """Resolve one profile in memory. No files are written and no ledger is opened."""

    root = (
        Path(coordinator_root)
        if coordinator_root is not None
        else coordinator_root_from_environ()
    )
    routes = _routes(args)
    selections = _selections(args, routes)
    config_path = _clean(getattr(args, "local_inference_config", None))
    snapshot_path = _clean(getattr(args, "local_inference_snapshot", None))
    if not selections and not config_path and not snapshot_path:
        return None
    if not selections:
        raise LocalInferenceError("role_required")
    if config_path and snapshot_path:
        raise LocalInferenceError("profile_conflict")
    inherited = None
    if snapshot_path:
        snapshot_file = Path(snapshot_path)
        snapshot = _read_snapshot(snapshot_file)
        expected = _clean(getattr(args, "local_inference_snapshot_hash", None))
        if expected is not None and expected != content_hash(snapshot):
            raise LocalInferenceError("snapshot_mismatch")
        resolved = load_private_worker_snapshot(snapshot)
        if snapshot_file.name == "private_snapshot.json" and snapshot_file.parent.name == "local_inference":
            if (snapshot_file.parent / "run_binding.json").exists():
                inherited = load_run_bundle(snapshot_file.parent.parent)
                if inherited.snapshot_hash != content_hash(snapshot):
                    raise LocalInferenceError("snapshot_mismatch")
                root = Path(inherited.coordinator_root)
    elif config_path:
        document = load_profile_path(config_path)
        resolved = resolve_run(document, selections, inference_policy=_policy(args))
        snapshot = private_worker_snapshot(resolved)
    else:
        raise LocalInferenceError("invalid_field", "config")
    if resolved.inference_policy != _policy(args):
        raise LocalInferenceError("profile_conflict")
    if tuple(resolved.roles) != tuple(item.role for item in selections):
        raise LocalInferenceError("snapshot_mismatch")
    for item in selections:
        selected = resolved.roles[item.role]
        if item.deployment_id != selected.deployment_id:
            raise LocalInferenceError("profile_conflict")
        if item.requested_model is not None and item.requested_model != selected.model:
            raise LocalInferenceError("model_conflict")
        if (
            item.requested_reasoning_mode is not None
            and item.requested_reasoning_mode != selected.reasoning_mode
        ):
            raise LocalInferenceError("reasoning_conflict")
        if (
            item.requested_reasoning_effort is not None
            and item.requested_reasoning_effort != selected.reasoning_effort
        ):
            raise LocalInferenceError("reasoning_conflict")
    manifest = public_manifest(resolved)
    preparation = LocalPreparation(
        snapshot=json.loads(canonical_json(snapshot)),
        manifest=json.loads(canonical_json(manifest)),
        snapshot_hash=content_hash(snapshot),
        manifest_hash=content_hash(manifest),
        profile_hash=resolved.profile_hash,
        selection_hash=resolved.selection_hash,
        inference_policy=resolved.inference_policy,
        budget_id="",
        coordinator_root=str(root.resolve()),
        budget_root="",
        roles=tuple(resolved.roles),
    )
    _reject_explicit_controls(args, preparation)
    flag = _clean(getattr(args, "local_inference_budget_id", None))
    if inherited is not None:
        if flag is not None and flag != inherited.budget_id:
            raise LocalInferenceError("profile_conflict")
        preparation = preparation.with_budget(inherited.budget_id, inherited.coordinator_root)
    elif flag:
        preparation = preparation.with_budget(flag, preparation.coordinator_root)
    return preparation


def prepare_local_inference(
    args: Any,
    *,
    coordinator_root: Path | None = None,
) -> LocalPreparation | None:
    """Publish an immutable run identity without writing startup artifacts."""
    root = (
        Path(coordinator_root)
        if coordinator_root is not None
        else coordinator_root_from_environ()
    )
    preparation = getattr(args, "_local_preparation", None)
    try:
        if preparation is None:
            preparation = resolve_local_inference(args, coordinator_root=root)
        if preparation is None:
            return None
        if not hasattr(args, "_local_inherited_budget"):
            args._local_inherited_budget = bool(preparation.budget_id)
        if not preparation.budget_id:
            preparation = preparation.with_budget(_new_budget_id(), str(root.resolve()))
    except LocalInferenceError as exc:
        raise SystemExit(str(exc)) from None
    _publish(args, preparation)
    return preparation


def activate_local_inference(
    args: Any,
    output_dir: str | Path,
    *,
    coordinator_root: Path | None = None,
) -> None:
    """Persist the snapshot after the run directory has been initialized."""
    preparation = prepare_local_inference(args, coordinator_root=coordinator_root)
    if preparation is not None:
        try:
            persist_local_inference(output_dir, preparation, include_binding=True)
        except LocalInferenceError as exc:
            raise SystemExit(str(exc)) from None


def initialize_local_resources(args: Any, *, allow_create: bool) -> None:
    """Prepare shared allocation once, after the run snapshot has been saved."""
    preparation = getattr(args, "_local_preparation", None)
    if preparation is None:
        return
    from .runtime import prepare_resources

    prepared = {}
    for role in preparation.roles:
        prepared[role] = prepare_resources(
            local_inference_binding(preparation, role),
            allow_create=allow_create,
        )
    args._local_prepared_bindings = prepared


def persist_local_inference(
    directory: str | Path,
    preparation: LocalPreparation,
    *,
    include_binding: bool,
) -> None:
    root = Path(directory) / "local_inference"
    if root.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    if include_binding and not preparation.budget_id:
        raise LocalInferenceError("invalid_field", "budget_id")
    existing = root / "run_binding.json"
    if include_binding and existing.is_file():
        current = read_json_object(
            existing, max_bytes=_MAX_BYTES, corrupt_code="snapshot_mismatch"
        )
        if (
            current.get("budget_id") != preparation.budget_id
            or current.get("snapshot_hash") != preparation.snapshot_hash
        ):
            raise LocalInferenceError("snapshot_mismatch")
    _write_json(root / "private_snapshot.json", preparation.snapshot, 0o600)
    _write_json(root / "public_manifest.json", preparation.manifest, 0o644)
    _write_text(
        root / "public_manifest.sha256", preparation.manifest_hash + "\n", 0o644
    )
    if include_binding:
        _write_json(root / "run_binding.json", _binding_record(preparation), 0o600)


def load_run_bundle(directory: str | Path) -> LocalPreparation:
    """Reload a saved snapshot. A missing file, bad hash, or new id is refused."""

    root = Path(directory) / "local_inference"
    private = root / "private_snapshot.json"
    binding_path = root / "run_binding.json"
    manifest_path = root / "public_manifest.json"
    if (
        not private.is_file()
        or not binding_path.is_file()
        or not manifest_path.is_file()
    ):
        raise LocalInferenceError("snapshot_missing")
    snapshot = read_json_object(
        private, max_bytes=_MAX_BYTES, corrupt_code="snapshot_mismatch"
    )
    record = read_json_object(
        binding_path, max_bytes=_MAX_BYTES, corrupt_code="snapshot_mismatch"
    )
    manifest = read_json_object(
        manifest_path, max_bytes=_MAX_BYTES, corrupt_code="snapshot_mismatch"
    )
    _reject_unknown(
        record,
        {
            "schema_version",
            "kind",
            "profile_hash",
            "selection_hash",
            "snapshot_hash",
            "manifest_hash",
            "inference_policy",
            "budget_id",
            "coordinator_root",
            "budget_root",
            "roles",
        },
    )
    if (
        type(record.get("schema_version")) is not int
        or record.get("schema_version") != 1
        or record.get("kind") != "local_inference_run_binding"
    ):
        raise LocalInferenceError("invalid_checkpoint_binding")
    snapshot_hash = content_hash(snapshot)
    manifest_hash = content_hash(manifest)
    if (
        record.get("snapshot_hash") != snapshot_hash
        or record.get("manifest_hash") != manifest_hash
        or manifest.get("profile_hash") != record.get("profile_hash")
    ):
        raise LocalInferenceError("snapshot_mismatch")
    resolved = load_private_worker_snapshot(snapshot)
    if (
        resolved.profile_hash != record.get("profile_hash")
        or resolved.selection_hash != record.get("selection_hash")
        or resolved.inference_policy != record.get("inference_policy")
        or content_hash(public_manifest(resolved)) != manifest_hash
    ):
        raise LocalInferenceError("snapshot_mismatch")
    budget_id = record.get("budget_id")
    _budget_id(budget_id)
    roles = record.get("roles")
    if type(roles) is not list or tuple(roles) != tuple(resolved.roles):
        raise LocalInferenceError("invalid_checkpoint_binding")
    coordinator_root = _canonical_absolute_directory(record.get("coordinator_root"))
    budget_root = _canonical_absolute_directory(record.get("budget_root"))
    if budget_root != str(Path(coordinator_root) / "budgets" / budget_id):
        raise LocalInferenceError("invalid_checkpoint_binding")
    return LocalPreparation(
        snapshot=json.loads(canonical_json(snapshot)),
        manifest=json.loads(canonical_json(manifest)),
        snapshot_hash=snapshot_hash,
        manifest_hash=manifest_hash,
        profile_hash=resolved.profile_hash,
        selection_hash=resolved.selection_hash,
        inference_policy=resolved.inference_policy,
        budget_id=budget_id,
        coordinator_root=coordinator_root,
        budget_root=budget_root,
        roles=tuple(resolved.roles),
    )


def local_inference_binding(
    preparation: LocalPreparation, role_name: str
) -> dict[str, Any]:
    """Return a fresh JSON object. Callers must not receive a proxy or a coordinator."""

    role = _profile_role(role_name)
    if role not in preparation.roles:
        raise LocalInferenceError("unknown_role")
    if not preparation.budget_id:
        raise LocalInferenceError("invalid_field", "budget_id")
    binding = {
        "snapshot": json.loads(canonical_json(preparation.snapshot)),
        "role": role,
        "coordinator_root": preparation.coordinator_root,
        "budget_root": preparation.budget_root,
        "budget_id": preparation.budget_id,
    }
    if tuple(binding) != BINDING_KEYS:
        raise LocalInferenceError("invalid_field", "binding")
    return binding


def local_role_config(
    preparation: LocalPreparation,
    *,
    role_name: str,
    model: str | None,
    timeout_s: float | None,
    request_timeout_s: float | None,
    request_timeout_disabled: bool | None,
    cli_args: Any = None,
) -> Any:
    """Build a RoleConfig whose public base URL cannot be used as a cloud route."""

    from ..config import RoleConfig

    role = _profile_role(role_name)
    resolved = load_private_worker_snapshot(preparation.snapshot)
    selected = resolved.roles.get(role)
    if selected is None:
        raise LocalInferenceError("unknown_role")
    requested = _requested_model(model, cli_args, role_name)
    if requested is not None and requested != selected.model:
        raise LocalInferenceError("model_conflict")
    if selected.billing_kind == "owned_compute":
        kind = "owned-compute"
    elif selected.billing_kind == "metered":
        kind = "metered"
    else:
        raise LocalInferenceError("invalid_field", "billing")
    timeout = _effective_timeout(
        preparation.snapshot,
        selected.deployment_id,
        timeout_s=timeout_s,
        request_timeout_s=request_timeout_s,
        request_timeout_disabled=request_timeout_disabled,
    )
    temperature, top_p = _sampling_numbers(preparation.snapshot, selected.deployment_id)
    cfg = RoleConfig(
        name=role_name,
        base_url=f"local://{kind}/{selected.deployment_fingerprint}",
        model=selected.model,
        api_key=None,
        temperature=temperature,
        top_p=top_p,
        max_tokens=selected.max_output_tokens,
        model_default_max_tokens=None,
        context_window=selected.context_tokens,
        timeout_s=timeout,
        local_inference_binding=local_inference_binding(preparation, role_name),
    )
    if selected.reasoning_mode in {"on", "off"}:
        cfg.reasoning_control_required = True
    if selected.reasoning_mode == "on":
        cfg.thinking_enabled = True
    prepared = getattr(cli_args, "_local_prepared_bindings", {}).get(role)
    if prepared is not None:
        cfg.local_inference_binding = json.loads(canonical_json(prepared))
    cfg.reasoning_effort = selected.reasoning_effort
    setattr(cfg, "reasoning_requested_mode", selected.reasoning_mode)
    setattr(cfg, "reasoning_requested_effort", selected.reasoning_effort or "")
    setattr(
        cfg,
        "llm_deadline_policy",
        str(getattr(cli_args, "llm_deadline_policy", "soft") or "soft"),
    )
    setattr(cfg, "request_timeout_s", timeout)
    setattr(cfg, "request_timeout_disabled", False)
    setattr(cfg, "subscription_inactivity_timeout_s", 0.0)
    return cfg


def project_local_public_config(config: dict[str, Any], args: Any) -> dict[str, Any]:
    """Drop private paths. Cloud checkpoints do not gain the local default keys."""

    for key in LOCAL_PRIVATE_KEYS:
        config.pop(key, None)
    local = not getattr(
        args, "_legacy_local_inference_policy", False
    ) and _config_selects_local(config)
    if not local:
        for key in LOCAL_SCHEMA_KEYS:
            config.pop(key, None)
        for key in DEVICE_KEYS:
            if not config.get(key):
                config.pop(key, None)
        return config
    for key in LOCAL_SCHEMA_KEYS:
        config[key] = getattr(args, key, None)
    for key in DEVICE_KEYS:
        config[key] = getattr(args, key, None)
    return config


def align_local_checkpoint_schema(
    args: Any,
    saved: dict[str, Any],
    current: dict[str, Any],
    explicit: set[str],
) -> None:
    """Make a local resume match the saved key set, or keep a cloud checkpoint unchanged."""

    if not _saved_selects_local(saved):
        conflict = _legacy_override(args, explicit)
        if conflict:
            raise ValueError(
                f"Resume configuration override is incompatible: {conflict}"
            )
        for key in LOCAL_SCHEMA_KEYS:
            current.pop(key, None)
        for key in LOCAL_PRIVATE_KEYS:
            current.pop(key, None)
        for key in DEVICE_KEYS:
            if key in saved:
                current[key] = getattr(args, key, None)
            else:
                if key in explicit and _clean(getattr(args, key, None)):
                    raise ValueError(
                        f"Resume configuration override is incompatible: {key}"
                    )
                current.pop(key, None)
        args._legacy_local_inference_policy = True
        args._local_resume_skip = (
            set(LOCAL_SCHEMA_KEYS)
            | set(LOCAL_PRIVATE_KEYS)
            | {key for key in DEVICE_KEYS if key not in saved}
        )
        return
    try:
        preparation = load_run_bundle(getattr(args, "resume_from"))
        _reject_resume_source(args, explicit, preparation)
    except LocalInferenceError as exc:
        raise ValueError(str(exc)) from None
    for key in LOCAL_SCHEMA_KEYS:
        current[key] = getattr(args, key, None)
    for key in DEVICE_KEYS:
        current[key] = getattr(args, key, None)
    for key in LOCAL_PRIVATE_KEYS:
        current.pop(key, None)
    args._local_preparation = preparation
    args._local_resume_skip = set(LOCAL_PRIVATE_KEYS)


def freeze_invocation_args(
    argv: Sequence[str],
    directory: str | Path,
    *,
    allocate_budget: bool,
    coordinator_root: Path | None = None,
    probe_input: bool = False,
) -> list[str]:
    """Replace an editable profile path with the frozen snapshot identity."""

    source = list(argv)
    if not _argv_selects_local(source):
        return source
    tokens = ["--lean-file", "probe.lean", *source] if probe_input else source
    try:
        from ..mini_prover import _build_argparser

        parsed = _build_argparser().parse_args(tokens)
    except SystemExit:
        raise ValueError("mini prover arguments were rejected") from None
    preparation = resolve_local_inference(parsed, coordinator_root=coordinator_root)
    if preparation is None:
        return source
    if allocate_budget and not preparation.budget_id:
        root = preparation.coordinator_root
        preparation = preparation.with_budget(_new_budget_id(), root)
    persist_local_inference(
        directory,
        preparation,
        include_binding=bool(preparation.budget_id),
    )
    private = Path(directory) / "local_inference" / "private_snapshot.json"
    rewritten = _drop_flags(source)
    rewritten.extend(
        [
            "--local-inference-snapshot",
            str(private),
            "--local-inference-snapshot-hash",
            preparation.snapshot_hash,
        ]
    )
    if preparation.budget_id:
        rewritten.extend(["--local-inference-budget-id", preparation.budget_id])
    return rewritten


def _publish(args: Any, preparation: LocalPreparation) -> None:
    args._local_preparation = preparation
    args.local_inference_profile_hash = preparation.profile_hash
    args.local_inference_selection_hash = preparation.selection_hash
    args.local_inference_manifest_hash = preparation.manifest_hash
    for name in DEVICE_KEYS:
        if not _clean(getattr(args, name, None)):
            setattr(args, name, "cpu")


def _routes(args: Any) -> list[tuple[str, str, str | None]]:
    routes = [
        (
            "prover",
            str(getattr(args, "prover", "") or ""),
            _clean(getattr(args, "prover_deployment", None)),
        )
    ]
    refiner = _clean(getattr(args, "refiner", None))
    if (
        refiner is None
        and _clean(getattr(args, "refiner_deployment", None)) is not None
    ):
        raise LocalInferenceError("invalid_field", "deployment")
    if refiner is not None:
        routes.append(
            ("refiner", refiner, _clean(getattr(args, "refiner_deployment", None)))
        )
    escalation = planner_escalation_choice(args)
    if (
        escalation in {"", "off"}
        and _clean(getattr(args, "planner_escalation_deployment", None)) is not None
    ):
        raise LocalInferenceError("invalid_field", "deployment")
    if escalation not in {"", "off"}:
        routes.append(
            (
                "planner_escalation",
                escalation,
                _clean(getattr(args, "planner_escalation_deployment", None)),
            )
        )
    if _policy(args) == "local-only":
        for _role, provider, _deployment in routes:
            if provider != "local":
                raise LocalInferenceError("hosted_upstream_forbidden")
    for _role, provider, deployment in routes:
        if provider == "local" and deployment is None:
            raise LocalInferenceError("unknown_deployment")
        if provider != "local" and deployment is not None:
            raise LocalInferenceError("invalid_field", "deployment")
    return routes


def _selections(
    args: Any, routes: Sequence[tuple[str, str, str | None]]
) -> list[RoleSelection]:
    selections = []
    for role, provider, deployment in routes:
        if provider != "local":
            continue
        mode, effort = _requested_reasoning(args, role)
        selections.append(
            RoleSelection(
                role=role,
                deployment_id=str(deployment),
                requested_model=_requested_model(
                    getattr(args, _model_dest(role), None), args, role
                ),
                requested_reasoning_mode=mode,
                requested_reasoning_effort=effort,
            )
        )
    return selections


def _reject_explicit_controls(args: Any, preparation: LocalPreparation) -> None:
    explicit = _explicit_set(args)
    if explicit is None:
        return
    for role in preparation.roles:
        _reject_temperature(args, explicit, preparation.snapshot, role)
        _effective_timeout(
            preparation.snapshot,
            _deployment_id(preparation.snapshot, role),
            timeout_s=_optional_timeout(args, role, "timeout_s"),
            request_timeout_s=_optional_timeout(args, role, "request_timeout_s"),
            request_timeout_disabled=_disabled_timeout(args, role),
        )


def _reject_temperature(
    args: Any, explicit: set[str], snapshot: dict[str, Any], role: str
) -> None:
    axis = snapshot["document"]["deployments"][_deployment_id(snapshot, role)][
        "sampling"
    ]["temperature"]
    policy = axis.get("policy")
    dests = _REFINER_TEMPERATURES if role == "refiner" else _PROVER_TEMPERATURES
    values = [getattr(args, dest) for dest in dests if dest in explicit]
    if "parallel_temps" in explicit and _clean(getattr(args, "parallel_temps", None)):
        values.extend(
            part.strip() for part in str(args.parallel_temps).split(",") if part.strip()
        )
    phase_flag = "mini_phase_temperatures" in explicit
    if policy == "unrestricted" or (not values and not phase_flag):
        return
    if policy == "forbidden" or (phase_flag and not values):
        raise LocalInferenceError("invalid_field", "temperature")
    if policy != "fixed":
        raise LocalInferenceError("invalid_field", "temperature")
    try:
        target = Decimal(str(axis.get("value")))
        if any(Decimal(str(value)) != target for value in values):
            raise LocalInferenceError("invalid_field", "temperature")
    except (InvalidOperation, ValueError):
        raise LocalInferenceError("invalid_field", "temperature") from None


def _effective_timeout(
    snapshot: dict[str, Any],
    deployment_id: str,
    *,
    timeout_s: float | None,
    request_timeout_s: float | None,
    request_timeout_disabled: bool | None,
) -> float:
    if request_timeout_disabled is True:
        raise LocalInferenceError("invalid_field", "request_timeout")
    deployment = snapshot["document"]["deployments"][deployment_id]
    endpoint = snapshot["document"]["endpoints"][deployment["endpoint"]]
    limit = float(
        snapshot["document"]["capacity_groups"][endpoint["capacity_group"]][
            "request_timeout_s"
        ]
    )
    chosen = limit
    for value in (timeout_s, request_timeout_s):
        if value is None:
            continue
        try:
            number = float(value)
        except (TypeError, ValueError, OverflowError):
            raise LocalInferenceError("invalid_field", "request_timeout") from None
        if not math.isfinite(number) or number <= 0 or number > limit:
            raise LocalInferenceError("invalid_field", "request_timeout")
        chosen = min(chosen, number)
    return chosen


def _sampling_numbers(
    snapshot: dict[str, Any], deployment_id: str
) -> tuple[float, float]:
    sampling = snapshot["document"]["deployments"][deployment_id]["sampling"]
    return _axis_number(sampling["temperature"], 0.2), _axis_number(
        sampling["top_p"], 0.95
    )


def _axis_number(axis: Mapping[str, Any], default: float) -> float:
    if axis.get("policy") != "fixed":
        return default
    return float(str(axis.get("value")))


def _reject_resume_source(
    args: Any, explicit: set[str], preparation: LocalPreparation
) -> None:
    if "local_inference_snapshot_hash" in explicit:
        if (
            getattr(args, "local_inference_snapshot_hash", None)
            != preparation.snapshot_hash
        ):
            raise LocalInferenceError("snapshot_mismatch")
    if "local_inference_budget_id" in explicit:
        if getattr(args, "local_inference_budget_id", None) != preparation.budget_id:
            raise LocalInferenceError("profile_conflict")
    snapshot = _clean(getattr(args, "local_inference_snapshot", None))
    if "local_inference_snapshot" in explicit and snapshot:
        if content_hash(_read_snapshot(Path(snapshot))) != preparation.snapshot_hash:
            raise LocalInferenceError("snapshot_mismatch")
    config_path = _clean(getattr(args, "local_inference_config", None))
    if "local_inference_config" in explicit and config_path:
        # Roles and controls have not yet inherited saved CLI values here.
        # Compare the explicit source document independently; the normal
        # checkpoint compatibility pass checks explicit role overrides.
        document = load_profile_path(config_path)
        if document.profile_hash != preparation.profile_hash:
            raise LocalInferenceError("profile_conflict")


def _legacy_override(args: Any, explicit: set[str]) -> str | None:
    if "prover" in explicit and getattr(args, "prover", None) == "local":
        return "prover"
    if "refiner" in explicit and getattr(args, "refiner", None) == "local":
        return "refiner"
    if (
        "planner_escalation" in explicit
        and getattr(args, "planner_escalation", None) == "local"
    ):
        return "planner_escalation"
    for key in (
        "prover_deployment",
        "refiner_deployment",
        "planner_escalation_deployment",
    ):
        if key in explicit and _clean(getattr(args, key, None)):
            return key
    if "inference_policy" in explicit and _policy(args) != "mixed":
        return "inference_policy"
    if "local_inference_config" in explicit and _clean(
        getattr(args, "local_inference_config", None)
    ):
        return "local_inference_config"
    if "local_inference_snapshot" in explicit and _clean(
        getattr(args, "local_inference_snapshot", None)
    ):
        return "local_inference_snapshot"
    return None


def _binding_record(preparation: LocalPreparation) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "kind": "local_inference_run_binding",
        "profile_hash": preparation.profile_hash,
        "selection_hash": preparation.selection_hash,
        "snapshot_hash": preparation.snapshot_hash,
        "manifest_hash": preparation.manifest_hash,
        "inference_policy": preparation.inference_policy,
        "budget_id": preparation.budget_id,
        "coordinator_root": preparation.coordinator_root,
        "budget_root": preparation.budget_root,
        "roles": list(preparation.roles),
    }


def _read_snapshot(path: Path) -> dict[str, Any]:
    if not path.is_file():
        raise LocalInferenceError("snapshot_missing")
    payload = read_json_object(
        path, max_bytes=_MAX_BYTES, corrupt_code="snapshot_mismatch"
    )
    resolved = load_private_worker_snapshot(payload)
    if resolved.profile_hash != payload.get("profile_hash"):
        raise LocalInferenceError("snapshot_mismatch")
    return payload


def _deployment_id(snapshot: dict[str, Any], role: str) -> str:
    for item in snapshot["selections"]:
        if item["role"] == role:
            return str(item["deployment_id"])
    raise LocalInferenceError("unknown_role")


def _requested_model(model: Any, cli_args: Any, role_name: str) -> str | None:
    if model is None or str(model).strip() == "":
        return None
    explicit = _explicit_set(cli_args)
    if explicit is not None and _model_dest(role_name) not in explicit:
        return None
    return str(model).strip()


def _requested_reasoning(args: Any, role: str) -> tuple[str | None, str | None]:
    explicit = _explicit_set(args)
    if explicit is None:
        return None, None
    mode = None
    effort = None
    if f"{role}_reasoning_mode" in explicit or "reasoning_mode" in explicit:
        raw = getattr(args, f"{role}_reasoning_mode", None)
        if raw is None:
            raw = getattr(args, "reasoning_mode", None)
        if raw is not None:
            mode = str(raw).strip().lower()
            if mode == "auto":
                mode = "provider-default"
    if f"{role}_reasoning_effort" in explicit or "reasoning_effort" in explicit:
        raw_effort = getattr(args, f"{role}_reasoning_effort", None)
        if raw_effort is None:
            raw_effort = getattr(args, "reasoning_effort", None)
        if raw_effort is not None and str(raw_effort).strip():
            effort = str(raw_effort).strip().lower()
    return mode, effort


def _model_dest(role_name: str) -> str:
    role = _profile_role(role_name)
    if role == "planner_escalation":
        return "planner_escalation_model"
    return f"{role}_model"


def _profile_role(role_name: str) -> str:
    if role_name == "answer_discovery":
        return "prover"
    return role_name


def _optional_timeout(args: Any, role: str, suffix: str) -> float | None:
    specific = getattr(args, f"{role}_{suffix}", None)
    value = specific if specific is not None else getattr(args, f"llm_{suffix}", None)
    if value is None or (
        suffix == "request_timeout_s"
        and isinstance(value, str)
        and value.strip().lower() in {"none", "off", "disabled", "unbounded"}
    ):
        return None
    try:
        return float(value)
    except (TypeError, ValueError, OverflowError):
        raise LocalInferenceError("invalid_field", "request_timeout") from None


def _disabled_timeout(args: Any, role: str) -> bool | None:
    for name in (f"{role}_request_timeout_s", "llm_request_timeout_s"):
        value = getattr(args, name, None)
        if isinstance(value, str) and value.strip().lower() in {
            "none",
            "off",
            "disabled",
            "unbounded",
        }:
            return True
    return None


def _policy(args: Any) -> str:
    policy = str(getattr(args, "inference_policy", "mixed") or "mixed")
    if policy not in {"mixed", "local-only"}:
        raise LocalInferenceError("invalid_field", "inference_policy")
    return policy


def _namespace_selects_local(args: Any) -> bool:
    return _config_selects_local(
        {
            "prover": getattr(args, "prover", None),
            "refiner": getattr(args, "refiner", None),
            "planner_escalation": getattr(args, "planner_escalation", None),
            "prover_deployment": getattr(args, "prover_deployment", None),
            "refiner_deployment": getattr(args, "refiner_deployment", None),
            "planner_escalation_deployment": getattr(
                args, "planner_escalation_deployment", None
            ),
            "local_inference_profile_hash": getattr(
                args, "local_inference_profile_hash", None
            ),
        }
    )


def _config_selects_local(config: Mapping[str, Any]) -> bool:
    if "local" in {
        config.get("prover"),
        config.get("refiner"),
        config.get("planner_escalation"),
    }:
        return True
    if config.get("local_inference_profile_hash"):
        return True
    return any(
        config.get(name)
        for name in (
            "prover_deployment",
            "refiner_deployment",
            "planner_escalation_deployment",
        )
    )


def _saved_selects_local(saved: Mapping[str, Any]) -> bool:
    return _config_selects_local(saved)


def _argv_selects_local(argv: Sequence[str]) -> bool:
    flags = {
        "--local-inference-config",
        "--local-inference-snapshot",
        "--prover-deployment",
        "--refiner-deployment",
        "--planner-escalation-deployment",
        "--inference-policy",
    }
    providers = {"--prover", "--refiner", "--planner-escalation"}
    index = 0
    while index < len(argv):
        token = argv[index]
        name, sep, value = token.partition("=")
        if name in providers and (
            (sep and value == "local")
            or (not sep and index + 1 < len(argv) and argv[index + 1] == "local")
        ):
            return True
        if name in flags:
            return True
        index += 1
    return False


def _drop_flags(argv: Sequence[str]) -> list[str]:
    result: list[str] = []
    index = 0
    while index < len(argv):
        token = argv[index]
        name = token.split("=", 1)[0]
        if name in _DROP_FLAGS:
            index += 1 if "=" in token or index + 1 >= len(argv) else 2
            continue
        result.append(token)
        index += 1
    return result


def _explicit_set(args: Any) -> set[str] | None:
    value = getattr(args, "_explicit_cli_destinations", None)
    if value is None:
        return None
    return set(value)


def _clean(value: Any) -> str | None:
    if value is None:
        return None
    text = str(value).strip()
    return text or None


def _budget_id(value: Any) -> None:
    if type(value) is not str or _BUDGET.fullmatch(value) is None:
        raise LocalInferenceError("invalid_field", "budget_id")


def _canonical_absolute_directory(value: Any) -> str:
    if type(value) is not str or not value or "\x00" in value:
        raise LocalInferenceError("invalid_checkpoint_binding")
    path = Path(value)
    if not path.is_absolute() or str(path.resolve()) != value:
        raise LocalInferenceError("invalid_checkpoint_binding")
    return value


def _new_budget_id() -> str:
    return secrets.token_hex(16)


def _reject_unknown(data: Mapping[str, Any], allowed: set[str]) -> None:
    if type(data) is not dict or set(data) - allowed:
        raise LocalInferenceError("invalid_checkpoint_binding")


def _write_json(path: Path, value: dict[str, Any], mode: int) -> None:
    atomic_write_json(path, value, max_bytes=_MAX_BYTES)
    os.chmod(path, mode)


def _write_text(path: Path, text: str, mode: int) -> None:
    if path.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=".local-inference-", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(text.encode("utf-8"))
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temporary, mode)
        os.replace(temporary, path)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
