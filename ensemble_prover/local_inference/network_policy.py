"""Per-run application network policy.

Startup calls ``apply_network_policy(args, resolved, project_root)`` before
model and Lean setup. ``offline`` blocks application-managed cloud literature,
model downloads, and Lean toolchain or dependency downloads. Exact local
inference endpoints admitted for the run stay usable.

The value is immutable context state plus a child-process environment marker.
It does not patch sockets, isolate the OS, or attest that an external server
makes no upstream calls. Application pricing downloads are blocked; arbitrary
Lean code, plugins, and unowned subprocesses remain outside this boundary.
"""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import asdict, dataclass, replace
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import threading
import time
from typing import Any, Iterator, Mapping, Sequence
from types import SimpleNamespace
from urllib.parse import urlsplit

from .config import ResolvedLocalRun, load_private_worker_snapshot
from .errors import LocalInferenceError
from .strictload import content_hash, atomic_write_json, read_json_object
from ..subprocess_environment import sanitized_subprocess_environment

NETWORK_POLICY_ENV = "ENSEMBLE_NETWORK_POLICY"
NETWORK_POLICY_ID_ENV = "ENSEMBLE_NETWORK_POLICY_ID"
CLOSED_BOUNDARIES = (
    "remote_literature",
    "embedding_download",
    "reranker_download",
    "owned_lean_spawn",
    "pricing_catalog",
)
UNCLOSED_BOUNDARIES = ("unowned_subprocesses", "arbitrary_lean_code")
_PIN = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:/-]{0,200}$")
_LEAN_VERBS = frozenset({"env", "build", "lean"})
_FETCH_VERBS = frozenset({"update", "upload", "init", "new", "unpack", "pack"})
_FETCH_TOOLS = frozenset({"curl", "wget", "ssh", "nc", "ncat", "elan"})
_SHELLS = frozenset({"python", "python3", "bash", "sh", "dash"})
_CHILD_OFFLINE = (
    ("HF_HUB_OFFLINE", "1"),
    ("TRANSFORMERS_OFFLINE", "1"),
    ("HF_HUB_DISABLE_TELEMETRY", "1"),
    ("HF_DATASETS_OFFLINE", "1"),
)
_CURRENT: ContextVar["NetworkPolicy | None"] = ContextVar("ensemble_network_policy", default=None)


class NetworkPolicyError(LocalInferenceError):
    """Refusal before a connection, download, or toolchain install."""


@dataclass(frozen=True)
class AllowedEndpoint:
    fingerprint: str
    scheme: str
    host: str
    port: int
    path: str


@dataclass(frozen=True)
class NetworkPolicy:
    mode: str
    inference_policy: str
    allowed_endpoints: tuple[AllowedEndpoint, ...]
    policy_id: str
    project_root: str
    lean_preflight: str
    os_network_isolated: bool = False
    upstream_attested: bool = False

    def __post_init__(self) -> None:
        if self.mode not in {"default", "offline"} or self.lean_preflight not in {"not_applicable", "cached"}:
            raise NetworkPolicyError("network_policy_invalid")
        if self.os_network_isolated or self.upstream_attested:
            raise NetworkPolicyError("network_policy_invalid")
        object.__setattr__(self, "allowed_endpoints", tuple(self.allowed_endpoints))


def current_network_policy() -> NetworkPolicy:
    """Policy for this context. A parent environment marker is not consulted."""

    return _CURRENT.get() or _default_policy("")


def remote_fetch_allowed(policy: NetworkPolicy | None = None) -> bool:
    selected = current_network_policy() if policy is None else policy
    return selected.mode != "offline"


def inference_target_allowed(url: str, policy: NetworkPolicy | None = None) -> bool:
    selected = current_network_policy() if policy is None else policy
    if selected.mode != "offline":
        return True
    candidate = _candidate_url(url)
    if candidate is None:
        return False
    scheme, host, port, path = candidate
    return any(
        item.scheme == scheme and item.host == host and item.port == port and _path_under(item.path, path)
        for item in selected.allowed_endpoints
    )


def require_inference_target(url: str, policy: NetworkPolicy | None = None) -> None:
    if not inference_target_allowed(url, policy):
        raise NetworkPolicyError("inference_target_forbidden")


@contextmanager
def network_policy_scope(policy: NetworkPolicy) -> Iterator[NetworkPolicy]:
    """Bind one request and restore the previous context afterward."""

    if type(policy) is not NetworkPolicy:
        raise NetworkPolicyError("network_policy_invalid")
    token = _CURRENT.set(policy)
    try:
        yield policy
    finally:
        _CURRENT.reset(token)


def build_network_policy(args: Any, resolved: Any, project_root: str | Path) -> NetworkPolicy:
    """Validate admission. This does not activate the context or run Lean."""

    root = _root_text(project_root)
    if _mode(args) == "default":
        policy = _default_policy(root)
        validate_policy_marker(policy)
        return policy
    run = _as_run(resolved)
    if run.inference_policy != "local-only" or not run.roles:
        raise NetworkPolicyError("offline_requires_local_only")
    by_endpoint: dict[str, AllowedEndpoint] = {}
    for role in run.roles.values():
        deployment = run.document.deployments.get(role.deployment_id)
        endpoint = run.document.endpoints.get(role.endpoint_id)
        if (
            deployment is None
            or endpoint is None
            or deployment.execution != "operator_asserted_local"
            or role.execution != "operator_asserted_local"
        ):
            raise NetworkPolicyError("hosted_upstream_forbidden", role.role)
        by_endpoint.setdefault(endpoint.name, _allowed_endpoint(endpoint))
    allowed = tuple(sorted(by_endpoint.values(), key=lambda item: item.fingerprint))
    policy = NetworkPolicy(
        mode="offline",
        inference_policy="local-only",
        allowed_endpoints=allowed,
        policy_id=_policy_id("offline", "local-only", allowed),
        project_root=root,
        lean_preflight="not_applicable",
    )
    validate_policy_marker(policy)
    return policy


def apply_network_policy(args: Any, resolved: Any, project_root: str | Path) -> NetworkPolicy:
    """Admit the run, preflight a visible Lean project, and activate this context."""

    policy = build_network_policy(args, resolved, project_root)
    if policy.mode == "offline":
        lean = _explicit_lean_project(args, policy.project_root)
        if lean is not None:
            preflight_lean_project(lean)
            policy = replace(policy, lean_preflight="cached")
    _CURRENT.set(policy)
    return policy


def network_policy_record(policy: NetworkPolicy) -> dict[str, Any]:
    """Stable resume record with no URLs, secrets, or filesystem paths."""

    if type(policy) is not NetworkPolicy:
        raise NetworkPolicyError("network_policy_invalid")
    return {
        "schema": 1,
        "mode": policy.mode,
        "inference_policy": policy.inference_policy,
        "policy_id": policy.policy_id,
        "allowed_endpoint_fingerprints": [item.fingerprint for item in policy.allowed_endpoints],
        "lean_preflight": policy.lean_preflight,
        "os_network_isolated": False,
        "upstream_attested": False,
        "closed_boundaries": list(CLOSED_BOUNDARIES) if policy.mode == "offline" else [],
        "unclosed_boundaries": list(UNCLOSED_BOUNDARIES),
    }


def resume_network_policy(record: Mapping[str, Any], args: Any, resolved: Any, project_root: str | Path) -> NetworkPolicy:
    """Re-admit from the live profile and refuse a drifted or overclaiming record."""

    policy = build_network_policy(args, resolved, project_root)
    if policy.mode == "offline":
        lean = _explicit_lean_project(args, policy.project_root)
        if lean is not None:
            preflight_lean_project(lean)
            policy = replace(policy, lean_preflight="cached")
    expected = network_policy_record(policy)
    if (type(record) is not dict
            or not isinstance(record.get("lean_preflight"), str)
            or record.get("lean_preflight") not in {"cached", "not_applicable"}
            or any(record.get(key) != expected[key] for key in expected if key != "lean_preflight")):
        raise NetworkPolicyError("network_policy_marker_mismatch")
    _CURRENT.set(policy)
    return policy


def validate_policy_marker(policy: NetworkPolicy, environ: Mapping[str, str] | None = None) -> None:
    """Check an inherited marker. A parent offline marker does not adopt itself."""

    env = os.environ if environ is None else environ
    owned = env.get(_OWNED_POLICY_ENV)
    if owned is not None:
        try:
            inherited = json.loads(owned)
            if inherited.get("mode") != policy.mode or inherited.get("policy_id") != policy.policy_id:
                raise ValueError
        except (ValueError, TypeError, AttributeError):
            raise NetworkPolicyError("network_policy_marker_mismatch") from None
    marker = str(env.get(NETWORK_POLICY_ENV, "") or "")
    ident = str(env.get(NETWORK_POLICY_ID_ENV, "") or "")
    if policy.mode == "default":
        if marker not in {"", "default", "offline"}:
            raise NetworkPolicyError("network_policy_marker_mismatch")
        return
    if marker in {"", "default"}:
        if ident:
            raise NetworkPolicyError("network_policy_marker_mismatch")
        return
    if marker != "offline" or (ident and ident != policy.policy_id):
        raise NetworkPolicyError("network_policy_marker_mismatch")


def prepare_owned_subprocess(
    argv: Sequence[str],
    *,
    project: str | Path | None = None,
    base: Mapping[str, str] | None = None,
    kind: str = "lean",
) -> dict[str, str]:
    """Child environment for one owned spawn.

    Default policy strips a parent marker so an unrelated sweep does not inherit
    it. Offline policy rejects downloaders and requires an installed toolchain
    and cached packages. The marker is written only on the returned mapping.
    """

    policy = current_network_policy()
    if policy.mode != "offline":
        env = sanitized_subprocess_environment(base)
        env.pop(NETWORK_POLICY_ENV, None)
        env.pop(NETWORK_POLICY_ID_ENV, None)
        return env
    command = _argv(argv)
    root = Path(project) if project is not None else None
    if kind == "local_tool":
        _reject_local_tool(command)
    elif kind == "lean":
        _reject_lean_downloader(command)
        if root is None:
            raise NetworkPolicyError("unsupported_preflight", "lean_project")
        preflight_lean_project(root)
    else:
        raise NetworkPolicyError("unsupported_preflight", "subprocess")
    env = sanitized_subprocess_environment(base)
    env[NETWORK_POLICY_ENV] = "offline"
    env[NETWORK_POLICY_ID_ENV] = policy.policy_id
    env.update(_CHILD_OFFLINE)
    pin = _toolchain_pin(root) if root is not None and kind == "lean" else None
    if kind == "lean":
        env["LAKE_NO_CACHE"] = "true"
        env["GIT_ALLOW_PROTOCOL"] = ""
        env["GIT_TERMINAL_PROMPT"] = "0"
        env.pop("GIT_CONFIG_PARAMETERS", None)
        prefix = _toolchain_prefix(pin) if pin else Path(str(shutil.which("lean"))).resolve().parent.parent
        executable = Path(command[0])
        if executable.is_absolute() and executable.resolve() != (prefix / "bin" / executable.name).resolve():
            raise NetworkPolicyError("unsupported_preflight", "lean_toolchain")
        env["PATH"] = str(prefix / "bin") + os.pathsep + env.get("PATH", "")
        if pin:
            env["ELAN_TOOLCHAIN"] = pin
        # Lake may invoke Git; all network protocols are disabled for this child.
        protocols = ("", "http", "https", "ssh", "git", "file", "ext")
        env["GIT_CONFIG_COUNT"] = str(len(protocols))
        for index, protocol in enumerate(protocols):
            env[f"GIT_CONFIG_KEY_{index}"] = f"protocol.{protocol}.allow" if protocol else "protocol.allow"
            env[f"GIT_CONFIG_VALUE_{index}"] = "never"
    return env


def preflight_lean_project(project: str | Path) -> None:
    """Require an installed toolchain and cached packages without executing them."""

    root = Path(project).expanduser()
    if not _is_lean_project(root):
        raise NetworkPolicyError("unsupported_preflight", "lean_project")
    _require_installed_toolchain(root)
    lakefile = (root / "lakefile.lean").is_file() or (root / "lakefile.toml").is_file()
    manifest_path = root / "lake-manifest.json"
    if lakefile and not manifest_path.is_file():
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
    if not manifest_path.is_file():
        return
    try:
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest") from None
    if type(data) is not dict or type(data.get("packages", [])) is not list:
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
    packages_root = _packages_root(root, data.get("packagesDir", ".lake/packages"))
    for package in data.get("packages", []):
        _require_cached_package(root, packages_root, package)


def _default_policy(project_root: str) -> NetworkPolicy:
    return NetworkPolicy(
        mode="default",
        inference_policy="",
        allowed_endpoints=(),
        policy_id=_policy_id("default", "", ()),
        project_root=project_root,
        lean_preflight="not_applicable",
    )


def _policy_id(mode: str, inference_policy: str, endpoints: Sequence[AllowedEndpoint]) -> str:
    return content_hash({
        "schema": 1,
        "mode": mode,
        "inference_policy": inference_policy,
        "allowed_endpoints": [asdict(item) for item in endpoints],
    })


def _mode(args: Any) -> str:
    if args is None:
        return "default"
    raw = getattr(args, "network_policy", None)
    if raw is None:
        return "default"
    if type(raw) is not str:
        raise NetworkPolicyError("network_policy_invalid")
    mode = raw.strip().lower()
    if mode in {"", "default"}:
        return "default"
    if mode == "offline":
        return "offline"
    raise NetworkPolicyError("network_policy_invalid")


def _root_text(project_root: str | Path) -> str:
    if not isinstance(project_root, (str, Path)) or not str(project_root).strip():
        raise NetworkPolicyError("unsupported_preflight", "project_root")
    return str(Path(str(project_root).strip()).expanduser())


def _as_run(resolved: Any) -> ResolvedLocalRun:
    if isinstance(resolved, ResolvedLocalRun):
        return resolved
    snapshot = None
    if isinstance(resolved, Mapping) and resolved.get("kind") == "private_worker_snapshot":
        snapshot = resolved
    else:
        candidate = resolved.get("snapshot") if isinstance(resolved, Mapping) else getattr(resolved, "snapshot", None)
        if isinstance(candidate, Mapping):
            snapshot = candidate
    if snapshot is None:
        raise NetworkPolicyError("offline_requires_local_only")
    payload = snapshot if type(snapshot) is dict else json.loads(json.dumps(dict(snapshot)))
    return load_private_worker_snapshot(payload)


def _allowed_endpoint(endpoint: Any) -> AllowedEndpoint:
    parts = urlsplit(endpoint.base_url)
    path = parts.path or "/"
    if path != "/":
        path = path.rstrip("/")
    return AllowedEndpoint(
        fingerprint=endpoint.endpoint_fingerprint,
        scheme=parts.scheme,
        host=(parts.hostname or "").lower().rstrip("."),
        port=parts.port or (443 if parts.scheme == "https" else 80),
        path=path,
    )


def _candidate_url(url: str) -> tuple[str, str, int, str] | None:
    if type(url) is not str or not url or any(ord(char) < 33 or ord(char) == 127 for char in url):
        return None
    if any(mark in url for mark in ("@", "\\", "#", "%")):
        return None
    try:
        parts = urlsplit(url)
        port = parts.port
    except ValueError:
        return None
    if parts.username or parts.password or parts.query or parts.scheme not in {"http", "https"}:
        return None
    host = parts.hostname
    if not host or "%" in host:
        return None
    pieces: list[str] = []
    for piece in (parts.path or "/").split("/"):
        if piece in {"", "."}:
            continue
        if piece == "..":
            if not pieces:
                return None
            pieces.pop()
            continue
        pieces.append(piece)
    return (
        parts.scheme.lower(),
        host.lower().rstrip("."),
        port or (443 if parts.scheme == "https" else 80),
        "/" + "/".join(pieces),
    )


def _path_under(base: str, path: str) -> bool:
    return True if base in {"", "/"} else path == base or path.startswith(base + "/")


def _explicit_lean_project(args: Any, project_root: str) -> Path | None:
    value = getattr(args, "lean_project_dir", None) or getattr(args, "project_path", None)
    if isinstance(value, Path) or (type(value) is str and value.strip()):
        return Path(value).expanduser()
    root = Path(project_root)
    return root if _is_lean_project(root) else None


def _is_lean_project(project: Path) -> bool:
    names = ("lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json")
    return any((project / name).is_file() for name in names)


def _toolchain_pin(project: Path) -> str | None:
    path = project / "lean-toolchain"
    if not path.is_file():
        return None
    try:
        name = path.read_text(encoding="utf-8").strip()
    except (OSError, UnicodeError):
        raise NetworkPolicyError("unsupported_preflight", "lean_toolchain") from None
    if name and not any(char.isspace() for char in name) and (Path(name).is_absolute() or _PIN.fullmatch(name)):
        return name
    raise NetworkPolicyError("unsupported_preflight", "lean_toolchain")


def _toolchain_prefix(name: str) -> Path:
    if Path(name).is_absolute():
        return Path(name)
    elan = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))).expanduser()
    return elan / "toolchains" / name.replace("/", "--").replace(":", "---")


def _is_elan_proxy(path: Path) -> bool:
    try:
        resolved = path.resolve()
        resolved.relative_to((Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))).expanduser() / "bin").resolve())
        return True
    except (OSError, ValueError):
        elan = shutil.which("elan")
    if not elan:
        return False
    try:
        return path.resolve().samefile(elan)
    except OSError:
        return False


def _require_installed_toolchain(project: Path) -> None:
    pin = _toolchain_pin(project)
    if pin:
        prefix = _toolchain_prefix(pin)
        if all((prefix / "bin" / name).is_file() and os.access(prefix / "bin" / name, os.X_OK) for name in ("lean", "lake")):
            return
        raise NetworkPolicyError("lean_toolchain_missing", "lean")
    located = [shutil.which(name) for name in ("lean", "lake")]
    if any(item is None for item in located):
        raise NetworkPolicyError("lean_toolchain_missing", "lean")
    paths = [Path(str(item)) for item in located]
    if any(_is_elan_proxy(path) or not path.is_file() or not os.access(path, os.X_OK) for path in paths):
        raise NetworkPolicyError("unsupported_preflight", "elan_shim")


def _packages_root(project: Path, raw: Any) -> Path:
    if type(raw) is not str or not raw.strip():
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts:
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
    root = (project / relative).resolve()
    try:
        root.relative_to(project.resolve())
    except ValueError:
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest") from None
    return root


def _require_cached_package(project: Path, packages_root: Path, package: Any) -> None:
    if type(package) is not dict:
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
    name = package.get("name")
    kind = package.get("type")
    if type(name) is not str or not name or name in {".", ".."} or "/" in name or "\\" in name:
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
    if kind == "git":
        checkout = (packages_root / name).resolve()
        try:
            checkout.relative_to(packages_root)
            populated = checkout.is_dir() and any(checkout.iterdir())
        except (OSError, ValueError):
            populated = False
        if not populated:
            raise NetworkPolicyError("lean_cache_missing", "package")
        revision = package.get("rev")
        if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-fA-F]{40}|[0-9a-fA-F]{64}", revision):
            raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
        try:
            actual_revision = _cached_git_revision(checkout)
        except TimeoutError:
            raise
        except (OSError, subprocess.TimeoutExpired):
            raise NetworkPolicyError("lean_cache_missing", "package") from None
        if actual_revision is None or actual_revision.lower() != revision.lower():
            raise NetworkPolicyError("lean_cache_missing", "package_revision")
        return
    if kind != "path" or type(package.get("dir")) is not str or not str(package.get("dir")).strip():
        raise NetworkPolicyError("unsupported_preflight", "lean_manifest")
    candidate = Path(str(package.get("dir")))
    if not candidate.is_absolute():
        candidate = project / candidate
    if not candidate.is_dir():
        raise NetworkPolicyError("lean_cache_missing", "package")


def _cached_git_revision(checkout: Path) -> str | None:
    from ..mini_theory.environment import (
        _check_fingerprint_owner,
        _owned_git_output,
        environment_fingerprint_scope,
    )

    args = ("--no-replace-objects", "-C", str(checkout), "rev-parse", "--verify", "HEAD")
    environment = {
        key: value for key, value in sanitized_subprocess_environment().items()
        if not key.startswith("GIT_")
    }
    owner_deadline = _check_fingerprint_owner()
    if owner_deadline is not None:
        deadline = min(owner_deadline, time.monotonic() + 5)
        with environment_fingerprint_scope(
            cancellation_event=threading.Event(), deadline_monotonic=deadline
        ):
            return _owned_git_output(
                checkout, args, deadline, environment=environment,
                acquire_process_slot=False,
            )
    checked = subprocess.run(
        ["git", *args], capture_output=True, text=True, timeout=5, check=False,
        env=environment,
    )
    return checked.stdout.strip() if checked.returncode == 0 else None


def _argv(argv: Sequence[str]) -> tuple[str, ...]:
    if isinstance(argv, (str, bytes)) or not isinstance(argv, Sequence):
        raise NetworkPolicyError("unsupported_preflight", "lean_command")
    values = tuple(argv)
    if not values or any(type(item) is not str or not item for item in values):
        raise NetworkPolicyError("unsupported_preflight", "lean_command")
    return values


def _reject_lean_downloader(argv: tuple[str, ...]) -> None:
    exe = Path(argv[0]).name
    if exe in _FETCH_TOOLS or exe in _SHELLS:
        raise NetworkPolicyError(
            "lean_download_forbidden" if exe == "elan" else "unsupported_preflight",
            "elan" if exe == "elan" else "downloader",
        )
    if exe not in {"lake", "lean"}:
        raise NetworkPolicyError("unsupported_preflight", "lean_command")
    if any(part.startswith("+") for part in argv[1:]):
        raise NetworkPolicyError("lean_download_forbidden", "toolchain_override")
    if exe == "lean":
        return
    if any(part in _FETCH_VERBS for part in argv[1:]):
        raise NetworkPolicyError("lean_download_forbidden", "update")
    if "cache" in argv[1:] and ("get" in argv[1:] or "cache" == next((part for part in argv[1:] if not part.startswith("-")), "")):
        raise NetworkPolicyError("lean_download_forbidden", "cache")
    # Owned callers use these explicit forms; unknown global options can select
    # another project or enable downloads, so they are not accepted offline.
    if len(argv) < 2 or argv[1] not in _LEAN_VERBS:
        raise NetworkPolicyError("lean_download_forbidden", "lean_command")
    if any(part.startswith(("--update", "--try-cache", "--dir", "--file", "--packages", "-d", "-f")) for part in argv[2:]):
        raise NetworkPolicyError("lean_download_forbidden", "lean_command")
    if argv[1] == "env" and not (
        len(argv) >= 3 and argv[2] == "lean"
        or argv[2:] in {("printenv", "LEAN_PATH"), ("which", "lean")}
    ):
        raise NetworkPolicyError("unsupported_preflight", "lean_command")
    verb = next((part for part in argv[1:] if not part.startswith("-")), "")
    if verb not in _LEAN_VERBS:
        raise NetworkPolicyError("unsupported_preflight", "lean_command")


def _reject_local_tool(argv: tuple[str, ...]) -> None:
    exe = Path(argv[0]).name
    if exe in _FETCH_TOOLS or exe in _SHELLS or exe in {"lake", "lean"}:
        raise NetworkPolicyError(
            "lean_download_forbidden" if exe in {"elan", "lake", "lean"} else "unsupported_preflight",
            "elan" if exe == "elan" else "downloader" if exe in _FETCH_TOOLS else "subprocess",
        )


_POLICY_RECORD_NAME = "network_policy.json"


def add_network_policy_argument(parser: Any) -> None:
    """Expose application networking separately from local model selection."""
    parser.add_argument(
        "--network-policy", choices=("default", "offline"), default=None,
        help="offline requires local-only roles and cached Lean/model assets; blocks application downloads and web research. This is not OS network isolation.",
    )


def admit_network_policy(args: Any, resolved: Any, project_root: str | Path, *, directory: str | Path | None = None) -> NetworkPolicy:
    """Activate a CLI/workflow policy before model, retrieval, or Lean setup."""
    resume = getattr(args, "resume_from", None)
    saved_root = Path(resume or directory) if resume or directory else None
    record_path = saved_root / _POLICY_RECORD_NAME if saved_root else None
    if record_path is not None and record_path.exists():
        record = read_json_object(record_path, max_bytes=16384, corrupt_code="network_policy_marker_mismatch")
        requested = getattr(args, "network_policy", None)
        if requested is not None and requested != record.get("mode"):
            raise NetworkPolicyError("network_policy_marker_mismatch")
        args.network_policy = record.get("mode")
        policy = resume_network_policy(record, args, resolved, project_root)
    else:
        if resume and getattr(args, "network_policy", None) == "offline":
            raise NetworkPolicyError("network_policy_marker_mismatch")
        policy = apply_network_policy(args, resolved, project_root)
    args._network_policy_record = network_policy_record(policy)
    return policy


def persist_network_policy(directory: str | Path) -> None:
    """Save the admitted offline policy alongside a run's immutable binding."""
    policy = current_network_policy()
    path = Path(directory) / _POLICY_RECORD_NAME
    if policy.mode == "offline":
        record = network_policy_record(policy)
        if path.exists():
            saved = read_json_object(path, max_bytes=16384, corrupt_code="network_policy_marker_mismatch")
            if any(saved.get(key) != record[key] for key in record if key != "lean_preflight"):
                raise NetworkPolicyError("network_policy_marker_mismatch")
        atomic_write_json(path, record, max_bytes=16384)
    elif path.exists():
        raise NetworkPolicyError("network_policy_marker_mismatch")


def restore_network_policy(directory: str | Path, resolved: Any = None) -> NetworkPolicy:
    """Re-admit a saved workflow in a fresh process; no parent marker is trusted."""
    path = Path(directory) / _POLICY_RECORD_NAME
    if path.exists() and resolved is None:
        from .roles import load_run_bundle
        resolved = load_run_bundle(directory)
    return admit_network_policy(SimpleNamespace(network_policy=None), resolved, directory, directory=directory)


def network_handoff_arguments(args: Any, arguments: Sequence[str]) -> list[str]:
    """Preserve offline policy across an explicit prover subprocess handoff."""
    result = list(arguments)
    offline = getattr(args, "network_policy", None) == "offline" or current_network_policy().mode == "offline"
    if not offline:
        return result
    present = False
    for index, value in enumerate(result):
        if value == "--network-policy":
            if index + 1 >= len(result) or result[index + 1] != "offline":
                raise NetworkPolicyError("network_policy_marker_mismatch")
            present = True
        if value.startswith("--network-policy="):
            if value != "--network-policy=offline":
                raise NetworkPolicyError("network_policy_marker_mismatch")
            present = True
    return result if present else ["--network-policy", "offline", *result]


_OWNED_POLICY_ENV = "ENSEMBLE_OWNED_NETWORK_POLICY"


def owned_worker_environment(base: Mapping[str, str] | None = None, *, overrides: Mapping[str, str] | None = None) -> dict[str, str]:
    """Serialize admitted policy only for explicitly owned internal workers."""
    env = sanitized_subprocess_environment(base, overrides=overrides)
    return propagate_owned_network_policy(env)


def propagate_owned_network_policy(environment: Mapping[str, str]) -> dict[str, str]:
    """Add policy to an already trusted/sanitized internal worker environment."""
    env = dict(environment)
    policy = current_network_policy()
    for name in (_OWNED_POLICY_ENV, NETWORK_POLICY_ENV, NETWORK_POLICY_ID_ENV):
        env.pop(name, None)
    if policy.mode == "offline":
        env[_OWNED_POLICY_ENV] = json.dumps(asdict(policy), separators=(",", ":"))
    return env


def restore_owned_worker_network_policy() -> NetworkPolicy:
    """Explicit private-worker entrypoint; ordinary CLIs never adopt an env marker."""
    raw = os.environ.get(_OWNED_POLICY_ENV)
    if raw is None:
        policy = _default_policy("")
    else:
        try:
            if len(raw.encode("utf-8")) > 65536:
                raise ValueError
            record = json.loads(raw)
            if not isinstance(record, dict) or record.get("mode") != "offline" or record.get("inference_policy") != "local-only":
                raise ValueError
            endpoints = record.get("allowed_endpoints")
            if not isinstance(endpoints, list) or not endpoints:
                raise ValueError
            allowed = []
            for endpoint in endpoints:
                item = AllowedEndpoint(**endpoint)
                if (not isinstance(item.fingerprint, str) or not item.fingerprint
                        or item.scheme not in ("http", "https")
                        or not isinstance(item.host, str) or not item.host
                        or isinstance(item.port, bool) or not isinstance(item.port, int) or not 0 < item.port < 65536
                        or not isinstance(item.path, str) or not item.path.startswith("/")):
                    raise ValueError
                allowed.append(item)
            record["allowed_endpoints"] = tuple(allowed)
            policy = NetworkPolicy(**record)
            if policy.policy_id != _policy_id(policy.mode, policy.inference_policy, policy.allowed_endpoints):
                raise ValueError
        except (ValueError, TypeError, KeyError, UnicodeError):
            raise NetworkPolicyError("network_policy_marker_mismatch") from None
    _CURRENT.set(policy)
    return policy
