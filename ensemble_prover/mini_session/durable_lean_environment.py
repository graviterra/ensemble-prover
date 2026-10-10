"""Material Lean input identity, computed once per fresh verifier generation."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import threading
from typing import Any
from weakref import WeakKeyDictionary

from ensemble_prover.formalization.environment import (
    _SnapshotBuilder, _imports, _module_file, _CAPTURE_CHECK, _check_capture, _file, _read_capture_bytes,
    runtime_selector_snapshot,
)
from ensemble_prover.theorem_project import _lean_name_components

_CACHE: WeakKeyDictionary[Any, dict[str, str]] = WeakKeyDictionary()
_MATERIAL_CACHE: WeakKeyDictionary[Any, dict[str, tuple[_SnapshotBuilder | None, str]]] = WeakKeyDictionary()
_CAPTURE_LOCKS: WeakKeyDictionary[Any, Any] = WeakKeyDictionary()
_CAPTURE_LOCKS_GUARD = threading.Lock()


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                     separators=(",", ":")).encode()).hexdigest()


def _resolved_coordinates(lean: Any, project: Path) -> tuple[tuple[str, str], ...]:
    """Read the configured, shared, and live coordinates available this epoch."""
    from ensemble_prover.lean_server import LeanREPL

    config = getattr(lean, "cfg", None)
    path = str(getattr(config, "resolved_lean_path", "") or "").strip()
    executable = str(getattr(config, "resolved_lean_executable", "") or "").strip()
    epoch = LeanREPL.global_env_epoch(str(project))
    configured_epoch = getattr(config, "resolved_lean_environment_epoch", None)
    pairs = []

    def add_base_coordinates(pair: tuple[str, str]) -> None:
        roots = tuple(str(root) for root in getattr(config, "module_search_paths", ()) if str(root).strip())
        pairs.append((os.pathsep.join((*roots, pair[0])).rstrip(os.pathsep), pair[1]))

    if (path and executable and (type(configured_epoch) is int and configured_epoch == epoch
                                or configured_epoch is None and epoch == 0)):
        add_base_coordinates((path, executable))
    with LeanREPL._GLOBAL_ENV_CACHE_LOCK:
        cached = LeanREPL._GLOBAL_ENV_CACHE.get(str(project))
        if cached is not None:
            add_base_coordinates(cached)
    repl = getattr(lean, "_repl", None)
    if isinstance(repl, LeanREPL):
        admitted = repl._admit_check_environment()
        if admitted is not None:
            binary, environment = admitted
            pairs.append((environment.get("LEAN_PATH", ""), binary))
    return tuple(dict.fromkeys(pairs))


def _validate_resolved_coordinates(
    builder: _SnapshotBuilder, lean: Any, project: Path, config: dict[str, Any],
) -> None:
    """Bind direct Lean resolution to the declared material import closure.

    A normal lazy Lake lookup selects these same files and does not change
    checkpoint identity. Pre-resolved paths must not silently shadow one of
    the captured modules with a different compiled declaration environment.
    """
    for lean_path, executable in _resolved_coordinates(lean, project):
        _validate_coordinate_pair(builder, project, lean_path, executable)


def _validate_coordinate_pair(
    builder: _SnapshotBuilder, project: Path,
    lean_path: str, executable: str,
) -> None:
    toolchain = builder.metadata.get("toolchain")
    if not toolchain:
        raise ValueError("resolved Lean environment has no captured toolchain")
    toolchain_root = Path(toolchain["resolved_origin"])
    expected_executables = {(toolchain_root / "bin/lean").resolve()}
    selected_command = builder.metadata.get("runtime_selection", {}).get("commands", {}).get("lean")
    if selected_command:
        expected_executables.add(Path(selected_command["resolved_path"]).resolve())
    executable_path = Path(shutil.which(executable) or executable) if os.sep not in executable else Path(executable)
    if not executable_path.is_absolute():
        executable_path = project / executable_path
    if executable_path.resolve() not in expected_executables:
        raise ValueError("resolved Lean executable differs from the captured toolchain")
    search_roots = []
    for raw in lean_path.split(os.pathsep):
        root = Path(raw) if raw else project
        search_roots.append((root if root.is_absolute() else project / root).resolve())
    # Lean appends its own standard library even when LEAN_PATH omits it.
    search_roots = list(dict.fromkeys([*search_roots, (toolchain_root / "lib/lean").resolve()]))
    compiled_roots = sorted({
        root.resolve() for _, _, _, roots in builder.roots for root in roots
    }, key=lambda path: len(path.parts), reverse=True)
    for entry in builder.files.values():
        expected = Path(entry["path"])
        if expected.suffix != ".olean":
            continue
        expected = expected.resolve()
        relative = next((expected.relative_to(root) for root in compiled_roots
                         if expected.is_relative_to(root)), None)
        if relative is None:
            raise ValueError("captured Lean module has no declared compiled root")
        selected = next((root / relative for root in search_roots if (root / relative).is_file()), None)
        if selected is None or selected.resolve() != expected:
            raise ValueError(f"resolved Lean module differs from captured import: {relative}")


def _local_inputs(project: Path, imports: list[str], sources: dict[str, str]) -> dict[str, str]:
    """Bind source-only project fixtures before a Lake project is initialized.

    Fresh Lean checking still establishes proof authority. Missing files are
    explicit identity entries; no artifact is represented as kernel-checked.
    """
    pending = list(imports)
    seen: set[str] = set()
    result: dict[str, str] = {}
    while pending:
        _check_capture()
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        components = _lean_name_components(module)
        if not components:
            raise ValueError(f"invalid Lean module path: {module}")
        relative = Path(*components)
        source = Path(sources.get(module, str(_module_file(project, relative, ".lean"))))
        if not source.is_absolute():
            source = project / source
        for path in (source, _module_file(project / ".lake/build/lib/lean", relative, ".olean"),
                     _module_file(project / ".lake/build/lib", relative, ".olean")):
            result[str(path.resolve())] = (
                _file(path, "project")["sha256"] if path.is_file() else "missing"
            )
        if source.is_file():
            pending.extend(_imports(_read_capture_bytes(source).decode()))
    return result


def material_environment_hash(lean: Any, project: Path, config: dict[str, Any], preamble: str) -> str:
    """Coalesce cold captures only for the exact live verifier capability."""
    runtime_selectors = runtime_selector_snapshot()
    key, _ = _environment_key(lean, project, config, preamble, runtime_selectors=runtime_selectors)
    from .session import _dispatch_capability_identity

    # Recursive leases wrap the same verifier in non-weak-referenceable views.
    # Cache by its owning generation after reading through the live lease, so
    # a revoked view still fails before it can reuse any cached identity.
    owner = _dispatch_capability_identity(lean)
    try:
        completed = _CACHE.get(owner, {}).get(key)
    except TypeError:
        completed = None
    if completed is not None:
        if runtime_selector_snapshot() != runtime_selectors:
            raise ValueError("Lean process runtime selectors changed during environment capture")
        return completed
    with _CAPTURE_LOCKS_GUARD:
        try:
            lock = _CAPTURE_LOCKS.get(owner)
            if lock is None:
                lock = threading.Lock()
                _CAPTURE_LOCKS[owner] = lock
        except TypeError:
            # Non-weak-referenceable adapters retain the uncached behavior.
            lock = threading.Lock()
    if _CAPTURE_CHECK.get() is None:
        with lock:
            return _material_environment_hash(lean, project, config, preamble)
    while not lock.acquire(timeout=0.01):
        _check_capture()
    try:
        _check_capture()
        return _material_environment_hash(lean, project, config, preamble)
    finally:
        lock.release()


def _environment_key(
    lean: Any, project: Path, config: dict[str, Any], preamble: str, *, bind_resolution: bool = True,
    runtime_selectors: tuple[tuple[str, str | None], ...] | None = None,
) -> tuple[str, list[str]]:
    from ensemble_prover.lean_server import LeanREPL

    imports = list(dict.fromkeys([
        *config["project_imports"], *_imports(preamble),
        *_imports(str(config["preamble_import"])),
        *_imports(str(config["preamble_tactics"])),
        *[str(item).removeprefix("import ").strip() for item in config["extra_imports"]],
    ]))
    key = _digest({"project": str(project), "config": config, "imports": imports,
                   "generation": getattr(lean, "_execution_environment_generation", 0),
                   "global_epoch": LeanREPL.global_env_epoch(str(project)),
                   "runtime_selectors": runtime_selector_snapshot() if runtime_selectors is None else runtime_selectors,
                   "resolved_coordinates": _resolved_coordinates(lean, project) if bind_resolution else None})
    return key, imports


def _material_environment_hash(lean: Any, project: Path, config: dict[str, Any], preamble: str) -> str:
    """Recheck the cache under ownership; fresh runners recapture disk inputs."""
    runtime_selectors = runtime_selector_snapshot()
    key, imports = _environment_key(lean, project, config, preamble, runtime_selectors=runtime_selectors)
    from .session import _dispatch_capability_identity

    def require_current_selectors() -> None:
        if runtime_selector_snapshot() != runtime_selectors:
            raise ValueError("Lean process runtime selectors changed during environment capture")

    owner = _dispatch_capability_identity(lean)
    try:
        cached = _CACHE.get(owner, {})
    except TypeError:
        cached = {}
    if key in cached:
        require_current_selectors()
        return cached[key]
    material_key, _ = _environment_key(
        lean, project, config, preamble, bind_resolution=False, runtime_selectors=runtime_selectors,
    )
    try:
        captured = _MATERIAL_CACHE.get(owner, {}).get(material_key)
    except TypeError:
        captured = None
    if captured is not None:
        builder, digest = captured
        if builder is not None:
            _validate_resolved_coordinates(builder, lean, project, config)
        _check_capture()
        require_current_selectors()
        try:
            _CACHE.setdefault(owner, {})[key] = digest
        except TypeError:
            pass
        return digest
    builder = None
    if any((project / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
        builder = _SnapshotBuilder(project)
        for raw_project in config["support_project_builds"]:
            support = Path(raw_project).resolve()
            manifest = builder._configuration(support, "support")
            builder._packages(support, manifest)
        for raw_root in config["module_search_paths"]:
            root = Path(raw_root).resolve()
            builder.roots.append((root, "external", (root,), (root,)))
            builder._mutable_build(root, root)
        builder.collect(tuple(imports))
        _validate_resolved_coordinates(builder, lean, project, config)
        material = {"files": sorted(builder.files.values(), key=lambda item: item["path"]),
                    "metadata": builder.metadata}
    else:
        material = _local_inputs(project, imports, config["project_import_sources"])
    digest = _digest(material)
    _check_capture()
    require_current_selectors()
    try:
        _MATERIAL_CACHE.setdefault(owner, {})[material_key] = (builder, digest)
        _CACHE.setdefault(owner, {})[key] = digest
    except TypeError:
        pass
    return digest
