"""Material Lean input identity, computed once per fresh verifier generation."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import threading
from typing import Any
from weakref import WeakKeyDictionary

from ensemble_prover.formalization.environment import _SnapshotBuilder, _imports

_CACHE: WeakKeyDictionary[Any, dict[str, str]] = WeakKeyDictionary()
_CAPTURE_LOCKS: WeakKeyDictionary[Any, Any] = WeakKeyDictionary()
_CAPTURE_LOCKS_GUARD = threading.Lock()


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                     separators=(",", ":")).encode()).hexdigest()


def _local_inputs(project: Path, imports: list[str], sources: dict[str, str]) -> dict[str, str]:
    """Bind source-only project fixtures before a Lake project is initialized.

    Fresh Lean checking still establishes proof authority. Missing files are
    explicit identity entries; no artifact is represented as kernel-checked.
    """
    pending = list(imports)
    seen: set[str] = set()
    result: dict[str, str] = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        relative = Path(*module.split("."))
        source = Path(sources.get(module, str(project / relative.with_suffix(".lean"))))
        if not source.is_absolute():
            source = project / source
        for path in (source, project / ".lake/build/lib/lean" / relative.with_suffix(".olean"),
                     project / ".lake/build/lib" / relative.with_suffix(".olean")):
            result[str(path.resolve())] = (
                hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else "missing"
            )
        if source.is_file():
            pending.extend(_imports(source.read_text()))
    return result


def material_environment_hash(lean: Any, project: Path, config: dict[str, Any], preamble: str) -> str:
    """Coalesce cold captures only for the exact live verifier capability."""
    key, _ = _environment_key(lean, project, config, preamble)
    try:
        completed = _CACHE.get(lean, {}).get(key)
    except TypeError:
        completed = None
    if completed is not None:
        return completed
    with _CAPTURE_LOCKS_GUARD:
        try:
            lock = _CAPTURE_LOCKS.get(lean)
            if lock is None:
                lock = threading.Lock()
                _CAPTURE_LOCKS[lean] = lock
        except TypeError:
            # Non-weak-referenceable adapters retain the uncached behavior.
            lock = threading.Lock()
    with lock:
        return _material_environment_hash(lean, project, config, preamble)


def _environment_key(lean: Any, project: Path, config: dict[str, Any], preamble: str) -> tuple[str, list[str]]:
    imports = list(dict.fromkeys([
        *config["project_imports"], *_imports(preamble),
        *_imports(str(config["preamble_import"])),
        *[str(item).removeprefix("import ").strip() for item in config["extra_imports"]],
    ]))
    key = _digest({"project": str(project), "config": config, "imports": imports,
                   "generation": getattr(lean, "_execution_environment_generation", 0)})
    return key, imports


def _material_environment_hash(lean: Any, project: Path, config: dict[str, Any], preamble: str) -> str:
    """Recheck the cache under ownership; fresh runners recapture disk inputs."""
    key, imports = _environment_key(lean, project, config, preamble)
    try:
        cached = _CACHE.get(lean, {})
    except TypeError:
        cached = {}
    if key in cached:
        return cached[key]
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
        material = {"files": sorted(builder.files.values(), key=lambda item: item["path"]),
                    "metadata": builder.metadata}
    else:
        material = _local_inputs(project, imports, config["project_import_sources"])
    digest = _digest(material)
    try:
        _CACHE.setdefault(lean, {})[key] = digest
    except TypeError:
        pass
    return digest
