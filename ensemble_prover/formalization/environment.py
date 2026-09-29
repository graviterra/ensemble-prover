"""Snapshots of trusted Lake inputs, with explicit local import closure.

Capture and full validation belong at campaign open/resume, not on every node.
The default snapshot pins package realizations and the installed toolchain;
explicit imports additionally pin their source and compiled dependency closure.
Generated campaign modules are recorded independently by their compiler.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import tomllib
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

from ..mini_theory.environment import dependency_environment_fingerprint
from ..subprocess_environment import sanitized_subprocess_environment
from ..theorem_project import (
    _lean_name_components,
    _project_module_source_roots,
    normalize_imports,
)
from ..utils import strip_lean_comments_and_string_literals


_CONFIG_FILES = (
    "lean-toolchain",
    "lakefile.toml",
    "lakefile.lean",
    "lake-manifest.json",
)
_COMPILED_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir")
_GENERATED_PATHS = (
    "Formalization",
    "lean/Formalization",
    "Formalization.olean",
    "lean/Formalization.olean",
)
_RUNTIME_SELECTORS = (
    "PATH",
    "ELAN_HOME",
    "ELAN_TOOLCHAIN",
    "LEAN_SYSROOT",
    "LEAN_PATH",
    "LEAN_SRC_PATH",
)


def _encoded(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        ensure_ascii=False,
        allow_nan=False,
        separators=(",", ":"),
    ).encode("utf-8")


def _inside(path: Path, root: Path) -> bool:
    return path.resolve().is_relative_to(root.resolve())


def _file(path: Path, scope: str, *, data: bytes | None = None) -> dict[str, Any]:
    resolved = path.resolve()
    digest = None
    if path.exists():
        if not path.is_file():
            raise ValueError(f"environment input is not a file: {path}")
        if data is not None:
            digest = hashlib.sha256(data).hexdigest()
        else:
            with path.open("rb") as handle:
                digest = hashlib.file_digest(handle, "sha256").hexdigest()
    elif path.is_symlink():
        raise ValueError(f"environment input is a broken symlink: {path}")
    return {
        "path": str(path.absolute()),
        "resolved_path": str(resolved),
        "sha256": digest,
        "scope": scope,
    }


def _module_file(root: Path, relative: Path, suffix: str) -> Path:
    # A dot inside a quoted Lean name belongs to the filename, not its suffix.
    return root / relative.parent / (relative.name + suffix)


def _compiled_tree_identity(
    root: Path, origin: Path, *, excluded: Sequence[str] = ()
) -> dict[str, Any]:
    """Bind installed build state without rehashing multi-gigabyte payloads.

    This is a filesystem build-identity fence, not a compiled-content hash.
    Even a same-content rebuild may invalidate it conservatively. Every file is
    statted at full snapshot boundaries; directory-only caching would miss
    ordinary in-place rewrites.
    """
    resolved_origin = origin.resolve()
    if not root.resolve().is_relative_to(resolved_origin):
        raise ValueError(f"compiled build directory escapes its origin: {root}")
    digest = hashlib.sha256()
    count = 0
    seen: set[Path] = set()

    def fail(error: OSError) -> None:
        raise ValueError(f"cannot inspect installed compiled tree: {root}") from error

    if root.is_symlink() and not root.exists():
        raise ValueError(f"compiled build directory is a broken symlink: {root}")
    if root.exists() and not root.is_dir():
        raise ValueError(f"compiled build directory is not a directory: {root}")
    walk = os.walk(root, onerror=fail, followlinks=True) if root.exists() else ()
    for raw, directories, files in walk:
        directory = Path(raw)
        resolved = directory.resolve()
        if not resolved.is_relative_to(resolved_origin) or resolved in seen:
            raise ValueError(f"escaped or cyclic compiled build directory: {directory}")
        seen.add(resolved)
        directories[:] = sorted(
            name
            for name in directories
            if str((directory / name).relative_to(root)) not in excluded
        )
        for name in sorted(files):
            if str((directory / name).relative_to(root)) in excluded:
                continue
            if not name.endswith((*_COMPILED_SUFFIXES, ".so")):
                continue
            path = directory / name
            info = path.lstat()
            actual = resolved / name
            if stat.S_ISLNK(info.st_mode):
                actual = path.resolve(strict=True)
                info = path.stat()
            if not actual.is_relative_to(resolved_origin) or not stat.S_ISREG(
                info.st_mode
            ):
                raise ValueError(f"invalid installed compiled input: {path}")
            digest.update(
                _encoded(
                    [
                        str(path.relative_to(root)),
                        str(actual),
                        info.st_dev,
                        info.st_ino,
                        info.st_size,
                        info.st_mtime_ns,
                        info.st_ctime_ns,
                    ]
                )
                + b"\n"
            )
            count += 1
    return {
        "path": str(root.absolute()),
        "resolved_path": str(root.resolve()),
        "exists": root.exists(),
        "file_count": count,
        "identity_sha256": digest.hexdigest(),
        "excluded": list(excluded),
    }


def _git(root: Path, *args: str) -> bytes:
    try:
        command = subprocess.run(
            ["git", "-C", str(root), *args],
            check=True,
            capture_output=True,
            env=sanitized_subprocess_environment(),
            timeout=60,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise ValueError(f"cannot identify resolved git dependency: {root}") from exc
    return command.stdout


def _runtime_selection(project: Path) -> dict[str, Any]:
    """Identify child-process runtime selection without executing or installing it."""

    environment = {key: os.environ.get(key) for key in _RUNTIME_SELECTORS}
    # A child starts in the Lake project, so relative PATH entries resolve
    # there, even when the controller started in a different directory.
    search_path = os.pathsep.join(
        str(Path(entry) if Path(entry).is_absolute() else project / entry)
        for entry in os.environ.get("PATH", os.defpath).split(os.pathsep)
    )
    commands = {}
    for name in ("lean", "lake", "elan"):
        value = shutil.which(name, path=search_path)
        commands[name] = (
            {
                "path": str(Path(value).absolute()),
                "resolved_path": str(Path(value).resolve()),
            }
            if value
            else None
        )
    elan = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))).expanduser()
    if not elan.is_absolute():
        elan = project / elan
    settings_path = elan / "settings.toml"
    settings = (
        tomllib.loads(settings_path.read_text()) if settings_path.is_file() else {}
    )
    selected = os.environ.get("ELAN_TOOLCHAIN", "").strip()
    overrides = settings.get("overrides", {})
    if not isinstance(overrides, dict):
        raise ValueError("invalid Elan toolchain overrides")
    if not selected:
        for directory in (project, *project.parents):
            selected = overrides.get(str(directory), "")
            if selected:
                break
            toolchain = directory / "lean-toolchain"
            if toolchain.is_file():
                selected = toolchain.read_text().strip()
                break
        else:
            selected = settings.get("default_toolchain", "")
    if not isinstance(selected, str):
        raise ValueError("invalid selected Lean toolchain")
    return {
        "environment": environment,
        "commands": commands,
        "elan_home": str(elan.absolute()),
        "elan_settings": _file(settings_path, "toolchain"),
        "selected_toolchain": selected,
    }


def _imports(source: str) -> tuple[str, ...]:
    # A Lean import command can list several modules on the same line.
    masked = strip_lean_comments_and_string_literals(source)
    result: list[str] = []
    for line in masked.splitlines():
        match = re.match(r"^\s*(?:(?:public|private)\s+)?import\s+(.+?)\s*$", line)
        if match:
            names = match.group(1).split()
            if names and names[0] == "all":
                names = names[1:]
            if not names:
                raise ValueError("unsupported empty Lean import")
            result.extend(normalize_imports(names))
    return tuple(dict.fromkeys(result))


@dataclass(frozen=True)
class EnvironmentSnapshot:
    """A restorable identity of configured trusted sources and runtime inputs."""

    id: str
    project_path: Path
    trusted_imports: tuple[str, ...]
    files: tuple[dict[str, Any], ...]
    metadata: dict[str, Any]

    @classmethod
    def capture(
        cls, project_path: Path, *, trusted_imports: Sequence[str] = ()
    ) -> EnvironmentSnapshot:
        project = Path(project_path).expanduser().resolve(strict=True)
        if not project.is_dir() or not any(
            (project / name).is_file() for name in ("lakefile.toml", "lakefile.lean")
        ):
            raise ValueError("environment requires an existing Lake project")
        imports = normalize_imports(trusted_imports)
        builder = _SnapshotBuilder(project)
        builder.collect(imports)
        payload = {
            "version": 1,
            "project_path": str(project),
            "trusted_imports": list(imports),
            "files": sorted(builder.files.values(), key=lambda entry: entry["path"]),
            "metadata": builder.metadata,
        }
        return cls.from_dict(
            {"id": hashlib.sha256(_encoded(payload)).hexdigest(), **payload}
        )

    def to_dict(self) -> dict[str, Any]:
        return json.loads(
            _encoded(
                {
                    "version": 1,
                    "id": self.id,
                    "project_path": str(self.project_path),
                    "trusted_imports": list(self.trusted_imports),
                    "files": list(self.files),
                    "metadata": self.metadata,
                }
            )
        )

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> EnvironmentSnapshot:
        fields = {
            "version",
            "id",
            "project_path",
            "trusted_imports",
            "files",
            "metadata",
        }
        if (
            not isinstance(data, dict)
            or set(data) != fields
            or data["version"] != 1
            or isinstance(data["version"], bool)
        ):
            raise ValueError("invalid environment snapshot schema")
        if (
            not isinstance(data["project_path"], str)
            or not Path(data["project_path"]).is_absolute()
        ):
            raise ValueError("snapshot requires an absolute project path")
        if not isinstance(data["trusted_imports"], list) or normalize_imports(
            data["trusted_imports"]
        ) != tuple(data["trusted_imports"]):
            raise ValueError("invalid snapshot imports")
        if not isinstance(data["files"], list) or not isinstance(
            data["metadata"], dict
        ):
            raise ValueError("invalid snapshot records")
        for entry in data["files"]:
            if not isinstance(entry, dict) or set(entry) != {
                "path",
                "resolved_path",
                "sha256",
                "scope",
            }:
                raise ValueError("invalid snapshot file record")
            if any(
                not isinstance(entry[key], str) or not Path(entry[key]).is_absolute()
                for key in ("path", "resolved_path")
            ):
                raise ValueError("snapshot file origins must be absolute")
            if entry["sha256"] is not None and (
                not isinstance(entry["sha256"], str)
                or re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is None
            ):
                raise ValueError("invalid snapshot file hash")
            if entry["scope"] not in {"project", "package", "toolchain"}:
                raise ValueError("invalid snapshot file scope")
        payload = {key: value for key, value in data.items() if key != "id"}
        if hashlib.sha256(_encoded(payload)).hexdigest() != data["id"]:
            raise ValueError("environment snapshot identity mismatch")
        copied = json.loads(_encoded(data))
        return cls(
            copied["id"],
            Path(copied["project_path"]),
            tuple(copied["trusted_imports"]),
            tuple(copied["files"]),
            copied["metadata"],
        )

    def validate(self) -> None:
        """Recompute the full snapshot at open/resume and reject any change."""
        self.from_dict(self.to_dict())
        try:
            current = self.capture(
                self.project_path, trusted_imports=self.trusted_imports
            )
        except (OSError, ValueError) as exc:
            raise ValueError(f"trusted Lean environment changed: {exc}") from exc
        if current.id != self.id:
            raise ValueError("trusted Lean environment changed since snapshot")

    def validate_local(self) -> None:
        """Check runtime selection and selected project/path-package files at commit.

        This inexpensive check does not replace full validation after a restart
        or after changes to installed git packages/toolchains.
        """
        if self.metadata.get("runtime_selection") != _runtime_selection(
            self.project_path
        ):
            raise ValueError("trusted Lean runtime selection changed")
        if "mutable_compiled_builds" not in self.metadata:
            raise ValueError("Lean environment has no mutable compiled input receipt")
        for record in self.metadata["mutable_compiled_builds"]:
            expected = record["tree"]
            current = _compiled_tree_identity(
                Path(expected["path"]),
                Path(record["origin"]),
                excluded=expected["excluded"],
            )
            if current != expected:
                raise ValueError(
                    f"trusted mutable compiled input changed: {expected['path']}"
                )
        path_packages = [
            record
            for record in self.metadata.get("packages", [])
            if record.get("type") == "path"
        ]
        for record in path_packages:
            if Path(record["origin"]).resolve() != Path(record["resolved_origin"]):
                raise ValueError("trusted local Lean package origin changed")
        path_roots = tuple(Path(record["resolved_origin"]) for record in path_packages)
        for entry in self.files:
            if (
                entry["scope"] == "project"
                or any(
                    Path(entry["resolved_path"]).is_relative_to(root)
                    for root in path_roots
                )
            ) and _file(Path(entry["path"]), entry["scope"]) != entry:
                raise ValueError(f"trusted local Lean input changed: {entry['path']}")

    def validate_module_root(self, root: Path) -> None:
        """Keep generated outputs distinct from every configured base origin."""
        generated = root.resolve()
        records = [
            *self.metadata.get("compiled_builds", []),
            *(
                record["tree"]
                for record in self.metadata.get("mutable_compiled_builds", [])
            ),
        ]
        for record in records:
            base = Path(record["path"]).resolve()
            if generated.is_relative_to(base) or base.is_relative_to(generated):
                raise ValueError(
                    "generated module root overlaps a base compiled origin"
                )
            # Snapshot-only callers may create unrelated reserved outputs, but
            # a compiler cannot accept an alternative campaign import origin.
            for relative in _GENERATED_PATHS:
                path = base / relative
                if path.exists() or path.is_symlink():
                    raise ValueError(
                        "base compiled origin contains the reserved generated namespace"
                    )

    def validate_automatic_import(
        self, module: str, *, extra_roots: Sequence[Path] = ()
    ) -> None:
        """Require explicit pinned trust for local Mathlib/Lean name shadows.

        Namespace spelling alone does not identify the installed library. Check
        project, package, and caller search roots without hashing that library's
        complete compiled tree on each generated module.
        """
        components = _lean_name_components(module)
        if not components:
            raise ValueError(f"invalid Lean module path: {module}")
        if components[0] not in {"Mathlib", "Lean"}:
            return
        namespace = components[0]
        relative = Path(*components)
        pinned = {entry["path"]: entry for entry in self.files}
        roots: list[tuple[Path, Path, bool]] = []
        packages = [
            {"resolved_origin": str(self.project_path)},
            *self.metadata.get("packages", []),
        ]
        for package in packages:
            origin = Path(package["resolved_origin"])
            automatic = (
                namespace == "Mathlib"
                and package.get("name") == "mathlib"
                and package.get("type") == "git"
            )
            manifest_path = origin / "lake-manifest.json"
            manifest = (
                json.loads(manifest_path.read_bytes())
                if manifest_path.is_file()
                else {}
            )
            built = origin / manifest.get("lakeDir", ".lake") / "build/lib"
            roots.extend(
                (origin, root, automatic)
                for root in (
                    *_project_module_source_roots(origin),
                    built / "lean",
                    built,
                )
            )
        toolchain = self.metadata.get("toolchain")
        if toolchain:
            origin = Path(toolchain["resolved_origin"])
            roots.extend(
                (origin, origin / path, namespace == "Lean")
                for path in ("src/lean", "lib/lean")
            )
        configured = {root.resolve() for _, root, _ in roots}
        search_paths = (
            *extra_roots,
            *(
                Path(value) if Path(value).is_absolute() else self.project_path / value
                for value in os.environ.get("LEAN_PATH", "").split(os.pathsep)
                if value
            ),
        )
        roots.extend(
            (root, root, False)
            for root in search_paths
            if root.resolve() not in configured
        )
        for origin, root, automatic in roots:
            for suffix in (".lean", ".olean"):
                path = _module_file(root, relative, suffix)
                if not path.exists() and not path.is_symlink():
                    continue
                if automatic and _inside(path, origin):
                    continue
                entry = pinned.get(str(path.absolute()))
                if entry is not None and _file(path, entry["scope"]) == entry:
                    continue
                raise ValueError(
                    f"unpinned {namespace} import origin requires an explicit trusted import: {module}: {path}"
                )


class _SnapshotBuilder:
    def __init__(self, project: Path) -> None:
        self.project = project
        self.files: dict[str, dict[str, Any]] = {}
        self.metadata: dict[str, Any] = {
            "packages": [],
            "toolchain": None,
            "compiled_builds": [],
            "mutable_compiled_builds": [],
        }
        self.roots: list[tuple[Path, str, tuple[Path, ...], tuple[Path, ...]]] = []
        self.seen_packages: set[Path] = set()
        self.root_package_names: set[str] = set()

    def _record(self, path: Path, scope: str, *, data: bytes | None = None) -> None:
        self.files[str(path.absolute())] = _file(path, scope, data=data)

    def _mutable_build(self, root: Path, origin: Path) -> None:
        self.metadata["mutable_compiled_builds"].append(
            {
                "origin": str(origin.resolve()),
                "tree": _compiled_tree_identity(
                    root, origin, excluded=_GENERATED_PATHS
                ),
            }
        )

    def _configuration(self, root: Path, scope: str) -> dict[str, Any]:
        manifest: dict[str, Any] = {}
        for name in _CONFIG_FILES:
            path = root / name
            data = path.read_bytes() if path.is_file() else None
            self._record(path, scope, data=data)
            if name == "lake-manifest.json" and data is not None:
                parsed = json.loads(data)
                if not isinstance(parsed, dict) or not isinstance(
                    parsed.get("packages"), list
                ):
                    raise ValueError("invalid Lake manifest package graph")
                manifest = parsed
        source_roots = _project_module_source_roots(root)
        if any(not _inside(source, root) for source in source_roots):
            raise ValueError(
                "external srcDir must be supplied as an explicit path dependency"
            )
        lake_dir = manifest.get("lakeDir", ".lake")
        if not isinstance(lake_dir, str) or not _inside(root / lake_dir, root):
            raise ValueError("unsupported Lake build directory outside package")
        built = root / lake_dir / "build" / "lib"
        self.roots.append((root, scope, source_roots, (built / "lean", built)))
        for native in sorted(built.glob("*.so")):
            if not _inside(native, root):
                raise ValueError("native library escapes its configured project")
            self._record(native, scope)
        return manifest

    def _packages(self, root: Path, manifest: dict[str, Any]) -> None:
        packages_dir = manifest.get("packagesDir", ".lake/packages")
        if not isinstance(packages_dir, str):
            raise ValueError("invalid Lake packagesDir")
        for package in manifest.get("packages", []):
            if not isinstance(package, dict) or not isinstance(
                package.get("name"), str
            ):
                raise ValueError("invalid Lake package")
            name, kind = package["name"], package.get("type")
            if not name or Path(name).name != name or name in {".", ".."}:
                raise ValueError("invalid Lake package name")
            if root != self.project and name in self.root_package_names:
                # Lake flattens the resolved graph into the root manifest.
                # Dependency-local manifests can retain obsolete locations or
                # revisions; the root realization (including overrides) wins.
                continue
            record: dict[str, Any] = {"owner": str(root), "name": name, "type": kind}
            if kind == "git":
                origin = root / packages_dir / name
                checkout = origin.resolve(strict=True)
                top = Path(
                    _git(checkout, "rev-parse", "--show-toplevel").decode().strip()
                ).resolve()
                if top != checkout:
                    raise ValueError("package is not its own resolved git checkout")
                head = _git(checkout, "rev-parse", "HEAD").decode().strip()
                if package.get("rev") != head:
                    raise ValueError(
                        "Lake manifest revision differs from actual package HEAD"
                    )
                record.update(
                    head=head,
                    tracked_diff_sha256=hashlib.sha256(
                        _git(checkout, "diff", "--binary", "HEAD", "--")
                    ).hexdigest(),
                )
                subdir = package.get("subDir") or ""
                if not isinstance(subdir, str) or not _inside(
                    checkout / subdir, checkout
                ):
                    raise ValueError("package subDir escapes its checkout")
                selected = checkout / subdir
            elif kind == "path":
                relative = package.get("dir")
                if not isinstance(relative, str) or not relative:
                    raise ValueError("path package requires an explicit dir")
                origin = root / relative
                selected = origin.resolve(strict=True)
            else:
                raise ValueError(f"unsupported Lake package type: {kind}")
            selected = selected.resolve(strict=True)
            if not selected.is_dir():
                raise ValueError("package origin is not a directory")
            record.update(origin=str(origin.absolute()), resolved_origin=str(selected))
            self.metadata["packages"].append(record)
            if selected not in self.seen_packages:
                self.seen_packages.add(selected)
                child_manifest = self._configuration(selected, "package")
                if kind == "git":
                    built = (
                        selected / child_manifest.get("lakeDir", ".lake") / "build/lib"
                    )
                    self.metadata["compiled_builds"].append(
                        _compiled_tree_identity(built, selected)
                    )
                else:
                    self._mutable_build(
                        selected / child_manifest.get("lakeDir", ".lake") / "build/lib",
                        selected,
                    )
                self._packages(selected, child_manifest)

    def _toolchain(self) -> None:
        selection = _runtime_selection(self.project)
        self.metadata["runtime_selection"] = selection
        for command in selection["commands"].values():
            if command:
                self._record(Path(command["path"]), "toolchain")
        self._record(Path(selection["elan_settings"]["path"]), "toolchain")
        name = selection["selected_toolchain"]
        prefix = (
            (
                Path(name)
                if Path(name).is_absolute()
                else Path(selection["elan_home"])
                / "toolchains"
                / name.replace("/", "--").replace(":", "---")
            )
            if name
            else None
        )
        lake_command = selection["commands"]["lake"]
        if lake_command:
            lake_path = Path(lake_command["path"])
            elan_command = selection["commands"]["elan"]
            elan_candidates = [lake_path.with_name("elan")]
            if elan_command:
                elan_candidates.append(Path(elan_command["path"]))
            is_shim = any(
                candidate.is_file() and lake_path.samefile(candidate)
                for candidate in elan_candidates
            )
            if not is_shim:
                # A standalone Lake installation takes precedence over Elan's
                # selected release. Lake invokes the Lean binary beside it.
                prefix = Path(lake_command["resolved_path"]).parent.parent
                name = str(prefix)
                if not (prefix / "bin/lean").is_file():
                    raise ValueError(
                        "cannot resolve the selected standalone Lake runtime"
                    )
        if prefix is None or not prefix.is_dir():
            # Ledger-only initialization remains possible before installing
            # Lean. The selection is still bound; actual compilation requires
            # a working runtime and will fail explicitly without one.
            return
        if any(not (prefix / "bin" / binary).is_file() for binary in ("lean", "lake")):
            raise ValueError("selected installed Lean toolchain is incomplete")
        resolved = prefix.resolve()
        self.metadata["toolchain"] = {
            "name": name,
            "origin": str(prefix.absolute()),
            "resolved_origin": str(resolved),
        }
        for binary in ("lean", "lake", "leanchecker"):
            self._record(resolved / "bin" / binary, "toolchain")
        library = resolved / "lib/lean"
        self.metadata["compiled_builds"].append(
            _compiled_tree_identity(library, resolved)
        )
        for runtime in sorted(library.glob("*.so")):
            self._record(runtime, "toolchain")
        self.roots.append((resolved, "toolchain", (resolved / "src/lean",), (library,)))

    def _module(self, module: str) -> tuple[bytes, str]:
        components = _lean_name_components(module)
        if not components:
            raise ValueError("invalid imported module")
        relative = Path(*components)
        candidates = []
        for root, scope, source_roots, compiled_roots in self.roots:
            for source_root in source_roots:
                path = _module_file(source_root, relative, ".lean")
                if path.exists() or path.is_symlink():
                    if not _inside(path, root):
                        raise ValueError(
                            f"module source escapes declared origin: {module}"
                        )
                    candidates.append((path, root, scope, compiled_roots))
        unique = {str(item[0].resolve()): item for item in candidates}
        if len(unique) != 1:
            raise ValueError(f"unresolved or ambiguous trusted module: {module}")
        source, root, scope, compiled_roots = next(iter(unique.values()))
        data = source.read_bytes()
        self._record(source, scope, data=data)
        compiled = [
            directory / relative
            for directory in compiled_roots
            if _module_file(directory, relative, ".olean").is_file()
        ]
        if len(compiled) != 1:
            raise ValueError(f"missing or ambiguous compiled trusted module: {module}")
        for suffix in _COMPILED_SUFFIXES:
            path = compiled[0].with_name(compiled[0].name + suffix)
            if not _inside(path, root):
                raise ValueError(f"compiled module escapes declared origin: {module}")
            self._record(path, scope)
        return data, scope

    def collect(self, imports: tuple[str, ...]) -> None:
        manifest = self._configuration(self.project, "project")
        self._mutable_build(
            self.project / manifest.get("lakeDir", ".lake") / "build/lib",
            self.project,
        )
        self.root_package_names = {
            package["name"]
            for package in manifest.get("packages", [])
            if isinstance(package, dict) and isinstance(package.get("name"), str)
        }
        self.seen_packages.add(self.project)
        self._packages(self.project, manifest)
        self._toolchain()
        installed = [
            Path(record["path"]).resolve()
            for record in self.metadata["compiled_builds"]
        ]
        mutable = [
            Path(record["tree"]["path"]).resolve()
            for record in self.metadata["mutable_compiled_builds"]
        ]
        for value in os.environ.get("LEAN_PATH", "").split(os.pathsep):
            if not value:
                continue
            root = Path(value) if Path(value).is_absolute() else self.project / value
            resolved = root.resolve()
            if any(resolved.is_relative_to(known) for known in (*installed, *mutable)):
                continue
            self._mutable_build(root, root)
            mutable.append(resolved)
        # Preserve the existing clean git-package compatibility key when it
        # applies; path/dirty realizations are covered by our explicit records.
        self.metadata["legacy_dependency_fingerprint"] = (
            dependency_environment_fingerprint(self.project) if manifest else ""
        )
        self.metadata["packages"].sort(key=lambda item: (item["owner"], item["name"]))
        self.metadata["compiled_builds"].sort(key=lambda item: item["path"])
        self.metadata["mutable_compiled_builds"].sort(
            key=lambda item: item["tree"]["path"]
        )
        pending = deque(imports)
        seen: set[str] = set()
        while pending:
            module = pending.popleft()
            if module in seen:
                continue
            seen.add(module)
            data, _ = self._module(module)
            pending.extend(_imports(data.decode("utf-8")))
