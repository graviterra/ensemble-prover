"""Bounded local project choices without tool execution or credential disclosure.

Discovery checks the repository and nearby project folders. Source inspection
returns named declarations from regular Lean files in a selected Lake project.
Hidden directories, dependencies, and symlinks are excluded. Declaration listing
uses the same parser as theorem selection.
"""

from __future__ import annotations

import os
import re
import shutil
import stat
from collections import deque
from pathlib import Path
from typing import Any

from console.launcher import read_launches
from .local_registry import CURSOR_UNAVAILABLE, OperatorLocalRegistry
from ensemble_prover.theorem_project import scan_lean_theorems

MAX_DIRECTORY_ENTRIES = 1000
MAX_PROJECT_FILES = 1000
MAX_WALK_DIRECTORIES = 250
MAX_WALK_ENTRIES = 20000
MAX_LEAN_BYTES = 256 * 1024
MAX_DECLARATIONS = 400
MAX_PROJECTS = 40
_SKIP_DIRS = frozenset({
    "node_modules", "venv", "dist", "build", "output", "__pycache__",
    "site-packages", "runs", "artifacts",
})
_HOME_PROJECT_FOLDERS = frozenset({"projects", "code", "src", "work", "repos", "documents", "desktop"})
_PROVIDERS = (
    ("openai", "OpenAI", "OPENAI_API_KEY", ("gpt-5.2", "gpt-5.4")),
    ("deepseek", "DeepSeek", "DEEPSEEK_API_KEY", ("deepseek-v4-pro",)),
    ("openrouter", "OpenRouter", "OPENROUTER_API_KEY", ()),
    ("codex", "Codex", "", ()),
    ("claude-code", "Claude Code", "", ()),
    ("local", "Local", "", ()),
    ("cursor", "Cursor", "", ()),
)
_MODEL_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:/@+-]{0,159}\Z")
_NO_HISTORY = frozenset({"local", "cursor"})


_CATALOG_MESSAGES = {
    "directory_unreadable": "This directory could not be read. Choose another folder.",
    "choose_directory": "Choose a directory within the available locations.",
    "symlink": "Symlinks are not included in the project browser.",
    "directory_missing": "Choose an existing directory.",
    "source_missing": "Choose an existing Lean source file.",
    "path_unavailable": "The selected path is unavailable.",
    "outside_locations": "This path is outside the available project locations.",
    "project_missing": "Choose a Lake project containing lakefile.toml or lakefile.lean.",
    "outside_project": "Choose a Lean file inside the selected project.",
    "declarations_unreadable": "Could not read the declarations in this Lean file. Check that declaration headers are complete.",
    "source_irregular": "Choose a regular Lean source file.",
    "source_large": "This Lean file is too large for the declaration picker.",
    "source_encoding": "This Lean file is not valid UTF-8 text.",
    "source_unreadable": "The selected Lean file could not be read.",
}


class CatalogError(ValueError):
    """Catalog failure with a public message selected independently of its detail."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(_CATALOG_MESSAGES.get(code, "The selected path is unavailable."))

    @property
    def public_message(self) -> str:
        return _CATALOG_MESSAGES.get(self.code, "The selected path is unavailable.")


def _visible(name: str) -> bool:
    return bool(name) and not name.startswith(".") and name not in _SKIP_DIRS


def _open_directory(path: Path) -> int:
    """Open every directory component without following a replacement symlink."""
    descriptor = os.open(path.anchor, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for component in path.parts[1:]:
            child = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return descriptor
    except OSError:
        os.close(descriptor)
        raise


def _is_project(path: Path) -> bool:
    descriptor = None
    try:
        descriptor = _open_directory(path)
        for name in ("lakefile.toml", "lakefile.lean"):
            try:
                if stat.S_ISREG(os.stat(name, dir_fd=descriptor, follow_symlinks=False).st_mode):
                    return True
            except OSError:
                pass
    except OSError:
        return False
    finally:
        if descriptor is not None:
            os.close(descriptor)
    return False


def _children(directory: Path, limit: int) -> tuple[list[tuple[Path, bool]], bool, int]:
    """Bound work before sorting; do not traverse directory or file symlinks."""
    rows: list[tuple[Path, bool]] = []
    seen = 0
    descriptor = None
    try:
        descriptor = _open_directory(directory)
        with os.scandir(descriptor) as entries:
            for entry in entries:
                seen += 1
                if seen > limit:
                    return sorted(rows, key=lambda row: row[0].name.casefold()), True, limit
                if not _visible(entry.name) or entry.is_symlink():
                    continue
                try:
                    is_dir = entry.is_dir(follow_symlinks=False)
                    if is_dir or entry.is_file(follow_symlinks=False):
                        rows.append((directory / entry.name, is_dir))
                except OSError:
                    continue
    except OSError as exc:
        raise CatalogError("directory_unreadable") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
    return sorted(rows, key=lambda row: row[0].name.casefold()), False, seen


def _flag(argv: list[str], key: str) -> str:
    for index, arg in enumerate(argv[:256]):
        if arg == key and index + 1 < len(argv):
            return argv[index + 1]
        if arg.startswith(key + "="):
            return arg[len(key) + 1:]
    return ""


def _metadata_text(path: Path) -> str:
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(descriptor, "rb") as handle:
            info = os.fstat(handle.fileno())
            if not stat.S_ISREG(info.st_mode) or info.st_size > 4096:
                return ""
            raw = handle.read(4097)
        return raw.decode("utf-8").strip() if len(raw) <= 4096 else ""
    except (OSError, UnicodeError):
        return ""


def repository_locations(repo_root: Path) -> list[Path]:
    """Recognize a linked Git worktree using bounded local metadata reads."""
    repo = Path(repo_root).resolve()
    locations = [repo]
    marker = _metadata_text(repo / ".git")
    if not marker.startswith("gitdir: ") or "\n" in marker:
        return locations
    try:
        metadata = (repo / marker.removeprefix("gitdir: ")).resolve(strict=True)
        common_name = _metadata_text(metadata / "commondir")
        back_link = _metadata_text(metadata / "gitdir")
        if not common_name or "\n" in common_name or not back_link:
            return locations
        common = (metadata / common_name).resolve(strict=True)
        if (
            common.name != ".git"
            or metadata.parent.name != "worktrees"
            or metadata.parent.parent != common
            or Path(back_link).resolve() != repo / ".git"
            or not _metadata_text(common / "HEAD")
        ):
            return locations
        primary = common.parent
        if primary.is_dir() and primary != repo:
            locations.append(primary)
    except (OSError, RuntimeError, ValueError):
        pass
    return locations


def default_run_root(repo_root: Path) -> Path:
    """Prefer existing local runs, then runs in the linked primary repository."""
    locations = repository_locations(repo_root)
    for root in locations:
        runs = root / "runs" / "mini_prover"
        if runs.is_dir():
            return runs
    return locations[0] / "runs" / "mini_prover"


class ProjectCatalog:
    def __init__(self, repo_root: Path, state_root: Path, *, roots: list[Path] | None = None):
        self.repo_root = Path(repo_root).resolve()
        self.repository_roots = repository_locations(self.repo_root)
        self.state_root = Path(state_root)
        self.roots: list[Path] = []
        for candidate in roots if roots is not None else (*self.repository_roots, Path.home()):
            try:
                resolved = Path(candidate).resolve(strict=True)
                if resolved.is_dir() and resolved != Path("/") and resolved not in self.roots:
                    self.roots.append(resolved)
            except (OSError, RuntimeError):
                continue

    def _contained(self, selector: str, *, directory: bool = True) -> Path:
        if not selector or len(selector) > 4096 or any(ch in selector for ch in "\0\n\r"):
            raise CatalogError("choose_directory")
        path = Path(selector)
        if not path.is_absolute() or ".." in path.parts:
            raise CatalogError("choose_directory")
        for root in sorted(self.roots, key=lambda item: len(item.parts), reverse=True):
            try:
                relative = path.relative_to(root)
            except ValueError:
                continue
            if any(not _visible(part) for part in relative.parts):
                continue
            cursor = root
            try:
                for part in relative.parts:
                    cursor = cursor / part
                    if cursor.is_symlink():
                        raise CatalogError("symlink")
                resolved = cursor.resolve(strict=True)
                resolved.relative_to(root)
                if directory and not resolved.is_dir():
                    raise CatalogError("directory_missing")
                if not directory and not resolved.is_file():
                    raise CatalogError("source_missing")
                return resolved
            except (OSError, RuntimeError, ValueError) as exc:
                if isinstance(exc, CatalogError):
                    raise
                raise CatalogError("path_unavailable") from exc
        raise CatalogError("outside_locations")

    def _project(self, selector: str) -> Path:
        directory = self._contained(selector)
        if not _is_project(directory):
            raise CatalogError("project_missing")
        return directory

    def workspace(self, *, control: bool, local_registry: OperatorLocalRegistry | None = None) -> dict[str, Any]:
        records = read_launches(self.state_root)[:1000]
        projects: dict[Path, dict[str, str]] = {}
        models: dict[str, list[str]] = {provider: [] for provider, *_rest in _PROVIDERS}
        for record in records:
            selected = _flag(record.argv, "--project-path")
            try:
                path = self._project(selected)
            except CatalogError:
                path = None
            if path is not None and len(projects) < MAX_PROJECTS:
                projects[path] = {"path": str(path), "name": path.name}
            for role in ("prover", "refiner"):
                provider = _flag(record.argv, f"--{role}")
                model = _flag(record.argv, f"--{role}-model")
                if provider in models and provider not in _NO_HISTORY and _MODEL_NAME.fullmatch(model) and model not in models[provider]:
                    if len(models[provider]) < 12:
                        models[provider].append(model)
        # Linked worktrees often omit ignored Lake build artifacts. Prefer the
        # existing primary repository for shared project locations, while still
        # listing worktree projects as independent selectable environments.
        for root in reversed(self.repository_roots):
            for relative in ("lean_project", "external/PutnamBench/lean4", "mini_theory/lean4"):
                if len(projects) >= MAX_PROJECTS:
                    break
                try:
                    path = self._project(str(root / relative))
                except CatalogError:
                    continue
                projects.setdefault(path, {"path": str(path), "name": path.name})
        queue: deque[tuple[Path, int, int]] = deque()
        for root in self.roots:
            queue.append((root, 0, 3 if root in self.repository_roots else 1))
        visited: set[Path] = set()
        entry_count = 0
        while queue and len(visited) < MAX_WALK_DIRECTORIES and len(projects) < MAX_PROJECTS:
            directory, depth, max_depth = queue.popleft()
            if directory in visited:
                continue
            visited.add(directory)
            if _is_project(directory):
                projects.setdefault(directory, {"path": str(directory), "name": directory.name})
                continue
            if depth >= max_depth:
                continue
            try:
                children, _truncated, count = _children(directory, min(MAX_DIRECTORY_ENTRIES, MAX_WALK_ENTRIES - entry_count))
            except CatalogError:
                continue
            entry_count += count
            for child, is_dir in children:
                if not is_dir:
                    continue
                next_depth = max_depth
                if depth == 0 and directory not in self.repository_roots and child.name.casefold() in _HOME_PROJECT_FOLDERS:
                    next_depth = 2
                queue.append((child, depth + 1, next_depth))
            if entry_count >= MAX_WALK_ENTRIES:
                break
        declared = local_registry.public_deployments() if local_registry is not None and local_registry.loaded else []
        providers = []
        for provider, label, env_key, defaults in _PROVIDERS:
            if provider == "cursor":
                available = False
                availability = CURSOR_UNAVAILABLE
            elif provider == "local":
                available = bool(declared)
                if local_registry is not None and local_registry.loaded:
                    noun = "deployment" if len(declared) == 1 else "deployments"
                    availability = (
                        f"{len(declared)} {noun} declared in the operator profile. "
                        "Availability is configured, not probed."
                    )
                else:
                    availability = "No operator local profile is configured. Deployments are not probed."
            elif env_key:
                available = bool(os.environ.get(env_key, "").strip())
                availability = f"{env_key} is {'present' if available else 'not set'} in the service environment; authentication is not checked."
            else:
                executable = "claude" if provider == "claude-code" else "codex"
                available = shutil.which(executable) is not None
                availability = f"{executable} CLI is {'available' if available else 'not found'} on PATH; authentication is not checked."
            history = [] if provider in _NO_HISTORY else models[provider]
            providers.append({
                "id": provider, "label": label,
                "models": list(dict.fromkeys([*history, *defaults])),
                "available": available, "availability": availability,
            })
        return {
            "projects": list(projects.values()), "providers": providers,
            "deployments": declared,
            "roots": [{"path": str(root), "name": "This repository" if root == self.repo_root else "Main repository" if root in self.repository_roots else "Home" if root == Path.home() else root.name} for root in self.roots],
            "control": control,
            "notice": "Projects are discovered nearby. Browse folders to select another project.",
        }

    def browse(self, selector: str) -> dict[str, Any]:
        directory = self._contained(selector)
        children, truncated, _count = _children(directory, MAX_DIRECTORY_ENTRIES)
        parent = None
        if directory not in self.roots:
            try:
                parent = str(self._contained(str(directory.parent)))
            except CatalogError:
                pass
        return {
            "path": str(directory), "parent": parent, "isProject": _is_project(directory),
            "directories": [{"path": str(child), "name": child.name, "isProject": _is_project(child)} for child, is_dir in children if is_dir],
            "truncated": truncated,
        }

    def project(self, selector: str) -> dict[str, Any]:
        directory = self._project(selector)
        queue = deque([(directory, 0)])
        files = []
        visited = 0
        scanned = 0
        truncated = False
        while queue and visited < MAX_WALK_DIRECTORIES:
            folder, depth = queue.popleft()
            visited += 1
            try:
                children, limited, count = _children(folder, min(MAX_DIRECTORY_ENTRIES, MAX_WALK_ENTRIES - scanned))
            except CatalogError:
                truncated = True
                continue
            truncated = truncated or limited
            scanned += count
            for child, is_dir in children:
                if is_dir:
                    if depth < 12:
                        queue.append((child, depth + 1))
                    else:
                        truncated = True
                elif child.suffix == ".lean" and child.name != "lakefile.lean":
                    if len(files) >= MAX_PROJECT_FILES:
                        truncated = True
                        queue.clear()
                        break
                    files.append({"path": child.relative_to(directory).as_posix(), "name": child.name})
            if scanned >= MAX_WALK_ENTRIES:
                truncated = True
                break
        return {"path": str(directory), "name": directory.name, "files": sorted(files, key=lambda row: row["path"].casefold()), "truncated": truncated or bool(queue)}

    def theorems(self, selector: str, filename: str) -> dict[str, Any]:
        project = self._project(selector)
        relative = Path(filename)
        if not filename or relative.is_absolute() or any(not _visible(part) for part in relative.parts) or relative.suffix != ".lean":
            raise CatalogError("outside_project")
        source = self._contained(str(project / relative), directory=False)
        try:
            source.relative_to(project)
        except ValueError as exc:
            raise CatalogError("outside_project") from exc
        content = self._read_source(source)
        try:
            declarations = [item for item in scan_lean_theorems(content) if not item.private]
        except (ValueError, RecursionError) as exc:
            raise CatalogError("declarations_unreadable") from exc
        return {
            "theorems": [{"name": item.canonical_name, "statement": item.statement_type[:8000]} for item in declarations[:MAX_DECLARATIONS]],
            "truncated": len(declarations) > MAX_DECLARATIONS,
            "notice": "Lists named theorem and lemma declarations. Private declarations, anonymous examples, and macro-generated declarations are excluded. Lean has not checked these statements.",
        }

    def _read_source(self, source: Path) -> str:
        root = next(root for root in self.roots if source.is_relative_to(root))
        parts = source.relative_to(root).parts
        directory_fd = None
        try:
            directory_fd = _open_directory(root)
            for part in parts[:-1]:
                next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory_fd)
                os.close(directory_fd)
                directory_fd = next_fd
            source_fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory_fd)
            with os.fdopen(source_fd, "rb") as handle:
                info = os.fstat(handle.fileno())
                if not stat.S_ISREG(info.st_mode):
                    raise CatalogError("source_irregular")
                if info.st_size > MAX_LEAN_BYTES:
                    raise CatalogError("source_large")
                content = handle.read(MAX_LEAN_BYTES + 1)
                if len(content) > MAX_LEAN_BYTES:
                    raise CatalogError("source_large")
            return content.decode("utf-8")
        except UnicodeError as exc:
            raise CatalogError("source_encoding") from exc
        except OSError as exc:
            raise CatalogError("source_unreadable") from exc
        finally:
            if directory_fd is not None:
                os.close(directory_fd)
