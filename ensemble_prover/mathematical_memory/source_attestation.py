"""Live imported-source bindings checked against independently loaded kernel data."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile
from typing import Any, Callable
import uuid

from .profiles import lean_call, remaining


class SourceAttestationRejected(ValueError):
    pass


@dataclass(frozen=True)
class SourceLocation:
    source_store_id: str
    module_name: str
    declaration_name: str
    module_parts: tuple[str, ...]
    declaration_parts: tuple[str, ...]
    source_path: Path
    artifact_path: Path


@dataclass(frozen=True)
class ArtifactBinding:
    path: Path
    digest: str
    identity: tuple[int, ...] | None


@dataclass(frozen=True)
class ModuleBinding:
    module_parts: tuple[str, ...]
    artifact_path: Path
    artifacts: tuple[ArtifactBinding, ...]


@dataclass(frozen=True)
class ImportedSourceReceipt:
    candidate_id: str
    candidate: Any
    location: SourceLocation
    source_digest: str
    artifact_digests: tuple[tuple[str, str], ...]
    environment_id: str
    context_digest: str
    search_paths: tuple[str, ...]
    context_guard: Callable[[], bool]
    dependencies: tuple[ModuleBinding, ...]


def _name_parts(value: str) -> tuple[str, ...]:
    from ensemble_prover.utils import _lean_qualified_identifier_segments, _consume_lean_identifier_prefix

    parts = _lean_qualified_identifier_segments(value.removeprefix("_root_."))
    if not parts:
        raise SourceAttestationRejected("invalid imported declaration or module name")
    decoded = []
    for part in parts:
        if part.startswith("«") and part.endswith("»"):
            part = part[1:-1]
        elif _consume_lean_identifier_prefix(part) != part:
            raise SourceAttestationRejected("invalid imported declaration or module name")
        if not part or part in {".", ".."} or any(c in part for c in "/\\\0\n\r"):
            raise SourceAttestationRejected("invalid imported declaration or module name")
        decoded.append(part)
    return tuple(decoded)


def _resolved_path(path: Path, *, previously_bound: bool = False) -> Path:
    try:
        return path.resolve()
    except RuntimeError as exc:
        # pathlib reports a symlink cycle differently across Python versions.
        # It is unavailable storage, never a changed mathematical source policy.
        error = OSError if previously_bound else SourceAttestationRejected
        raise error("source or artifact path cannot be resolved") from exc


def source_location(
    session: Any, candidate: Any, *, previously_bound: bool = False,
) -> SourceLocation | None:
    """Derive paths from configured retrieval adapters, never a candidate path."""
    from ensemble_prover.mathematical_retrieval.service import ProjectSupportSource, StaticMathlibSource

    sources = tuple(getattr(session.searcher, "sources", ()))
    for origin in candidate.origins:
        adapter = next((item for item in sources if item.source_id == origin.source_id), None)
        if not origin.module_name:
            continue
        if isinstance(adapter, ProjectSupportSource) and origin.source_kind == "project":
            project = _resolved_path(adapter.project_root, previously_bound=previously_bound)
            roots = tuple(_resolved_path(Path(root), previously_bound=previously_bound) for root in adapter.module_roots)
        elif isinstance(adapter, StaticMathlibSource) and origin.source_kind == "mathlib":
            project = _resolved_path(Path(session.lean.cfg.project_dir) / ".lake/packages/mathlib",
                                     previously_bound=previously_bound)
            roots = (project,)
        else:
            continue
        module_parts = _name_parts(origin.module_name)
        relative = Path(*module_parts)
        source_paths = [root / relative.with_suffix(".lean") for root in roots]
        source_paths = [path for path in source_paths if path.is_file()]
        if not source_paths:
            error = FileNotFoundError if previously_bound else SourceAttestationRejected
            raise error("configured module source is unavailable")
        if len(source_paths) != 1:
            raise SourceAttestationRejected("configured module source is ambiguous")
        source_path = source_paths[0]
        if _resolved_path(source_path, previously_bound=previously_bound) != source_path:
            error = OSError if previously_bound else SourceAttestationRejected
            raise error("module source traverses a symbolic link")
        return SourceLocation(
            origin.source_id, origin.module_name, candidate.declaration_name,
            module_parts, _name_parts(candidate.declaration_name), source_path,
            project / ".lake/build/lib/lean" / relative.with_suffix(".olean"),
        )
    return None


def _read(
    path: Path, cap: int, budget: Any = None, *, expected_identity: tuple[int, ...] | None = None,
) -> bytes:
    if budget is not None:
        remaining(budget)
    if _resolved_path(path) != path:
        raise SourceAttestationRejected("source or artifact path changed")
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as handle:
        opened = os.fstat(handle.fileno())
        if not stat.S_ISREG(opened.st_mode):
            raise SourceAttestationRejected("source or artifact is not a regular file")
        if expected_identity is not None and _stat_identity(opened) != expected_identity:
            raise SourceAttestationRejected("artifact changed before its bytes were captured")
        data = handle.read(cap + 1)
        if expected_identity is not None and _stat_identity(os.fstat(handle.fileno())) != expected_identity:
            raise SourceAttestationRejected("artifact changed while its bytes were captured")
    if len(data) > cap:
        raise SourceAttestationRejected("source or artifact exceeds the configured byte allowance")
    if budget is not None:
        remaining(budget)
    return data


def _artifact_paths(path: Path) -> tuple[Path, ...]:
    return path, Path(str(path) + ".server"), Path(str(path) + ".private")


def _artifact_digests(path: Path, cap: int, budget: Any = None) -> tuple[tuple[str, str], ...]:
    result = []
    for index, part in enumerate(_artifact_paths(path)):
        try:
            data = _read(part, cap, budget)
        except FileNotFoundError:
            if index == 0:
                raise
            result.append((str(part), "absent"))
        else:
            result.append((str(part), hashlib.sha256(data).hexdigest()))
    return tuple(result)


def _resolves_to(location: SourceLocation, paths: tuple[str, ...]) -> bool:
    prefix = location.module_parts[0]
    relative = Path(*location.module_parts).with_suffix(".olean")
    for raw in paths:
        root = Path(raw)
        if (root / prefix).is_dir() or (root / (prefix + ".olean")).is_file():
            return _resolved_path(root / relative, previously_bound=True) == location.artifact_path
    return False


def _stat_identity(observed: os.stat_result) -> tuple[int, ...]:
    return (observed.st_dev, observed.st_ino, observed.st_size,
            observed.st_mtime_ns, observed.st_ctime_ns)


def _identity(path: Path) -> tuple[int, ...] | None:
    try:
        observed = path.stat(follow_symlinks=False)
    except FileNotFoundError:
        return None
    if not stat.S_ISREG(observed.st_mode):
        raise OSError("dependency artifact storage is not a regular file")
    return _stat_identity(observed)


def _dependencies_valid(
    dependencies: tuple[ModuleBinding, ...], paths: tuple[str, ...], budget: Any = None,
    *, verify_contents: bool = True,
) -> bool:
    # Resolve each namespace prefix once, preserving Lean's first-prefix rule.
    roots: dict[str, Path | None] = {}
    parents: set[Path] = set()
    for dependency in dependencies:
        if budget is not None:
            remaining(budget)
        # Missing previously bound bytes are an operational outage at every
        # consumption boundary. Check before resolution: losing a whole module
        # directory must not become an apparent namespace ownership mismatch.
        for artifact in dependency.artifacts:
            if artifact.identity is not None and _resolved_path(artifact.path, previously_bound=True) != artifact.path:
                raise OSError("previously bound dependency storage traverses a symbolic link")
            observed = _identity(artifact.path)
            if artifact.identity is not None and observed is None:
                raise FileNotFoundError(
                    f"imported dependency artifact is unavailable: {artifact.path}"
                )
            if observed != artifact.identity:
                return False
            # An already writable mmap can change bytes without changing stat
            # metadata. File identity is a rejection shortcut, never current
            # source authority. Internal inventory checks may omit hashing only
            # before the final content-verified receipt is issued.
            if verify_contents and observed is not None:
                content = _read(artifact.path, observed[2], budget, expected_identity=observed)
                if hashlib.sha256(content).hexdigest() != artifact.digest:
                    return False
        prefix = dependency.module_parts[0]
        if prefix not in roots:
            roots[prefix] = next((Path(raw) for raw in paths if
                (Path(raw) / prefix).is_dir() or (Path(raw) / (prefix + ".olean")).is_file()), None)
        root = roots[prefix]
        if root is None:
            return False
        expected = root / (str(Path(*dependency.module_parts)) + ".olean")
        if expected.parent not in parents:
            if _resolved_path(expected.parent, previously_bound=True) != expected.parent:
                return False
            parents.add(expected.parent)
        if expected != dependency.artifact_path:
            return False
    return True


# The audited modules are loaded as data. Their elaborators/initializers cannot
# emit a success message or change the comparison code in this independent file.
_AUDIT_HEADER = r'''
import Lean
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.ConstantInfo
private def nameFromJson (j : Lean.Json) : IO Lean.Name := do
  let parts ← IO.ofExcept j.getArr?
  let mut result := Lean.Name.anonymous
  for p in parts do result := Lean.Name.str result (← IO.ofExcept p.getStr?)
  return result
private def pathsFromJson (j : Lean.Json) : IO (Array System.FilePath) := do
  let parts ← IO.ofExcept j.getArr?
  parts.mapM fun p => return System.FilePath.mk (← IO.ofExcept p.getStr?)
'''

_INVENTORY = _AUDIT_HEADER + r'''
#eval do
  let config ← IO.ofExcept (Lean.Json.parse __CONFIG__)
  let context ← nameFromJson (← IO.ofExcept (config.getObjVal? "context"))
  let env ← Lean.importModules #[{module := context}] {} (loadExts := false)
  let mut modules : Array Lean.Json := #[]
  for mod in env.header.moduleNames do
    if mod != context then
      modules := modules.push <| Lean.Json.mkObj [
        ("name", Lean.toJson mod.toString),
        ("artifact", Lean.toJson (← Lean.findOLean mod).toString)]
  IO.println <| (Lean.Json.mkObj [
    ("modules", Lean.Json.arr modules),
    ("searchPaths", Lean.toJson ((← Lean.searchPathRef.get).map System.FilePath.toString))]).compress
'''


_AUDITOR = _AUDIT_HEADER + r'''
#eval do
  let config ← IO.ofExcept (Lean.Json.parse __CONFIG__)
  let get (key : String) := IO.ofExcept (config.getObjVal? key)
  let original ← Lean.readModuleDataParts (← pathsFromJson (← get "original"))
  let rebuilt ← Lean.readModuleDataParts (← pathsFromJson (← get "rebuilt"))
  unless original.size == rebuilt.size do throw <| IO.userError "module part inventory changed"
  for (left, right) in original.zip rebuilt do
    unless left.1.isModule == right.1.isModule && left.1.imports == right.1.imports &&
        left.1.constants == right.1.constants && left.1.extraConstNames == right.1.extraConstNames do
      throw <| IO.userError "source kernel declarations differ from imported artifact"
  let target ← nameFromJson (← get "declaration")
  let mod ← nameFromJson (← get "module")
  unless original.any (fun part => part.1.constNames.contains target) do
    throw <| IO.userError "declaration is not owned by the source module"
  let context ← nameFromJson (← get "context")
  let env ← Lean.importModules #[{module := context}] {} (loadExts := false)
  let some moduleIdx := env.getModuleIdx? mod
    | throw <| IO.userError "source module is not imported in the live context"
  unless env.getModuleIdxFor? target == some moduleIdx do
    throw <| IO.userError "live declaration has a different owning module"
  let resolved ← Lean.findOLean mod
  let mut modules : Array Lean.Json := #[]
  for imported in env.header.moduleNames do
    if imported != context then
      modules := modules.push <| Lean.Json.mkObj [
        ("name", Lean.toJson imported.toString),
        ("artifact", Lean.toJson (← Lean.findOLean imported).toString)]
  IO.println <| (Lean.Json.mkObj [
    ("artifact", Lean.toJson resolved.toString),
    ("modules", Lean.Json.arr modules),
    ("searchPaths", Lean.toJson ((← Lean.searchPathRef.get).map System.FilePath.toString)),
    ("checked", Lean.toJson true)]).compress
'''


class ImportedSourceAttestor:
    """Session owner; receipts are exact live objects and cannot be restored from JSON."""

    def __init__(self, service: Any) -> None:
        self.service = service
        self._receipts: OrderedDict[str, ImportedSourceReceipt] = OrderedDict()
        self._obligations: set[str] = set()
        self._module_cache: dict[tuple[tuple[str, ...], Path], ModuleBinding] = {}

    def requires_receipt(self, candidate_id: str) -> bool:
        return candidate_id in self._obligations

    def receipt(self, candidate_id: str) -> ImportedSourceReceipt | None:
        return self._receipts.get(candidate_id)

    def valid(self, receipt: ImportedSourceReceipt, budget: Any = None) -> bool:
        """Check current authority, propagating unavailable bound storage as OSError."""
        if self._receipts.get(receipt.candidate_id) is not receipt:
            return False
        service = self.service
        session = service.session()
        if session is None:
            return False
        try:
            _, preamble, lemmas = service.context()
            context = session.lean._resolve_preamble(preamble + "\n" + "\n".join(lemmas))
            # Inspect previously bound storage before namespace resolution.
            # Losing a flat module, its entire build tree, or replacing it with
            # an unreadable/unsafe path is an outage, not a source-policy verdict.
            bound_paths = (receipt.location.source_path, *(Path(path) for path, value
                           in receipt.artifact_digests if value != "absent"))
            for path in bound_paths:
                if (_resolved_path(path, previously_bound=True) != path
                        or not stat.S_ISREG(path.stat(follow_symlinks=False).st_mode)):
                    raise OSError("previously bound source storage is unavailable")
            return bool(
                receipt.context_guard()
                and source_location(session, receipt.candidate, previously_bound=True) == receipt.location
                and service.context_id() == receipt.environment_id
                and hashlib.sha256(context.encode()).hexdigest() == receipt.context_digest
                and _resolves_to(receipt.location, receipt.search_paths)
                and hashlib.sha256(_read(receipt.location.source_path, service.config.artifact_byte_cap, budget)).hexdigest()
                    == receipt.source_digest
                and _artifact_digests(receipt.location.artifact_path, service.config.artifact_byte_cap, budget)
                    == receipt.artifact_digests
                and _dependencies_valid(receipt.dependencies, receipt.search_paths, budget)
            )
        except ValueError:
            return False

    def _snapshot_dependencies(
        self, modules: tuple[tuple[tuple[str, ...], Path], ...],
        paths: tuple[str, ...], budget: Any,
    ) -> tuple[ModuleBinding, ...]:
        dependencies = []
        for name, path in modules:
            parts = []
            for index, part in enumerate(_artifact_paths(path)):
                remaining(budget)
                before = _identity(part)
                if before is None and index == 0:
                    raise FileNotFoundError("imported dependency artifact is unavailable")
                content = _read(
                    part, self.service.config.artifact_byte_cap, budget, expected_identity=before,
                ) if before else None
                if _identity(part) != before:
                    raise SourceAttestationRejected("dependency changed while its bytes were captured")
                binding = ArtifactBinding(
                    part, hashlib.sha256(content).hexdigest() if content is not None else "absent", before,
                )
                parts.append(binding)
            # Many declaration receipts share the same imported closure. Reuse
            # immutable bindings without retaining a separate copy per theorem.
            key = (name, path)
            module = self._module_cache.get(key)
            if module is None or module.artifacts != tuple(parts):
                module = ModuleBinding(name, path, tuple(parts))
                if len(self._module_cache) >= 65536:
                    self._module_cache.clear()
                self._module_cache[key] = module
            dependencies.append(module)
        result = tuple(dependencies)
        if not _dependencies_valid(result, paths, budget, verify_contents=False):
            raise SourceAttestationRejected("dependency resolution changed during attestation")
        return result

    async def attest(self, candidate: Any, location: SourceLocation, budget: Any) -> ImportedSourceReceipt:
        cached = self._receipts.get(candidate.candidate_id)
        if cached is not None and cached.location == location and self.valid(cached, budget):
            self._receipts.move_to_end(candidate.candidate_id)
            return cached
        from ensemble_prover.verified_helper_contract import (
            helper_contract_context_guard, helper_contract_runner_context,
        )
        from ensemble_prover.lean_parser import parse_lean_output
        from ensemble_prover.lean_runner import termination_signal_from_returncode

        service = self.service
        session = service.session()
        runner = session.lean
        self._obligations.add(candidate.candidate_id)
        cap = service.config.artifact_byte_cap
        source = _read(location.source_path, cap, budget)
        artifacts = _artifact_digests(location.artifact_path, cap, budget)
        initial_runner_context = helper_contract_runner_context(runner)
        guard = helper_contract_context_guard(runner)
        environment_id = service.context_id()
        _, preamble, lemmas = service.context()
        context = runner._resolve_preamble(preamble + "\n" + "\n".join(lemmas))

        async def execute() -> tuple[tuple[str, ...], tuple[ModuleBinding, ...]]:
            nonlocal guard
            dependencies: tuple[ModuleBinding, ...] | None = None
            initial_paths: tuple[str, ...] = ()
            with tempfile.TemporaryDirectory(prefix="memory_source_", dir=runner.temp_dir) as temporary:
                root = Path(temporary).resolve()
                source_root = root / "source"
                copied = source_root / Path(*location.module_parts).with_suffix(".lean")
                copied.parent.mkdir(parents=True)
                copied.write_bytes(source)
                context_root = root / "context"
                context_root.mkdir()
                context_name = "MemorySourceContext" + uuid.uuid4().hex
                context_file = context_root / (context_name + ".lean")
                context_file.write_text(context, encoding="utf-8")

                async def compile_file(
                    path: Path, *, requires_live_context: bool = False, **kwargs: Any,
                ) -> str:
                    code, output = await runner._run_via_lake(path, timeout_s=remaining(budget), **kwargs)
                    parsed = parse_lean_output(output, code)
                    if code == 124 or parsed.timeout:
                        raise TimeoutError("imported source attestation timed out")
                    if parsed.infra_failure or termination_signal_from_returncode(code):
                        raise OSError("imported source attestation checker unavailable")
                    if code != 0:
                        # Failure to rebuild the active context is not evidence
                        # against this candidate. Source/audit failures are only
                        # local rejections while their import snapshot is intact.
                        if requires_live_context or (
                            dependencies is not None
                            and not _dependencies_valid(dependencies, initial_paths, budget, verify_contents=False)
                        ):
                            raise OSError("live imported context is unavailable or changed")
                        raise SourceAttestationRejected("imported source failed independent checking")
                    remaining(budget)
                    return output

                # Resolve a cold runner with owner-authored input before fixing
                # the receipt's live guard. Only its initial runtime-coordinate
                # binding may change; source/context checks follow this point.
                bootstrap = context_root / "Bootstrap.lean"
                bootstrap.write_text("import Lean\n", encoding="utf-8")
                await compile_file(
                    bootstrap, source_root=context_root,
                    output_path=bootstrap.with_suffix(".olean"), requires_live_context=True,
                )
                observed = helper_contract_runner_context(runner)
                if observed != initial_runner_context and (
                    observed[:-1] != initial_runner_context[:-1]
                    or initial_runner_context[-1] != ("", "", None)
                ):
                    raise SourceAttestationRejected("runner context changed during initialization")
                guard = helper_contract_context_guard(runner)
                # Bind the full live import closure before recompiling either
                # source or context; later comparisons must see these bytes.
                await compile_file(
                    context_file, source_root=context_root,
                    output_path=context_file.with_suffix(".olean"), requires_live_context=True,
                )
                inventory_file = context_root / "Inventory.lean"
                inventory_file.write_text(_INVENTORY.replace(
                    "__CONFIG__", json.dumps(json.dumps(dict(context=[context_name]))),
                ), encoding="utf-8")

                def decode_inventory(output: str) -> tuple[Any, tuple[str, ...], tuple[tuple[tuple[str, ...], Path], ...]]:
                    try:
                        result = json.loads(output)
                        paths = tuple(str((runner.project_dir / path).resolve()) for path in result["searchPaths"])
                        paths = tuple(path for path in paths if Path(path) != context_root)
                        modules = tuple((_name_parts(row["name"]),
                                         (runner.project_dir / row["artifact"]).resolve())
                                        for row in result["modules"])
                    except (ValueError, KeyError, TypeError) as exc:
                        raise SourceAttestationRejected("invalid independent dependency inventory") from exc
                    if not modules or len(modules) > 65536 or len(set(modules)) != len(modules):
                        raise SourceAttestationRejected("invalid dependency inventory size or ownership")
                    return result, paths, modules

                _, initial_paths, modules = decode_inventory(await compile_file(
                    inventory_file, extra_module_paths=(context_root,), requires_live_context=True,
                ))
                dependencies = self._snapshot_dependencies(
                    tuple(item for item in modules if item[1] != location.artifact_path),
                    initial_paths, budget,
                )
                await compile_file(copied, source_root=source_root, output_path=copied.with_suffix(".olean"))
                await compile_file(
                    context_file, source_root=context_root,
                    output_path=context_file.with_suffix(".olean"), requires_live_context=True,
                )
                rebuilt = _artifact_digests(copied.with_suffix(".olean"), cap, budget)
                config = dict(
                    original=[path for path, value in artifacts if value != "absent"],
                    rebuilt=[path for path, value in rebuilt if value != "absent"],
                    module=location.module_parts, declaration=location.declaration_parts,
                    context=[context_name],
                )
                audit = context_root / "Audit.lean"
                audit.write_text(_AUDITOR.replace("__CONFIG__", json.dumps(json.dumps(config))), encoding="utf-8")
                output = await compile_file(audit, extra_module_paths=(context_root,))
                result, paths, final_modules = decode_inventory(output)
                if result.get("checked") is not True or (runner.project_dir / result.get("artifact", "")).resolve() != location.artifact_path:
                    raise SourceAttestationRejected("imported artifact differs from configured source module")
                if paths != initial_paths or final_modules != modules or not _dependencies_valid(
                    dependencies, paths, budget, verify_contents=False,
                ):
                    raise OSError("live imports changed during source attestation")
                return paths, dependencies

        paths, dependencies = await lean_call(runner, budget, execute)
        receipt = ImportedSourceReceipt(
            candidate.candidate_id, candidate, location, hashlib.sha256(source).hexdigest(), artifacts,
            environment_id, hashlib.sha256(context.encode()).hexdigest(), paths, guard, dependencies,
        )
        self._receipts[candidate.candidate_id] = receipt
        if not self.valid(receipt, budget):
            self._receipts.pop(candidate.candidate_id, None)
            raise SourceAttestationRejected("source or live context changed during attestation")
        while len(self._receipts) > 128:
            self._receipts.popitem(last=False)
        return receipt
