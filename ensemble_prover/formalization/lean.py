"""Immutable, independently checked Lean modules for a formalization campaign."""

from __future__ import annotations

import asyncio
import fcntl
import hashlib
import json
import math
import os
import re
import tempfile
import time
from contextlib import asynccontextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

from ..config import LeanConfig
from ..lean_runner import LeanRunner
from ..nl_lean import _lean_string
from ..theorem_project import (
    _strip_root_prefix,
    is_valid_lean_qualified_name,
    scan_lean_imports,
)
from ..utils import strip_lean_comments_and_string_literals
from .environment import EnvironmentSnapshot, _compiled_tree_identity
from .documents import _mkdir_durable, _sync_directory


def _hash(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class ModuleArtifact:
    module_name: str
    source_sha256: str
    olean_sha256: str
    source_path: Path
    olean_path: Path
    declarations: tuple[dict[str, Any], ...]

    def to_dict(self) -> dict[str, Any]:
        return {
            "module_name": self.module_name,
            "source_sha256": self.source_sha256,
            "olean_sha256": self.olean_sha256,
            "source_path": str(self.source_path),
            "olean_path": str(self.olean_path),
            "declarations": list(self.declarations),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "ModuleArtifact":
        if not isinstance(data, dict):
            raise ValueError("invalid module artifact")
        for key in (
            "module_name",
            "source_sha256",
            "olean_sha256",
            "source_path",
            "olean_path",
        ):
            if not isinstance(data.get(key), str) or not data[key]:
                raise ValueError(f"invalid module artifact {key}")
        inventory = data.get("declarations")
        if not isinstance(inventory, list) or any(
            not isinstance(item, dict) for item in inventory
        ):
            raise ValueError("invalid module declaration inventory")
        return cls(
            data["module_name"],
            data["source_sha256"],
            data["olean_sha256"],
            Path(data["source_path"]),
            Path(data["olean_path"]),
            tuple(inventory),
        )


_ACTIVE = re.compile(
    r"\b(?:sorry|sorryAx|admit|by_elab|run_tac|run_cmd|run_elab|run_meta|"
    r"run_term_elab|elabTermEnsuringType|unsafe|unsafeBaseIO|unsafeIO|unsafeEIO|"
    r"unsafeCast|include_str|include_bytes|from_lrat|initialize|builtin_initialize)\b"
    r"|\beval\s*%|#(?:eval|check|print|exec|compile)\b"
)
_MODULE = re.compile(r"Formalization\.M_([0-9a-f]{64})\Z")
_SAFE_OPTIONS = {"autoImplicit", "maxRecDepth", "maxHeartbeats"}


_GUARD = r"""
private partial def campaignSyntaxSafe (stx : Lean.Syntax) : Bool :=
  match stx with
  | .atom _ value => !(["sorry", "admit", "by_elab", "run_tac", "run_cmd",
      "run_elab", "run_meta", "run_term_elab", "elabTermEnsuringType", "unsafe",
      "eval%", "include_str", "include_bytes", "from_lrat", "initialize",
      "builtin_initialize", "@["] : List String).contains value
  | .ident _ _ name _ =>
      !(["sorryAx", "unsafeBaseIO", "unsafeIO", "unsafeEIO", "unsafeCast"].contains name.toString)
  | .node _ _ args => args.all campaignSyntaxSafe
  | .missing => false

private def campaignImportsSafe (env : Lean.Environment) : Bool := Id.run do
  for index in [:env.header.moduleNames.size] do
    let imported := env.header.moduleNames[index]!
    unless (`Formalization).isPrefixOf imported do
      if env.header.moduleData[index]!.imports.any
          (fun dependency => (`Formalization).isPrefixOf dependency.module) then
        return false
  return true
"""


class ModuleCompiler:
    """Compile exact source against selected immutable modules and trusted imports.

    Trusted imports and the project toolchain are executable caller code. The
    generated-source gate restricts executable metaprogramming; it is not an OS
    sandbox. A manifest is published last and is the artifact admission marker.
    """

    def __init__(
        self,
        project_path: Path,
        root: Path,
        timeout_s: float = 300,
        *,
        trusted_imports: Sequence[str] = (),
        environment: EnvironmentSnapshot | None = None,
    ) -> None:
        if not math.isfinite(timeout_s) or timeout_s <= 0:
            raise ValueError("module timeout must be finite and positive")
        self.project_path = Path(project_path).expanduser().resolve(strict=True)
        self.root = Path(root).expanduser().resolve()
        self.timeout_s = timeout_s
        self.trusted_imports = tuple(trusted_imports)
        if any(not is_valid_lean_qualified_name(name) for name in self.trusted_imports):
            raise ValueError("invalid trusted import")
        self.environment = environment or EnvironmentSnapshot.capture(
            self.project_path, trusted_imports=self.trusted_imports
        )
        if (
            self.environment.project_path != self.project_path
            or self.environment.trusted_imports != self.trusted_imports
        ):
            raise ValueError("compiler environment project or trusted imports mismatch")
        if environment is not None:
            environment.validate()
        self._environment = self._base_environment()
        _mkdir_durable(self.root / "Formalization")
        self._runner = LeanRunner(
            LeanConfig(
                project_dir=str(self.project_path),
                scratch_dir=str(self.root / "Formalization" / ".checks"),
                backend_mode="lake",
                timeout_s=math.ceil(timeout_s),
                module_search_paths=[str(self.root)],
            )
        )

    def _base_environment(self) -> str:
        self._validate_module_root()
        self.environment.validate_local()
        self.environment.validate_automatic_import("Lean", extra_roots=(self.root,))
        return self.environment.id

    def _validate_module_root(self) -> None:
        self.environment.validate_module_root(self.root)
        if (self.root / "Formalization").is_symlink():
            raise ValueError("generated module namespace cannot be a symlink")
        unmanaged = _compiled_tree_identity(
            self.root, self.root, excluded=("Formalization",)
        )
        if unmanaged["file_count"]:
            raise ValueError("unmanaged compiled input in generated module root")

    async def close(self) -> None:
        await self._runner.aclose()

    @asynccontextmanager
    async def _module_lock(self, source_hash: str):
        locks = self.root / "Formalization" / ".locks"
        locks.mkdir(exist_ok=True)
        with (locks / source_hash).open("a+") as handle:
            deadline = time.monotonic() + self.timeout_s
            while True:
                try:
                    fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise ValueError("timed out waiting for module publication")
                    await asyncio.sleep(0.05)
            try:
                yield
            finally:
                fcntl.flock(handle, fcntl.LOCK_UN)

    def _paths(self, name: str) -> tuple[Path, Path, Path]:
        if _MODULE.fullmatch(name) is None:
            raise ValueError("invalid campaign module name")
        stem = self.root.joinpath(*name.split("."))
        return (
            stem.with_suffix(".lean"),
            stem.with_suffix(".olean"),
            stem.with_suffix(".json"),
        )

    def _load(self, name: str) -> tuple[ModuleArtifact, dict[str, Any]]:
        source_path, olean_path, manifest = self._paths(name)
        try:
            record = json.loads(manifest.read_bytes())
            artifact = ModuleArtifact.from_dict(record["artifact"])
            if record["environment"] != self._environment or record["version"] != 1:
                raise ValueError("module environment or version changed")
            if (
                artifact.module_name != name
                or artifact.source_path != source_path
                or artifact.olean_path != olean_path
                or name != f"Formalization.M_{artifact.source_sha256}"
            ):
                raise ValueError("module manifest identity mismatch")
            if _hash(source_path.read_bytes()) != artifact.source_sha256:
                raise ValueError("module source hash mismatch")
            if _hash(olean_path.read_bytes()) != artifact.olean_sha256:
                raise ValueError("compiled module hash mismatch")
            source_imports = scan_lean_imports(source_path.read_text(encoding="utf-8"))
            for imported_name in source_imports:
                self.environment.validate_automatic_import(
                    imported_name, extra_roots=(self.root,)
                )
            imported = {
                name for name in source_imports if name.startswith("Formalization.")
            }
            if imported != set(record["dependencies"]):
                raise ValueError(
                    "module dependency manifest differs from source imports"
                )
            return artifact, record
        except (OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
            raise ValueError(f"module is not admitted: {name}: {exc}") from exc

    def validate(self, artifact: ModuleArtifact) -> ModuleArtifact:
        """Validate a restored artifact against its authoritative local manifest."""
        return self.validate_many([artifact])[0]

    def validate_many(
        self, artifacts: Sequence[ModuleArtifact]
    ) -> list[ModuleArtifact]:
        """Validate direct artifacts with one environment check, preserving order.

        Each distinct module is loaded once. Every supplied metadata record is
        compared even when a module occurs more than once. This does not walk
        transitive dependencies; finalization uses validate_closure for that.
        """
        if self._base_environment() != self._environment:
            raise ValueError("Lean project environment changed")
        loaded: dict[str, ModuleArtifact] = {}
        result = []
        for artifact in artifacts:
            name = artifact.module_name
            if name not in loaded:
                loaded[name], _ = self._load(name)
            if loaded[name] != artifact:
                raise ValueError("module metadata differs from admitted artifact")
            result.append(loaded[name])
        return result

    def validate_closure(
        self, artifacts: Sequence[ModuleArtifact]
    ) -> list[ModuleArtifact]:
        """Validate each reachable module once, returning dependency-first order.

        Used at finalization/export, not on every project scheduling quantum.
        Iterative traversal supports deep developments beyond Python recursion.
        """
        self._validate_module_root()
        self.environment.validate()
        roots = {artifact.module_name: artifact for artifact in artifacts}
        result: list[ModuleArtifact] = []
        colors: dict[str, int] = {}
        loaded: dict[str, ModuleArtifact] = {}
        stack = [(name, False) for name in reversed(tuple(roots))]
        while stack:
            name, leaving = stack.pop()
            if leaving:
                colors[name] = 2
                result.append(loaded[name])
                continue
            if colors.get(name) == 2:
                continue
            if colors.get(name) == 1:
                raise ValueError("cycle in compiled module dependencies")
            artifact, record = self._load(name)
            if name in roots and artifact != roots[name]:
                raise ValueError("root metadata differs from admitted artifact")
            loaded[name] = artifact
            colors[name] = 1
            stack.append((name, True))
            stack.extend(
                (dependency, False) for dependency in reversed(record["dependencies"])
            )
        return result

    def _check_inputs(
        self,
        source: str,
        dependencies: Sequence[ModuleArtifact],
        expected_name: str | None,
        expected_statement: str | None,
    ) -> tuple[str, ...]:
        if not isinstance(source, str) or not source.strip():
            raise ValueError("module source must be nonempty")
        if self._base_environment() != self._environment:
            raise ValueError("Lean project environment changed")
        if expected_name is not None and not is_valid_lean_qualified_name(
            expected_name
        ):
            raise ValueError("invalid expected declaration name")
        if expected_statement is not None and (
            not expected_name or not expected_statement.strip()
        ):
            raise ValueError(
                "expected statement requires a declaration name and nonempty type"
            )
        clean = strip_lean_comments_and_string_literals(source)
        if _ACTIVE.search(clean):
            raise ValueError(
                "module contains placeholders or executable metaprogramming"
            )
        for match in re.finditer(r"\bset_option\s+([A-Za-z0-9_.]+)", clean):
            if match[1] not in _SAFE_OPTIONS:
                raise ValueError(f"generated module option is not allowed: {match[1]}")
        selected = set()
        for dependency in dependencies:
            admitted, _ = self._load(dependency.module_name)
            if admitted != dependency:
                raise ValueError("dependency metadata differs from admitted artifact")
            selected.add(dependency.module_name)
        imports = scan_lean_imports(source)
        for name in imports:
            self.environment.validate_automatic_import(name, extra_roots=(self.root,))
            if name.startswith("Formalization."):
                if name not in selected:
                    raise ValueError(f"unselected or unresolved dependency: {name}")
            elif not (
                name in self.trusted_imports
                or name in {"Mathlib", "Lean"}
                or name.startswith(("Mathlib.", "Lean."))
            ):
                raise ValueError(f"untrusted import: {name}")
        if selected != set(imports).intersection(selected):
            raise ValueError("selected dependency is not imported by module")
        return imports

    def _admission_source(self, source: str, imports: Sequence[str]) -> str:
        import_names = ", ".join(f"({_lean_string(name)}).toName" for name in imports)
        return (
            "import Lean\n"
            + "".join(f"import {name}\n" for name in imports)
            + _GUARD
            + f"""
run_cmd do
  unless campaignImportsSafe (← Lean.getEnv) do
    Lean.throwError "base import crosses the generated module namespace"
  let module ← Lean.Parser.testParseModule (← Lean.getEnv) "candidate.lean" {_lean_string(source)}
  let header : Lean.Elab.HeaderSyntax := ⟨module.raw[0]⟩
  let actual := (header.imports (includeInit := false)).map (·.module)
  unless actual == #[{import_names}] do
    Lean.throwError "parsed imports differ from admitted dependency imports"
  for command in module.raw[1].getArgs do
    unless campaignSyntaxSafe command do
      Lean.throwError "prohibited executable source syntax"
    if command.isOfKind ``Lean.Parser.Command.declaration then
      unless [``Lean.Parser.Command.definition, ``Lean.Parser.Command.abbrev,
          ``Lean.Parser.Command.theorem, ``Lean.Parser.Command.structure,
          ``Lean.Parser.Command.inductive, ``Lean.Parser.Command.classInductive,
          ``Lean.Parser.Command.instance].contains command[1].getKind do
        Lean.throwError "unsupported declaration kind"
    else
      unless [``Lean.Parser.Command.namespace, ``Lean.Parser.Command.end,
          ``Lean.Parser.Command.section,
          ``Lean.Parser.Command.open, ``Lean.Parser.Command.variable,
          ``Lean.Parser.Command.universe, ``Lean.Parser.Command.set_option].contains command.getKind do
        Lean.throwError "unsupported generated command: {{command.getKind}}"
"""
        )

    def _audit_source(
        self, name: str, expected_name: str | None, expected_statement: str | None
    ) -> str:
        target = ""
        if expected_name:
            expected_name = _strip_root_prefix(expected_name)
            target = f"""
  let wanted := ({_lean_string(expected_name)}).toName
  unless names.contains wanted do
    Lean.throwError "expected declaration was not introduced by this module"
"""
            if expected_statement is not None:
                if _ACTIVE.search(
                    strip_lean_comments_and_string_literals(expected_statement)
                ):
                    raise ValueError(
                        "expected type contains executable metaprogramming"
                    )
                target += f"""
  let expectedInfo ← Lean.getConstInfo wanted
  Lean.Elab.Command.liftTermElabM <| Lean.Elab.Term.withLevelNames expectedInfo.levelParams do
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term {_lean_string(expected_statement)} with
      | .ok stx => pure stx
      | .error error => Lean.throwError error
    unless campaignSyntaxSafe stx do Lean.throwError "unsafe expected type"
    let expected ← Lean.Elab.Term.withoutErrToSorry do
      Lean.Elab.Term.elabTerm stx (some (Lean.mkSort Lean.Level.zero))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    -- Expected universes are universally quantified, not holes the candidate
    -- may specialize. Generalize them before any comparison with its type.
    let expected ← Lean.Elab.Term.levelMVarToParam (← Lean.instantiateMVars expected)
    if expected.hasMVar || expected.hasSorry || expected.hasFVar then
      Lean.throwError "expected type contains unresolved placeholders"
    -- A more-general theorem may specialize its own universes to the rigid
    -- expected ones, including renamings, repeated levels, and maxima.
    let proof := Lean.mkConst wanted (← Lean.Meta.mkFreshLevelMVarsFor expectedInfo)
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType proof) expected do
      Lean.throwError "compiled target differs from expected statement"
    let proof ← Lean.instantiateMVars proof
    -- Default any candidate universes not fixed by comparison, then recheck;
    -- no expected universe parameter is changed or assignable.
    let proof := proof.replaceLevel fun level =>
      match level with
      | .mvar _ => some Lean.Level.zero
      | _ => none
    if proof.hasMVar || proof.hasSorry || proof.hasFVar then
      Lean.throwError "compiled target proof contains unresolved placeholders"
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType proof) expected do
      Lean.throwError "compiled target differs from expected statement"
    -- Checking the constant alone would not check the promised target. The
    -- annotated let asks the kernel to check that exact, still-rigid type.
    Lean.Meta.checkWithKernel (Lean.mkLet `_campaignChecked expected proof (Lean.mkBVar 0))
"""
        return (
            f"import Lean\nimport {name}\n"
            + _GUARD
            + f"""
run_cmd do
  let env ← Lean.getEnv
  unless campaignImportsSafe env do
    Lean.throwError "base import crosses the generated module namespace"
  let some idx := env.header.moduleNames.findIdx? (· == ({_lean_string(name)}).toName)
    | Lean.throwError "compiled module absent from audit environment"
  let names := env.header.moduleData[idx]!.constNames
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut inventory : Array Lean.Json := #[]
  for name in names do
    let info ← Lean.getConstInfo name
    if info.isUnsafe || info.type.hasSorry || info.type.hasMVar || info.type.hasFVar || info.type.hasLooseBVars then
      Lean.throwError "unsafe or unresolved declaration: {{name}}"
    if let some value := info.value? then
      if value.hasSorry || value.hasMVar || value.hasFVar || value.hasLooseBVars then
        Lean.throwError "unresolved declaration value: {{name}}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError "unapproved axiom {{ax}} in {{name}}"
    let type ← Lean.Elab.Command.liftTermElabM do
      return (← Lean.Meta.ppExpr info.type).pretty
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | _ => "other"
    inventory := inventory.push <| Lean.Json.mkObj [
      ("name", Lean.toJson name.toString), ("type", Lean.toJson type),
      ("kind", Lean.toJson kind), ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
  if inventory.isEmpty then Lean.throwError "module introduces no declarations"
{target}
  Lean.logInfo ("CAMPAIGN_AUDIT:" ++ (Lean.Json.arr inventory).compress)
"""
        )

    async def _run_check(self, source: str, stage: Path, name: str) -> str:
        path = stage / name
        path.write_bytes(source.encode("utf-8"))
        code, output = await self._runner._run_via_lake(
            path,
            timeout_s=self.timeout_s,
            extra_module_paths=(stage, self.root),
        )
        if code:
            raise ValueError(output or f"Lean check failed: {name}")
        return output

    async def compile(
        self,
        source: str,
        *,
        dependencies: Sequence[ModuleArtifact] = (),
        expected_name: str | None = None,
        expected_statement: str | None = None,
    ) -> ModuleArtifact:
        imports = self._check_inputs(
            source, dependencies, expected_name, expected_statement
        )
        source_hash = _hash(source.encode("utf-8"))
        async with self._module_lock(source_hash):
            name = f"Formalization.M_{source_hash}"
            final_source, final_olean, manifest = self._paths(name)
            # Build expected-type code before compilation: even a malicious
            # expected statement cannot trigger source or audit execution.
            audit = self._audit_source(name, expected_name, expected_statement)
            with tempfile.TemporaryDirectory(
                prefix=".stage-", dir=self.root / "Formalization"
            ) as raw:
                stage = Path(raw)
                if manifest.exists():
                    artifact, _ = self._load(name)
                    if expected_name:
                        await self._run_check(audit, stage, "Audit.lean")
                    self._check_inputs(
                        source, dependencies, expected_name, expected_statement
                    )
                    # A prior attempt may have renamed its marker but failed
                    # the final directory barrier. Retry that barrier before
                    # acknowledging even an otherwise valid cache hit.
                    _sync_directory(manifest.parent)
                    return artifact
                await self._run_check(
                    self._admission_source(source, imports), stage, "Admission.lean"
                )
                source_path = stage / "Candidate.lean"
                source_path.write_bytes(source.encode("utf-8"))
                olean_path = stage / "Candidate.olean"
                # Lean resolves a namespace in one search root, not an overlay.
                # Keep the canonical Formalization directory shared. Files are
                # unadmitted until their independently checked manifest exists.
                os.replace(source_path, final_source)
                try:
                    code, output = await self._runner._run_via_lake(
                        final_source,
                        timeout_s=self.timeout_s,
                        output_path=olean_path,
                        extra_module_paths=(self.root,),
                    )
                    if code or not olean_path.is_file():
                        raise ValueError(
                            output or "Lean did not produce a compiled module"
                        )
                    os.replace(olean_path, final_olean)
                    output = await self._run_check(audit, stage, "Audit.lean")
                except BaseException:
                    final_source.unlink(missing_ok=True)
                    final_olean.unlink(missing_ok=True)
                    raise
                rows = [
                    line[len("CAMPAIGN_AUDIT:") :]
                    for line in output.splitlines()
                    if line.startswith("CAMPAIGN_AUDIT:")
                ]
                if len(rows) != 1:
                    raise ValueError("missing or ambiguous module audit\n" + output)
                inventory = json.loads(rows[0])
                # Compilation/audit can run for minutes. Recheck the bound
                # local inputs at publication, not only before those awaits.
                self._check_inputs(
                    source, dependencies, expected_name, expected_statement
                )
                for path in (final_source, final_olean):
                    with path.open("rb") as handle:
                        os.fsync(handle.fileno())
                _sync_directory(final_source.parent)
                artifact = ModuleArtifact(
                    name,
                    source_hash,
                    _hash(final_olean.read_bytes()),
                    final_source,
                    final_olean,
                    tuple(inventory),
                )
                record = {
                    "version": 1,
                    "environment": self._environment,
                    "artifact": artifact.to_dict(),
                    "dependencies": [item.module_name for item in dependencies],
                }
                pending_manifest = stage / "manifest.json"
                with pending_manifest.open("w", encoding="utf-8") as handle:
                    handle.write(
                        json.dumps(record, ensure_ascii=False, indent=2) + "\n"
                    )
                    handle.flush()
                    os.fsync(handle.fileno())
                # Consumers only admit modules with a complete manifest.
                os.replace(pending_manifest, manifest)
                _sync_directory(manifest.parent)
                return artifact
